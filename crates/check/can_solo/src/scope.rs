use bumpalo::collections::Vec;
use bumpalo::{vec, Bump};
use roc_collections::ArenaVecMap;
use roc_error_macros::internal_error;
use roc_module::ident::{Ident, IdentStr, ModuleName};
use roc_module::symbol::{IdentId, ModuleId, ModuleIds, Symbol};
use roc_problem::can::{RuntimeError, ScopeModuleSource};
use roc_region::all::{Loc, Region};
use roc_types::subs::Variable;
use roc_types::types::{EarlyReturnKind, Type};

use bitvec::vec::BitVec;

use crate::alias::{Alias, AliasKind, AliasVar};
use crate::ident_ids::IdentIds;
use crate::module::BuiltinExposedValues;

// ability -> member names
// pub(crate) type PendingAbilitiesInScope = VecMap<Symbol, VecSet<Symbol>>;

pub struct ShadowOfSymbol {
    /// The original symbol that was introduced into scope first.
    pub shadowed_symbol: Symbol,
    /// The new ident that shadowed the original symbol.
    pub shadow_ident: Loc<Ident>,
    /// A new symbol created for the shadow.
    pub shadow_symbol: Symbol,
}

#[derive(Debug)]
pub struct Scope<'a, 's> {
    /// The type aliases currently in scope
    pub aliases: ArenaVecMap<'s, Symbol, Alias<'a>>,

    /// The current module being processed. This will be used to turn
    /// unqualified idents into Symbols.
    home: ModuleId,

    // /// The first `exposed_ident_count` identifiers are exposed
    // exposed_ident_count: usize,
    //
    /// Modules that are imported
    pub modules: ScopeModules<'s>,

    // /// Identifiers that are imported
    // imported_symbols: Vec<'a, (Ident, Symbol, Region)>,
    //
    // /// Shadows of an ability member, for example a local specialization of `eq` for the ability
    // /// member `Eq implements eq : a, a -> Bool where a implements Eq` gets a shadow symbol it can use for its
    // /// implementation.
    // ///
    // /// Only one shadow of an ability member is permitted per scope.
    // shadows: VecMap<Symbol, Loc<Symbol>>,
    //
    /// Identifiers that are in scope, and defined in the current module
    pub locals: ScopedIdentIds<'a, 's>,

    /// Ignored variables (variables that start with an underscore).
    /// We won't intern them because they're only used during canonicalization for error reporting.
    ignored_locals: ArenaVecMap<'s, String, Region>,

    // TODO: is there a better way to handle these?
    pub early_returns: Vec<'s, (Variable, Region, EarlyReturnKind)>,
}

impl<'a, 's> Scope<'a, 's> {
    pub fn new<'b>(
        home: ModuleId,
        module_name: ModuleName,
        builtin_exposed_values: &'b BuiltinExposedValues<'b>,
        arena: &'s Bump,
    ) -> Scope<'a, 's> {
        // Add all `Apply` types.
        // let default_imports = Symbol::apply_types_in_scope()
        //     .into_iter()
        //     .map(|(a, (b, c))| (a, b, c))
        //     .collect();

        Scope {
            home,
            // exposed_ident_count: initial_ident_ids.len(),
            locals: ScopedIdentIds::new_in(home, arena),
            aliases: ArenaVecMap::new_in(arena),
            // shadows: ArenaVecMap::new_in(arena),
            modules: ScopeModules::new_in(home, module_name, arena),
            // imported_symbols: default_imports,
            ignored_locals: ArenaVecMap::new_in(arena),
            early_returns: Vec::new_in(arena),
        }
    }

    pub fn lookup(&self, ident: &Ident, region: Region) -> Result<Symbol, RuntimeError> {
        self.lookup_str(ident.as_str(), region)
    }

    // pub fn add_docs_imports(&mut self) {
    //     self.imported_symbols
    //         .push(("Dict".into(), Symbol::DICT_DICT, Region::zero()));
    //     self.imported_symbols
    //         .push(("Set".into(), Symbol::SET_SET, Region::zero()));
    // }

    pub fn lookup_str(&self, ident: &str, region: Region) -> Result<Symbol, RuntimeError> {
        use ContainsIdent::*;

        match self.scope_contains_ident(ident) {
            InScope(symbol, _) => Ok(symbol),
            NotInScope(_) | NotPresent => {
                // identifier not found

                let error = RuntimeError::LookupNotInScope {
                    loc_name: Loc {
                        region,
                        value: Ident::from(ident),
                    },
                    suggestion_options: self.idents_in_scope().map(|v| v.as_ref().into()).collect(),
                    // Check if the user just forgot to remove an underscore from an ignored identifier
                    underscored_suggestion_region: self.lookup_ignored_local(ident),
                };

                Err(error)
            }
        }
    }

    fn idents_in_scope(&self) -> impl Iterator<Item = Ident> + '_ {
        let it1 = self.locals.idents_in_scope();
        let it2 = self.imported_symbols.iter().map(|t| t.0.clone());

        it2.chain(it1)
    }

    /// Check if there is an custom type alias referenced by `custom_ref` referenced in the
    /// current scope. E.g. `@Age` must reference an opaque `Age` declared in this module, not any
    /// other!
    pub fn lookup_custom_ref(
        &self,
        opaque_ref: &str,
        lookup_region: Region,
    ) -> Result<(Symbol, &Alias), RuntimeError> {
        debug_assert!(opaque_ref.starts_with('@'));

        let opaque_str = &opaque_ref[1..];
        let opaque = opaque_str.into();

        match self.locals.has_in_scope(&opaque) {
            Some((symbol, _)) => match self.lookup_custom_alias(symbol) {
                Ok(alias) => Ok((symbol, alias)),
                Err(opt_alias_def_region) => {
                    Err(self.opaque_not_defined_error(opaque, lookup_region, opt_alias_def_region))
                }
            },
            None => {
                // opaque types can only be wrapped/unwrapped in the scope they are defined in (and below)
                let error = if let Some((_, decl_region)) = self.has_imported_symbol(opaque_str) {
                    // specific error for when the opaque is imported, which definitely does not work
                    RuntimeError::OpaqueOutsideScope {
                        opaque,
                        referenced_region: lookup_region,
                        imported_region: decl_region,
                    }
                } else {
                    self.opaque_not_defined_error(opaque, lookup_region, None)
                };

                Err(error)
            }
        }
    }

    fn lookup_custom_alias(&self, symbol: Symbol) -> Result<&Alias, Option<Region>> {
        match self.aliases.get(&symbol) {
            None => Err(None),

            Some(alias) => match alias.kind {
                AliasKind::Custom => Ok(alias),
                AliasKind::Structural | AliasKind::Builtin => Err(Some(alias.header_region())),
            },
        }
    }

    fn is_custom(&self, ident_id: IdentId, string: &str) -> Option<Box<str>> {
        if string.is_empty() {
            return None;
        }

        let symbol = Symbol::new(self.home, ident_id);

        if let Some(AliasKind::Opaque) = self.aliases.get(&symbol).map(|alias| alias.kind) {
            Some(string.into())
        } else {
            None
        }
    }

    fn custom_not_defined_error(
        &self,
        custom: Ident,
        lookup_region: Region,
        opt_defined_alias: Option<Region>,
    ) -> RuntimeError {
        // for customs, we only look at the locals because customs can only be matched
        // on in the module that defines them.
        let customs_in_scope = self
            .locals
            .ident_ids
            .ident_strs()
            .filter_map(|(ident_id, string)| self.is_custom(ident_id, string))
            .collect();

        RuntimeError::CustomNotDefined {
            usage: Loc::at(lookup_region, custom),
            customs_in_scope,
            opt_defined_alias,
        }
    }

    fn has_imported_symbol(&self, ident: &str) -> Option<(Symbol, Region)> {
        self.imported_symbols
            .iter()
            .find_map(|(import, symbol, original_region)| {
                if ident == import.as_str() {
                    match self.modules.lookup_by_id(&symbol.module_id()) {
                        Some(module) => Some((module.into_symbol(*symbol), *original_region)),
                        None => Some((*symbol, *original_region)),
                    }
                } else {
                    None
                }
            })
    }

    /// Is an identifier in scope, either in the locals or imports
    fn scope_contains_ident(&self, ident: &str) -> ContainsIdent {
        // exposed imports are likely to be small
        match self.has_imported_symbol(ident) {
            Some((symbol, region)) => ContainsIdent::InScope(symbol, region),
            None => self.locals.contains_ident(ident),
        }
    }

    fn introduce_help(&mut self, ident: &str, region: Region) -> Result<Symbol, (Symbol, Region)> {
        match self.scope_contains_ident(ident) {
            ContainsIdent::InScope(original_symbol, original_region) => {
                // the ident is already in scope; up to the caller how to handle that
                // (usually it's shadowing, but it is valid to shadow ability members)
                Err((original_symbol.symbol, original_region))
            }
            ContainsIdent::NotPresent => {
                // We know nothing about this ident yet; introduce it to the scope
                let ident_id = self.locals.introduce_into_scope(ident, region);
                Ok(Symbol::new(self.home, ident_id))
            }
            ContainsIdent::NotInScope(existing) => {
                // The ident is not in scope, but its name is already in the string interner
                if existing.index() < self.exposed_ident_count {
                    // if the identifier is exposed, use the IdentId we already have for it
                    // other modules depend on the symbol having that IdentId
                    let symbol = Symbol::new(self.home, existing);

                    self.locals.in_scope.set(existing.index(), true);
                    self.locals.regions[existing.index()] = region;

                    Ok(symbol)
                } else {
                    // create a new IdentId that under the hood uses the same string bytes as an existing one
                    let ident_id = self.locals.introduce_into_scope_duplicate(existing, region);

                    Ok(Symbol::new(self.home, ident_id))
                }
            }
        }
    }

    /// Introduce a new ident to scope.
    ///
    /// Returns Err if this would shadow an existing ident, including the
    /// Symbol and Region of the ident we already had in scope under that name.
    ///
    /// If this ident shadows an existing one, a new ident is allocated for the shadow. This is
    /// done so that all identifiers have unique symbols, which is important in particular when
    /// we generate code for value identifiers.
    /// If this behavior is undesirable, use [`Self::introduce_without_shadow_symbol`].
    pub fn introduce(
        &mut self,
        ident: Ident,
        region: Region,
    ) -> Result<Symbol, (Loc<Symbol>, Loc<Ident>, Symbol)> {
        self.introduce_str(ident.as_str(), region)
    }

    pub fn introduce_str(
        &mut self,
        ident: &str,
        region: Region,
    ) -> Result<Symbol, (Loc<Symbol>, Loc<Ident>, Symbol)> {
        match self.introduce_help(ident, region) {
            Ok(symbol) => Ok(symbol),
            Err((shadowed_symbol, original_region)) => {
                let shadow = Loc {
                    value: Ident::from(ident),
                    region,
                };
                let symbol = self.locals.scopeless_symbol(ident, region);

                Err((Loc::at(original_region, shadowed_symbol), shadow, symbol))
            }
        }
    }

    /// Like [Self::introduce], but does not introduce a new symbol for the shadowing symbol.
    pub fn introduce_without_shadow_symbol(
        &mut self,
        ident: &Ident,
        region: Region,
    ) -> Result<Symbol, (Symbol, Region, Loc<Ident>)> {
        match self.introduce_help(ident.as_str(), region) {
            Err((symbol, original_region)) => {
                let shadow = Loc {
                    value: ident.clone(),
                    region,
                };
                Err((symbol, original_region, shadow))
            }
            Ok(symbol) => Ok(symbol),
        }
    }

    /// Create a new symbol, but don't add it to the scope (yet)
    ///
    /// Used for record guards like { x: Just _ } where the `x` is not added to the scope,
    /// but also in other places where we need to create a symbol and we don't have the right
    /// scope information yet. An identifier can be introduced later, and will use the same IdentId
    pub fn scopeless_symbol(&mut self, ident: &Ident, region: Region) -> Symbol {
        self.locals.scopeless_symbol(ident.as_str(), region)
    }

    /// Import a Symbol from another module into this module's top-level scope.
    ///
    /// Returns Err if this would shadow an existing ident, including the
    /// Symbol and Region of the ident we already had in scope under that name.
    pub fn import_symbol(
        &mut self,
        ident: Ident,
        symbol: Symbol,
        region: Region,
    ) -> Result<(), (Symbol, Region)> {
        match self.scope_contains_ident(ident.as_str()) {
            ContainsIdent::InScope(symbol, region) => Err((symbol, region)),
            ContainsIdent::NotPresent | ContainsIdent::NotInScope(_) => {
                self.imported_symbols.push((ident, symbol, region));
                Ok(())
            }
        }
    }

    pub fn add_alias(
        &mut self,
        name: Symbol,
        region: Region,
        vars: Vec<Loc<AliasVar>>,
        infer_ext_in_output_variables: Vec<Variable>,
        typ: Type,
        kind: AliasKind,
    ) {
        let alias = create_alias(name, region, vars, infer_ext_in_output_variables, typ, kind);
        self.aliases.insert(name, alias);
    }

    pub fn lookup_alias(&self, symbol: Symbol) -> Option<&Alias> {
        self.aliases.get(&symbol)
    }

    pub fn contains_alias(&mut self, name: Symbol) -> bool {
        self.aliases.contains_key(&name)
    }

    /// Enter an inner scope within a definition, e.g. a def or when block.
    pub fn inner_def_scope<F, T>(&mut self, f: F) -> T
    where
        F: FnOnce(&mut Scope) -> T,
    {
        // TODO:add a new ScopeLevel, then run f, then remove that ScopeLevel
        //
        // store enough information to roll back to the original outer scope
        //
        // - abilities_store: ability definitions not allowed in inner scopes
        // - locals: everything introduced in the inner scope is marked as not in scope in the rollback
        // - imports: everything that was imported in the inner scope is removed in the rollback
        // - aliases: stored in a VecMap, we just discard anything added in an inner scope
        // - exposed_ident_count: unchanged
        // - home: unchanged
        let aliases_count = self.aliases.len();
        let ignored_locals_count = self.ignored_locals.len();
        let locals_snapshot = self.locals.in_scope.len();
        let imported_symbols_snapshot = self.imported_symbols.len();
        let imported_modules_snapshot = self.modules.len();

        let result = f(self);

        self.aliases.truncate(aliases_count);
        self.ignored_locals.truncate(ignored_locals_count);
        self.imported_symbols.truncate(imported_symbols_snapshot);
        self.modules.truncate(imported_modules_snapshot);

        // anything added in the inner scope is no longer in scope now
        for i in locals_snapshot..self.locals.in_scope.len() {
            self.locals.in_scope.set(i, false);
        }

        result
    }

    /// Enter an inner scope within a child function, e.g. a closure body.
    pub fn inner_function_scope<F, T>(&mut self, f: F) -> T
    where
        F: FnOnce(&mut Scope) -> T,
    {
        let early_returns_snapshot = std::mem::take(&mut self.early_returns);

        let result = self.inner_def_scope(f);

        self.early_returns = early_returns_snapshot;

        result
    }

    pub fn register_debug_idents(&self) {
        self.home.register_debug_idents(&self.locals.ident_ids)
    }

    /// Generates a unique, new symbol like "1" or "5",
    /// using the home module as the module_id.
    ///
    /// This is used, for example, during canonicalization of an Expr::Closure
    /// to generate a unique symbol to refer to that closure.
    pub fn gen_unique_symbol(&mut self) -> Symbol {
        Symbol::new(self.home, self.locals.gen_unique())
    }

    /// Generates a unique new symbol and return the symbol's unqualified identifier name.
    pub fn gen_unique_symbol_name(&mut self) -> &str {
        let ident_id = self.locals.gen_unique();
        self.locals.ident_ids.get_name(ident_id).unwrap()
    }

    /// Introduce a new ignored variable (variable starting with an underscore).
    /// The underscore itself should not be included in `ident`.
    pub fn introduce_ignored_local(&mut self, ident: &str, region: Region) {
        self.ignored_locals.insert(ident.to_owned(), region);
    }

    /// Lookup an ignored variable (variable starting with an underscore).
    /// The underscore itself should not be included in `ident`.
    /// Returns the source code region of the ignored variable if it's found.
    pub fn lookup_ignored_local(&self, ident: &str) -> Option<Region> {
        self.ignored_locals.get(&ident.to_owned()).copied()
    }
}

pub fn create_alias<'a>(
    name: Symbol,
    region: Region,
    vars: Vec<'a, Loc<AliasVar>>,
    infer_ext_in_output_variables: Vec<Variable>,
    typ: Type,
    kind: AliasKind,
) -> Alias<'a> {
    let roc_types::types::VariableDetail {
        type_variables,
        lambda_set_variables,
        recursion_variables,
    } = typ.variables_detail();

    debug_assert!({
        let mut hidden = type_variables;

        for var in (vars.iter().map(|lv| lv.value.var))
            .chain(recursion_variables.iter().copied())
            .chain(infer_ext_in_output_variables.iter().copied())
        {
            hidden.remove(&var);
        }

        if !hidden.is_empty() {
            internal_error!(
                "Found unbound type variables {:?} \n in type alias {:?} {:?} {:?} : {:?}",
                hidden,
                name,
                &vars,
                &infer_ext_in_output_variables,
                &typ
            )
        }

        true
    });

    Alias {
        region,
        type_variables: vars,
        infer_ext_in_output_variables,
        recursion_variables,
        typ,
        kind,
    }
}

#[derive(Debug)]
enum ContainsIdent {
    InScope(Symbol, Region),
    NotInScope(IdentId),
    NotPresent,
}

#[derive(Debug)]
pub struct ScopeLevel<'a, 's> {
    names: Vec<'s, &'a str>,
    ident_ids: Vec<'s, IdentId>,
    in_scope: BitVec,
    regions: Vec<'s, Region>,
}

impl<'a, 's> ScopeLevel<'a, 's> {
    pub fn new_in(arena: &'s Bump) -> Self {
        ScopeLevel {
            names: Vec::new_in(arena),
            ident_ids: Vec::new_in(arena),
            in_scope: BitVec::new(),
            regions: Vec::new_in(arena),
        }
    }

    pub fn add_ident(&mut self, name: &'a str, id: IdentId, in_scope: bool, region: Region) {
        self.names.push(name);
        self.ident_ids.push(id);
        self.in_scope.push(false);
        self.regions.push(region);
    }
}

#[derive(Debug)]
pub struct ScopedIdentIds<'a, 's> {
    arena: &'s Bump,
    home: ModuleId,
    all_ident_ids: &'a mut IdentIds<'a>,
    levels: Vec<'s, ScopeLevel<'a, 's>>,
}

impl<'a, 's> ScopedIdentIds<'a, 's> {
    fn new_in(home: ModuleId, ident_ids: &'a mut IdentIds<'a>, arena: &'s Bump) -> Self {
        let first_level = ScopeLevel::new_in(arena);

        Self {
            arena,
            home,
            all_ident_ids: ident_ids,
            levels: vec![in arena; first_level],
        }
    }

    fn has_in_scope(&self, ident: &Ident) -> Option<(Symbol, Region)> {
        match self.contains_ident(ident.as_str()) {
            ContainsIdent::InScope(symbol, region) => Some((symbol.symbol, region)),
            ContainsIdent::NotInScope(_) | ContainsIdent::NotPresent => None,
        }
    }

    fn contains_ident(&self, ident: &str) -> ContainsIdent {
        let mut result = ContainsIdent::NotPresent;

        for level in self.levels.iter().rev() {
            for ident_index in 0..level.ident_ids.len() {
                let name = level.names[ident_index];
                if ident != name {
                    continue;
                }

                let ident_id = level.ident_ids[ident_index];

                if level.in_scope[ident_index] {
                    return ContainsIdent::InScope(
                        Symbol::new(self.home, ident_id),
                        level.regions[ident_index],
                    );
                } else {
                    result = ContainsIdent::NotInScope(ident_id)
                }
            }
        }

        result
    }

    fn push_scope_level(&mut self) {
        let next_level = ScopeLevel::new_in(self.arena);
        self.levels.push(next_level);
    }

    fn pop_scope_level(&mut self) {
        self.levels.pop();
    }

    // TODO: should this just return `&str`?
    fn idents_in_scope(&self) -> impl Iterator<Item = Ident> + '_ {
        self.levels.iter().flat_map(|level| {
            level
                .names
                .iter()
                .zip(level.in_scope.iter())
                .filter_map(|(name, in_scope)| {
                    if *in_scope {
                        Some(Ident::from(IdentStr::from_str(name)))
                    } else {
                        None
                    }
                })
        })
    }

    fn introduce_into_scope(&mut self, ident_name: &str, region: Region) -> IdentId {
        let id = self.all_ident_ids.add_str(ident_name);

        if let Some(level) = self.levels.last_mut() {
            level.add_ident(ident_name, id, true, region);
        }

        id
    }

    fn introduce_into_scope_duplicate(&mut self, existing: IdentId, region: Region) -> IdentId {
        let id = self.all_ident_ids.duplicate_ident(existing);

        if let Some(level) = self.levels.last_mut() {
            level.add_ident(ident_name, id, true, region);
        }

        id
    }

    /// Adds an IdentId, but does not introduce it to the scope
    fn scopeless_symbol(&mut self, ident_name: &str, region: Region) -> Symbol {
        let id = self.all_ident_ids.add_str(ident_name);

        if let Some(level) = self.levels.last_mut() {
            level.add_ident(ident_name, id, false, region);
        }

        Symbol::new(self.home, id)
    }

    fn gen_unique(&mut self) -> IdentId {
        let id = self.all_ident_ids.gen_unique();

        if let Some(level) = self.levels.last_mut() {
            level.add_ident("", id, false, Region::zero());
        }

        id
    }
}

#[derive(Debug, Clone)]
pub struct ScopeModules<'s> {
    latest_id: ModuleId,
    /// The ids of all modules in scope
    ids: Vec<'s, ModuleId>,
    /// The alias or original name of each module in scope
    names: Vec<'s, ModuleName>,
    /// Why is this module in scope?
    sources: Vec<'s, ScopeModuleSource>,
}

impl<'s> ScopeModules<'s> {
    pub fn new_in(home_id: ModuleId, home_name: ModuleName, arena: &'s Bump) -> Self {
        let builtins = ModuleIds::default();
        let builtins_iter = builtins.iter();
        let count = builtins_iter.len();

        let mut ids = Vec::with_capacity_in(count + 1, arena);
        let mut names = Vec::with_capacity_in(count + 1, arena);
        let mut sources = vec![in arena; ScopeModuleSource::Builtin; count];

        for (module_id, module_name) in builtins_iter {
            ids.push(module_id);
            names.push(module_name.clone());
        }

        if !home_id.is_builtin() {
            ids.push(home_id);
            names.push(home_name);
            sources.push(ScopeModuleSource::Current);
        }

        Self {
            latest_id: home_id,
            ids,
            names,
            sources,
        }
    }

    pub fn lookup(&self, module_name: &ModuleName) -> Option<ModuleId> {
        self.names
            .iter()
            .position(|name| name == module_name)
            .map(|index| self.ids[index])
    }

    pub fn contains_id(&self, module_id: &ModuleId) -> bool {
        self.ids.contains(module_id)
    }

    pub fn available_names(&self) -> impl Iterator<Item = &ModuleName> {
        self.names.iter()
    }

    pub fn insert(
        &mut self,
        module_name: ModuleName,
        module_id: ModuleId,
        params: Option<(Variable, Symbol)>,
        region: Region,
    ) -> Result<(), ScopeModuleSource> {
        if let Some(index) = self.names.iter().position(|name| name == &module_name) {
            if self.ids[index] == module_id {
                return Ok(());
            }

            return Err(self.sources[index]);
        }

        self.ids.push(module_id);
        self.names.push(module_name);
        self.sources.push(ScopeModuleSource::Import(region));
        self.params.push(params);
        Ok(())
    }

    pub fn len(&self) -> usize {
        debug_assert_eq!(self.ids.len(), self.names.len());
        debug_assert_eq!(self.ids.len(), self.sources.len());
        debug_assert_eq!(self.ids.len(), self.params.len());

        self.ids.len()
    }

    pub fn is_empty(&self) -> bool {
        self.ids.is_empty()
    }

    pub fn truncate(&mut self, len: usize) {
        self.ids.truncate(len);
        self.names.truncate(len);
        self.sources.truncate(len);
        self.params.truncate(len);
    }
}

// #[cfg(test)]
// mod test {
//     use super::*;
//     use roc_module::symbol::ModuleIds;
//     use roc_region::all::Position;

//     use pretty_assertions::{assert_eq, assert_ne};

//     #[test]
//     fn scope_contains_introduced() {
//         let _register_module_debug_names = ModuleIds::default();
//         let mut scope = Scope::new(
//             ModuleId::ATTR,
//             "#Attr".into(),
//             IdentIds::default(),
//             PendingAbilitiesStore::default(),
//         );

//         let region = Region::zero();
//         let ident = Ident::from("mezolit");

//         assert!(scope.lookup(&ident, region).is_err());

//         assert!(scope.introduce(ident.clone(), region).is_ok());

//         assert!(scope.lookup(&ident, region).is_ok());
//     }

//     #[test]
//     fn second_introduce_shadows() {
//         let _register_module_debug_names = ModuleIds::default();
//         let mut scope = Scope::new(
//             ModuleId::ATTR,
//             "#Attr".into(),
//             IdentIds::default(),
//             PendingAbilitiesStore::default(),
//         );

//         let region1 = Region::from_pos(Position { offset: 10 });
//         let region2 = Region::from_pos(Position { offset: 20 });
//         let ident = Ident::from("mezolit");

//         assert!(scope.lookup(&ident, Region::zero()).is_err());

//         let first = scope.introduce(ident.clone(), region1).unwrap();
//         let (original, _ident, shadow_symbol) =
//             scope.introduce(ident.clone(), region2).unwrap_err();

//         scope.register_debug_idents();

//         assert_ne!(first, shadow_symbol);
//         assert_eq!(original.region, region1);

//         let lookup = scope.lookup(&ident, Region::zero()).unwrap();

//         assert_eq!(first, lookup.symbol);
//     }

//     #[test]
//     fn inner_def_scope_does_not_influence_outer() {
//         let _register_module_debug_names = ModuleIds::default();
//         let mut scope = Scope::new(
//             ModuleId::ATTR,
//             "#Attr".into(),
//             IdentIds::default(),
//             PendingAbilitiesStore::default(),
//         );

//         let region = Region::zero();
//         let ident = Ident::from("uránia");

//         assert!(scope.lookup(&ident, region).is_err());

//         scope.inner_def_scope(|inner| {
//             assert!(inner.introduce(ident.clone(), region).is_ok());
//         });

//         assert!(scope.lookup(&ident, region).is_err());
//     }

//     #[test]
//     fn default_idents_in_scope() {
//         let _register_module_debug_names = ModuleIds::default();
//         let scope = Scope::new(
//             ModuleId::ATTR,
//             "#Attr".into(),
//             IdentIds::default(),
//             PendingAbilitiesStore::default(),
//         );

//         let idents: Vec<_> = scope.idents_in_scope().collect();

//         assert_eq!(
//             &idents,
//             &[Ident::from("Str"), Ident::from("List"), Ident::from("Box"),]
//         );
//     }

//     #[test]
//     fn idents_with_inner_def_scope() {
//         let _register_module_debug_names = ModuleIds::default();
//         let mut scope = Scope::new(
//             ModuleId::ATTR,
//             "#Attr".into(),
//             IdentIds::default(),
//             PendingAbilitiesStore::default(),
//         );

//         let idents: Vec<_> = scope.idents_in_scope().collect();

//         assert_eq!(
//             &idents,
//             &[Ident::from("Str"), Ident::from("List"), Ident::from("Box"),]
//         );

//         let builtin_count = idents.len();

//         let region = Region::zero();

//         let ident1 = Ident::from("uránia");
//         let ident2 = Ident::from("malmok");
//         let ident3 = Ident::from("Járnak");

//         scope.introduce(ident1.clone(), region).unwrap();
//         scope.introduce(ident2.clone(), region).unwrap();
//         scope.introduce(ident3.clone(), region).unwrap();

//         let idents: Vec<_> = scope.idents_in_scope().collect();

//         assert_eq!(
//             &idents[builtin_count..],
//             &[ident1.clone(), ident2.clone(), ident3.clone(),]
//         );

//         scope.inner_def_scope(|inner| {
//             let ident4 = Ident::from("Ångström");
//             let ident5 = Ident::from("Sirály");

//             inner.introduce(ident4.clone(), region).unwrap();
//             inner.introduce(ident5.clone(), region).unwrap();

//             let idents: Vec<_> = inner.idents_in_scope().collect();

//             assert_eq!(
//                 &idents[builtin_count..],
//                 &[
//                     ident1.clone(),
//                     ident2.clone(),
//                     ident3.clone(),
//                     ident4,
//                     ident5
//                 ]
//             );
//         });

//         let idents: Vec<_> = scope.idents_in_scope().collect();

//         assert_eq!(&idents[builtin_count..], &[ident1, ident2, ident3,]);
//     }

//     #[test]
//     fn import_is_in_scope() {
//         let _register_module_debug_names = ModuleIds::default();
//         let mut scope = Scope::new(
//             ModuleId::ATTR,
//             "#Attr".into(),
//             IdentIds::default(),
//             PendingAbilitiesStore::default(),
//         );

//         let ident = Ident::from("product");
//         let symbol = Symbol::LIST_PRODUCT;
//         let region = Region::zero();

//         assert!(scope.lookup(&ident, region).is_err());

//         assert!(scope.import_symbol(ident.clone(), symbol, region).is_ok());

//         assert!(scope.lookup(&ident, region).is_ok());

//         assert!(scope.idents_in_scope().any(|x| x == ident));
//     }

//     #[test]
//     fn shadow_of_import() {
//         let _register_module_debug_names = ModuleIds::default();
//         let mut scope = Scope::new(
//             ModuleId::ATTR,
//             "#Attr".into(),
//             IdentIds::default(),
//             PendingAbilitiesStore::default(),
//         );

//         let ident = Ident::from("product");
//         let symbol = Symbol::LIST_PRODUCT;

//         let region1 = Region::from_pos(Position { offset: 10 });
//         let region2 = Region::from_pos(Position { offset: 20 });

//         scope.import_symbol(ident.clone(), symbol, region1).unwrap();

//         let (original, _ident, shadow_symbol) =
//             scope.introduce(ident.clone(), region2).unwrap_err();

//         scope.register_debug_idents();

//         assert_ne!(symbol, shadow_symbol);
//         assert_eq!(original.region, region1);

//         let lookup = scope.lookup(&ident, Region::zero()).unwrap();

//         assert_eq!(symbol, lookup.symbol);
//     }
// }
