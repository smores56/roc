use std::path::Path;

use crate::alias::{Alias, AliasMethod};
use crate::annotation::{canonicalize_annotation, AnnotationFor};
use crate::def::{canonicalize_defs, report_unused_imports, sort_top_level_can_defs, Def, DefKind};
use crate::env::Env;
use crate::expr::Declarations;
use crate::ident_ids::IdentIds;
use crate::pattern::{Pattern, RecordDestruct};
use crate::procedure::References;
use crate::scope::Scope;

use bumpalo::collections::Vec;
use bumpalo::Bump;
use roc_collections::{ArenaVecMap, ArenaVecSet};
use roc_error_macros::internal_error;
use roc_module::ident::{Ident, Lowercase, ModuleName};
use roc_module::symbol::{IdentId, ModuleId, Symbol};
use roc_parse::ast::Defs;
use roc_parse::header::{ExposedName, HeaderType, TypedIdent};
use roc_parse::ident::UppercaseIdent;
use roc_parse::pattern::PatternType;
use roc_problem::can::{Problem, RuntimeError};
use roc_region::all::{Loc, Region};
use roc_types::subs::{ExposedTypesStorageSubs, Subs, VarStore, Variable};
use roc_types::types::Type;

// TODO: is this needed?
//
/// The types of all exposed values/functions of a collection of modules
#[derive(Clone, Debug)]
pub struct ExposedByModule<'a> {
    arena: &'a Bump,
    exposed: ArenaVecMap<'a, ModuleId, ExposedModuleTypes>,
}

impl<'a> ExposedByModule<'a> {
    pub fn new_in(arena: &'a Bump) -> Self {
        Self {
            arena,
            exposed: ArenaVecMap::new_in(arena),
        }
    }

    pub fn insert(&mut self, module_id: ModuleId, exposed: ExposedModuleTypes) {
        self.exposed.insert(module_id, exposed);
    }

    pub fn get(&self, module_id: &ModuleId) -> Option<&ExposedModuleTypes> {
        self.exposed.get(module_id)
    }

    /// Convenient when you need mutable access to the StorageSubs in the ExposedModuleTypes
    pub fn get_mut(&mut self, module_id: &ModuleId) -> Option<&mut ExposedModuleTypes> {
        self.exposed.get_mut(module_id)
    }

    /// Create a clone of `self` that has just a subset of the modules
    ///
    /// Useful when we know what modules a particular module imports, and want just
    /// the exposed types for those exposed modules.
    pub fn retain_modules(&self, it: impl Iterator<Item = &'a ModuleId>) -> Self {
        let mut output = Self::new_in(self.arena);

        for module_id in it {
            match self.exposed.get(module_id) {
                None => {
                    internal_error!("Module {:?} did not register its exposed values", module_id)
                }
                Some(exposed_types) => {
                    output.exposed.insert(*module_id, exposed_types.clone());
                }
            }
        }

        output
    }

    pub fn iter_all(&self) -> impl Iterator<Item = (&ModuleId, &ExposedModuleTypes)> {
        self.exposed.iter()
    }

    /// # Safety
    ///
    /// May only be called when the exposed types of a modules are no longer needed, or may be
    /// transitioned into another context.
    pub unsafe fn remove(&mut self, module_id: &ModuleId) -> Option<ExposedModuleTypes> {
        self.exposed.remove(module_id).map(|(id, types)| types)
    }
}

#[derive(Clone, Debug, Default)]
pub struct ExposedForModule<'a> {
    pub exposed_by_module: ExposedByModule<'a>,
    pub imported_values: Vec<'a, Symbol>,
}

impl<'a> ExposedForModule<'a> {
    pub fn new(
        it: impl Iterator<Item = &'a Symbol>,
        exposed_by_module: ExposedByModule,
        arena: &'a Bump,
    ) -> Self {
        let mut imported_values = Vec::new_in(arena);

        for symbol in it {
            let module = exposed_by_module.exposed.get(&symbol.module_id());
            if let Some(ExposedModuleTypes { .. }) = module {
                imported_values.push(*symbol);
            } else {
                continue;
            }
        }

        Self {
            imported_values,
            exposed_by_module,
        }
    }
}

/// The types of all exposed values/functions of a module. This includes ability member
/// specializations.
#[derive(Clone, Debug)]
pub struct ExposedModuleTypes {
    pub exposed_types_storage_subs: ExposedTypesStorageSubs,
}

#[derive(Debug)]
pub struct AliasWithMethods<'a> {
    pub exposed: bool,
    pub alias: Alias<'a>,
    pub methods: &'a [AliasMethod],
}

#[derive(Debug)]
pub struct Module<'a> {
    pub module_id: ModuleId,
    pub exposed_imports: ArenaVecMap<'a, Symbol, Region>,
    pub exposed_symbols: ArenaVecSet<'a, Symbol>,
    pub referenced_values: ArenaVecSet<'a, Symbol>,
    pub aliases: ArenaVecMap<'a, Symbol, AliasWithMethods<'a>>,
    pub rigid_variables: RigidVariables<'a>,
    pub loc_expects: ArenaVecMap<'a, Region, Vec<'a, ExpectLookup>>,
    pub has_dbgs: bool,
    pub module_params: Option<ModuleParams<'a>>,
}

#[derive(Debug, Clone)]
pub struct ModuleParams<'a> {
    pub region: Region,
    pub whole_symbol: Symbol,
    pub whole_var: Variable,
    pub record_var: Variable,
    pub record_ext_var: Variable,
    pub destructs: &'a [Loc<RecordDestruct<'a>>],
    // used while lowering passed functions
    pub arity_by_name: ArenaVecMap<'a, IdentId, usize>,
}

impl<'a> ModuleParams<'a> {
    pub fn pattern(&self) -> Loc<Pattern<'a>> {
        let record_pattern = Pattern::RecordDestructure {
            whole_var: self.record_var,
            ext_var: self.record_ext_var,
            destructs: self.destructs,
        };
        let loc_record_pattern = Loc::at(self.region, record_pattern);

        let as_pattern = Pattern::As(Box::new(loc_record_pattern), self.whole_symbol);
        Loc::at(self.region, as_pattern)
    }
}

#[derive(Debug)]
pub struct RigidVariables<'a> {
    pub named: ArenaVecMap<'a, Variable, Lowercase>,
    pub named_with_methods: ArenaVecMap<'a, Variable, (Lowercase, Vec<'a, AliasMethod>)>,
    pub wildcards: ArenaVecSet<'a, Variable>,
}

impl<'a> RigidVariables<'a> {
    pub fn new_in(arena: &'a Bump) -> Self {
        Self {
            named: ArenaVecMap::new_in(arena),
            named_with_methods: ArenaVecMap::new_in(arena),
            wildcards: ArenaVecSet::new_in(arena),
        }
    }
}

#[derive(Debug)]
pub struct ModuleOutput<'a, 's> {
    pub aliases: ArenaVecMap<'a, Symbol, Alias<'a>>,
    pub rigid_variables: RigidVariables<'a>,
    pub module_params: Option<ModuleParams<'a>>,
    pub declarations: Declarations,
    pub exposed_imports: ArenaVecMap<'a, Symbol, Region>,
    pub exposed_symbols: ArenaVecSet<'a, Symbol>,
    pub problems: Vec<'a, Problem>,
    pub referenced_values: ArenaVecSet<'a, Symbol>,
    pub symbols_from_requires: std::vec::Vec<(Loc<Symbol>, Loc<Type>)>,
    pub pending_methods: ArenaVecMap<'a, Symbol, Vec<'a, AliasMethod>>,
    pub scope: Scope<'a, 's>,
    pub loc_expects: ArenaVecMap<'a, Region, std::vec::Vec<ExpectLookup>>,
    pub has_dbgs: bool,
}

// #[derive(Debug)]
// pub struct Module<'a> {
//     pub module_id: ModuleId,
//     pub exposed_imports: ArenaVecMap<'a, Symbol, Region>,
//     pub exposed_symbols: ArenaVecSet<'a, Symbol>,
//     pub referenced_values: ArenaVecSet<'a, Symbol>,
//     /// all aliases. `bool` indicates whether it is exposed
//     pub aliases: ArenaVecMap<'a, Symbol, (bool, Alias)>,
//     pub alias_methods: ArenaVecMap<'a, Symbol, &'a [AliasMethod]>,
//     pub rigid_variables: RigidVariables,
//     pub loc_expects: ArenaVecMap<'a, Region, Vec<'a, ExpectLookup>>,
//     pub has_dbgs: bool,
//     pub module_params: Option<ModuleParams<'a>>,
// }

fn has_no_implementation(expr: &Expr) -> bool {
    match expr {
        Expr::RuntimeError(RuntimeError::NoImplementationNamed { .. }) => true,
        Expr::Closure(closure_data)
            if matches!(
                closure_data.loc_body.value,
                Expr::RuntimeError(RuntimeError::NoImplementationNamed { .. })
            ) =>
        {
            true
        }

        _ => false,
    }
}

pub struct BuiltinExposedValues<'b> {
    aliases: ArenaVecMap<'b, Symbol, Alias<'b>>,
    alias_methods: ArenaVecMap<'b, Symbol, &'b [AliasMethod]>,
    // values: ArenaVecMap,
}

pub struct InitialScope<'a, 's> {
    pub scope: Scope<'a, 's>,
    pub exposed_idents: ArenaVecMap<'a, IdentId, (Symbol, Region)>,
    pub required_symbols: ArenaVecSet<'a, Symbol>,
    pub provides: ArenaVecMap<'a, IdentId, (Symbol, Region)>,
}

fn build_initial_scope<'a, 's, 'b>(
    home: ModuleId,
    module_name: ModuleName,
    header_type: &'a roc_parse::header::HeaderType<'a>,
    exposed_builtins: &'b BuiltinExposedValues<'b>,
    problems: &mut Vec<'a, Problem>,
    ident_ids: &mut IdentIds<'a>,
    arena: &'a Bump,
    scratch_arena: &'s Bump,
) -> InitialScope<'a, 's> {
    let mut can_exposed_imports = ArenaVecMap::new_in(arena);

    let mut scope = Scope::new(home, module_name, exposed_builtins, scratch_arena);

    let (exposed_names, exposed_module_names, required_idents, required_types, provided_idents): (
        &'a [Loc<ExposedName<'a>>],
        &'a [Loc<roc_parse::header::ModuleName<'a>>],
        &'a [Loc<TypedIdent<'a>>],
        &'a [Loc<UppercaseIdent<'a>>],
        &'a [Loc<ExposedName<'a>>],
    ) = match header_type {
        HeaderType::App { provides, .. } => (&[], &[], &[], &[], provides),
        HeaderType::Package { exposes, .. } => (&[], exposes, &[], &[], &[]),
        HeaderType::Hosted { exposes, .. }
        | HeaderType::Builtin { exposes, .. }
        | HeaderType::Module { exposes, .. } => (exposes, &[], &[], &[], &[]),
        HeaderType::Platform {
            provides,
            requires,
            requires_types,
            exposes,
            ..
        } => (&[], exposes, requires, requires_types, provides),
    };

    let mut exposed_idents = ArenaVecMap::with_capacity_in(exposed_names.len(), arena);
    for exposed_name in exposed_names {
        let name = exposed_name.value.as_str();
        let ident_id = ident_ids.get_or_insert(name);

        if let Some(&(_symbol, existing_region)) = exposed_idents.get(&ident_id) {
            problems.push(Problem::DuplicateExposes {
                region: exposed_name.region,
                existing_region,
            });
        } else {
            let symbol = Symbol::new(home, ident_id);
            exposed_idents.insert(ident_id, (symbol, exposed_name.region));
        }
    }

    let mut latest_module_id = home;
    for exposed_module_name in exposed_module_names {
        let ident = Ident::from(exposed_module_name.value.into());
        let next_module_id = latest_module_id.next();

        match scope.modules.insert(
            exposed_module_name.value.into(),
            next_module_id,
            None,
            exposed_module_name.region,
        ) {
            Ok(()) => {
                // only increment on success to only use module IDs on valid modules
                latest_module_id = next_module_id;
            }
            Err(scope_module_source) => {
                problems.push(Problem::DuplicateExposesModule {
                    region: exposed_module_name.region,
                    source: scope_module_source,
                });
            }
        }
    }

    let mut required_symbols = ArenaVecMap::new_in(arena);
    for required_ident in required_idents {
        let ident = Ident::from(required_ident.value.ident.value);

        match scope.introduce_without_shadow_symbol(&ident, required_ident.value.ident.region) {
            Ok(symbol) => {
                required_symbols.insert(symbol, ());
            }
            Err((symbol, existing_region, shadow)) => {
                problems.push(Problem::DuplicateRequires {
                    // TODO: should we use these outer regions, or just the inner (e.g. name) regions?
                    region: required_ident.region,
                    existing_region,
                });
            }
        }
    }

    // TODO: handle requiring of builtin types e.g. List
    for required_type in required_types {
        let ident = Ident::from(required_type.value.into());

        match scope.introduce_without_shadow_symbol(&ident, required_type.region) {
            Ok(symbol) => {
                required_symbols.insert(symbol, ());
            }
            Err((symbol, existing_region, shadow)) => {
                problems.push(Problem::DuplicateRequires {
                    region: required_type.region,
                    existing_region,
                });
            }
        }
    }

    let mut provides = ArenaVecMap::new_in(arena);
    for provided_ident in provided_idents {
        let name = provided_ident.value.as_str();
        let ident_id = ident_ids.get_or_insert(name);

        if let Some(&(_symbol, existing_region)) = provides.get(&ident_id) {
            problems.push(Problem::DuplicateProvides {
                region: provided_ident.region,
                existing_region,
            });
        } else {
            let symbol = Symbol::new(home, ident_id);
            provides.insert(ident_id, (symbol, provided_ident.region));
        }
    }

    for (name, alias) in exposed_builtins.aliases.into_iter() {
        scope.add_alias(
            name,
            alias.region,
            alias.type_variables,
            alias.infer_ext_in_output_variables,
            alias.typ,
            alias.kind,
        );
    }

    InitialScope {
        scope,
        exposed_idents,
        required_symbols,
        provides,
    }
}

pub fn canonicalize_module_defs<'a, 's, 'b>(
    home: ModuleId,
    module_name: ModuleName,
    module_path: &'a str,
    src: &'a str,
    loc_defs: &'a mut Defs<'a>,
    header_type: &'a roc_parse::header::HeaderType,
    exposed_builtins: &'b BuiltinExposedValues<'b>,
    var_store: &mut VarStore,
    arena: &'a Bump,
    scratch_arena: &'s Bump,
) -> ModuleOutput<'a, 's> {
    let mut can_exposed_imports = ArenaVecMap::new_in(arena);

    let mut env = Env::new(
        home,
        arena,
        src,
        arena.alloc(Path::new(module_path)),
        exposed_builtins,
    );

    let InitialScope {
        mut scope,
        exposed_idents,
        required_symbols,
        provides,
    } = build_initial_scope(
        home,
        module_name,
        header_type,
        exposed_builtins,
        &mut env.problems,
        &mut env.ident_ids,
        arena,
        scratch_arena,
    );

    // Desugar operators (convert them to Apply calls, taking into account
    // operator precedence and associativity rules), before doing other canonicalization.
    //
    // If we did this *during* canonicalization, then each time we
    // visited a BinOp node we'd recursively try to apply this to each of its nested
    // operators, and then again on *their* nested operators, ultimately applying the
    // rules multiple times unnecessarily.

    roc_can::desugar::desugar_defs_node_values(&mut env, &mut scope, loc_defs, true);

    let mut rigid_variables = RigidVariables::new_in(arena);

    // // Initial scope values are treated like defs that appear before any others.
    // // They include builtin types that are automatically imported, and for a platform
    // // package, the required values from the app.
    // //
    // // Here we essentially add those "defs" to "the beginning of the module"
    // // by canonicalizing them right before we canonicalize the actual ast::Def nodes.
    // for (ident, (symbol, region)) in initial_scope {
    //     let first_char = ident.as_inline_str().as_str().chars().next().unwrap();

    //     if first_char.is_lowercase() {
    //         match scope.import_symbol(ident, symbol, region) {
    //             Ok(()) => {
    //                 // Add an entry to exposed_imports using the current module's name
    //                 // as the key; e.g. if this is the Foo module and we have
    //                 // Bar exposes [baz] then insert Foo.baz as the key, so when
    //                 // anything references `baz` in this Foo module, it will resolve to Bar.baz.
    //                 can_exposed_imports.insert(symbol, region);
    //             }
    //             Err((_shadowed_symbol, _region)) => {
    //                 internal_error!("TODO gracefully handle shadowing in imports.")
    //             }
    //         }
    //     } else {
    //         // This is a type alias

    //         // but now we know this symbol by a different identifier, so we still need to add it to
    //         // the scope
    //         match scope.import_symbol(ident, symbol, region) {
    //             Ok(()) => {
    //                 // here we do nothing special
    //             }
    //             Err((shadowed_symbol, _region)) => {
    //                 internal_error!(
    //                     "TODO gracefully handle shadowing in imports, {:?} is shadowed.",
    //                     shadowed_symbol
    //                 )
    //             }
    //         }
    //     }
    // }

    let mut output = Output::default();

    let module_params = header_type.get_params().as_ref().map(
        |roc_parse::header::ModuleParams {
             pattern,
             before_arrow: _,
             after_arrow: _,
         }| {
            let desugared_patterns =
                roc_can::desugar::desugar_record_destructures(&mut env, &mut scope, pattern.value);

            let (destructs, _) = canonicalize_record_destructs(
                &mut env,
                var_store,
                &mut scope,
                &mut output,
                PatternType::ModuleParams,
                &desugared_patterns,
                pattern.region,
                PermitShadows(false),
            );

            let whole_symbol = scope.gen_unique_symbol();
            env.top_level_symbols.insert(whole_symbol, ());

            let whole_var = var_store.fresh();

            env.home_params_record = Some((whole_symbol, whole_var));

            ModuleParams {
                region: pattern.region,
                whole_var,
                whole_symbol,
                record_var: var_store.fresh(),
                record_ext_var: var_store.fresh(),
                destructs,
                arity_by_name: ArenaVecMap::new_in(arena),
            }
        },
    );

    let (defs, output, symbols_introduced, imports_introduced) = canonicalize_defs(
        &mut env,
        output,
        var_store,
        &mut scope,
        loc_defs,
        PatternType::TopLevelDef,
    );

    for (_early_return_var, early_return_region, early_return_kind) in &scope.early_returns {
        env.problem(Problem::ReturnOutsideOfFunction {
            region: *early_return_region,
            return_kind: *early_return_kind,
        });
    }

    let pending_derives = output.pending_derives;

    // See if any of the new idents we defined went unused.
    // If any were unused and also not exposed, report it.
    //
    // We'll catch symbols that are only referenced due to (mutual) recursion later,
    // when sorting the defs.
    //
    // TODO: update this condition
    for (symbol, region) in symbols_introduced {
        if !output.references.has_type_or_value_lookup(symbol)
            && !exposed_symbols.contains(&symbol)
            && !scope.abilities_store.is_specialization_name(symbol)
            && !symbol.is_exposed_for_builtin_derivers()
        {
            env.problem(Problem::UnusedDef(symbol, region));
        }
    }

    for named in output.introduced_variables.named {
        rigid_variables.named.insert(named.variable, named.name);
    }

    for able in output.introduced_variables.able {
        rigid_variables
            .able
            .insert(able.variable, (able.name, able.abilities));
    }

    for var in output.introduced_variables.wildcards {
        rigid_variables.wildcards.insert(var.value);
    }

    let mut referenced_values = ArenaVecSet::new_in(arena);

    // Gather up all the symbols that were referenced across all the defs' lookups.
    referenced_values.extend(output.references.value_lookups().copied());

    // Gather up all the symbols that were referenced across all the defs' calls.
    referenced_values.extend(output.references.calls().copied());

    // Gather up all the symbols that were referenced from other modules.
    referenced_values.extend(env.qualified_value_lookups.iter().copied());

    // NOTE previously we inserted builtin defs into the list of defs here
    // this is now done later, in file.rs.

    // assume all exposed symbols are not actually defined in the module
    // then as we walk the module and encounter the definitions, remove
    // symbols from this set
    let mut exposed_but_not_defined = exposed_symbols.clone();

    let new_output = Output {
        aliases: output.aliases,
        references: output.references,
        ..Default::default()
    };

    let (mut declarations, mut output) = sort_top_level_can_defs(
        &mut env,
        &mut scope,
        var_store,
        defs,
        new_output,
        &exposed_symbols,
    );

    let module_params = module_params.map(|params| ModuleParams {
        arity_by_name: declarations.take_arity_by_name(),
        ..params
    });

    debug_assert!(
        output.pending_derives.is_empty(),
        "I thought pending derives are only found during def introduction"
    );

    let symbols_from_requires = symbols_from_requires
        .iter()
        .map(|(symbol, loc_ann)| {
            // We've already canonicalized the module, so there are no pending abilities.
            let pending_abilities_in_scope = &Default::default();

            let ann = canonicalize_annotation(
                &mut env,
                &mut scope,
                &loc_ann.value,
                loc_ann.region,
                var_store,
                pending_abilities_in_scope,
                AnnotationFor::Value,
            );

            ann.add_to(
                &mut output.aliases,
                &mut output.references,
                &mut output.introduced_variables,
            );

            (
                *symbol,
                Loc {
                    value: ann.typ,
                    region: loc_ann.region,
                },
            )
        })
        .collect();

    report_unused_imports(imports_introduced, &output.references, &mut env, &mut scope);

    for index in 0..declarations.len() {
        use crate::expr::DeclarationTag::*;

        let tag = declarations.declarations[index];

        match tag {
            Value | Function(_) | Recursive(_) | TailRecursive(_) => {
                let symbol = &declarations.symbols[index].value;

                // Remove this from exposed_symbols,
                // so that at the end of the process,
                // we can see if there were any
                // exposed symbols which did not have
                // corresponding defs.
                exposed_but_not_defined.remove(symbol);

                // Temporary hack: we don't know exactly what symbols are hosted symbols,
                // and which are meant to be normal definitions without a body. So for now
                // we just assume they are hosted functions (meant to be provided by the platform)
                if has_no_implementation(&declarations.expressions[index].value) {
                    match header_type {
                        HeaderType::Builtin { .. } => {
                            match crate::builtins::builtin_defs_map(*symbol, var_store) {
                                None => {
                                    internal_error!("A builtin module contains a signature without implementation for {:?}", symbol)
                                }
                                Some(replacement_def) => {
                                    declarations.update_builtin_def(index, replacement_def);
                                }
                            }
                        }
                        HeaderType::Hosted { .. } => {
                            let ident_id = symbol.ident_id();
                            let ident = scope
                                .locals
                                .ident_ids
                                .get_name(ident_id)
                                .unwrap()
                                .to_string();

                            let def_annotation = declarations.annotations[index].clone().unwrap();

                            let annotation = crate::annotation::Annotation {
                                typ: def_annotation.signature,
                                introduced_variables: def_annotation.introduced_variables,
                                references: References::new(),
                                aliases: Default::default(),
                            };

                            let hosted_def = crate::effect_module::build_host_exposed_def(
                                &mut scope, *symbol, &ident, var_store, annotation,
                            );

                            declarations.update_builtin_def(index, hosted_def);
                        }
                        _ => (),
                    }
                }
            }
            Destructure(d_index) => {
                let destruct_def = &declarations.destructs[d_index.index()];

                for (symbol, _) in BindingsFromPattern::new(&destruct_def.loc_pattern) {
                    exposed_but_not_defined.remove(&symbol);
                }
            }
            MutualRecursion { .. } => {
                // the declarations of this group will be treaded individually by later iterations
            }
            Expectation => { /* ignore */ }
        }
    }

    let mut aliases = MutMap::default();

    for (symbol, alias) in output.aliases {
        // Remove this from exposed_symbols,
        // so that at the end of the process,
        // we can see if there were any
        // exposed symbols which did not have
        // corresponding defs.
        exposed_but_not_defined.remove(&symbol);

        aliases.insert(symbol, alias);
    }

    for (ability, members) in scope
        .abilities_store
        .iter_abilities()
        .filter(|(ab, _)| ab.module_id() == home)
    {
        exposed_but_not_defined.remove(&ability);
        members.iter().for_each(|member| {
            debug_assert!(member.module_id() == home);
            exposed_but_not_defined.remove(member);
        });
    }

    // By this point, all exposed symbols should have been removed from
    // exposed_symbols and added to exposed_vars_by_symbol. If any were
    // not, that means they were declared as exposed but there was
    // no actual declaration with that name!
    for symbol in exposed_but_not_defined {
        env.problem(Problem::ExposedButNotDefined(symbol));

        // In case this exposed value is referenced by other modules,
        // create a decl for it whose implementation is a runtime error.
        let mut pattern_vars = SendMap::default();
        pattern_vars.insert(symbol, var_store.fresh());

        let runtime_error = RuntimeError::ExposedButNotDefined(symbol);
        let def = Def {
            loc_pattern: Loc::at(Region::zero(), Pattern::Identifier(symbol)),
            loc_expr: Loc::at(Region::zero(), Expr::RuntimeError(runtime_error)),
            expr_var: var_store.fresh(),
            pattern_vars,
            annotation: None,
            kind: DefKind::Let,
        };

        declarations.push_def(def);
    }

    // Incorporate any remaining output.lookups entries into references.
    referenced_values.extend(output.references.value_lookups().copied());

    // Incorporate any remaining output.calls entries into references.
    referenced_values.extend(output.references.calls().copied());

    // Gather up all the symbols that were referenced from other modules.
    referenced_values.extend(env.qualified_value_lookups.iter().copied());

    let collected = declarations.expects();

    ModuleOutput {
        scope,
        aliases,
        rigid_variables,
        module_params,
        declarations,
        referenced_values,
        exposed_imports: can_exposed_imports,
        problems: env.problems,
        symbols_from_requires,
        pending_derives,
        loc_expects: collected.expects,
        has_dbgs: collected.has_dbgs,
        exposed_symbols,
    }
}

/// Type state for a single module.
#[derive(Debug)]
pub struct TypeState {
    pub subs: Subs,
    pub exposed_vars_by_symbol: Vec<(Symbol, Variable)>,
    pub abilities: AbilitiesStore,
    pub solved_implementations: ResolvedImplementations,
}

// impl TypeState {
//     pub fn serialize(&self, writer: &mut impl std::io::Write) -> std::io::Result<usize> {
//         let Self {
//             subs,
//             exposed_vars_by_symbol,
//             abilities,
//             solved_implementations,
//         } = self;

//         let written_subs = subs.serialize(exposed_vars_by_symbol, writer)?;
//         let written_ab = abilities.serialize(writer)?;
//         let written_solved_impls =
//             crate::abilities::serialize_solved_implementations(solved_implementations, writer)?;

//         Ok(written_subs + written_ab + written_solved_impls)
//     }

//     pub fn deserialize(bytes: &[u8]) -> (Self, usize) {
//         let ((subs, exposed_vars_by_symbol), len_subs) = Subs::deserialize(bytes);
//         let bytes = &bytes[len_subs..];

//         let (abilities, len_abilities) = AbilitiesStore::deserialize(bytes);
//         let bytes = &bytes[len_abilities..];

//         let (solved_implementations, len_solved_impls) =
//             crate::abilities::deserialize_solved_implementations(bytes);

//         let total_offset = len_subs + len_abilities + len_solved_impls;

//         (
//             Self {
//                 subs,
//                 exposed_vars_by_symbol: exposed_vars_by_symbol.to_vec(),
//                 abilities,
//                 solved_implementations,
//             },
//             total_offset,
//         )
//     }
// }
