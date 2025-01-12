use bumpalo::Bump;
use roc_collections::{ArenaSmallStringInterner, ArenaVecMap};
use roc_module::{
    ident::{IdentSuffix, Lowercase},
    module_err::{ModuleError, ModuleResult},
    symbol::{IdentId, ModuleId},
};

/// Stores a mapping between Ident and IdentId.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdentIds<'a> {
    pub interner: ArenaSmallStringInterner<'a>,
}

impl<'a> IdentIds<'a> {
    pub fn new_in(arena: &'a Bump) -> Self {
        Self {
            interner: ArenaSmallStringInterner::new_in(arena),
        }
    }

    pub fn ident_strs(&self) -> impl Iterator<Item = (IdentId, &str)> {
        self.interner
            .iter()
            .enumerate()
            .map(|(index, ident)| (IdentId::from_index_named(index, ident), ident))
    }

    pub fn add_str(&mut self, ident_name: &str) -> IdentId {
        IdentId::from_index_named(self.interner.insert(ident_name), ident_name)
    }

    pub fn duplicate_ident(&mut self, ident_id: IdentId) -> IdentId {
        IdentId::from_index(self.interner.duplicate(ident_id.index()), ident_id.suffix())
    }

    pub fn get_or_insert(&mut self, name: &str) -> IdentId {
        match self.get_id(name) {
            Some(id) => id,
            None => self.add_str(name),
        }
    }

    // necessary when the name of a value is changed in the editor
    // TODO fix when same ident_name is present multiple times, see issue #2548
    pub fn update_key(&mut self, old_name: &str, new_name: &str) -> Result<IdentId, String> {
        match self.interner.find_and_update(old_name, new_name) {
            Some(index) => Ok(IdentId::from_index_named(index, new_name)),
            None => Err(format!("The identifier {old_name:?} is not in IdentIds")),
        }
    }

    /// Generates a unique, new name that's just a strigified integer
    /// (e.g. "1" or "5"), using an internal counter. Since valid Roc variable
    /// names cannot begin with a number, this has no chance of colliding
    /// with actual user-defined variables.
    ///
    /// This is used, for example, during canonicalization of an Expr::Closure
    /// to generate a unique symbol to refer to that closure.
    pub fn gen_unique(&mut self) -> IdentId {
        IdentId::from_index(self.interner.insert_index_str(), IdentSuffix::None)
    }

    pub fn is_generated_id(&self, id: IdentId) -> bool {
        self.interner
            .try_get(id.index())
            .map_or(false, |str| str.starts_with(|c: char| c.is_ascii_digit()))
    }

    #[inline(always)]
    pub fn get_id(&self, ident_name: &str) -> Option<IdentId> {
        self.interner
            .find_index(ident_name)
            .map(|i| IdentId::from_index_named(i, ident_name))
    }

    #[inline(always)]
    pub fn get_id_many(&'a self, ident_name: &'a str) -> impl Iterator<Item = IdentId> + 'a {
        self.interner
            .find_indices(ident_name)
            .map(|i| IdentId::from_index_named(i, ident_name))
    }

    pub fn get_name(&self, id: IdentId) -> Option<&str> {
        self.interner.try_get(id.index())
    }

    pub fn get_name_str_res(&self, ident_id: IdentId) -> ModuleResult<&str> {
        self.get_name(ident_id)
            .ok_or_else(|| ModuleError::IdentIdNotFound {
                ident_id,
                ident_ids_str: format!("{self:?}"),
            })
    }

    pub fn len(&self) -> usize {
        self.interner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.interner.is_empty()
    }

    pub fn exposed_values(&self) -> Vec<Lowercase> {
        self.ident_strs()
            .filter(|(_, ident)| ident.starts_with(|c: char| c.is_lowercase()))
            .map(|(_, ident)| Lowercase::from(ident))
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct IdentIdsByModule<'a>(ArenaVecMap<'a, ModuleId, IdentIds<'a>>);

impl<'a> IdentIdsByModule<'a> {
    pub fn new_in(arena: &'a Bump) -> Self {
        Self(ArenaVecMap::new_in(arena))
    }

    pub fn get_or_insert(&mut self, module_id: ModuleId, arena: &'a Bump) -> &mut IdentIds {
        self.0.get_or_insert(module_id, || IdentIds::new_in(arena))
    }

    pub fn get_mut(&mut self, key: &ModuleId) -> Option<&mut IdentIds> {
        self.0.get_mut(key)
    }

    pub fn get(&self, key: &ModuleId) -> Option<&IdentIds> {
        self.0.get(key)
    }

    pub fn insert(&mut self, key: ModuleId, value: IdentIds) -> Option<IdentIds> {
        self.0.insert(key, value)
    }

    pub fn keys(&self) -> impl Iterator<Item = &ModuleId> {
        self.0.keys()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}
