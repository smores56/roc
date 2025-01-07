use bumpalo::{collections::Vec, Bump};
use roc_collections::ArenaVecMap;
use roc_module::{ident::Lowercase, symbol::Symbol};
use roc_region::all::{Loc, Region};
use roc_types::{subs::Variable, types::Type};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AliasMethod {
    Generated {
        method: GeneratedAliasMethod,
        typ: Type,
    },
    FromSymbol {
        name: Lowercase,
        symbol: Symbol,
        typ: Type,
    },
}

// TODO: what should these be?
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GeneratedAliasMethod {
    Equals,
    ToHash,
    Encode,
    Decode,
}

#[derive(Clone, Debug)]
pub struct AliasVar<'a> {
    pub name: Lowercase,
    pub var: Variable,
    // TODO: should this be in an Option to avoid the allocation?
    pub methods: ArenaVecMap<'a, Lowercase, Type>,
}

impl<'a> AliasVar<'a> {
    pub fn unbound(name: Lowercase, var: Variable, arena: &'a Bump) -> Self {
        Self {
            name,
            var,
            methods: ArenaVecMap::new_in(arena),
        }
    }
}

/// A type that references another type.
///
/// We have two types of aliases:
/// - structural
/// - custom
#[derive(Clone, Debug)]
pub struct Alias<'a> {
    /// Extension variables that should be inferred in output positions,
    /// and closed in input positions.
    // pub infer_ext_in_output_variables: Vec<'a, Variable>,
    //
    pub recursion_variables: ArenaVecMap<'a, Variable, ()>,

    pub region: Region,

    pub typ: Type,

    pub type_variables: Vec<'a, Loc<AliasVar<'a>>>,

    pub kind: AliasKind,
}

#[derive(Clone, Debug)]
pub enum AliasKind {
    /// Ad-hoc types
    Structural,
    /// Types with their own methods
    Custom,
    // TODO: I believe we need this to ensure type constructor arity
    // is properly checkable for these Zig-defined types, but I might
    // be wrong.
    //
    /// Types implemented in Zig, e.g. List
    Builtin,
}
