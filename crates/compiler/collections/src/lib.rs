//! Domain-specific collections created for the needs of the compiler.
#![warn(clippy::dbg_macro)]
// See github.com/roc-lang/roc/issues/800 for discussion of the large_enum_variant check.
#![allow(clippy::large_enum_variant)]

pub mod all;
mod arena_small_string_interner;
mod arena_vec_map;
mod arena_vec_set;
mod push;
mod reference_matrix;
mod small_string_interner;
mod small_vec;
pub mod soa;
mod vec_map;
mod vec_set;

pub use all::{default_hasher, BumpMap, ImEntry, ImMap, ImSet, MutMap, MutSet, SendMap};
pub use arena_small_string_interner::ArenaSmallStringInterner;
pub use arena_vec_map::ArenaVecMap;
pub use arena_vec_set::ArenaVecSet;
pub use push::Push;
pub use reference_matrix::{ReferenceMatrix, Sccs, TopologicalSort};
pub use small_string_interner::SmallStringInterner;
pub use small_vec::SmallVec;
pub use vec_map::VecMap;
pub use vec_set::VecSet;
