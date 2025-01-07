use crate::annotation::{freshen_opaque_def, IntroducedVariables};
use crate::def::{can_defs_with_return, Def};
use crate::env::Env;
use crate::interpolation::flatten_str_literal;
use crate::num::{
    finish_parsing_base, finish_parsing_float, finish_parsing_num, float_expr_from_result,
    int_expr_from_result, num_expr_from_result, FloatBound, IntBound, NumBound,
};
use crate::pattern::{canonicalize_pattern, BindingsFromPattern, Pattern, PermitShadows};
use crate::problem::{CompilerProblem, UndesugaredExprKind};
use crate::procedure::{QualifiedReference, References};
use crate::scope::{Scope, SymbolLookup};
use crate::traverse::walk_expr;
use bumpalo::collections::{CollectIn, Vec};
use bumpalo::Bump;
use roc_collections::{ArenaVecMap, ArenaVecSet};
use roc_module::called_via::CalledVia;
use roc_module::ident::{ForeignSymbol, Lowercase, TagName};
use roc_module::low_level::LowLevel;
use roc_module::symbol::Symbol;
use roc_parse::ast::{self, Defs, ResultTryKind};
use roc_parse::ident::Accessor;
use roc_parse::pattern::PatternType::*;
use roc_problem::can::{PrecedenceProblem, Problem, RuntimeError};
use roc_region::all::{Loc, Region};
use roc_types::num::SingleQuoteBound;
use roc_types::subs::{ExhaustiveMark, IllegalCycleMark, RedundantMark, VarStore, Variable};
use roc_types::types::{Alias, Category, EarlyReturnKind, IndexOrField, OptAbleVar, Type};
use std::fmt::{Debug, Display};
use std::path::PathBuf;
use std::{char, u32};

/// Derives that an opaque type has claimed, to checked and recorded after solving.
pub type PendingDerives<'a> = ArenaVecMap<'a, Symbol, (Type, Vec<'a, Loc<Symbol>>)>;

#[derive(Clone, Debug, PartialEq)]
pub struct FunctionDef<'a> {
    function_var: Variable,
    function_expr: Loc<Expr<'a>>,
    closure_var: Variable,
    return_var: Variable,
    fx_var: Variable,
}

#[derive(Clone, Debug)]
pub struct Output<'a> {
    pub references: References<'a>,
    pub tail_calls: Vec<'a, Symbol>,
    pub introduced_variables: IntroducedVariables<'a>,
    pub aliases: ArenaVecMap<'a, Symbol, Alias>,
    pub non_closures: ArenaVecSet<'a, Symbol>,
    pub pending_derives: PendingDerives<'a>,
}

impl<'a> Output<'a> {
    pub fn new_in(arena: &'a Bump) -> Self {
        Self {
            references: References::new_in(arena),
            tail_calls: Vec::new_in(arena),
            introduced_variables: IntroducedVariables::new_in(arena),
            aliases: ArenaVecMap::new_in(arena),
            non_closures: ArenaVecSet::new_in(arena),
            pending_derives: PendingDerives::new_in(arena),
        }
    }

    pub fn union(&mut self, other: Self) {
        self.references.union_mut(&other.references);

        if self.tail_calls.is_empty() && !other.tail_calls.is_empty() {
            self.tail_calls = other.tail_calls;
        }

        self.introduced_variables
            .union_owned(other.introduced_variables);
        self.aliases.extend(other.aliases);
        self.non_closures.extend(other.non_closures);

        {
            let expected_derives_size = self.pending_derives.len() + other.pending_derives.len();
            self.pending_derives.extend(other.pending_derives);
            debug_assert!(
                expected_derives_size == self.pending_derives.len(),
                "Derives overwritten from nested scope - something is very wrong"
            );
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum IntValue {
    I128([u8; 16]),
    U128([u8; 16]),
}

impl Display for IntValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntValue::I128(n) => Display::fmt(&i128::from_ne_bytes(*n), f),
            IntValue::U128(n) => Display::fmt(&u128::from_ne_bytes(*n), f),
        }
    }
}

impl IntValue {
    pub fn as_u8(self) -> u8 {
        self.as_u128() as u8
    }

    pub fn as_i8(self) -> i8 {
        self.as_i128() as i8
    }

    pub fn as_u16(self) -> u16 {
        self.as_u128() as u16
    }

    pub fn as_i16(self) -> i16 {
        self.as_i128() as i16
    }

    pub fn as_u32(self) -> u32 {
        self.as_u128() as u32
    }

    pub fn as_i32(self) -> i32 {
        self.as_i128() as i32
    }

    pub fn as_u64(self) -> u64 {
        self.as_u128() as u64
    }

    pub fn as_i64(self) -> i64 {
        self.as_i128() as i64
    }

    pub fn as_u128(self) -> u128 {
        match self {
            IntValue::I128(i128) => i128::from_ne_bytes(i128) as u128,
            IntValue::U128(u128) => u128::from_ne_bytes(u128),
        }
    }

    pub fn as_i128(self) -> i128 {
        match self {
            IntValue::I128(i128) => i128::from_ne_bytes(i128),
            IntValue::U128(u128) => u128::from_ne_bytes(u128) as i128,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    // Literals

    // Num stores the `a` variable in `Num a`. Not the same as the variable
    // stored in Int and Float below, which is strictly for better error messages
    Num {
        var: Variable,
        literal: &'a str,
        value: IntValue,
        bound: NumBound,
    },

    // Int and Float store a variable to generate better error messages
    Int {
        var: Variable,
        precision: Variable,
        literal: &'a str,
        value: IntValue,
        bound: IntBound,
    },
    Float {
        var: Variable,
        precision: Variable,
        literal: &'a str,
        value: f64,
        bound: FloatBound,
    },
    Str {
        literal: &'a str,
    },
    // Number variable, precision variable, value, bound
    SingleQuote {
        var: Variable,
        precision: Variable,
        literal: char,
        bound: SingleQuoteBound,
    },
    List {
        elem_var: Variable,
        loc_elems: &'a [Loc<Expr<'a>>],
    },

    IngestedFile {
        var: Variable,
        // TODO: make this arena allocator-friendly
        path: PathBuf,
    },

    // Lookups
    Var {
        symbol: Symbol,
        var: Variable,
    },

    // Branching
    When {
        /// The actual condition of the when expression.
        loc_cond: &'a Loc<Expr<'a>>,
        cond_var: Variable,
        /// Type of each branch (and therefore the type of the entire `when` expression)
        expr_var: Variable,
        region: Region,
        /// The branches of the when, and the type of the condition that they expect to be matched
        /// against.
        branches: &'a [WhenBranch<'a>],
        branches_cond_var: Variable,
        /// Whether the branches are exhaustive.
        exhaustive: ExhaustiveMark,
    },
    If {
        cond_var: Variable,
        branch_var: Variable,
        branches: &'a [(Loc<Expr<'a>>, Loc<Expr<'a>>)],
        final_else: &'a Loc<Expr<'a>>,
    },

    Let {
        defs: &'a [Def<'a>],
        continuation: &'a Loc<Expr<'a>>,
        cycle_mark: IllegalCycleMark,
    },

    /// This is *only* for calling functions, not for tag application.
    /// The Tag variant contains any applied values inside it.
    Call {
        func_type: &'a FunctionDef<'a>,
        args: &'a [(Variable, Loc<Expr<'a>>)],
        called_via: CalledVia,
    },
    /// Call a named method on an expression.
    MethodCall {
        target_var: Variable,
        target_expr: &'a Loc<Expr<'a>>,
        // TODO: use &'a str instead? Seems more obviously in the arena
        method_name: Lowercase,
        func_type: &'a FunctionDef<'a>,
        args: &'a [(Variable, Loc<Expr<'a>>)],
    },
    /// Call a local function in method-calling style on an expression.
    LocalMethodCall {
        target_var: Variable,
        target_expr: &'a Loc<Expr<'a>>,
        method_var: Variable,
        method_expr: &'a Loc<Expr<'a>>,
        func_type: &'a FunctionDef<'a>,
        args: &'a [(Variable, Loc<Expr<'a>>)],
    },
    RunLowLevel {
        op: LowLevel,
        args: &'a [(Variable, Expr<'a>)],
        ret_var: Variable,
    },
    ForeignCall {
        foreign_symbol: ForeignSymbol,
        args: &'a [(Variable, Expr<'a>)],
        ret_var: Variable,
    },

    Closure(ClosureData<'a>),

    // Product Types
    Record {
        record_var: Variable,
        fields: &'a [(Lowercase, Field<'a>)],
    },

    /// Empty record constant
    EmptyRecord,

    Tuple {
        tuple_var: Variable,
        elems: &'a [(Variable, &'a Loc<Expr<'a>>)],
    },

    // TODO: remove
    // /// Module params expression in import
    // ImportParams {
    //     module_id: ModuleId,
    //     region: Region,
    //     params: Option<(Variable, &'a Expr<'a>)>,
    // },
    //
    /// The "crash" keyword
    Crash {
        msg: &'a Loc<Expr<'a>>,
        ret_var: Variable,
    },

    /// Look up exactly one field on a record, e.g. (expr).foo.
    RecordAccess {
        record_var: Variable,
        ext_var: Variable,
        field_var: Variable,
        loc_expr: &'a Loc<Expr<'a>>,
        field: Lowercase,
    },

    /// tuple or field accessor as a function, e.g. (.foo) expr or (.1) expr
    RecordAccessor(StructAccessorData),

    TupleAccess {
        tuple_var: Variable,
        ext_var: Variable,
        elem_var: Variable,
        loc_expr: &'a Loc<Expr<'a>>,
        index: usize,
    },

    RecordUpdate {
        record_var: Variable,
        ext_var: Variable,
        symbol: Symbol,
        updates: &'a [(Lowercase, Field<'a>)],
    },

    // Sum Types
    Tag {
        tag_union_var: Variable,
        ext_var: Variable,
        name: TagName,
        arguments: &'a (Variable, Loc<Expr<'a>>),
    },

    ZeroArgumentTag {
        closure_name: Symbol,
        variant_var: Variable,
        ext_var: Variable,
        name: TagName,
    },

    // Custom sum types
    CustomTag {
        union_name: Option<TagName>,
        tag_union_var: Variable,
        ext_var: Variable,
        name: TagName,
        arguments: &'a (Variable, Loc<Expr<'a>>),
    },

    ZeroArgumentCustomTag {
        union_name: Option<TagName>,
        closure_name: Symbol,
        variant_var: Variable,
        ext_var: Variable,
        name: TagName,
    },

    // TODO: custom structs once those are redesigned
    //
    // Test
    Expect {
        loc_condition: &'a Loc<Expr<'a>>,
        loc_continuation: &'a Loc<Expr<'a>>,
        lookups_in_cond: &'a [ExpectLookup],
    },

    Dbg {
        source_location: &'a str,
        source: &'a str,
        loc_message: &'a Loc<Expr<'a>>,
        loc_continuation: &'a Loc<Expr<'a>>,
        variable: Variable,
        symbol: Symbol,
    },

    Try {
        result_expr: &'a Loc<Expr<'a>>,
        result_var: Variable,
        return_var: Variable,
        ok_payload_var: Variable,
        err_payload_var: Variable,
        err_ext_var: Variable,
        kind: TryKind,
    },

    Return {
        return_value: &'a Loc<Expr<'a>>,
        return_var: Variable,
    },

    /// Compiles, but will crash if reached
    RuntimeError(RuntimeError),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TryKind {
    KeywordPrefix,
    OperatorSuffix,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ExpectLookup {
    pub symbol: Symbol,
    pub var: Variable,
    // TODO: remove?
    // pub ability_info: Option<SpecializationId>,
}

impl<'a> Expr<'a> {
    pub fn category(&self) -> Category {
        match self {
            Self::Num(..) => Category::Num,
            Self::Int(..) => Category::Int,
            Self::Float(..) => Category::Frac,
            Self::Str(..) => Category::Str,
            Self::IngestedFile { path, .. } => Category::IngestedFile(path.clone()),
            Self::SingleQuote(..) => Category::Character,
            Self::List { .. } => Category::List,
            &Self::Var(sym, _) => Category::Lookup(sym),
            &Self::ParamsVar {
                symbol,
                var: _,
                params_symbol: _,
                params_var: _,
            } => Category::Lookup(symbol),
            &Self::AbilityMember(sym, _, _) => Category::Lookup(sym),
            Self::When { .. } => Category::When,
            Self::If { .. } => Category::If,
            Self::LetRec(_, expr, _) => expr.value.category(),
            Self::LetNonRec(_, expr) => expr.value.category(),
            &Self::Call(_, _, called_via) => Category::CallResult(None, called_via),
            &Self::RunLowLevel { op, .. } => Category::LowLevelOpResult(op),
            Self::ForeignCall { .. } => Category::ForeignCall,
            Self::Closure(..) => Category::Lambda,
            Self::Tuple { .. } => Category::Tuple,
            Self::Record { .. } => Category::Record,
            Self::EmptyRecord => Category::Record,
            Self::RecordAccess { field, .. } => Category::RecordAccess(field.clone()),
            Self::RecordAccessor(data) => Category::Accessor(data.field.clone()),
            Self::TupleAccess { index, .. } => Category::TupleAccess(*index),
            Self::RecordUpdate { .. } => Category::Record,
            Self::ImportParams(_, _, Some((_, expr))) => expr.category(),
            Self::ImportParams(_, _, None) => Category::Unknown,
            Self::Tag {
                name, arguments, ..
            } => Category::TagApply {
                tag_name: name.clone(),
                args_count: arguments.len(),
            },
            Self::ZeroArgumentTag { name, .. } => Category::TagApply {
                tag_name: name.clone(),
                args_count: 0,
            },
            &Self::OpaqueRef { name, .. } => Category::OpaqueWrap(name),
            &Self::OpaqueWrapFunction(OpaqueWrapFunctionData { opaque_name, .. }) => {
                Category::OpaqueWrap(opaque_name)
            }
            Self::Expect { .. } => Category::Expect,
            Self::Crash { .. } => Category::Crash,
            Self::Return { .. } => Category::Return(EarlyReturnKind::Return),

            Self::Dbg { .. } => Category::Expect,
            Self::Try { .. } => Category::TrySuccess,

            // these nodes place no constraints on the expression's type
            Self::RuntimeError(..) => Category::Unknown,
        }
    }

    pub fn contains_any_early_returns(&self) -> bool {
        match self {
            Self::Num { .. }
            | Self::Int { .. }
            | Self::Float { .. }
            | Self::Str { .. }
            | Self::IngestedFile { .. }
            | Self::SingleQuote { .. }
            | Self::Var { .. }
            | Self::AbilityMember { .. }
            | Self::ParamsVar { .. }
            | Self::Closure(..)
            | Self::EmptyRecord
            | Self::RecordAccessor(_)
            | Self::ZeroArgumentTag { .. }
            | Self::OpaqueWrapFunction(_)
            | Self::RuntimeError(..) => false,
            Self::Return { .. } | Self::Try { .. } => true,
            Self::List { loc_elems, .. } => loc_elems
                .iter()
                .any(|elem| elem.value.contains_any_early_returns()),
            Self::When {
                loc_cond, branches, ..
            } => {
                loc_cond.value.contains_any_early_returns()
                    || branches.iter().any(|branch| {
                        branch
                            .guard
                            .as_ref()
                            .is_some_and(|guard| guard.value.contains_any_early_returns())
                            || branch.value.value.contains_any_early_returns()
                    })
            }
            Self::If {
                branches,
                final_else,
                ..
            } => {
                final_else.value.contains_any_early_returns()
                    || branches.iter().any(|(cond, then)| {
                        cond.value.contains_any_early_returns()
                            || then.value.contains_any_early_returns()
                    })
            }
            Self::LetRec(defs, expr, _cycle_mark) => {
                expr.value.contains_any_early_returns()
                    || defs
                        .iter()
                        .any(|def| def.loc_expr.value.contains_any_early_returns())
            }
            Self::LetNonRec(def, expr) => {
                def.loc_expr.value.contains_any_early_returns()
                    || expr.value.contains_any_early_returns()
            }
            Self::Call(_func, args, _called_via) => args
                .iter()
                .any(|(_var, arg_expr)| arg_expr.value.contains_any_early_returns()),
            Self::RunLowLevel { args, .. } | Self::ForeignCall { args, .. } => args
                .iter()
                .any(|(_var, arg_expr)| arg_expr.contains_any_early_returns()),
            Self::Tuple { elems, .. } => elems
                .iter()
                .any(|(_var, loc_elem)| loc_elem.value.contains_any_early_returns()),
            Self::Record { fields, .. } => fields
                .iter()
                .any(|(_field_name, field)| field.loc_expr.value.contains_any_early_returns()),
            Self::RecordAccess { loc_expr, .. } => loc_expr.value.contains_any_early_returns(),
            Self::TupleAccess { loc_expr, .. } => loc_expr.value.contains_any_early_returns(),
            Self::RecordUpdate { updates, .. } => {
                updates.iter().any(|(_field_name, field_update)| {
                    field_update.loc_expr.value.contains_any_early_returns()
                })
            }
            Self::ImportParams(_module_id, _region, params) => params
                .as_ref()
                .is_some_and(|(_var, p)| p.contains_any_early_returns()),
            Self::Tag { arguments, .. } => arguments
                .iter()
                .any(|(_var, arg)| arg.value.contains_any_early_returns()),
            Self::OpaqueRef { argument, .. } => argument.1.value.contains_any_early_returns(),
            Self::Crash { msg, .. } => msg.value.contains_any_early_returns(),
            Self::Dbg {
                loc_message,
                loc_continuation,
                ..
            } => {
                loc_message.value.contains_any_early_returns()
                    || loc_continuation.value.contains_any_early_returns()
            }
            Self::Expect {
                loc_condition,
                loc_continuation,
                ..
            } => {
                loc_condition.value.contains_any_early_returns()
                    || loc_continuation.value.contains_any_early_returns()
            }
        }
    }
}

/// Stores exhaustiveness-checking metadata for a closure argument that may
/// have an annotated type.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct AnnotatedMark {
    pub annotation_var: Variable,
    pub exhaustive: ExhaustiveMark,
}

impl AnnotatedMark {
    pub fn new(var_store: &mut VarStore) -> Self {
        Self {
            annotation_var: var_store.fresh(),
            exhaustive: ExhaustiveMark::new(var_store),
        }
    }

    // NOTE: only ever use this if you *know* a pattern match is surely exhaustive!
    // Otherwise you will get unpleasant unification errors.
    pub fn known_exhaustive() -> Self {
        Self {
            annotation_var: Variable::EMPTY_TAG_UNION,
            exhaustive: ExhaustiveMark::known_exhaustive(),
        }
    }
}

// TODO: figure out what all of these fields do
#[derive(Clone, Debug, PartialEq)]
pub struct ClosureData<'a> {
    pub function_type: Variable,
    pub closure_type: Variable,
    pub return_type: Variable,
    pub fx_type: Variable,
    pub early_returns: &'a [(Variable, Region, EarlyReturnKind)],
    pub name: Symbol,
    pub captured_symbols: &'a [(Symbol, Variable)],
    pub recursive: Recursive,
    pub arguments: &'a [(Variable, AnnotatedMark, Loc<Pattern<'a>>)],
    pub loc_body: &'a Loc<Expr<'a>>,
}

/// A record or tuple accessor like `.foo` or `.0`, which is equivalent to `\r -> r.foo`
/// Struct accessors are desugared to closures; they need to have a name
/// so the closure can have a correct lambda set.
///
/// We distinguish them from closures so we can have better error messages
/// during constraint generation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructAccessorData {
    pub name: Symbol,
    pub function_var: Variable,
    pub record_var: Variable,
    pub closure_var: Variable,
    pub ext_var: Variable,
    pub field_var: Variable,

    /// Note that the `field` field is an `IndexOrField` in order to represent both
    /// record and tuple accessors. This is different from `TupleAccess` and
    /// `RecordAccess` (and RecordFields/TupleElems), which share less of their implementation.
    pub field: IndexOrField,
}

impl StructAccessorData {
    pub fn to_closure_data<'a>(self, record_symbol: Symbol, arena: &'a Bump) -> ClosureData<'a> {
        let StructAccessorData {
            name,
            function_var,
            record_var,
            closure_var,
            ext_var,
            field_var,
            field,
        } = self;

        // IDEA: convert accessor from
        //
        // .foo
        //
        // into
        //
        // (\r -> r.foo)
        let body = match field {
            IndexOrField::Index(index) => Expr::TupleAccess {
                tuple_var: record_var,
                ext_var,
                elem_var: field_var,
                loc_expr: arena.alloc(Loc::at_zero(Expr::Var(record_symbol, record_var))),
                index,
            },
            IndexOrField::Field(field) => Expr::RecordAccess {
                record_var,
                ext_var,
                field_var,
                loc_expr: arena.alloc(Loc::at_zero(Expr::Var(record_symbol, record_var))),
                field,
            },
        };

        let loc_body = Loc::at_zero(body);

        let arguments = &[(
            record_var,
            AnnotatedMark::known_exhaustive(),
            Loc::at_zero(Pattern::Identifier(record_symbol)),
        )];

        ClosureData {
            function_type: function_var,
            closure_type: closure_var,
            return_type: field_var,
            fx_type: Variable::PURE,
            early_returns: &[],
            name,
            captured_symbols: &[],
            recursive: Recursive::NotRecursive,
            arguments,
            loc_body: arena.alloc(loc_body),
        }
    }
}

/// An opaque wrapper like `@Foo`, which is equivalent to `\p -> @Foo p`
/// These are desugared to closures, but we distinguish them so we can have
/// better error messages during constraint generation.
#[derive(Clone, Debug, PartialEq)]
pub struct OpaqueWrapFunctionData<'a> {
    pub opaque_name: Symbol,
    pub opaque_var: Variable,
    // The following fields help link the concrete opaque type; see
    // `Expr::OpaqueRef` for more info on how they're used.
    pub specialized_def_type: Type,
    pub type_arguments: &'a [OptAbleVar],

    pub function_name: Symbol,
    pub function_var: Variable,
    pub argument_var: Variable,
    pub closure_var: Variable,
}

impl<'a> OpaqueWrapFunctionData<'a> {
    pub fn to_closure_data(self, argument_symbol: Symbol, arena: &'a Bump) -> ClosureData<'a> {
        let OpaqueWrapFunctionData {
            opaque_name,
            opaque_var,
            specialized_def_type,
            type_arguments,
            function_name,
            function_var,
            argument_var,
            closure_var,
        } = self;

        // IDEA: convert
        //
        // @Foo
        //
        // into
        //
        // (\p -> @Foo p)
        let body = Expr::OpaqueRef {
            opaque_var,
            name: opaque_name,
            argument: Box::new((
                argument_var,
                Loc::at_zero(Expr::Var(argument_symbol, argument_var)),
            )),
            specialized_def_type: Box::new(specialized_def_type),
            type_arguments,
        };

        let loc_body = Loc::at_zero(body);

        let arguments = &[(
            argument_var,
            AnnotatedMark::known_exhaustive(),
            Loc::at_zero(Pattern::Identifier(argument_symbol)),
        )];

        ClosureData {
            function_type: function_var,
            closure_type: closure_var,
            return_type: opaque_var,
            fx_type: Variable::PURE,
            early_returns: &[],
            name: function_name,
            captured_symbols: &[],
            recursive: Recursive::NotRecursive,
            arguments,
            loc_body: arena.alloc(loc_body),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Field<'a> {
    pub var: Variable,
    // The region of the full `foo: f bar`, rather than just `f bar`
    pub region: Region,
    pub loc_expr: &'a Loc<Expr<'a>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Recursive {
    NotRecursive = 0,
    Recursive = 1,
    TailRecursive = 2,
}

impl Recursive {
    pub fn is_recursive(&self) -> bool {
        match self {
            Recursive::NotRecursive => false,
            Recursive::Recursive | Recursive::TailRecursive => true,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct WhenBranchPattern<'a> {
    pub pattern: Loc<Pattern<'a>>,
    /// Degenerate branch patterns are those that don't fully bind symbols that the branch body
    /// needs. For example, in `A x | B y -> x`, the `B y` pattern is degenerate.
    /// Degenerate patterns emit a runtime error if reached in a program.
    pub degenerate: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub struct WhenBranch<'a> {
    pub patterns: &'a [WhenBranchPattern<'a>],
    pub value: Loc<Expr<'a>>,
    pub guard: Option<Loc<Expr<'a>>>,
    /// Whether this branch is redundant in the `when` it appears in
    pub redundant: RedundantMark,
}

pub fn canonicalize_expr<'a, 'b>(
    env: &mut Env<'a, 'b>,
    var_store: &mut VarStore,
    scope: &mut Scope,
    region: Region,
    expr: &'a ast::Expr<'a>,
) -> (Loc<Expr<'a>>, Output<'a>) {
    use Expr::*;

    let report_runtime_error = |error: roc_problem::can::RuntimeError| {
        env.problem(RuntimeError(error));

        error
    };

    let (expr, output) = match expr {
        &ast::Expr::Num(str) => {
            let answer = num_expr_from_result(var_store, finish_parsing_num(str), region, env);

            (answer, Output::default())
        }
        &ast::Expr::Float(str) => {
            let answer = float_expr_from_result(var_store, finish_parsing_float(str), region, env);

            (answer, Output::default())
        }
        ast::Expr::Record(fields) => canonicalize_record(env, var_store, scope, region, *fields),
        ast::Expr::RecordUpdate {
            fields,
            update: loc_update,
        } => {
            let (can_update, update_out) =
                canonicalize_expr(env, var_store, scope, loc_update.region, &loc_update.value);
            if let Var { symbol, .. } = &can_update.value {
                match canonicalize_fields(env, var_store, scope, region, fields.items) {
                    Ok((can_fields, mut output)) => {
                        output.references.union_mut(&update_out.references);

                        let answer = RecordUpdate {
                            record_var: var_store.fresh(),
                            ext_var: var_store.fresh(),
                            symbol: *symbol,
                            updates: can_fields,
                        };

                        (answer, output)
                    }
                    Err(CanonicalizeRecordProblem::InvalidOptionalValue {
                        field_name,
                        field_region,
                        record_region,
                    }) => (
                        Expr::RuntimeError(roc_problem::can::RuntimeError::InvalidOptionalValue {
                            field_name,
                            field_region,
                            record_region,
                        }),
                        Output::default(),
                    ),
                }
            } else {
                // only (optionally qualified) variables can be updated, not arbitrary expressions
                (
                    report_runtime_error(roc_problem::can::RuntimeError::InvalidRecordUpdate {
                        region: can_update.region,
                    }),
                    Output::new_in(env.arena),
                )
            }
        }

        ast::Expr::Tuple(fields) => {
            let mut can_elems = Vec::with_capacity(fields.len());
            let mut references = References::new();

            for loc_elem in fields.iter() {
                let (can_expr, elem_out) =
                    canonicalize_expr(env, var_store, scope, loc_elem.region, &loc_elem.value);

                references.union_mut(&elem_out.references);

                can_elems.push((var_store.fresh(), Box::new(can_expr)));
            }

            let output = Output {
                references,
                ..Default::default()
            };

            (
                Tuple {
                    tuple_var: var_store.fresh(),
                    elems: can_elems,
                },
                output,
            )
        }

        ast::Expr::Str(literal) => flatten_str_literal(env, var_store, scope, literal),

        ast::Expr::SingleQuote(string) => {
            let mut it = string.chars().peekable();
            if let Some(char) = it.next() {
                if it.peek().is_none() {
                    (
                        Expr::SingleQuote(
                            var_store.fresh(),
                            var_store.fresh(),
                            char,
                            SingleQuoteBound::from_char(char),
                        ),
                        Output::default(),
                    )
                } else {
                    // multiple chars is found
                    let error = roc_problem::can::RuntimeError::MultipleCharsInSingleQuote(region);
                    let answer = Expr::RuntimeError(error);

                    (answer, Output::default())
                }
            } else {
                // no characters found
                let error = roc_problem::can::RuntimeError::EmptySingleQuote(region);
                let answer = Expr::RuntimeError(error);

                (answer, Output::default())
            }
        }

        ast::Expr::List(loc_elems) => {
            if loc_elems.is_empty() {
                (
                    List {
                        elem_var: var_store.fresh(),
                        loc_elems: Vec::new(),
                    },
                    Output::default(),
                )
            } else {
                let mut can_elems = Vec::with_capacity(loc_elems.len());
                let mut references = References::new();

                for loc_elem in loc_elems.iter() {
                    let (can_expr, elem_out) =
                        canonicalize_expr(env, var_store, scope, loc_elem.region, &loc_elem.value);

                    references.union_mut(&elem_out.references);

                    can_elems.push(can_expr);
                }

                let output = Output {
                    references,
                    ..Default::default()
                };

                (
                    List {
                        elem_var: var_store.fresh(),
                        loc_elems: can_elems,
                    },
                    output,
                )
            }
        }
        ast::Expr::Apply(loc_fn, loc_args, application_style) => {
            // The expression that evaluates to the function being called, e.g. `foo` in
            // (foo) bar baz
            let fn_region = loc_fn.region;

            // The function's return type
            let mut args = Vec::new();
            let mut output = Output::default();

            for loc_arg in loc_args.iter() {
                let (arg_expr, arg_out) =
                    canonicalize_expr(env, var_store, scope, loc_arg.region, &loc_arg.value);

                args.push((var_store.fresh(), arg_expr));
                output.references.union_mut(&arg_out.references);
            }

            if let ast::Expr::OpaqueRef(name) = loc_fn.value {
                // We treat opaques specially, since an opaque can wrap exactly one argument.

                debug_assert!(!args.is_empty());

                if args.len() > 1 {
                    let problem =
                        roc_problem::can::RuntimeError::OpaqueAppliedToMultipleArgs(region);
                    env.problem(Problem::RuntimeError(problem.clone()));
                    (RuntimeError(problem), output)
                } else {
                    match scope.lookup_opaque_ref(name, loc_fn.region) {
                        Err(runtime_error) => {
                            env.problem(Problem::RuntimeError(runtime_error.clone()));
                            (RuntimeError(runtime_error), output)
                        }
                        Ok((name, opaque_def)) => {
                            let argument = Box::new(args.pop().unwrap());
                            output
                                .references
                                .insert_type_lookup(name, QualifiedReference::Unqualified);

                            let (type_arguments, lambda_set_variables, specialized_def_type) =
                                freshen_opaque_def(var_store, opaque_def);

                            // TODO
                            let opaque_ref = OpaqueRef {
                                opaque_var: var_store.fresh(),
                                name,
                                argument,
                                specialized_def_type: Box::new(specialized_def_type),
                                type_arguments,
                                lambda_set_variables,
                            };

                            (opaque_ref, output)
                        }
                    }
                }
            } else if let ast::Expr::Crash = loc_fn.value {
                // We treat crash specially, since crashing must be applied with one argument.

                debug_assert!(!args.is_empty());

                let mut args = Vec::new();
                let mut output = Output::default();

                for loc_arg in loc_args.iter() {
                    let (arg_expr, arg_out) =
                        canonicalize_expr(env, var_store, scope, loc_arg.region, &loc_arg.value);

                    args.push(arg_expr);
                    output.references.union_mut(&arg_out.references);
                }

                let crash = if args.len() > 1 {
                    let args_region = Region::span_across(
                        &loc_args.first().unwrap().region,
                        &loc_args.last().unwrap().region,
                    );
                    env.problem(Problem::OverAppliedCrash {
                        region: args_region,
                    });
                    // Still crash, just with our own message, and drop the references.
                    Crash {
                        msg: env.arena.alloc(Loc::at(
                            region,
                            Expr::Str(String::from("hit a crash!").into_boxed_str()),
                        )),
                        ret_var: var_store.fresh(),
                    }
                } else {
                    let msg = args.pop().unwrap();
                    Crash {
                        msg: env.arena.alloc(msg),
                        ret_var: var_store.fresh(),
                    }
                };

                (crash, output)
            } else {
                // Canonicalize the function expression and its arguments
                let (fn_expr, fn_expr_output) =
                    canonicalize_expr(env, var_store, scope, fn_region, &loc_fn.value);

                output.union(fn_expr_output);

                // Default: We're not tail-calling a symbol (by name), we're tail-calling a function value.
                output.tail_calls = vec![];

                let expr = match fn_expr.value {
                    Var { symbol, .. } => {
                        output.references.insert_call(symbol);

                        // we're tail-calling a symbol by name, check if it's the tail-callable symbol
                        if env
                            .tailcallable_symbol
                            .is_some_and(|tc_sym| tc_sym == symbol)
                        {
                            output.tail_calls.push(symbol);
                        }

                        Call {
                            func_type: env.arena.alloc((
                                var_store.fresh(),
                                fn_expr,
                                var_store.fresh(),
                                var_store.fresh(),
                                var_store.fresh(),
                            )),
                            args,
                            called_via: *application_style,
                        }
                    }
                    RuntimeError(_) => {
                        // We can't call a runtime error; bail out by propagating it!
                        return (fn_expr, output);
                    }
                    Tag {
                        tag_union_var: variant_var,
                        ext_var,
                        name,
                        ..
                    } => Tag {
                        tag_union_var: variant_var,
                        ext_var,
                        name,
                        arguments: args,
                    },
                    ZeroArgumentTag {
                        variant_var,
                        ext_var,
                        name,
                        ..
                    } => Tag {
                        tag_union_var: variant_var,
                        ext_var,
                        name,
                        arguments: args,
                    },
                    _ => {
                        // This could be something like ((if True then fn1 else fn2) arg1 arg2).
                        Call {
                            func_type: env.arena.alloc((
                                var_store.fresh(),
                                fn_expr,
                                var_store.fresh(),
                                var_store.fresh(),
                                var_store.fresh(),
                            )),
                            args,
                            called_via: *application_style,
                        }
                    }
                };

                (expr, output)
            }
        }
        ast::Expr::Var { module_name, ident } => {
            canonicalize_var_lookup(env, var_store, scope, module_name, ident, region)
        }
        ast::Expr::Underscore(name) => {
            // we parse underscores, but they are not valid expression syntax
            (
                report_runtime_error(roc_problem::can::RuntimeError::MalformedIdentifier(
                    (*name).into(),
                    if name.is_empty() {
                        roc_parse::ident::BadIdent::UnderscoreAlone(region.start())
                    } else {
                        roc_parse::ident::BadIdent::UnderscoreAtStart {
                            position: region.start(),
                            // Check if there's an ignored identifier with this name in scope (for better error messages)
                            declaration_region: scope.lookup_ignored_local(name),
                        }
                    },
                    region,
                )),
                Output::new_in(env.arena),
            )
        }
        ast::Expr::Crash => {
            // Naked crashes aren't allowed; we'll admit this with our own message, but yield an
            // error.
            env.problem(Problem::UnappliedCrash { region });

            (
                Crash {
                    msg: env.arena.alloc(Loc::at(
                        region,
                        Expr::Str(String::from("hit a crash!").into_boxed_str()),
                    )),
                    ret_var: var_store.fresh(),
                },
                Output::default(),
            )
        }
        ast::Expr::Defs(loc_defs, loc_ret) => {
            // The body expression gets a new scope for canonicalization,
            scope.inner_def_scope(|inner_scope| {
                let defs: Defs = (*loc_defs).clone();
                can_defs_with_return(env, var_store, inner_scope, env.arena.alloc(defs), loc_ret)
            })
        }
        ast::Expr::RecordBuilder { .. } => {
            report_runtime_error(roc_problem::can::RuntimeError::CompilerProblem(
                CompilerProblem::ExprShouldHaveBeenDesugared {
                    region,
                    kind: UndesugaredExprKind::RecordBuilder,
                },
            ))
        }
        ast::Expr::RecordUpdater(_) => {
            report_runtime_error(roc_problem::can::RuntimeError::CompilerProblem(
                CompilerProblem::ExprShouldHaveBeenDesugared {
                    region,
                    kind: UndesugaredExprKind::RecordUpdater,
                },
            ))
        }
        ast::Expr::Closure(loc_arg_patterns, loc_body_expr) => {
            let (closure_data, output) =
                canonicalize_closure(env, var_store, scope, loc_arg_patterns, loc_body_expr, None);

            (Closure(closure_data), output)
        }
        ast::Expr::When(loc_cond, branches) => {
            // Infer the condition expression's type.
            let cond_var = var_store.fresh();
            let (can_cond, mut output) =
                canonicalize_expr(env, var_store, scope, loc_cond.region, &loc_cond.value);

            // the condition can never be a tail-call
            output.tail_calls = vec![];

            let mut can_branches = Vec::with_capacity(branches.len());

            for branch in branches.iter() {
                let (can_when_branch, branch_references) = scope.inner_def_scope(|inner_scope| {
                    canonicalize_when_branch(
                        env,
                        var_store,
                        inner_scope,
                        region,
                        branch,
                        &mut output,
                    )
                });

                output.references.union_mut(&branch_references);

                can_branches.push(can_when_branch);
            }

            // A "when" with no branches is a runtime error, but it will mess things up
            // if code gen mistakenly thinks this is a tail call just because its condition
            // happened to be one. (The condition gave us our initial output value.)
            if branches.is_empty() {
                output.tail_calls = vec![];
            }

            // Incorporate all three expressions into a combined Output value.
            let expr = When {
                expr_var: var_store.fresh(),
                cond_var,
                region,
                loc_cond: env.arena.alloc(can_cond),
                branches: can_branches,
                branches_cond_var: var_store.fresh(),
                exhaustive: ExhaustiveMark::new(var_store),
            };

            (expr, output)
        }
        ast::Expr::RecordAccess(record_expr, field) => {
            let (loc_expr, output) = canonicalize_expr(env, var_store, scope, region, record_expr);

            (
                RecordAccess {
                    record_var: var_store.fresh(),
                    field_var: var_store.fresh(),
                    ext_var: var_store.fresh(),
                    loc_expr: env.arena.alloc(loc_expr),
                    field: Lowercase::from(*field),
                },
                output,
            )
        }
        ast::Expr::AccessorFunction(field) => (
            RecordAccessor(StructAccessorData {
                name: scope.gen_unique_symbol(),
                function_var: var_store.fresh(),
                record_var: var_store.fresh(),
                ext_var: var_store.fresh(),
                closure_var: var_store.fresh(),
                field_var: var_store.fresh(),
                field: match field {
                    Accessor::RecordField(field) => IndexOrField::Field((*field).into()),
                    Accessor::TupleIndex(index) => IndexOrField::Index(index.parse().unwrap()),
                },
            }),
            Output::default(),
        ),
        ast::Expr::TupleAccess(tuple_expr, field) => {
            let (loc_expr, output) = canonicalize_expr(env, var_store, scope, region, tuple_expr);

            (
                TupleAccess {
                    tuple_var: var_store.fresh(),
                    ext_var: var_store.fresh(),
                    elem_var: var_store.fresh(),
                    loc_expr: env.arena.alloc(loc_expr),
                    index: field.parse().unwrap(),
                },
                output,
            )
        }
        ast::Expr::TrySuffix { .. } => {
            report_runtime_error(roc_problem::can::RuntimeError::CompilerProblem(
                CompilerProblem::ExprShouldHaveBeenDesugared {
                    region,
                    kind: UndesugaredExprKind::TrySuffix,
                },
            ))
        }
        ast::Expr::Try => {
            // Treat remaining `try` keywords as normal variables so that we can continue to support `Result.try`
            canonicalize_var_lookup(env, var_store, scope, "", "try", region)
        }

        // TODO: if a custom tag union variant with this name is in scope, consider this a `ZeroArgumentCustomTag` instead
        ast::Expr::Tag(tag) => {
            let variant_var = var_store.fresh();
            let ext_var = var_store.fresh();

            let symbol = scope.gen_unique_symbol();

            (
                ZeroArgumentTag {
                    name: TagName((*tag).into()),
                    variant_var,
                    closure_name: symbol,
                    ext_var,
                },
                Output::default(),
            )
        }
        // ast::Expr::OpaqueRef(name) => {
        //     // If we're here, the opaque reference is definitely not wrapping an argument - wrapped
        //     // arguments are handled in the Apply branch.
        //     // Treat this as a function \payload -> @Opaque payload
        //     match scope.lookup_opaque_ref(name, region) {
        //         Err(runtime_error) => {
        //             env.problem(Problem::RuntimeError(runtime_error.clone()));
        //             (RuntimeError(runtime_error), Output::default())
        //         }
        //         Ok((name, opaque_def)) => {
        //             let mut output = Output::default();
        //             output
        //                 .references
        //                 .insert_type_lookup(name, QualifiedReference::Unqualified);

        //             let (type_arguments, lambda_set_variables, specialized_def_type) =
        //                 freshen_opaque_def(var_store, opaque_def);

        //             let fn_symbol = scope.gen_unique_symbol();

        //             (
        //                 OpaqueWrapFunction(OpaqueWrapFunctionData {
        //                     opaque_name: name,
        //                     opaque_var: var_store.fresh(),
        //                     specialized_def_type,
        //                     type_arguments,
        //                     lambda_set_variables,

        //                     function_name: fn_symbol,
        //                     function_var: var_store.fresh(),
        //                     argument_var: var_store.fresh(),
        //                     closure_var: var_store.fresh(),
        //                 }),
        //                 output,
        //             )
        //         }
        //     }
        // }
        ast::Expr::Dbg => {
            // Dbg was not desugared as either part of an `Apply` or a `Pizza` binop, so it's
            // invalid.
            env.problem(Problem::UnappliedDbg { region });

            let invalid_dbg_expr = crate::desugar::desugar_invalid_dbg_expr(env, scope, region);

            let (loc_expr, output) =
                canonicalize_expr(env, var_store, scope, region, invalid_dbg_expr);

            (loc_expr.value, output)
        }
        ast::Expr::DbgStmt { .. } => {
            report_runtime_error(roc_problem::can::RuntimeError::CompilerProblem(
                CompilerProblem::ExprShouldHaveBeenDesugared {
                    region,
                    kind: UndesugaredExprKind::DbgStmt,
                },
            ))
        }
        ast::Expr::LowLevelDbg((source_location, source), message, continuation) => {
            let mut output = Output::default();

            let (loc_message, output1) =
                canonicalize_expr(env, var_store, scope, message.region, &message.value);

            let (loc_continuation, output2) = canonicalize_expr(
                env,
                var_store,
                scope,
                continuation.region,
                &continuation.value,
            );

            output.union(output1);
            output.union(output2);

            // the symbol is used to bind the message `x = message`, and identify this `dbg`.
            // That would cause issues if we dbg a variable, like `dbg y`, because in the IR we
            // cannot alias variables. Hence, we make the dbg use that same variable `y`
            let symbol = match &loc_message.value {
                Expr::Var(symbol, _) => *symbol,
                _ => scope.gen_unique_symbol(),
            };

            (
                Dbg {
                    source_location: (*source_location).into(),
                    source: (*source).into(),
                    loc_message: env.arena.alloc(loc_message),
                    loc_continuation: env.arena.alloc(loc_continuation),
                    variable: var_store.fresh(),
                    symbol,
                },
                output,
            )
        }
        ast::Expr::LowLevelTry(loc_expr, kind) => {
            let (loc_result_expr, output) =
                canonicalize_expr(env, var_store, scope, loc_expr.region, &loc_expr.value);

            let return_var = var_store.fresh();

            scope
                .early_returns
                .push((return_var, loc_expr.region, EarlyReturnKind::Try));

            (
                Try {
                    result_expr: env.arena.alloc(loc_result_expr),
                    result_var: var_store.fresh(),
                    return_var,
                    ok_payload_var: var_store.fresh(),
                    err_payload_var: var_store.fresh(),
                    err_ext_var: var_store.fresh(),
                    kind: match kind {
                        ResultTryKind::KeywordPrefix => TryKind::KeywordPrefix,
                        ResultTryKind::OperatorSuffix => TryKind::OperatorSuffix,
                    },
                },
                output,
            )
        }
        ast::Expr::Return(return_expr, after_return) => {
            let mut output = Output::default();

            if let Some(after_return) = after_return {
                let region_with_return =
                    Region::span_across(&return_expr.region, &after_return.region);

                env.problem(Problem::StatementsAfterReturn {
                    region: region_with_return,
                });
            }

            let (loc_return_expr, output1) = canonicalize_expr(
                env,
                var_store,
                scope,
                return_expr.region,
                &return_expr.value,
            );

            output.union(output1);

            let return_var = var_store.fresh();

            scope
                .early_returns
                .push((return_var, return_expr.region, EarlyReturnKind::Return));

            (
                Return {
                    return_value: env.arena.alloc(loc_return_expr),
                    return_var,
                },
                output,
            )
        }
        ast::Expr::If {
            if_thens,
            final_else: final_else_branch,
            ..
        } => {
            let mut branches = Vec::with_capacity(if_thens.len());
            let mut output = Output::default();

            for (condition, then_branch) in if_thens.iter() {
                let (loc_cond, cond_output) =
                    canonicalize_expr(env, var_store, scope, condition.region, &condition.value);

                let (loc_then, then_output) = canonicalize_expr(
                    env,
                    var_store,
                    scope,
                    then_branch.region,
                    &then_branch.value,
                );

                branches.push((loc_cond, loc_then));

                output.references.union_mut(&cond_output.references);
                output.references.union_mut(&then_output.references);
            }

            let (loc_else, else_output) = canonicalize_expr(
                env,
                var_store,
                scope,
                final_else_branch.region,
                &final_else_branch.value,
            );

            output.references.union_mut(&else_output.references);

            (
                If {
                    cond_var: var_store.fresh(),
                    branch_var: var_store.fresh(),
                    branches,
                    final_else: env.arena.alloc(loc_else),
                },
                output,
            )
        }

        ast::Expr::PrecedenceConflict(ast::PrecedenceConflict {
            whole_region,
            binop1_position,
            binop2_position,
            binop1,
            binop2,
            expr: _,
        }) => {
            use roc_problem::can::RuntimeError::*;

            let region1 = Region::new(
                *binop1_position,
                binop1_position.bump_column(binop1.width() as u32),
            );
            let loc_binop1 = Loc::at(region1, *binop1);

            let region2 = Region::new(
                *binop2_position,
                binop2_position.bump_column(binop2.width() as u32),
            );
            let loc_binop2 = Loc::at(region2, *binop2);

            let problem =
                PrecedenceProblem::BothNonAssociative(*whole_region, loc_binop1, loc_binop2);

            env.problem(Problem::PrecedenceProblem(problem.clone()));

            (
                RuntimeError(InvalidPrecedence(problem, region)),
                Output::default(),
            )
        }
        ast::Expr::MalformedIdent(name, bad_ident) => (
            report_runtime_error(roc_problem::can::RuntimeError::MalformedIdentifier(
                (*name).into(),
                *bad_ident,
                region,
            )),
            Output::new_in(env.arena),
        ),
        ast::Expr::MalformedSuffixed(..) => (
            report_runtime_error(roc_problem::can::RuntimeError::MalformedSuffixed(region)),
            Output::new_in(env.arena),
        ),
        ast::Expr::EmptyRecordBuilder(sub_expr) => (
            report_runtime_error(roc_problem::can::RuntimeError::EmptyRecordBuilder(
                sub_expr.region,
            )),
            Output::new_in(env.arena),
        ),
        ast::Expr::SingleFieldRecordBuilder(sub_expr) => (
            report_runtime_error(roc_problem::can::RuntimeError::SingleFieldRecordBuilder(
                sub_expr.region,
            )),
            Output::new_in(env.arena),
        ),
        ast::Expr::OptionalFieldInRecordBuilder(loc_name, loc_value) => {
            let sub_region = Region::span_across(&loc_name.region, &loc_value.region);

            (
                report_runtime_error(
                    roc_problem::can::RuntimeError::OptionalFieldInRecordBuilder {
                        record: region,
                        field: sub_region,
                    },
                ),
                Output::new_in(env.arena),
            )
        }
        &ast::Expr::NonBase10Int {
            string,
            base,
            is_negative,
        } => {
            // the minus sign is added before parsing, to get correct overflow/underflow behavior
            let answer = match finish_parsing_base(string, base, is_negative) {
                Ok((int, bound)) => {
                    // Done in this kinda round about way with intermediate variables
                    // to keep borrowed values around and make this compile
                    let int_string = int.to_string();
                    let int_str = int_string.as_str();
                    int_expr_from_result(var_store, Ok((int_str, int, bound)), region, base, env)
                }
                Err(e) => int_expr_from_result(var_store, Err(e), region, base, env),
            };

            (answer, Output::default())
        }
        &ast::Expr::ParensAround(sub_expr) => {
            let (loc_expr, output) = canonicalize_expr(env, var_store, scope, region, sub_expr);

            (loc_expr.value, output)
        }
        // Below this point, we shouln't see any of these nodes anymore because
        // operator desugaring should have removed them!
        ast::Expr::SpaceBefore(_, _) => (
            report_runtime_error(roc_problem::can::RuntimeError::CompilerProblem(
                CompilerProblem::ExprShouldHaveBeenDesugared {
                    region,
                    kind: UndesugaredExprKind::SpaceBefore,
                },
            )),
            Output::new_in(env.arena),
        ),
        ast::Expr::SpaceAfter(_, _) => (
            report_runtime_error(roc_problem::can::RuntimeError::CompilerProblem(
                CompilerProblem::ExprShouldHaveBeenDesugared {
                    region,
                    kind: UndesugaredExprKind::SpaceAfter,
                },
            )),
            Output::new_in(env.arena),
        ),
        ast::Expr::BinOps(_, _) => (
            report_runtime_error(roc_problem::can::RuntimeError::CompilerProblem(
                CompilerProblem::ExprShouldHaveBeenDesugared {
                    region,
                    kind: UndesugaredExprKind::BinOps,
                },
            )),
            Output::new_in(env.arena),
        ),
        ast::Expr::UnaryOp(_, _) => (
            report_runtime_error(roc_problem::can::RuntimeError::CompilerProblem(
                CompilerProblem::ExprShouldHaveBeenDesugared {
                    region,
                    kind: UndesugaredExprKind::UnaryOp,
                },
            )),
            Output::new_in(env.arena),
        ),
    };

    // TODO: are these still relevant?
    //
    // At the end, diff used_idents and defined_idents to see which were unused.
    // Add warnings for those!

    // In a later phase, unused top level declarations won't get monomorphized or code-genned.
    // We aren't going to bother with DCE at the level of local defs. It's going to be
    // a rounding error anyway (especially given that they'll be surfaced as warnings), LLVM will
    // DCE them in optimized builds, and it's not worth the bookkeeping for dev builds.
    (
        Loc {
            region,
            value: expr,
        },
        output,
    )
}

pub fn canonicalize_record<'a, 'b>(
    env: &mut Env<'a, 'b>,
    var_store: &mut VarStore,
    scope: &mut Scope,
    region: Region,
    fields: ast::Collection<'a, Loc<ast::AssignedField<'a, ast::Expr<'a>>>>,
) -> (Expr<'a>, Output<'a>) {
    use Expr::*;

    if fields.is_empty() {
        return (EmptyRecord, Output::new_in(env.arena));
    }

    match canonicalize_fields(env, var_store, scope, region, fields.items) {
        Ok((can_fields, output)) => (
            Record {
                record_var: var_store.fresh(),
                fields: can_fields,
            },
            output,
        ),
        Err(CanonicalizeRecordProblem::InvalidOptionalValue {
            field_name,
            field_region,
            record_region,
        }) => {
            let runtime_error = roc_problem::can::RuntimeError::InvalidOptionalValue {
                field_name,
                field_region,
                record_region,
            };

            env.problem(Problem::RuntimeError(runtime_error));

            (Expr::RuntimeError(runtime_error), Output::new_in(env.arena))
        }
    }
}

// TODO: validate
pub fn canonicalize_closure<'a, 'b>(
    env: &mut Env<'a, 'b>,
    var_store: &mut VarStore,
    scope: &mut Scope,
    loc_arg_patterns: &'a [Loc<ast::Pattern<'a>>],
    loc_body_expr: &'a Loc<ast::Expr<'a>>,
    opt_def_name: Option<Symbol>,
) -> (ClosureData<'a>, Output<'a>) {
    scope.inner_function_scope(|inner_scope| {
        canonicalize_closure_body(
            env,
            var_store,
            inner_scope,
            loc_arg_patterns,
            loc_body_expr,
            opt_def_name,
        )
    })
}

// TODO: validate
fn canonicalize_closure_body<'a, 'b>(
    env: &mut Env<'a, 'b>,
    var_store: &mut VarStore,
    scope: &mut Scope,
    loc_arg_patterns: &'a [Loc<ast::Pattern<'a>>],
    loc_body_expr: &'a Loc<ast::Expr<'a>>,
    opt_def_name: Option<Symbol>,
) -> (ClosureData<'a>, Output<'a>) {
    // The globally unique symbol that will refer to this closure once it gets converted
    // into a top-level procedure for code gen.
    let (symbol, is_anonymous) = match opt_def_name {
        Some(name) => (name, false),
        None => (scope.gen_unique_symbol(), true),
    };

    let mut can_args = Vec::with_capacity_in(loc_arg_patterns.len(), env.arena);
    let mut output = Output::new_in(env.arena);

    for loc_pattern in loc_arg_patterns.iter() {
        let can_argument_pattern = canonicalize_pattern(
            env,
            var_store,
            scope,
            &mut output,
            FunctionArg,
            &loc_pattern.value,
            loc_pattern.region,
            PermitShadows(false),
        );

        can_args.push((
            var_store.fresh(),
            AnnotatedMark::new(var_store),
            can_argument_pattern,
        ));
    }

    let bound_by_argument_patterns: Vec<'_, _> =
        BindingsFromPattern::new_many(can_args.iter().map(|x| &x.2)).collect_in(env.arena);

    let (loc_body_expr, new_output) = canonicalize_expr(
        env,
        var_store,
        scope,
        loc_body_expr.region,
        &loc_body_expr.value,
    );

    let mut references_top_level = false;

    let mut captured_symbols: Vec<_> = new_output
        .references
        .value_lookups()
        .copied()
        // filter out the closure's name itself
        .filter(|s| *s != symbol)
        // symbols bound either in this pattern or deeper down are not captured!
        .filter(|s| !new_output.references.bound_symbols().any(|x| x == s))
        .filter(|s| bound_by_argument_patterns.iter().all(|(k, _)| s != k))
        // filter out top-level symbols those will be globally available, and don't need to be captured
        .filter(|s| {
            let is_top_level = env.top_level_symbols.contains(s);
            references_top_level = references_top_level || is_top_level;
            !is_top_level
        })
        // filter out imported symbols those will be globally available, and don't need to be captured
        .filter(|s| s.module_id() == env.home)
        // filter out functions that don't close over anything
        .filter(|s| !new_output.non_closures.contains(s))
        .filter(|s| !output.non_closures.contains(s))
        .map(|s| (s, var_store.fresh()))
        .collect();

    if references_top_level {
        if let Some(params_record) = env.home_params_record {
            // If this module has params and the closure references top-level symbols,
            // we need to capture the whole record so we can pass it.
            // The lower_params pass will take care of removing the captures for top-level fns.
            captured_symbols.push(params_record);
        }
    }

    output.union(new_output);

    // Now that we've collected all the references, check to see if any of the args we defined
    // went unreferenced. If any did, report them as unused arguments.
    for (sub_symbol, region) in bound_by_argument_patterns {
        if !output.references.has_value_lookup(sub_symbol) {
            // The body never referenced this argument we declared. It's an unused argument!
            env.problem(Problem::UnusedArgument(
                symbol,
                is_anonymous,
                sub_symbol,
                region,
            ));
        } else {
            // We shouldn't ultimately count arguments as referenced locals. Otherwise,
            // we end up with weird conclusions like the expression (\x -> x + 1)
            // references the (nonexistent) local variable x!
            output.references.remove_value_lookup(&sub_symbol);
        }
    }

    let mut final_expr = &loc_body_expr;
    while let Expr::Let { continuation, .. } = &final_expr.value {
        final_expr = continuation;
    }

    if let Expr::Return { return_value, .. } = &final_expr.value {
        env.problem(Problem::ReturnAtEndOfFunction {
            region: return_value.region,
        });
    }

    // store the references of this function in the Env. This information is used
    // when we canonicalize a surrounding def (if it exists)
    env.closures.insert(symbol, output.references.clone());

    // sort symbols, so we know the order in which they're stored in the closure record
    captured_symbols.sort();

    // store that this function doesn't capture anything. It will be promoted to a
    // top-level function, and does not need to be captured by other surrounding functions.
    if captured_symbols.is_empty() {
        output.non_closures.insert(symbol);
    }

    let return_type_var = var_store.fresh();

    let closure_data = ClosureData {
        function_type: var_store.fresh(),
        closure_type: var_store.fresh(),
        return_type: return_type_var,
        fx_type: var_store.fresh(),
        early_returns: scope.early_returns.into_bump_slice(),
        name: symbol,
        captured_symbols: &captured_symbols.into_bump_slice(),
        recursive: Recursive::NotRecursive,
        arguments: can_args.into_bump_slice(),
        loc_body: env.arena.alloc(loc_body_expr),
    };

    (closure_data, output)
}

enum MultiPatternVariables<'a> {
    OnePattern,
    MultiPattern {
        num_patterns: usize,
        bound_occurrences: ArenaVecMap<'a, Symbol, (Region, usize)>,
    },
}

// TODO: validate
impl<'a> MultiPatternVariables<'a> {
    #[inline(always)]
    fn new(num_patterns: usize, arena: &'a Bump) -> Self {
        if num_patterns > 1 {
            Self::MultiPattern {
                num_patterns,
                bound_occurrences: ArenaVecMap::with_capacity_in(num_patterns, arena),
            }
        } else {
            Self::OnePattern
        }
    }

    #[inline(always)]
    fn add_pattern(&mut self, pattern: &Loc<Pattern>) {
        match self {
            MultiPatternVariables::OnePattern => {}
            MultiPatternVariables::MultiPattern {
                bound_occurrences, ..
            } => {
                for (sym, region) in BindingsFromPattern::new(pattern) {
                    if !bound_occurrences.contains_key(&sym) {
                        bound_occurrences.insert(sym, (region, 0));
                    }
                    bound_occurrences.get_mut(&sym).unwrap().1 += 1;
                }
            }
        }
    }

    #[inline(always)]
    fn get_unbound(self) -> impl Iterator<Item = (Symbol, Region)> {
        let (bound_occurrences, num_patterns) = match self {
            MultiPatternVariables::OnePattern => (Default::default(), 1),
            MultiPatternVariables::MultiPattern {
                bound_occurrences,
                num_patterns,
            } => (bound_occurrences, num_patterns),
        };

        bound_occurrences
            .into_iter()
            .filter_map(move |(sym, (region, occurs))| {
                if occurs != num_patterns {
                    Some((sym, region))
                } else {
                    None
                }
            })
    }
}

// TODO: validate
#[inline(always)]
fn canonicalize_when_branch<'a, 'b>(
    env: &mut Env<'a, 'b>,
    var_store: &mut VarStore,
    scope: &mut Scope,
    _region: Region,
    branch: &'a ast::WhenBranch<'a>,
    output: &mut Output,
) -> (WhenBranch<'a>, References<'a>) {
    let mut patterns = Vec::with_capacity_in(branch.patterns.len(), env.arena);
    let mut multi_pattern_variables = MultiPatternVariables::new(branch.patterns.len(), env.arena);

    for (i, loc_pattern) in branch.patterns.iter().enumerate() {
        let permit_shadows = PermitShadows(i > 0); // patterns can shadow symbols defined in the first pattern.

        let can_pattern = canonicalize_pattern(
            env,
            var_store,
            scope,
            output,
            WhenBranch,
            &loc_pattern.value,
            loc_pattern.region,
            permit_shadows,
        );

        multi_pattern_variables.add_pattern(&can_pattern);
        patterns.push(WhenBranchPattern {
            pattern: can_pattern,
            degenerate: false,
        });
    }

    let mut some_symbols_not_bound_in_all_patterns = false;
    for (unbound_symbol, region) in multi_pattern_variables.get_unbound() {
        env.problem(Problem::NotBoundInAllPatterns {
            unbound_symbol,
            region,
        });

        some_symbols_not_bound_in_all_patterns = true;
    }

    let (value, mut branch_output) = canonicalize_expr(
        env,
        var_store,
        scope,
        branch.value.region,
        &branch.value.value,
    );

    let guard = match &branch.guard {
        None => None,
        Some(loc_expr) => {
            let (can_guard, guard_branch_output) =
                canonicalize_expr(env, var_store, scope, loc_expr.region, &loc_expr.value);

            branch_output.union(guard_branch_output);
            Some(can_guard)
        }
    };

    let references = branch_output.references.clone();
    output.union(branch_output);

    // Now that we've collected all the references for this branch, check to see if
    // any of the new idents it defined were unused. If any were, report it.
    let mut pattern_bound_symbols_body_needs = ArenaVecSet::new_in(env.arena);
    for (symbol, region) in BindingsFromPattern::new_many(patterns.iter().map(|pat| &pat.pattern)) {
        if output.references.has_value_lookup(symbol) {
            pattern_bound_symbols_body_needs.insert(symbol);
        } else {
            env.problem(Problem::UnusedBranchDef(symbol, region));
        }
    }

    if some_symbols_not_bound_in_all_patterns && !pattern_bound_symbols_body_needs.is_empty() {
        // There might be branches that don't bind all the symbols needed by the body; mark those
        // branches degenerate.
        for pattern in patterns.iter_mut() {
            let bound_by_pattern: ArenaVecSet<'_, _> = BindingsFromPattern::new(&pattern.pattern)
                .map(|(sym, _)| sym)
                .collect();

            let binds_all_needed = pattern_bound_symbols_body_needs
                .iter()
                .all(|sym| bound_by_pattern.contains(sym));

            if !binds_all_needed {
                pattern.degenerate = true;
            }
        }
    }

    (
        WhenBranch {
            patterns: patterns.into_bump_slice(),
            value,
            guard,
            redundant: RedundantMark::new(var_store),
        },
        references,
    )
}

enum CanonicalizeRecordProblem {
    InvalidOptionalValue {
        field_name: Lowercase,
        field_region: Region,
        record_region: Region,
    },
}

fn canonicalize_fields<'a, 'b>(
    env: &mut Env<'a, 'b>,
    var_store: &mut VarStore,
    scope: &mut Scope,
    region: Region,
    fields: &'a [Loc<ast::AssignedField<'a, ast::Expr<'a>>>],
) -> Result<(ArenaVecMap<'a, Lowercase, Field<'a>>, Output<'a>), CanonicalizeRecordProblem> {
    let mut can_fields = ArenaVecMap::new_in(env.arena);
    let mut output = Output::default();

    for loc_field in fields.iter() {
        match canonicalize_field(env, var_store, scope, &loc_field.value) {
            Ok((label, field_expr, field_out, field_var)) => {
                let field = Field {
                    var: field_var,
                    region: loc_field.region,
                    loc_expr: env.arena.alloc(field_expr),
                };

                let replaced = can_fields.insert(label.clone(), field);

                if let Some(old) = replaced {
                    env.problems.push(Problem::DuplicateRecordFieldValue {
                        field_name: label,
                        field_region: loc_field.region,
                        record_region: region,
                        replaced_region: old.region,
                    });
                }

                output.references.union_mut(&field_out.references);
            }
            Err(CanonicalizeFieldProblem::InvalidOptionalValue {
                field_name,
                field_region,
            }) => {
                env.problems.push(Problem::InvalidOptionalValue {
                    field_name: field_name.clone(),
                    field_region,
                    record_region: region,
                });
                return Err(CanonicalizeRecordProblem::InvalidOptionalValue {
                    field_name,
                    field_region,
                    record_region: region,
                });
            }
        }
    }

    Ok((can_fields, output))
}

enum CanonicalizeFieldProblem {
    InvalidOptionalValue {
        field_name: Lowercase,
        field_region: Region,
    },
}

fn canonicalize_field<'a, 'b>(
    env: &mut Env<'a, 'b>,
    var_store: &mut VarStore,
    scope: &mut Scope,
    field: &'a ast::AssignedField<'a, ast::Expr<'a>>,
) -> Result<(Lowercase, Loc<Expr<'a>>, Output<'a>, Variable), CanonicalizeFieldProblem> {
    use roc_parse::ast::AssignedField::*;

    let report_runtime_error = |runtime_error: roc_problem::can::RuntimeError| {
        env.problem(Problem::RuntimeError(runtime_error));

        Expr::RuntimeError(runtime_error)
    };

    match field {
        // Both a label and a value, e.g. `{ name: "blah" }`
        RequiredValue(label, _, loc_expr) => {
            let field_var = var_store.fresh();
            let (loc_can_expr, output) =
                canonicalize_expr(env, var_store, scope, loc_expr.region, &loc_expr.value);

            Ok((
                Lowercase::from(label.value),
                loc_can_expr,
                output,
                field_var,
            ))
        }

        OptionalValue(label, _, loc_expr) => Err(CanonicalizeFieldProblem::InvalidOptionalValue {
            field_name: Lowercase::from(label.value),
            field_region: Region::span_across(&label.region, &loc_expr.region),
        }),

        SpaceBefore(sub_field, _) | SpaceAfter(sub_field, _) => {
            canonicalize_field(env, var_store, scope, sub_field)
        }

        IgnoredValue(ignored_field_name, _, _) => {
            report_runtime_error(roc_problem::can::RuntimeError::CompilerProblem(
                CompilerProblem::ExprShouldHaveBeenDesugared {
                    region: ignored_field_name.region,
                    kind: UndesugaredExprKind::IgnoredValueRecordField,
                },
            ))
        }

        LabelOnly(label_name) => {
            report_runtime_error(roc_problem::can::RuntimeError::CompilerProblem(
                CompilerProblem::ExprShouldHaveBeenDesugared {
                    region: label_name.region,
                    kind: UndesugaredExprKind::LabelOnlyRecordField,
                },
            ))
        }
    }
}

fn canonicalize_var_lookup<'a, 'b>(
    env: &mut Env<'a, 'b>,
    var_store: &mut VarStore,
    scope: &mut Scope,
    module_name: &str,
    ident: &str,
    region: Region,
) -> (Expr<'a>, Output<'a>) {
    let report_runtime_error = |runtime_error: roc_problem::can::RuntimeError| {
        env.problem(Problem::RuntimeError(runtime_error));

        Expr::RuntimeError(runtime_error)
    };

    let mut output = Output::default();
    let can_expr = if module_name.is_empty() {
        // Since module_name was empty, this is an unqualified var.
        // Look it up in scope!
        match scope.lookup_str(ident, region) {
            Ok(lookup) => {
                output
                    .references
                    .insert_value_lookup(lookup, QualifiedReference::Unqualified);

                lookup_to_expr(var_store, lookup)
            }
            Err(runtime_error) => report_runtime_error(runtime_error),
        }
    } else {
        // Since module_name was nonempty, this is a qualified var.
        // Look it up in the env!
        match env.qualified_lookup(scope, module_name, ident, region) {
            Ok(lookup) => {
                output
                    .references
                    .insert_value_lookup(lookup, QualifiedReference::Qualified);

                lookup_to_expr(var_store, lookup)
            }
            // Either the module wasn't imported, or
            // it was imported but it doesn't expose this ident.
            Err(runtime_error) => report_runtime_error(runtime_error),
        }
    };

    // If it's valid, this ident should be in scope already.

    (can_expr, output)
}

fn lookup_to_expr(
    var_store: &mut VarStore,
    SymbolLookup {
        symbol,
        module_params,
    }: SymbolLookup,
) -> Expr {
    if let Some((params_var, params_symbol)) = module_params {
        Expr::ParamsVar {
            symbol,
            var: var_store.fresh(),
            params_symbol,
            params_var,
        }
    } else {
        Expr::Var(symbol, var_store.fresh())
    }
}

pub(crate) fn get_lookup_symbols<'a>(expr: &Expr) -> Vec<'a, ExpectLookup> {
    let mut stack: Vec<&Expr> = vec![expr];
    let mut lookups: Vec<ExpectLookup> = Vec::new();

    while let Some(expr) = stack.pop() {
        match expr {
            Expr::Var(symbol, var)
            | Expr::ParamsVar {
                symbol,
                var,
                params_symbol: _,
                params_var: _,
            }
            | Expr::RecordUpdate {
                symbol,
                record_var: var,
                ..
            } => {
                // Don't introduce duplicates, or make unused variables
                if !lookups.iter().any(|l| l.symbol == *symbol) {
                    lookups.push(ExpectLookup {
                        symbol: *symbol,
                        var: *var,
                    });
                }
            }
            Expr::AbilityMember(symbol, spec_id, var) => {
                if !lookups.iter().any(|l| l.symbol == *symbol) {
                    lookups.push(ExpectLookup {
                        symbol: *symbol,
                        var: *var,
                    });
                }
            }
            Expr::List { loc_elems, .. } => {
                stack.extend(loc_elems.iter().map(|loc_elem| &loc_elem.value));
            }
            Expr::When {
                loc_cond, branches, ..
            } => {
                stack.push(&loc_cond.value);

                stack.reserve(branches.len());

                for branch in branches {
                    stack.push(&branch.value.value);

                    if let Some(guard) = &branch.guard {
                        stack.push(&guard.value);
                    }
                }
            }
            Expr::If {
                branches,
                final_else,
                ..
            } => {
                stack.reserve(1 + branches.len() * 2);

                for (loc_cond, loc_body) in branches {
                    stack.push(&loc_cond.value);
                    stack.push(&loc_body.value);
                }

                stack.push(&final_else.value);
            }
            Expr::LetRec(defs, expr, _illegal_cycle_mark) => {
                for def in defs {
                    stack.push(&def.loc_expr.value);
                }
                stack.push(&expr.value);
            }
            Expr::LetNonRec(def, expr) => {
                stack.push(&def.loc_expr.value);
                stack.push(&expr.value);
            }
            Expr::Call(boxed_expr, args, _called_via) => {
                stack.reserve(1 + args.len());

                match &boxed_expr.1.value {
                    Expr::Var { .. } => {
                        // do nothing
                    }
                    function_expr => {
                        // add the expr being called
                        stack.push(function_expr);
                    }
                }

                for (_var, loc_arg) in args {
                    stack.push(&loc_arg.value);
                }
            }
            Expr::Tag { arguments, .. } => {
                stack.extend(arguments.iter().map(|(_var, loc_expr)| &loc_expr.value));
            }
            Expr::RunLowLevel { args, .. } | Expr::ForeignCall { args, .. } => {
                stack.extend(args.iter().map(|(_var, arg)| arg));
            }
            Expr::OpaqueRef { argument, .. } => {
                stack.push(&argument.1.value);
            }
            Expr::RecordAccess { loc_expr, .. }
            | Expr::TupleAccess { loc_expr, .. }
            | Expr::Closure(ClosureData {
                loc_body: loc_expr, ..
            }) => {
                stack.push(&loc_expr.value);
            }
            Expr::Record { fields, .. } => {
                stack.extend(fields.iter().map(|(_, field)| &field.loc_expr.value));
            }
            Expr::Tuple { elems, .. } => {
                stack.extend(elems.iter().map(|(_, elem)| &elem.value));
            }
            Expr::ImportParams(_, _, Some((_, expr))) => {
                stack.push(expr);
            }
            Expr::Expect {
                loc_continuation, ..
            }
            | Expr::Dbg {
                loc_continuation, ..
            } => {
                stack.push(&loc_continuation.value);

                // Intentionally ignore the lookups in the nested `expect` condition itself,
                // because they couldn't possibly influence the outcome of this `expect`!
            }
            Expr::Try { result_expr, .. } => {
                stack.push(&result_expr.value);
            }
            Expr::Return { return_value, .. } => {
                stack.push(&return_value.value);
            }
            Expr::Crash { msg, .. } => stack.push(&msg.value),
            Expr::Num(_, _, _, _)
            | Expr::Float(_, _, _, _, _)
            | Expr::Int(_, _, _, _, _)
            | Expr::Str(_)
            | Expr::IngestedFile(..)
            | Expr::ZeroArgumentTag { .. }
            | Expr::RecordAccessor(_)
            | Expr::SingleQuote(..)
            | Expr::EmptyRecord
            | Expr::RuntimeError(_)
            | Expr::ImportParams(_, _, None)
            | Expr::OpaqueWrapFunction(_) => {}
        }
    }

    lookups
}

/// Here we transform
///
/// ```ignore
/// expect
///     a = 1
///     b = 2
///
///     a == b
/// ```
///
/// into
///
/// ```ignore
/// a = 1
/// b = 2
///
/// expect a == b
///
/// {}
/// ```
///
/// This is supposed to happen just before monomorphization:
/// all type errors and such are generated from the user source,
/// but this transformation means that we don't need special codegen for toplevel expects
pub fn toplevel_expect_to_inline_expect_pure<'a>(
    mut loc_expr: Loc<Expr<'a>>,
    arena: &'a Bump,
) -> Loc<Expr<'a>> {
    enum StoredDef<'a> {
        NonRecursive(Region, &'a Def<'a>),
        Recursive(Region, &'a [Def<'a>], IllegalCycleMark),
    }

    let mut stack = Vec::new_in(arena);
    let mut lookups_in_cond = Vec::new_in(arena);

    loop {
        match loc_expr.value {
            Expr::Let {
                defs,
                continuation,
                cycle_mark,
            } => {
                for def in &defs {
                    lookups_in_cond.extend(def.pattern_vars.iter().map(|(a, b)| ExpectLookup {
                        symbol: *a,
                        var: *b,
                    }));
                }

                stack.push(StoredDef::Recursive(loc_expr.region, defs, cycle_mark));
                loc_expr = *continuation;
            }
            _ => break,
        }
    }

    let expect_region = loc_expr.region;
    let expect = Expr::Expect {
        loc_condition: arena.alloc(loc_expr),
        loc_continuation: arena.alloc(Loc::at_zero(Expr::EmptyRecord)),
        lookups_in_cond: lookups_in_cond.into_bump_slice(),
    };

    let mut loc_expr = Loc::at(expect_region, expect);

    for stored in stack.into_iter().rev() {
        match stored {
            StoredDef::NonRecursive(region, boxed_def) => {
                loc_expr = Loc::at(region, Expr::LetNonRec(boxed_def, Box::new(loc_expr)));
            }
            StoredDef::Recursive(region, defs, illegal_cycle_mark) => {
                let let_rec = Expr::LetRec(defs, Box::new(loc_expr), illegal_cycle_mark);
                loc_expr = Loc::at(region, let_rec);
            }
        }
    }

    loc_expr
}

pub struct ExpectCollector<'a> {
    pub expects: ArenaVecMap<'a, Region, Vec<'a, ExpectLookup>>,
    pub has_dbgs: bool,
}

impl<'a> crate::traverse::Visitor for ExpectCollector<'a> {
    fn visit_expr(&mut self, expr: &Expr, _region: Region, var: Variable) {
        match expr {
            Expr::Expect {
                lookups_in_cond,
                loc_condition,
                ..
            } => {
                self.expects
                    .insert(loc_condition.region, lookups_in_cond.to_vec());
            }
            Expr::Dbg { .. } => {
                self.has_dbgs = true;
            }
            _ => (),
        }

        walk_expr(self, expr, var)
    }
}
