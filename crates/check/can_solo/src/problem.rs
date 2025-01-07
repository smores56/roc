use roc_region::all::Region;

/// Problems with the compiler that might arise during canonicalization.
///
/// We should always prefer generating compiler problems when a `panic!`
/// might be used instead. This gets the Roc compiler as close as possible
/// to never crashing!
pub enum CompilerProblem {
    ExprShouldHaveBeenDesugared {
        region: Region,
        kind: UndesugaredExprKind,
    },
}

/// Parse AST expr kinds that should not exist after desugaring.
pub enum UndesugaredExprKind {
    RecordBuilder,
    RecordUpdater,
    TrySuffix,
    DbgStmt,
    SpaceBefore,
    SpaceAfter,
    BinOps,
    UnaryOp,
    /// An ignored value, e.g. `{ _name: 123 }`
    IgnoredValueRecordField,
    /// A label with no value, e.g. `{ name }` (this is sugar for { name: name })
    LabelOnlyRecordField,
}
