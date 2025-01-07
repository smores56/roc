use bumpalo::collections::Vec;
use bumpalo::Bump;
use roc_module::called_via::CalledVia;
use roc_module::symbol::Symbol;
use roc_parse::ast::StrLiteral;
use roc_parse::ast::{self, PrecedenceConflict};
use roc_problem::can::{Problem, RuntimeError};
use roc_region::all::{Loc, Region};
use roc_types::subs::VarStore;

use crate::expr::canonicalize_expr;
use crate::{
    env::Env,
    expr::{Expr, Output},
    scope::Scope,
};

pub fn flatten_str_literal<'a, 'b>(
    env: &mut Env<'a, 'b>,
    var_store: &mut VarStore,
    scope: &mut Scope,
    literal: &'a StrLiteral<'a>,
) -> (Expr<'a>, Output<'a>) {
    match literal {
        StrLiteral::PlainLine(str_slice) => {
            (Expr::Str((*str_slice).into()), Output::new_in(env.arena))
        }
        StrLiteral::Line(segments) => flatten_str_lines(env, var_store, scope, &[segments]),
        StrLiteral::Block(lines) => flatten_str_lines(env, var_store, scope, lines),
    }
}

/// Comments, newlines, and nested interpolation are disallowed inside interpolation
pub fn is_valid_interpolation(expr: &ast::Expr<'_>) -> bool {
    match expr {
        // These definitely contain neither comments nor newlines, so they are valid
        ast::Expr::Var { .. }
        | ast::Expr::SingleQuote(_)
        | ast::Expr::Str(StrLiteral::PlainLine(_))
        | ast::Expr::Float(_)
        | ast::Expr::Num(_)
        | ast::Expr::NonBase10Int { .. }
        | ast::Expr::AccessorFunction(_)
        | ast::Expr::RecordUpdater(_)
        | ast::Expr::Crash
        | ast::Expr::Dbg
        | ast::Expr::Try
        | ast::Expr::Underscore(_)
        | ast::Expr::MalformedIdent(_, _)
        | ast::Expr::Tag(_)
        | ast::Expr::OpaqueRef(_) => true,
        ast::Expr::LowLevelTry(loc_expr, _) => is_valid_interpolation(&loc_expr.value),
        // Newlines are disallowed inside interpolation, and these all require newlines
        ast::Expr::DbgStmt { .. }
        | ast::Expr::LowLevelDbg(_, _, _)
        | ast::Expr::Return(_, _)
        | ast::Expr::When(_, _)
        | ast::Expr::Backpassing(_, _, _)
        | ast::Expr::SpaceBefore(_, _)
        | ast::Expr::Str(StrLiteral::Block(_))
        | ast::Expr::SpaceAfter(_, _) => false,
        // Desugared dbg expression
        ast::Expr::Defs(_, loc_ret) => match loc_ret.value {
            ast::Expr::LowLevelDbg(_, _, continuation) => {
                is_valid_interpolation(&continuation.value)
            }
            _ => false,
        },
        // These can contain subexpressions, so we need to recursively check those
        ast::Expr::Str(StrLiteral::Line(segments)) => {
            segments.iter().all(|segment| match segment {
                ast::StrSegment::EscapedChar(_)
                | ast::StrSegment::Unicode(_)
                | ast::StrSegment::Plaintext(_) => true,
                // Disallow nested interpolation. Alternatively, we could allow it but require
                // a comment above it apologizing to the next person who has to read the code.
                ast::StrSegment::Interpolated(_) => false,
            })
        }
        ast::Expr::Record(fields) => fields.iter().all(|loc_field| match loc_field.value {
            ast::AssignedField::RequiredValue(_label, loc_comments, loc_val)
            | ast::AssignedField::OptionalValue(_label, loc_comments, loc_val)
            | ast::AssignedField::IgnoredValue(_label, loc_comments, loc_val) => {
                loc_comments.is_empty() && is_valid_interpolation(&loc_val.value)
            }
            ast::AssignedField::LabelOnly(_) => true,
            ast::AssignedField::SpaceBefore(_, _) | ast::AssignedField::SpaceAfter(_, _) => false,
        }),
        ast::Expr::Tuple(fields) => fields
            .iter()
            .all(|loc_field| is_valid_interpolation(&loc_field.value)),
        ast::Expr::MalformedSuffixed(loc_expr)
        | ast::Expr::EmptyRecordBuilder(loc_expr)
        | ast::Expr::SingleFieldRecordBuilder(loc_expr)
        | ast::Expr::OptionalFieldInRecordBuilder(_, loc_expr)
        | ast::Expr::PrecedenceConflict(PrecedenceConflict { expr: loc_expr, .. })
        | ast::Expr::UnaryOp(loc_expr, _)
        | ast::Expr::Closure(_, loc_expr) => is_valid_interpolation(&loc_expr.value),
        ast::Expr::TupleAccess(sub_expr, _)
        | ast::Expr::ParensAround(sub_expr)
        | ast::Expr::RecordAccess(sub_expr, _)
        | ast::Expr::TrySuffix { expr: sub_expr, .. } => is_valid_interpolation(sub_expr),
        ast::Expr::Apply(loc_expr, args, _called_via) => {
            is_valid_interpolation(&loc_expr.value)
                && args
                    .iter()
                    .all(|loc_arg| is_valid_interpolation(&loc_arg.value))
        }
        ast::Expr::BinOps(loc_exprs, loc_expr) => {
            is_valid_interpolation(&loc_expr.value)
                && loc_exprs
                    .iter()
                    .all(|(loc_expr, _binop)| is_valid_interpolation(&loc_expr.value))
        }
        ast::Expr::If {
            if_thens: branches,
            final_else: final_branch,
            ..
        } => {
            is_valid_interpolation(&final_branch.value)
                && branches.iter().all(|(loc_before, loc_after)| {
                    is_valid_interpolation(&loc_before.value)
                        && is_valid_interpolation(&loc_after.value)
                })
        }
        ast::Expr::List(elems) => elems
            .iter()
            .all(|loc_expr| is_valid_interpolation(&loc_expr.value)),
        ast::Expr::RecordUpdate { update, fields } => {
            is_valid_interpolation(&update.value)
                && fields.iter().all(|loc_field| match loc_field.value {
                    ast::AssignedField::RequiredValue(_label, loc_comments, loc_val)
                    | ast::AssignedField::OptionalValue(_label, loc_comments, loc_val)
                    | ast::AssignedField::IgnoredValue(_label, loc_comments, loc_val) => {
                        loc_comments.is_empty() && is_valid_interpolation(&loc_val.value)
                    }
                    ast::AssignedField::LabelOnly(_) => true,
                    ast::AssignedField::SpaceBefore(_, _)
                    | ast::AssignedField::SpaceAfter(_, _) => false,
                })
        }
        ast::Expr::RecordBuilder { mapper, fields } => {
            is_valid_interpolation(&mapper.value)
                && fields.iter().all(|loc_field| match loc_field.value {
                    ast::AssignedField::RequiredValue(_label, loc_comments, loc_val)
                    | ast::AssignedField::OptionalValue(_label, loc_comments, loc_val)
                    | ast::AssignedField::IgnoredValue(_label, loc_comments, loc_val) => {
                        loc_comments.is_empty() && is_valid_interpolation(&loc_val.value)
                    }
                    ast::AssignedField::LabelOnly(_) => true,
                    ast::AssignedField::SpaceBefore(_, _)
                    | ast::AssignedField::SpaceAfter(_, _) => false,
                })
        }
    }
}

enum StrSegment<'a> {
    Interpolation(Loc<Expr<'a>>),
    Plaintext(&'a str),
}

fn flatten_str_lines<'a, 'b>(
    env: &mut Env<'a, 'b>,
    var_store: &mut VarStore,
    scope: &mut Scope,
    lines: &[&[ast::StrSegment<'a>]],
) -> (Expr<'a>, Output<'a>) {
    use ast::StrSegment::*;

    let mut buf = String::new();
    let mut segments = Vec::new();
    let mut output = Output::default();

    for line in lines {
        for segment in line.iter() {
            match segment {
                Plaintext(string) => {
                    buf.push_str(string);
                }
                Unicode(loc_hex_digits) => match u32::from_str_radix(loc_hex_digits.value, 16) {
                    Ok(code_pt) => match char::from_u32(code_pt) {
                        Some(ch) => {
                            buf.push(ch);
                        }
                        None => {
                            env.problem(Problem::InvalidUnicodeCodePt(loc_hex_digits.region));

                            return (
                                Expr::RuntimeError(RuntimeError::InvalidUnicodeCodePt(
                                    loc_hex_digits.region,
                                )),
                                output,
                            );
                        }
                    },
                    Err(_) => {
                        env.problem(Problem::InvalidHexadecimal(loc_hex_digits.region));

                        return (
                            Expr::RuntimeError(RuntimeError::InvalidHexadecimal(
                                loc_hex_digits.region,
                            )),
                            output,
                        );
                    }
                },
                Interpolated(loc_expr) => {
                    if is_valid_interpolation(loc_expr.value) {
                        // Interpolations desugar to Str.concat calls
                        output.references.insert_call(Symbol::STR_CONCAT);

                        if !buf.is_empty() {
                            segments.push(StrSegment::Plaintext(buf.into()));

                            buf = String::new();
                        }

                        let (loc_expr, new_output) = canonicalize_expr(
                            env,
                            var_store,
                            scope,
                            loc_expr.region,
                            loc_expr.value,
                        );

                        output.union(new_output);

                        segments.push(StrSegment::Interpolation(loc_expr));
                    } else {
                        env.problem(Problem::InvalidInterpolation(loc_expr.region));

                        return (
                            Expr::RuntimeError(RuntimeError::InvalidInterpolation(loc_expr.region)),
                            output,
                        );
                    }
                }
                EscapedChar(escaped) => buf.push(escaped.unescape()),
            }
        }
    }

    if !buf.is_empty() {
        segments.push(StrSegment::Plaintext(buf.into()));
    }

    (desugar_str_segments(var_store, segments, env.arena), output)
}

/// Resolve string interpolations by desugaring a sequence of StrSegments
/// into nested calls to Str.concat
fn desugar_str_segments<'a>(
    var_store: &mut VarStore,
    segments: Vec<'a, StrSegment>,
    arena: &'a Bump,
) -> Expr<'a> {
    let n = segments.len();
    let mut iter = segments.into_iter().rev();
    let mut loc_expr = match iter.next() {
        Some(StrSegment::Plaintext(string)) => Loc::at_zero(Expr::Str(string)),
        Some(StrSegment::Interpolation(loc_expr)) => {
            if n != 1 {
                loc_expr
            } else {
                // We concat with the empty string to ensure a type error when loc_expr is not a string
                let empty_string = Loc::at_zero(Expr::Str("".into()));

                let fn_expr = Loc::at_zero(Expr::Var(Symbol::STR_CONCAT, var_store.fresh()));
                let expr = Expr::Call(
                    Box::new((
                        var_store.fresh(),
                        fn_expr,
                        var_store.fresh(),
                        var_store.fresh(),
                        var_store.fresh(),
                    )),
                    vec![
                        (var_store.fresh(), empty_string),
                        (var_store.fresh(), loc_expr),
                    ],
                    CalledVia::StringInterpolation,
                );

                Loc::at_zero(expr)
            }
        }
        None => {
            // No segments? Empty string!

            Loc::at(Region::zero(), Expr::Str("".into()))
        }
    };

    for seg in iter {
        let loc_new_expr = match seg {
            StrSegment::Plaintext(string) => Loc::at(Region::zero(), Expr::Str(string)),
            StrSegment::Interpolation(loc_interpolated_expr) => loc_interpolated_expr,
        };

        let fn_expr = Loc::at_zero(Expr::Var(Symbol::STR_CONCAT, var_store.fresh()));
        let expr = Expr::Call {
            func_type: arena.alloc((
                var_store.fresh(),
                fn_expr,
                var_store.fresh(),
                var_store.fresh(),
                var_store.fresh(),
            )),
            args: &[
                (var_store.fresh(), loc_new_expr),
                (var_store.fresh(), loc_expr),
            ],
            called_via: CalledVia::StringInterpolation,
        };

        loc_expr = Loc::at(Region::zero(), expr);
    }

    loc_expr.value
}
