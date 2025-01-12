use bumpalo::collections::Vec;
use bumpalo::Bump;
use roc_collections::{soa::index_push_new, ArenaVecMap};
use roc_module::symbol::{IdentId, Symbol};
use roc_region::all::{Loc, Region};
use roc_types::{
    subs::{IllegalCycleMark, Variable},
    types::EarlyReturnKind,
};
use soa::Index;

use crate::{
    annotation::Annotation,
    def::Def,
    expr::{AnnotatedMark, ClosureData, Expr, Recursive},
    pattern::Pattern,
};

#[derive(Clone, Debug)]
pub struct Declarations<'a> {
    arena: &'a Bump,
    pub declarations: Vec<'a, DeclarationTag>,

    /// same lengths as declarations; has a dummy value if not applicable
    pub variables: Vec<'a, Variable>,
    pub symbols: Vec<'a, Loc<Symbol>>,
    pub annotations: Vec<'a, Option<crate::def::Annotation<'a>>>,

    pub host_exposed_annotations: ArenaVecMap<'a, usize, (Variable, crate::def::Annotation<'a>)>,

    pub function_bodies: Vec<'a, Loc<FunctionDef>>,
    pub expressions: Vec<'a, Loc<Expr<'a>>>,
    pub destructs: Vec<'a, DestructureDef>,
}

impl<'a> Declarations<'a> {
    pub fn new_in(arena: &'a Bump) -> Self {
        Self::with_capacity_in(1, arena)
    }

    pub fn with_capacity_in(capacity: usize, arena: &'a Bump) -> Self {
        Self {
            arena,
            declarations: Vec::with_capacity_in(capacity, arena),
            variables: Vec::with_capacity_in(capacity, arena),
            symbols: Vec::with_capacity_in(capacity, arena),
            annotations: Vec::with_capacity_in(capacity, arena),
            host_exposed_annotations: ArenaVecMap::new_in(arena),
            function_bodies: Vec::with_capacity_in(capacity, arena),
            expressions: Vec::with_capacity_in(capacity, arena),
            destructs: Vec::new_in(arena), // number of destructs is probably low
        }
    }

    /// To store a recursive group in the vectors without nesting, we first push a "header"
    /// here, then push the definitions that are part of that recursive group
    pub fn push_recursive_group(&mut self, length: u16, cycle_mark: IllegalCycleMark) -> usize {
        let index = self.declarations.len();

        let tag = DeclarationTag::MutualRecursion { length, cycle_mark };
        self.declarations.push(tag);

        // dummy values
        self.variables.push(Variable::NULL);
        self.symbols.push(Loc::at_zero(Symbol::ATTR_ATTR));
        self.annotations.push(None);
        self.expressions.push(Loc::at_zero(Expr::EmptyRecord));

        index
    }

    pub fn push_recursive_def(
        &mut self,
        symbol: Loc<Symbol>,
        loc_closure_data: Loc<ClosureData<'a>>,
        expr_var: Variable,
        annotation: Option<Annotation<'a>>,
        host_annotation: Option<(Variable, Annotation<'a>)>,
        specializes: Option<Symbol>,
    ) -> usize {
        let index = self.declarations.len();

        let function_def = FunctionDef {
            return_type: loc_closure_data.value.return_type,
            fx_type: loc_closure_data.value.fx_type,
            early_returns: loc_closure_data.value.early_returns,
            arguments: loc_closure_data.value.arguments,
        };

        let loc_function_def = Loc::at(loc_closure_data.region, function_def);

        let function_def_index = index_push_new(&mut self.function_bodies, loc_function_def);

        let tag = match loc_closure_data.value.recursive {
            Recursive::NotRecursive | Recursive::Recursive => {
                DeclarationTag::Recursive(function_def_index)
            }
            Recursive::TailRecursive => DeclarationTag::TailRecursive(function_def_index),
        };

        if let Some(annotation) = host_annotation {
            self.host_exposed_annotations
                .insert(self.declarations.len(), annotation);
        }

        self.declarations.push(tag);
        self.variables.push(expr_var);
        self.symbols.push(symbol);
        self.annotations.push(annotation);

        self.expressions.push(*loc_closure_data.value.loc_body);

        if let Some(specializes) = specializes {
            self.specializes.insert(index, specializes);
        }

        index
    }

    pub fn push_function_def(
        &mut self,
        symbol: Loc<Symbol>,
        loc_closure_data: Loc<ClosureData>,
        expr_var: Variable,
        annotation: Option<Annotation>,
        host_annotation: Option<(Variable, Annotation)>,
        specializes: Option<Symbol>,
    ) -> usize {
        let index = self.declarations.len();

        let function_def = FunctionDef {
            return_type: loc_closure_data.value.return_type,
            fx_type: loc_closure_data.value.fx_type,
            early_returns: loc_closure_data.value.early_returns,
            arguments: loc_closure_data.value.arguments,
        };

        let loc_function_def = Loc::at(loc_closure_data.region, function_def);

        let function_def_index = index_push_new(&mut self.function_bodies, loc_function_def);

        if let Some(annotation) = host_annotation {
            self.host_exposed_annotations
                .insert(self.declarations.len(), annotation);
        }

        self.declarations
            .push(DeclarationTag::Function(function_def_index));
        self.variables.push(expr_var);
        self.symbols.push(symbol);
        self.annotations.push(annotation);

        self.expressions.push(*loc_closure_data.value.loc_body);

        if let Some(specializes) = specializes {
            self.specializes.insert(index, specializes);
        }

        index
    }

    pub fn push_expect(
        &mut self,
        preceding_comment: Region,
        name: Symbol,
        loc_expr: Loc<Expr>,
    ) -> usize {
        let index = self.declarations.len();

        self.declarations.push(DeclarationTag::Expectation);
        self.variables.push(Variable::BOOL);
        self.symbols.push(Loc::at(preceding_comment, name));
        self.annotations.push(None);

        self.expressions.push(loc_expr);

        index
    }

    pub fn push_value_def(
        &mut self,
        symbol: Loc<Symbol>,
        loc_expr: Loc<Expr>,
        expr_var: Variable,
        annotation: Option<Annotation>,
        host_annotation: Option<(Variable, Annotation)>,
        specializes: Option<Symbol>,
    ) -> usize {
        let index = self.declarations.len();

        if let Some(annotation) = host_annotation {
            self.host_exposed_annotations
                .insert(self.declarations.len(), annotation);
        }

        self.arity_by_name.insert(symbol.value.ident_id(), 0);

        self.declarations.push(DeclarationTag::Value);
        self.variables.push(expr_var);
        self.symbols.push(symbol);
        self.annotations.push(annotation);

        self.expressions.push(loc_expr);

        if let Some(specializes) = specializes {
            self.specializes.insert(index, specializes);
        }

        index
    }

    /// Any def with a weird pattern
    pub fn push_destructure_def(
        &mut self,
        loc_pattern: Loc<Pattern<'a>>,
        loc_expr: Loc<Expr>,
        expr_var: Variable,
        annotation: Option<Annotation>,
        pattern_vars: ArenaVecMap<'a, Symbol, Variable>,
    ) -> usize {
        let index = self.declarations.len();

        let destruct_def = DestructureDef {
            loc_pattern,
            pattern_vars,
        };

        let destructure_def_index = index_push_new(&mut self.destructs, destruct_def);

        self.declarations
            .push(DeclarationTag::Destructure(destructure_def_index));
        self.variables.push(expr_var);
        self.symbols.push(Loc::at_zero(Symbol::ATTR_ATTR));
        self.annotations.push(annotation);

        self.expressions.push(loc_expr);

        index
    }

    pub fn push_def(&mut self, def: Def<'a>) {
        match def.loc_pattern.value {
            Pattern::Identifier(symbol) => match def.loc_expr.value {
                Expr::Closure(closure_data) => match closure_data.recursive {
                    Recursive::NotRecursive => {
                        self.push_function_def(
                            Loc::at(def.loc_pattern.region, symbol),
                            Loc::at(def.loc_expr.region, closure_data),
                            def.expr_var,
                            def.annotation,
                            None,
                            None,
                        );
                    }

                    Recursive::Recursive | Recursive::TailRecursive => {
                        self.push_recursive_def(
                            Loc::at(def.loc_pattern.region, symbol),
                            Loc::at(def.loc_expr.region, closure_data),
                            def.expr_var,
                            def.annotation,
                            None,
                            None,
                        );
                    }
                },
                _ => {
                    self.push_value_def(
                        Loc::at(def.loc_pattern.region, symbol),
                        def.loc_expr,
                        def.expr_var,
                        def.annotation,
                        None,
                        None,
                    );
                }
            },
            _ => todo!(),
        }
    }

    pub fn update_builtin_def(&mut self, index: usize, def: Def) {
        match def.loc_pattern.value {
            Pattern::Identifier(s) => assert_eq!(s, self.symbols[index].value),
            p => internal_error!("a builtin definition has a non-identifier pattern: {:?}", p),
        }

        match def.loc_expr.value {
            Expr::Closure(closure_data) => {
                let function_def = FunctionDef {
                    return_type: closure_data.return_type,
                    fx_type: closure_data.fx_type,
                    early_returns: closure_data.early_returns,
                    arguments: closure_data.arguments,
                };

                let loc_function_def = Loc::at(def.loc_expr.region, function_def);

                let function_def_index =
                    index_push_new(&mut self.function_bodies, loc_function_def);

                self.declarations[index] = DeclarationTag::Function(function_def_index);
                self.expressions[index] = *closure_data.loc_body;
                self.variables[index] = def.expr_var;
            }
            _ => {
                self.declarations[index] = DeclarationTag::Value;
                self.expressions[index] = def.loc_expr;
                self.variables[index] = def.expr_var;
            }
        }
    }

    pub fn len(&self) -> usize {
        self.declarations.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter_top_down(&self) -> impl Iterator<Item = (usize, DeclarationTag)> + '_ {
        self.declarations.iter().scan(0, |state, e| {
            let length_so_far = *state;

            *state += e.len();

            Some((length_so_far, *e))
        })
    }

    pub fn iter_bottom_up(&self) -> impl Iterator<Item = (usize, DeclarationTag)> + '_ {
        self.declarations
            .iter()
            .rev()
            .scan(self.declarations.len() - 1, |state, e| {
                let length_so_far = *state;

                *state = length_so_far.saturating_sub(e.len());

                Some((length_so_far, *e))
            })
    }

    pub fn expects(&self) -> ExpectCollector {
        let mut collector = ExpectCollector {
            expects: VecMap::default(),
            has_dbgs: false,
        };

        let var = Variable::EMPTY_RECORD;

        for index in 0..self.len() {
            use crate::expr::DeclarationTag::*;

            match self.declarations[index] {
                Value | Function(_) | Recursive(_) | TailRecursive(_) | Destructure(_) => {
                    // def pattern has no default expressions, so skip
                    let loc_expr = &self.expressions[index];

                    collector.visit_expr(&loc_expr.value, loc_expr.region, var);
                }
                MutualRecursion { .. } => {
                    // the self of this group will be treaded individually by later iterations
                }
                Expectation => {
                    let loc_expr =
                        toplevel_expect_to_inline_expect_pure(self.expressions[index].clone());

                    collector.visit_expr(&loc_expr.value, loc_expr.region, var);
                }
            }
        }

        collector
    }
}

roc_error_macros::assert_sizeof_default!(DeclarationTag, 8);

#[derive(Clone, Copy, Debug)]
pub enum DeclarationTag<'a> {
    Value,
    Expectation,
    Function(Index<Loc<FunctionDef<'a>>>),
    // TODO: do we need recursion tracking?
    Recursive(Index<Loc<FunctionDef<'a>>>),
    TailRecursive(Index<Loc<FunctionDef<'a>>>),
    Destructure(Index<DestructureDef<'a>>),
    MutualRecursion {
        length: u16,
        cycle_mark: IllegalCycleMark,
    },
}

impl<'a> DeclarationTag<'a> {
    fn len(self) -> usize {
        use DeclarationTag::*;

        match self {
            Function(_) | Recursive(_) | TailRecursive(_) => 1,
            Value => 1,
            Expectation => 1,
            Destructure(_) => 1,
            MutualRecursion { length, .. } => length as usize + 1,
        }
    }
}

#[derive(Clone, Debug)]
pub struct FunctionDef<'a> {
    pub return_type: Variable,
    pub fx_type: Variable,
    pub early_returns: Vec<'a, (Variable, Region, EarlyReturnKind)>,
    pub arguments: Vec<'a, (Variable, AnnotatedMark, Loc<Pattern<'a>>)>,
}

#[derive(Clone, Debug)]
pub struct DestructureDef<'a> {
    pub loc_pattern: Loc<Pattern<'a>>,
    pub pattern_vars: ArenaVecMap<'a, Symbol, Variable>,
}
