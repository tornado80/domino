// SPDX-License-Identifier: MIT OR Apache-2.0

use std::convert::Infallible;

use crate::{
    expressions::{Expression, ExpressionKind},
    identifier::{pkg_ident::PackageIdentifier, Identifier},
    package::Composition,
    parser::package::ForComp,
    statement::{
        Assignment, AssignmentRhs, CodeBlock, IfThenElse, InvokeOracle, Pattern, Statement,
    },
};

pub struct Transformation<'a>(pub &'a Composition);

impl super::Transformation for Transformation<'_> {
    type Err = Infallible;
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), Infallible> {
        let insts = self.0.pkgs.iter().map(|inst| {
            let mut newinst = inst.clone();
            newinst.pkg.oracles.iter_mut().for_each(|oracle| {
                oracle.code = unroll(&oracle.code, &Vec::new());
            });
            newinst
        });
        Ok((
            Composition {
                pkgs: insts.collect(),
                ..self.0.clone()
            },
            (),
        ))
    }
}

/// The values of the loop variable `ident` of `for ident: lower <(=) ident <(=) upper`, with the
/// comparisons the loop declares.
fn iterations(ident: &Identifier, lower: i64, upper: i64) -> std::ops::Range<i64> {
    let (start_comp, end_comp) = match ident {
        Identifier::PackageIdentifier(PackageIdentifier::CodeLoopVar(var)) => {
            (var.start_comp, var.end_comp)
        }
        other => unreachable!("the variable of a `for` loop is a code loop variable: {other:?}"),
    };
    let start = if start_comp == ForComp::Lt {
        lower + 1
    } else {
        lower
    };
    let end = if end_comp == ForComp::Lte {
        upper + 1
    } else {
        upper
    };
    start..end
}

/// `cb` with each loop that has literal bounds unrolled. Other loops stay.
pub(crate) fn unroll_block(cb: &CodeBlock) -> CodeBlock {
    unroll(cb, &Vec::new())
}

fn unroll(cb: &CodeBlock, subst: &Vec<(&Identifier, &Identifier)>) -> CodeBlock {
    let mut newcode = Vec::new();

    let fn_subst = |expr: Expression| {
        if let Some(ident) = expr.as_identifier() {
            if let Some((_, sub)) = subst.iter().find(|(old, _)| &ident == old) {
                (*sub).clone().into()
            } else {
                expr
            }
        } else {
            expr
        }
    };

    for stmt in &cb.0 {
        match stmt {
            Statement::For(ident, lower, upper, code, span) => {
                if let (
                    ExpressionKind::IntegerLiteral(lower),
                    ExpressionKind::IntegerLiteral(upper),
                ) = (lower.kind(), upper.kind())
                {
                    let gen_ident = Identifier::Generated(ident.ident(), ident.get_type().clone());

                    let mut newsubst = subst.clone();
                    newsubst.push((ident, &gen_ident));
                    let loopcode = unroll(code, &newsubst);

                    for i in iterations(ident, *lower, *upper) {
                        newcode.push(Statement::Assignment(
                            Assignment {
                                pattern: Pattern::Ident(gen_ident.clone()),
                                rhs: AssignmentRhs::Expression(Expression::integer(i)),
                            },
                            *span,
                        ));
                        newcode.extend(loopcode.0.iter().cloned());
                    }
                } else {
                    newcode.push(Statement::For(
                        ident.clone(),
                        lower.map(fn_subst),
                        upper.map(fn_subst),
                        unroll(code, subst),
                        *span,
                    ));
                }
            }
            Statement::IfThenElse(ite) => {
                newcode.push(Statement::IfThenElse(IfThenElse {
                    cond: ite.cond.map(fn_subst),
                    then_block: unroll(&ite.then_block, subst),
                    else_block: unroll(&ite.else_block, subst),
                    ..ite.clone()
                }));
            }
            Statement::Assignment(assign, span) => {
                let pattern = if let Pattern::Table { ident, index } = &assign.pattern {
                    Pattern::Table {
                        ident: ident.clone(),
                        index: index.map(fn_subst),
                    }
                } else {
                    assign.pattern.clone()
                };
                let rhs = match assign.rhs.clone() {
                    AssignmentRhs::Expression(e) => AssignmentRhs::Expression(e.map(fn_subst)),
                    r @ AssignmentRhs::Sample { .. } => r,
                    AssignmentRhs::Invoke {
                        oracle_name,
                        args,
                        edge,
                        return_type,
                    } => AssignmentRhs::Invoke {
                        oracle_name,
                        args: args.iter().map(|expr| expr.map(fn_subst)).collect(),
                        edge,
                        return_type,
                    },
                };
                newcode.push(Statement::Assignment(Assignment { pattern, rhs }, *span));
            }
            Statement::InvokeOracle(io) => {
                newcode.push(Statement::InvokeOracle(InvokeOracle {
                    args: io.args.iter().map(|expr| expr.map(fn_subst)).collect(),
                    ..io.clone()
                }));
            }
            Statement::Return(expr, span) => newcode.push(Statement::Return(
                expr.as_ref().map(|expr| expr.map(fn_subst)),
                *span,
            )),
            Statement::Abort(_) => newcode.push(stmt.clone()),
        }
    }

    CodeBlock(newcode)
}

#[cfg(test)]
mod iteration_tests {
    use super::*;
    use crate::identifier::pkg_ident::PackageOracleCodeLoopVarIdentifier;

    fn var(start_comp: ForComp, end_comp: ForComp) -> Identifier {
        Identifier::PackageIdentifier(PackageIdentifier::CodeLoopVar(
            PackageOracleCodeLoopVarIdentifier {
                pkg_name: "P".into(),
                name: "i".into(),
                start: Box::new(Expression::integer(1)),
                end: Box::new(Expression::integer(2)),
                start_comp,
                end_comp,
                pkg_inst_name: None,
                game_name: None,
                game_inst_name: None,
                theorem_name: None,
            },
        ))
    }

    #[test]
    fn the_loop_bounds_follow_the_declared_comparisons() {
        assert_eq!(iterations(&var(ForComp::Lte, ForComp::Lte), 1, 2), 1..3);
        assert_eq!(iterations(&var(ForComp::Lte, ForComp::Lt), 1, 2), 1..2);
        assert_eq!(iterations(&var(ForComp::Lt, ForComp::Lte), 1, 2), 2..3);
        assert_eq!(iterations(&var(ForComp::Lt, ForComp::Lt), 0, 3), 1..3);
    }
}
