// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::package::{Composition, Edge, OracleDef, Package, PackageInstance};
use crate::statement::{Assignment, AssignmentRhs, CodeBlock, IfThenElse, InvokeOracle, Statement};

use std::collections::HashMap;

pub struct Transformation<'a>(pub &'a Composition);

#[derive(Debug)]
pub(crate) struct ResolutionError(pub(crate) Vec<(String, usize)>); // (oracle_name, position)

type Result<T> = std::result::Result<T, ResolutionError>;

/// The edge each name a package instance invokes resolves to. An import the composition does
/// not wire maps to `None`: an **open call** (ADR 0017), whose invoke keeps `edge: None`. A
/// parsed game wires every import, so only a package checked on its own (the package tree,
/// symbolic-execution story 29) has open calls. A name that is not imported is an error.
type Table<'a> = HashMap<String, Option<&'a Edge>>;

fn transform_helper_outer(table: &Table<'_>, block: CodeBlock) -> Result<CodeBlock> {
    fn transform_helper(
        table: &Table<'_>,
        block: CodeBlock,
        err_stmts: &mut Vec<(String, usize)>,
    ) -> CodeBlock {
        let mut pos = 0;
        let out = block
            .0
            .into_iter()
            .filter_map(|stmt| {
                let current_pos = pos;
                pos += 1;
                match stmt {
                    Statement::Assignment(
                        Assignment {
                            pattern,
                            rhs:
                                AssignmentRhs::Invoke {
                                    oracle_name,
                                    args,
                                    edge: _,
                                    return_type,
                                },
                        },
                        span,
                    ) => {
                        if let Some(edge) = table.get(&oracle_name) {
                            Some(Statement::Assignment(
                                Assignment {
                                    pattern,
                                    rhs: AssignmentRhs::Invoke {
                                        oracle_name,
                                        args,
                                        edge: edge.cloned(),
                                        return_type,
                                    },
                                },
                                span,
                            ))
                        } else {
                            err_stmts.push((oracle_name, current_pos));
                            None
                        }
                    }
                    Statement::InvokeOracle(InvokeOracle {
                        oracle_name,
                        args,
                        edge: _,
                        file_pos,
                    }) => {
                        if let Some(edge) = table.get(&oracle_name) {
                            Some(Statement::InvokeOracle(InvokeOracle {
                                oracle_name,
                                args,
                                edge: edge.cloned(),
                                file_pos,
                            }))
                        } else {
                            err_stmts.push((oracle_name, current_pos));
                            None
                        }
                    }
                    Statement::IfThenElse(ite) => Some(Statement::IfThenElse(IfThenElse {
                        then_block: transform_helper(table, ite.then_block.clone(), err_stmts),
                        else_block: transform_helper(table, ite.else_block.clone(), err_stmts),
                        ..ite.clone()
                    })),
                    Statement::For(var, lower, upper, code, span) => Some(Statement::For(
                        var,
                        lower,
                        upper,
                        transform_helper(table, code.clone(), err_stmts),
                        span,
                    )),
                    _ => Some(stmt),
                }
            })
            .collect();

        CodeBlock(out)
    }

    let mut err_stmts = vec![];

    let out = transform_helper(table, block, &mut err_stmts);

    if !err_stmts.is_empty() {
        Err(ResolutionError(err_stmts))
    } else {
        Ok(out)
    }
}

impl super::Transformation for Transformation<'_> {
    type Err = ResolutionError;
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ())> {
        let mut pkgs = vec![];

        for (pos, inst) in self.0.pkgs.iter().enumerate() {
            let mut table: Table<'_> = inst
                .pkg
                .imports
                .iter()
                .map(|(sig, _)| (sig.name.clone(), None))
                .collect();
            let relevant = self.0.edges.iter().filter(|edge| edge.from() == pos);

            for edge in relevant {
                let name = if let Some(alias) = edge.alias() {
                    alias.clone()
                } else {
                    edge.sig().name.clone()
                };
                table.insert(name, Some(edge));
            }

            let mut odefs = vec![];
            for oracle in &inst.pkg.oracles {
                odefs.push(OracleDef {
                    code: transform_helper_outer(&table, oracle.code.clone())?,
                    ..oracle.clone()
                });
            }

            pkgs.push(PackageInstance {
                pkg: Package {
                    oracles: odefs,
                    ..inst.pkg.clone()
                },
                ..inst.clone()
            });
        }
        Ok((
            Composition {
                pkgs,
                ..self.0.clone()
            },
            (),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::tests::packages;
    use crate::transforms::Transformation as _;

    const PKG: &str = r#"
package Ctr {
    state {
        ctr: Integer,
    }

    import oracles {
        Get(x: Integer) -> Integer,
    }

    oracle Step(x: Integer) -> Integer {
        y <- invoke Get(x);
        return y;
    }
}
"#;

    fn alone(pkg: Package) -> Composition {
        Composition {
            pkgs: vec![PackageInstance::new("ctr", "G", &pkg, vec![], vec![])],
            edges: vec![],
            exports: vec![],
            name: "G".to_string(),
            consts: vec![],
            invariants: vec![],
            file_name: pkg.file_name.clone(),
            file_contents: pkg.file_contents.clone(),
        }
    }

    fn invoke_edges(block: &CodeBlock) -> Vec<Option<Edge>> {
        block
            .0
            .iter()
            .filter_map(|stmt| match stmt {
                Statement::Assignment(
                    Assignment {
                        rhs: AssignmentRhs::Invoke { edge, .. },
                        ..
                    },
                    _,
                ) => Some(edge.clone()),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn an_import_the_composition_does_not_wire_is_an_open_call() {
        let (_, pkg) = packages::parse(PKG.trim_start(), "Ctr.pkg.ssp");
        let (comp, ()) = Transformation(&alone(pkg)).transform().unwrap();
        assert_eq!(invoke_edges(&comp.pkgs[0].pkg.oracles[0].code), [None]);
    }

    #[test]
    fn a_name_the_package_does_not_import_is_an_error() {
        let (_, mut pkg) = packages::parse(PKG.trim_start(), "Ctr.pkg.ssp");
        pkg.imports.clear();
        let Err(ResolutionError(failed)) = Transformation(&alone(pkg)).transform() else {
            panic!("an invoke of an unknown name resolves")
        };
        assert_eq!(failed, [("Get".to_string(), 0)]);
    }
}
