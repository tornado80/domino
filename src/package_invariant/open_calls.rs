// SPDX-License-Identifier: MIT OR Apache-2.0

//! Open calls (ADR 0017): the imports of a package, checked on its own, have unknown outcomes.
//!
//! [`close_package`] rewrites each oracle `O` of package `P` so that it calls nothing:
//!
//!  * The loops with literal bounds are unrolled first. Then each import call site gets an index
//!    `k`, from 1, in control-flow order (the then-branch before the else-branch).
//!  * `O` gets one more argument, [`CALLS_ARG`], of the call-result record type `<P>-<O>-calls`
//!    ([`record_name`]). Field `k` has the type `Maybe(<return type of site k>)`.
//!  * The body starts with `(open$1, ..., open$n) <- calls$`, and site `k` becomes
//!    `<assignee> <- Unwrap(open$k)`. `None` aborts `O` at the site, as an abort of the callee
//!    does; `Some v` binds `v`.
//!
//! An oracle without import calls stays as it is. The package that comes out imports nothing.
//! The record is an argument, so the check holds for every value of it: each site has its own
//! outcome, and two calls of the same import can return different values.

use miette::{NamedSource, SourceSpan};

use crate::{
    expressions::{Expression, ExpressionKind},
    identifier::{
        pkg_ident::{PackageIdentifier, PackageLocalIdentifier, PackageOracleArgIdentifier},
        Identifier,
    },
    package::{OracleDef, Package},
    statement::{
        Assignment, AssignmentRhs, CodeBlock, IfThenElse, InvokeOracle, Pattern, Statement,
    },
    transforms::loopunroll,
    types::{Type, TypeKind},
};

use super::error::{Error, Result};

/// The name of the oracle argument that holds the call-result record.
pub(crate) const CALLS_ARG: &str = "calls$";

/// The name of the call-result record type of oracle `oracle_name` of package `pkg_name`.
pub(crate) fn record_name(pkg_name: &str, oracle_name: &str) -> String {
    format!("{pkg_name}-{oracle_name}-calls")
}

/// `pkg` with each import call replaced by a read of the call-result record, and no imports.
///
/// Errors: [`Error::OpenCallInLoop`] when a call site is in a loop that could not be unrolled.
pub(crate) fn close_package(pkg: &Package) -> Result<Package> {
    let oracles = pkg
        .oracles
        .iter()
        .map(|odef| close_oracle(pkg, odef))
        .collect::<Result<_>>()?;
    Ok(Package {
        oracles,
        imports: vec![],
        ..pkg.clone()
    })
}

fn close_oracle(pkg: &Package, odef: &OracleDef) -> Result<OracleDef> {
    let mut sites = Sites {
        pkg,
        oracle_name: &odef.sig.name,
        field_types: vec![],
    };
    let code = sites.rewrite_block(&loopunroll::unroll_block(&odef.code))?;
    if sites.field_types.is_empty() {
        return Ok(odef.clone());
    }

    let record_ty = Type::from_kind(TypeKind::UserDefined(record_name(
        &pkg.name,
        &odef.sig.name,
    )));
    let calls_arg =
        Identifier::PackageIdentifier(PackageIdentifier::OracleArg(PackageOracleArgIdentifier {
            pkg_name: pkg.name.clone(),
            oracle_name: odef.sig.name.clone(),
            name: CALLS_ARG.to_string(),
            ty: record_ty.clone(),
            pkg_inst_name: None,
            game_name: None,
            game_inst_name: None,
            theorem_name: None,
        }));
    let fields = (1..=sites.field_types.len())
        .zip(&sites.field_types)
        .map(|(site, ty)| sites.field_local(site, ty.clone()))
        .collect();
    let destructure = Statement::Assignment(
        Assignment {
            pattern: Pattern::Tuple(fields),
            rhs: AssignmentRhs::Expression(calls_arg.into()),
        },
        odef.file_pos,
    );

    let mut sig = odef.sig.clone();
    sig.args.push((CALLS_ARG.to_string(), record_ty));
    Ok(OracleDef {
        sig,
        code: CodeBlock(std::iter::once(destructure).chain(code.0).collect()),
        file_pos: odef.file_pos,
    })
}

/// The import call sites of one oracle, found while rewriting its body.
struct Sites<'a> {
    pkg: &'a Package,
    oracle_name: &'a str,
    /// the field type of each site so far, in control-flow order
    field_types: Vec<Type>,
}

impl Sites<'_> {
    fn rewrite_block(&mut self, block: &CodeBlock) -> Result<CodeBlock> {
        block
            .0
            .iter()
            .map(|stmt| self.rewrite_stmt(stmt))
            .collect::<Result<_>>()
            .map(CodeBlock)
    }

    fn rewrite_stmt(&mut self, stmt: &Statement) -> Result<Statement> {
        Ok(match stmt {
            Statement::Assignment(
                Assignment {
                    pattern,
                    rhs: AssignmentRhs::Invoke { oracle_name, .. },
                },
                span,
            ) => self.read_site(pattern.clone(), oracle_name, *span),
            Statement::InvokeOracle(InvokeOracle {
                oracle_name,
                file_pos,
                ..
            }) => {
                // the value is not used, but `None` still aborts
                let discard = self.local(
                    &format!("open${}$discarded", self.field_types.len() + 1),
                    self.return_type(oracle_name),
                );
                self.read_site(Pattern::Ident(discard), oracle_name, *file_pos)
            }
            Statement::IfThenElse(ite) => Statement::IfThenElse(IfThenElse {
                then_block: self.rewrite_block(&ite.then_block)?,
                else_block: self.rewrite_block(&ite.else_block)?,
                ..ite.clone()
            }),
            Statement::For(_, _, _, body, span) if has_call(body) => {
                return Err(Error::OpenCallInLoop {
                    pkg_name: self.pkg.name.clone(),
                    oracle_name: self.oracle_name.to_string(),
                    src: NamedSource::new(&self.pkg.file_name, self.pkg.file_contents.clone()),
                    at: *span,
                })
            }
            Statement::For(..)
            | Statement::Abort(_)
            | Statement::Return(..)
            | Statement::Assignment(..) => stmt.clone(),
        })
    }

    /// `<pattern> <- Unwrap(open$k)` for the next site `k`.
    fn read_site(&mut self, pattern: Pattern, oracle_name: &str, span: SourceSpan) -> Statement {
        let ty = self.return_type(oracle_name);
        self.field_types.push(Type::maybe(ty.clone()));
        let site = self.field_types.len();
        let field = self.field_local(site, Type::maybe(ty));
        Statement::Assignment(
            Assignment {
                pattern,
                rhs: AssignmentRhs::Expression(Expression::from_kind(ExpressionKind::Unwrap(
                    Box::new(field.into()),
                ))),
            },
            span,
        )
    }

    /// The return type of the import `oracle_name`. The parser has checked that it exists.
    fn return_type(&self, oracle_name: &str) -> Type {
        self.pkg
            .imports
            .iter()
            .find(|(sig, _)| sig.name == oracle_name)
            .map(|(sig, _)| sig.ty.clone())
            .unwrap_or_else(|| panic!("package {} does not import {oracle_name}", self.pkg.name))
    }

    /// The local that holds field `site` of the record.
    fn field_local(&self, site: usize, ty: Type) -> Identifier {
        self.local(&format!("open${site}"), ty)
    }

    fn local(&self, name: &str, ty: Type) -> Identifier {
        Identifier::PackageIdentifier(PackageIdentifier::Local(PackageLocalIdentifier {
            pkg_name: self.pkg.name.clone(),
            oracle_name: self.oracle_name.to_string(),
            name: name.to_string(),
            ty,
            pkg_inst_name: None,
            game_name: None,
            game_inst_name: None,
            theorem_name: None,
        }))
    }
}

fn has_call(block: &CodeBlock) -> bool {
    block.0.iter().any(|stmt| match stmt {
        Statement::Assignment(
            Assignment {
                rhs: AssignmentRhs::Invoke { .. },
                ..
            },
            _,
        )
        | Statement::InvokeOracle(_) => true,
        Statement::IfThenElse(ite) => has_call(&ite.then_block) || has_call(&ite.else_block),
        Statement::For(_, _, _, body, _) => has_call(body),
        Statement::Abort(_) | Statement::Return(..) | Statement::Assignment(..) => false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::tests::packages;

    const CTR: &str = r#"
package Ctr {
    params {
        n: Integer,
    }

    state {
        ctr: Integer,
    }

    import oracles {
        Get(x: Integer) -> Bits(n),
        Put(y: Integer),
    }

    oracle Step(x: Integer) -> Bits(n) {
        y <- invoke Get(x);
        if (x == 0) {
            invoke Put(x);
        } else {
            z <- invoke Get(x);
        }
        for i: 1 <= i <= 2 {
            invoke Put(x);
        }
        ctr <- (ctr + 1);
        return y;
    }

    oracle Peek() -> Integer {
        return ctr;
    }

    oracle Loop(m: Integer) {
        for i: 1 <= i <= m {
            invoke Put(i);
        }
        return;
    }
}
"#;

    fn ctr() -> Package {
        packages::parse(CTR.trim_start(), "Ctr.pkg.ssp").1
    }

    fn oracle(pkg: Package, name: &str) -> OracleDef {
        let pkg = Package {
            oracles: pkg
                .oracles
                .into_iter()
                .filter(|odef| odef.sig.name != "Loop")
                .collect(),
            ..pkg
        };
        close_package(&pkg)
            .unwrap()
            .oracles
            .into_iter()
            .find(|odef| odef.sig.name == name)
            .unwrap()
    }

    #[test]
    fn each_call_site_is_one_field_in_control_flow_order() {
        let step = oracle(ctr(), "Step");
        let (name, ty) = step.sig.args.last().unwrap();
        assert_eq!(name, CALLS_ARG);
        assert_eq!(
            *ty.kind(),
            TypeKind::UserDefined("Ctr-Step-calls".to_string())
        );
        let Statement::Assignment(
            Assignment {
                pattern: Pattern::Tuple(fields),
                ..
            },
            _,
        ) = &step.code.0[0]
        else {
            panic!("{:?}", step.code.0[0])
        };
        let fields: Vec<(String, String)> = fields
            .iter()
            .map(|f| (f.ident(), f.get_type().to_string()))
            .collect();
        // Get, Put (then), Get (else), Put twice (the unrolled loop)
        let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, ["open$1", "open$2", "open$3", "open$4", "open$5"]);
        assert!(fields[0].1.starts_with("Maybe(Bits"), "{fields:?}");
        assert!(fields[1].1.starts_with("Maybe(()"), "{fields:?}");
        assert!(!has_call(&step.code));
    }

    #[test]
    fn an_oracle_without_calls_is_unchanged() {
        let pkg = ctr();
        let peek = oracle(pkg.clone(), "Peek");
        let orig = pkg.oracles.iter().find(|o| o.sig.name == "Peek").unwrap();
        assert_eq!(&peek, orig);
    }

    #[test]
    fn a_call_in_a_loop_that_is_not_unrolled_is_an_error() {
        let err = close_package(&ctr()).unwrap_err();
        let Error::OpenCallInLoop { oracle_name, .. } = &err else {
            panic!("{err}")
        };
        assert_eq!(oracle_name, "Loop");
    }

    #[test]
    fn the_closed_package_imports_nothing() {
        let pkg = ctr();
        let pkg = Package {
            oracles: pkg.oracles[..2].to_vec(),
            ..pkg
        };
        assert!(close_package(&pkg).unwrap().imports.is_empty());
    }
}
