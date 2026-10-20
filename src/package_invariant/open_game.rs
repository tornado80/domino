// SPDX-License-Identifier: MIT OR Apache-2.0

//! The one-game theorem a package invariant is proved in.
//!
//! The package is closed first ([`super::open_calls`]): its import calls read the call-result
//! record, so it imports nothing and the game has no other package. The game exports each oracle
//! of the package. The package parameters become game constants and then theorem constants of
//! the same name, with no value: the invariant is proved for arbitrary package constants.
//!
//! The SMT writer works on a [`Theorem`] with [`GameInstance`]s, so this module builds one. There
//! is no virtual environment package (ADR 0017).

use miette::SourceSpan;

use crate::{
    expressions::Expression,
    identifier::{
        game_ident::{GameConstIdentifier, GameIdentifier},
        pkg_ident::{PackageConstIdentifier, PackageIdentifier},
        theorem_ident::TheoremConstIdentifier,
        Identifier,
    },
    package::{Composition, Export, Package, PackageInstance},
    theorem::{GameInstance, Theorem},
    types::{CountSpec, Type, TypeKind},
};

/// The theorem with one game instance: the closed package `pkg`, alone.
///
/// The game, its instance and the theorem are named `<P>$Invariant`; the package instance keeps
/// the name of the package.
pub(crate) fn open_game_theorem<'a>(pkg: &Package) -> Theorem<'a> {
    let pkg_name = pkg.name.clone();
    let theorem_name = format!("{pkg_name}$Invariant");
    let game_name = theorem_name.clone();

    let mut game_consts: Vec<(String, Type)> = pkg
        .params
        .iter()
        .map(|(name, ty, _)| {
            (
                name.clone(),
                lift_type(ty, &pkg_name, Level::Game(&game_name)),
            )
        })
        .collect();
    game_consts.sort();

    let pkg_inst = PackageInstance::new(
        &pkg_name,
        &game_name,
        pkg,
        game_const_assignments(&pkg.params, &pkg_name, &game_name, &game_consts),
        vec![],
    );
    let exports = pkg_inst
        .pkg
        .oracles
        .iter()
        .map(|odef| {
            Export::new(
                0,
                pkg_inst.instantiate_oracle_signature(odef.sig.clone()),
                None,
            )
        })
        .collect();

    let game = Composition {
        pkgs: vec![pkg_inst],
        edges: vec![],
        exports,
        name: game_name.clone(),
        consts: game_consts.clone(),
        invariants: vec![],
        // the game has no source of its own; point at the package
        file_name: pkg.file_name.clone(),
        file_contents: pkg.file_contents.clone(),
    };

    let theorem_consts: Vec<(String, Type)> = game_consts
        .iter()
        .map(|(name, ty)| {
            (
                name.clone(),
                lift_type(ty, &game_name, Level::Theorem(&theorem_name)),
            )
        })
        .collect();

    let game_inst_consts: Vec<(GameConstIdentifier, Expression)> = game_consts
        .iter()
        .zip(&theorem_consts)
        .map(|((name, game_ty), (_, theorem_ty))| {
            let game_const = GameConstIdentifier {
                game_name: game_name.clone(),
                name: name.clone(),
                ty: game_ty.clone(),
                game_inst_name: None,
                theorem_name: None,
                inst_info: None,
                assigned_value: None,
            };
            let theorem_const = TheoremConstIdentifier {
                theorem_name: theorem_name.clone(),
                name: name.clone(),
                ty: theorem_ty.clone(),
                inst_info: None,
            };
            (
                game_const,
                Expression::from(Identifier::from(theorem_const)),
            )
        })
        .collect();

    let game_inst = GameInstance::new(
        theorem_name.clone(),
        theorem_name.clone(),
        game,
        vec![],
        game_inst_consts,
    );

    Theorem {
        name: theorem_name,
        consts: theorem_consts,
        instances: vec![game_inst],
        assumptions: vec![],
        proofs: vec![],
        game_hops: vec![],
        pkgs: vec![pkg.clone()],
    }
}

/// Assigns each parameter of a package the game constant of the same name.
fn game_const_assignments(
    params: &[(String, Type, SourceSpan)],
    pkg_name: &str,
    game_name: &str,
    game_consts: &[(String, Type)],
) -> Vec<(PackageConstIdentifier, Expression)> {
    let mut assignments: Vec<_> = params
        .iter()
        .map(|(name, _ty, _span)| {
            let (_, game_ty) = game_consts
                .iter()
                .find(|(game_const_name, _)| game_const_name == name)
                .unwrap_or_else(|| {
                    panic!("no game constant for parameter `{name}' of package `{pkg_name}'")
                });

            let value = Expression::from(Identifier::GameIdentifier(GameIdentifier::Const(
                GameConstIdentifier {
                    game_name: game_name.to_string(),
                    name: name.clone(),
                    ty: game_ty.clone(),
                    game_inst_name: None,
                    theorem_name: None,
                    inst_info: None,
                    assigned_value: None,
                },
            )));

            let ident = PackageConstIdentifier {
                pkg_name: pkg_name.to_string(),
                name: name.clone(),
                ty: value.get_type(),
                game_name: None,
                game_assignment: None,
                pkg_inst_name: None,
                game_inst_name: None,
                theorem_name: None,
            };

            (ident, value)
        })
        .collect();

    assignments.sort();
    assignments
}

/// The two levels the constants of the package are lifted to. A `Bits(n)` length is spelled with a different kind of
/// identifier depending on which level the surrounding type belongs to.
#[derive(Clone, Copy)]
enum Level<'a> {
    Game(&'a str),
    Theorem(&'a str),
}

/// Rewrites the `Bits(<length>)` lengths of `ty` to refer to the constants of `to`.
///
/// Every level (package, game, theorem) refers to its constants with its own kind of identifier,
/// and in the game we build here a constant is always assigned the constant of the same
/// name at the next level. So lifting a type just means swapping the identifier, keeping the name.
fn lift_type(ty: &Type, from: &str, to: Level) -> Type {
    let lift_all =
        |tys: &[Type]| -> Vec<Type> { tys.iter().map(|ty| lift_type(ty, from, to)).collect() };

    match ty.kind() {
        TypeKind::Bits(count_spec) => Type::bits(lift_count_spec(count_spec, from, to)),
        TypeKind::Tuple(tys) => Type::tuple(lift_all(tys)),
        TypeKind::Table(key, value) => {
            Type::table(lift_type(key, from, to), lift_type(value, from, to))
        }
        TypeKind::Fn(arg_tys, ret_ty) => Type::fun(lift_all(arg_tys), lift_type(ret_ty, from, to)),
        TypeKind::List(inner) => Type::list(lift_type(inner, from, to)),
        TypeKind::Set(inner) => Type::set(lift_type(inner, from, to)),
        TypeKind::Maybe(inner) => Type::maybe(lift_type(inner, from, to)),
        _ => ty.clone(),
    }
}

fn lift_count_spec(count_spec: &CountSpec, from: &str, to: Level) -> CountSpec {
    let CountSpec::Identifier(ident) = count_spec else {
        return count_spec.clone();
    };

    // only rewrite constants that belong to the level we are lifting away from
    let name = match ident.as_ref() {
        Identifier::PackageIdentifier(PackageIdentifier::Const(pkg_const))
            if pkg_const.pkg_name == from =>
        {
            &pkg_const.name
        }
        Identifier::GameIdentifier(GameIdentifier::Const(game_const))
            if game_const.game_name == from =>
        {
            &game_const.name
        }
        _ => return count_spec.clone(),
    };

    let lifted = match to {
        Level::Game(game_name) => {
            Identifier::GameIdentifier(GameIdentifier::Const(GameConstIdentifier {
                game_name: game_name.to_string(),
                name: name.clone(),
                ty: Type::integer(),
                game_inst_name: None,
                theorem_name: None,
                inst_info: None,
                assigned_value: None,
            }))
        }
        Level::Theorem(theorem_name) => Identifier::from(TheoremConstIdentifier {
            theorem_name: theorem_name.to_string(),
            name: name.clone(),
            ty: Type::integer(),
            inst_info: None,
        }),
    };

    CountSpec::Identifier(Box::new(lifted))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::tests::packages;

    const CLOSED: &str = r#"
package Closed {
    params {
        n: Integer,
    }

    state {
        ctr: Integer,
    }

    oracle Peek() -> Integer {
        return ctr;
    }

    oracle Bump() {
        ctr <- (ctr + 1);
        return;
    }
}
"#;

    #[test]
    fn the_game_is_the_package_alone_with_each_oracle_exported() {
        let (_, pkg) = packages::parse(CLOSED.trim_start(), "Closed.pkg.ssp");
        let theorem = open_game_theorem(&pkg);
        let game = theorem.instances[0].game();
        assert_eq!(game.pkgs.len(), 1);
        assert_eq!(game.pkgs[0].name, "Closed");
        assert!(game.edges.is_empty());
        let exported: Vec<&str> = game.exports.iter().map(|e| e.name()).collect();
        assert_eq!(exported, ["Peek", "Bump"]);
    }

    #[test]
    fn the_package_constants_become_theorem_constants() {
        let (_, pkg) = packages::parse(CLOSED.trim_start(), "Closed.pkg.ssp");
        let theorem = open_game_theorem(&pkg);
        let names: Vec<&str> = theorem.consts.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, ["n"]);
    }
}
