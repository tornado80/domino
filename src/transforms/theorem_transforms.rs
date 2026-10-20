// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::HashSet;

use miette::Diagnostic;
use thiserror::Error;

use crate::{theorem::GameInstance, types::Type};

use super::{
    deconstructinvoke, easycryptify, loopunroll,
    resolveoracles::{self, ResolutionError},
    returnify, sample_max_counter_extractor, samplify, tableinitialize, treeify, type_extract,
    unwrapify, GameTransform, Transformation,
};

pub struct EquivalenceTransform;

/// A failure raised while running the equivalence transform pipeline over a
/// game instance.
#[derive(Debug, Clone, PartialEq, Eq, Error, Diagnostic)]
pub enum EquivalenceTransformError {
    /// A sampling position is reachable through a loop `loopunroll` could not
    /// unroll. This is the only pipeline failure a parser-accepted project can
    /// still trigger; everything else the pipeline could hit is ruled out by
    /// an earlier stage and panics via `unreachable!`.
    #[error(transparent)]
    #[diagnostic(transparent)]
    UnboundedLoop(#[from] sample_max_counter_extractor::UnboundedLoopError),

    /// A loop `loopunroll` could not unroll survived into an oracle body that
    /// [`EasyCryptTransform`] has to lower. EasyCrypt export has no
    /// translation for it; only [`EasyCryptTransform`] raises this.
    #[error(transparent)]
    #[diagnostic(transparent)]
    EasyCryptUnsupportedLoop(#[from] easycryptify::UnsupportedLoopError),

    /// A temporary [`EasyCryptTransform`] has to keep would be named after
    /// the value it holds, but that name is already taken in the oracle
    /// (story 17 §3.4). Only [`EasyCryptTransform`] raises this.
    #[error(transparent)]
    #[diagnostic(transparent)]
    EasyCryptTemporaryNameCollision(#[from] easycryptify::TemporaryNameCollision),
}

impl From<easycryptify::EasyCryptifyError> for EquivalenceTransformError {
    fn from(err: easycryptify::EasyCryptifyError) -> Self {
        match err {
            easycryptify::EasyCryptifyError::UnsupportedLoop(e) => e.into(),
            easycryptify::EasyCryptifyError::TemporaryNameCollision(e) => e.into(),
        }
    }
}

// Bundles the per-game-instance data produced by the transform pipeline
#[derive(Clone, Debug)]
pub struct GameInstAux {
    pub types: HashSet<Type>,
    pub sample_info: samplify::SampleInfo,
    pub max_offsets: sample_max_counter_extractor::MaxOffsets,
}

impl super::TheoremTransform for EquivalenceTransform {
    type Err = EquivalenceTransformError;

    type Aux = Vec<(String, GameInstAux)>;

    fn transform_theorem<'a>(
        &self,
        theorem: &'a crate::theorem::Theorem<'a>,
    ) -> Result<(crate::theorem::Theorem<'a>, Self::Aux), Self::Err> {
        let results = theorem
            .instances
            .iter()
            .map(|game_inst| transform_game_inst_common(game_inst, PipelineOptions::EQUIVALENCE));
        let (instances, auxs) = itertools::process_results(results, |res| res.unzip())?;
        let theorem = theorem.with_new_instances(instances);

        Ok((theorem, auxs))
    }
}

/// Like [`EquivalenceTransform`], but prepares game instances for the
/// symbolic-execution debugger (`domino debug` / `domino inline`) instead of the
/// monolithic SMT writer.
///
/// It runs the exact same pipeline as [`EquivalenceTransform`] **minus
/// `treeify`**: `treeify` only exists so the SMT writer can emit `ite` by pushing
/// every statement that follows an `if` into both branches. For symbolic
/// execution that duplication is harmful — it multiplies the number of syntactic
/// paths and breaks the 1:1 relationship between a source statement and an IR
/// statement that the debugger's line labels depend on.
///
/// The `Aux` type is identical to [`EquivalenceTransform`]'s so downstream
/// consumers (`EquivalenceContext::new`, every `emit_*` in
/// `writers::smt::contexts::equivalence::emit`) keep working unchanged.
pub struct DebugTransform;

impl super::TheoremTransform for DebugTransform {
    type Err = EquivalenceTransformError;

    type Aux = Vec<(String, GameInstAux)>;

    fn transform_theorem<'a>(
        &self,
        theorem: &'a crate::theorem::Theorem<'a>,
    ) -> Result<(crate::theorem::Theorem<'a>, Self::Aux), Self::Err> {
        let results = theorem
            .instances
            .iter()
            .map(|game_inst| transform_game_inst_common(game_inst, PipelineOptions::DEBUG));
        let (instances, auxs) = itertools::process_results(results, |res| res.unzip())?;
        let theorem = theorem.with_new_instances(instances);

        Ok((theorem, auxs))
    }
}

/// Like [`EquivalenceTransform`], but prepares game instances for the
/// EasyCrypt exporter (`domino easycrypt export`) — and, once stories 08/09 add the
/// flag, for `domino inline/debug --easycrypt`
/// (`docs/stories/easycrypt/16-easycryptify.md`).
///
/// It runs the exact same pipeline **minus `treeify`**, plus
/// [`easycryptify`] as the very last stage, after `tableinitialize`
/// (`tableinitialize` pattern-matches on `T[k] <- invoke …`, a shape
/// `easycryptify` rewrites). `easycryptify` lowers every early exit into
/// EasyCrypt's single-exit shape without duplicating code, and turns every
/// oracle's return type `T` into `Maybe(T)` (`None` is abort).
///
/// [`DebugTransform`] stays the transform for a plain Domino listing: it never
/// runs `easycryptify`, so an `assert` there still renders as `assert`.
pub struct EasyCryptTransform;

impl super::TheoremTransform for EasyCryptTransform {
    type Err = EquivalenceTransformError;

    type Aux = Vec<(String, GameInstAux)>;

    fn transform_theorem<'a>(
        &self,
        theorem: &'a crate::theorem::Theorem<'a>,
    ) -> Result<(crate::theorem::Theorem<'a>, Self::Aux), Self::Err> {
        let results = theorem
            .instances
            .iter()
            .map(|game_inst| transform_game_inst_common(game_inst, PipelineOptions::EASYCRYPT));
        let (instances, auxs) = itertools::process_results(results, |res| res.unzip())?;
        let theorem = theorem.with_new_instances(instances);

        Ok((theorem, auxs))
    }
}

/// Like [`DebugTransform`], but for read-only views of a theorem (`domino html`)
/// that never emit a randomness mapping and so don't need
/// [`GameInstAux::max_offsets`].
///
/// Such views render *every* game instance of a theorem, including ones that
/// only appear in reduction hops and whose sampling loops have symbolic bounds
/// (e.g. `for j: 1 <= j <= w` in the Yao example). `loopunroll` cannot unroll
/// those, so `sample_max_counter_extractor` would reject the whole theorem.
/// Here that is not an error: the affected instance just gets empty
/// `max_offsets`, and [`crate::debug::view::render_oracle_view`] prints the
/// loop as-is.
///
/// It also skips `deconstructinvoke` and `unwrapify`: they only split
/// statements into `invoke-result-N` / `unwrap-N` temporaries for the SMT
/// encoding and the debugger's IR, which a reader is better off without.
pub struct ViewTransform;

impl super::TheoremTransform for ViewTransform {
    type Err = EquivalenceTransformError;

    type Aux = Vec<(String, GameInstAux)>;

    fn transform_theorem<'a>(
        &self,
        theorem: &'a crate::theorem::Theorem<'a>,
    ) -> Result<(crate::theorem::Theorem<'a>, Self::Aux), Self::Err> {
        let results = theorem
            .instances
            .iter()
            .map(|game_inst| transform_game_inst_common(game_inst, PipelineOptions::VIEW));
        let (instances, auxs) = itertools::process_results(results, |res| res.unzip())?;
        let theorem = theorem.with_new_instances(instances);

        Ok((theorem, auxs))
    }
}

/// How control flow after an `if` / early exit is lowered for the consumer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ControlFlowLowering {
    /// [`EquivalenceTransform`]: `treeify` (the SMT writer's nested `ite`).
    Treeify,
    /// [`DebugTransform`] and [`ViewTransform`]: none — keep the source's 1:1
    /// statement structure.
    None,
    /// [`EasyCryptTransform`]: `easycryptify`, run after `tableinitialize`.
    EasyCryptify,
}

/// The knobs on which [`EquivalenceTransform`], [`DebugTransform`],
/// [`EasyCryptTransform`] and [`ViewTransform`] differ; everything else in the
/// pipeline is shared.
#[derive(Clone, Copy)]
struct PipelineOptions {
    lowering: ControlFlowLowering,
    /// Fail on a sampling loop `loopunroll` could not unroll. When `false`, the
    /// instance gets empty `max_offsets` instead.
    require_max_offsets: bool,
    /// Run `deconstructinvoke` and `unwrapify`.
    split_temporaries: bool,
}

impl PipelineOptions {
    const EQUIVALENCE: Self = Self {
        lowering: ControlFlowLowering::Treeify,
        require_max_offsets: true,
        split_temporaries: true,
    };
    const DEBUG: Self = Self {
        lowering: ControlFlowLowering::None,
        require_max_offsets: true,
        split_temporaries: true,
    };
    const EASYCRYPT: Self = Self {
        lowering: ControlFlowLowering::EasyCryptify,
        require_max_offsets: true,
        split_temporaries: true,
    };
    const VIEW: Self = Self {
        lowering: ControlFlowLowering::None,
        require_max_offsets: false,
        split_temporaries: false,
    };
}

/// Runs one game instance through the pipeline of [`EquivalenceTransform`]: the shape the SMT
/// writers expect. The package-invariant check uses it for its virtual game.
pub(crate) fn transform_game_inst(
    game_inst: &GameInstance,
) -> Result<(GameInstance, GameInstAux), EquivalenceTransformError> {
    transform_game_inst_common(game_inst, PipelineOptions::EQUIVALENCE)
        .map(|(game_inst, (_name, aux))| (game_inst, aux))
}

/// Shared pipeline for every theorem transform of this module. They must never
/// drift, so the only differences between them live here, selected by `opts`.
fn transform_game_inst_common(
    game_inst: &GameInstance,
    opts: PipelineOptions,
) -> Result<(GameInstance, (String, GameInstAux)), EquivalenceTransformError> {
    let comp = game_inst.game();

    let (comp, types) = type_extract::Transformation(comp)
        .transform()
        .expect("type extraction transformation failed unexpectedly");
    /*
     * Note 1: we currently do samplify and sample_max_counter_extractor before
     * treeify so a `if foo { stuff } else { other stuff } ... x <- Integer`
     * gets the same sample counter for the x sampling after returnify (instead
     * of different ones depending on which branch was taken)
     * Note 2: samplify only compiles sampling points and assigns identifiers
     * to them. The maximum possible counter/offset each sampling point can
     * be sampled from is computed afterwards by `sample_max_counter_extractor`,
     * which needs to run after loop unrolling (so samples inside bounded
     * loops are counted once per unrolled iteration) and after oracle
     * resolution (to follow resolved oracle invocations).
     */
    let comp = if opts.split_temporaries {
        deconstructinvoke::Transformation(&comp)
            .transform()
            .expect("splitinvoke failed unexpectedly")
            .0
    } else {
        comp
    };
    let (comp, sample_info) = samplify::Transformation(&comp)
        .transform()
        .expect("samplify transformation failed unexpectedly");
    let comp = if opts.split_temporaries {
        unwrapify::Transformation(&comp)
            .transform()
            .expect("unwrapify transformation failed unexpectedly")
            .0
    } else {
        comp
    };
    let (comp, _) = resolveoracles::Transformation(&comp)
        .transform()
        .unwrap_or_else(|ResolutionError(failed_oracle_stmts)| {
            // The game parser rejects invocations of unknown oracles
            // (`no_such_oracle`), so resolution cannot fail on a parsed game.
            // An unwired import is an open call (ADR 0017), not a failure.
            unreachable!("resolveoracles should have caught this: {failed_oracle_stmts:?}")
        });
    let (comp, _) = returnify::TransformNg
        .transform_game(&comp)
        .expect("returnify transformation failed unexpectedly");
    let (comp, _) = loopunroll::Transformation(&comp)
        .transform()
        .expect("unroll transformation failed unexpectedly");
    let (comp, max_offsets) =
        match sample_max_counter_extractor::Transformation(&comp, &sample_info.positions)
            .transform()
        {
            Ok(result) => result,
            Err(_) if !opts.require_max_offsets => (comp, Default::default()),
            Err(err) => return Err(err.into()),
        };
    let comp = if opts.lowering == ControlFlowLowering::Treeify {
        treeify::Transformation(&comp)
            .transform()
            .expect("treeify transformation failed unexpectedly")
            .0
    } else {
        comp
    };
    let (comp, _) = tableinitialize::Transformation(&comp)
        .transform()
        .expect("tableinitialize transformation failed unexpectedly");
    let comp = if opts.lowering == ControlFlowLowering::EasyCryptify {
        easycryptify::Transformation(&comp).transform()?.0
    } else {
        comp
    };

    Ok((
        game_inst.with_other_game(comp),
        (
            game_inst.name().to_string(),
            GameInstAux {
                types,
                sample_info,
                max_offsets,
            },
        ),
    ))
}
