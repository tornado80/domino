// SPDX-License-Identifier: MIT OR Apache-2.0

// We have a lot of large errors.
// This is fine for now. We will want to address that at some point in the future.
#![allow(clippy::result_large_err)]

use clap::Parser;
use miette::Diagnostic;
use shadow_rs::shadow;
use thiserror::Error;
shadow!(build);

use sspverif::project;
use sspverif::project::Project;

mod cli;
use crate::cli::*;

#[derive(Parser, Debug)]
#[clap(author, version, long_version = build::CLAP_LONG_VERSION, about, long_about = None)]
#[clap(propagate_version = true)]
pub(crate) struct Cli {
    #[clap(subcommand)]
    pub(crate) command: Commands,
}

#[derive(Error, Diagnostic, Debug)]
#[error("{0}")]
#[diagnostic(code(cli::incompatible_arguments))]
pub struct IncompatibleArgumentsError(pub &'static str);

#[derive(Error, Diagnostic, Debug)]
#[error(
    "`domino debug` needs the native cvc5 backend, which is behind the `cvc5-lib` cargo feature"
)]
#[diagnostic(help(
    "rebuild with `cargo build --features cvc5-lib` (see the cvc5-lib section of Readme.md \
     and scripts/setup-cvc5-lib.sh for the one-time prerequisites)"
))]
pub struct Cvc5LibNotEnabled;

#[derive(Error, Diagnostic, Debug)]
#[error("`domino debug` found unresolved pairs (GOAL FAILS / inconclusive) or stopped early")]
#[diagnostic(code(debug::claim_not_verified))]
pub struct DebugNotVerified;

#[derive(Error, Diagnostic, Debug)]
#[error("theorem `{0}` not found")]
#[diagnostic(code(cli::theorem_not_found))]
pub struct TheoremNotFound(pub String);


#[allow(clippy::large_enum_variant)]
#[derive(Debug, Error, Diagnostic)]
enum Error {
    #[error(transparent)]
    #[diagnostic(transparent)]
    ProjectError(#[from] project::error::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    IncompatibleArgumentsErrorError(#[from] IncompatibleArgumentsError),
    #[error("could not read model file")]
    ModelFileReadError(#[from] std::io::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    ModelViewError(#[from] sspverif::modelview::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    Cvc5LibNotEnabled(#[from] Cvc5LibNotEnabled),
    #[error(transparent)]
    #[diagnostic(transparent)]
    DebugNotVerified(#[from] DebugNotVerified),
    #[error(transparent)]
    #[diagnostic(transparent)]
    TheoremNotFound(#[from] TheoremNotFound),
    #[error(transparent)]
    #[diagnostic(transparent)]
    InlineRender(#[from] sspverif::debug::render::RenderError),
    #[cfg(feature = "cvc5-lib")]
    #[error(transparent)]
    #[diagnostic(transparent)]
    Debug(#[from] sspverif::debug::driver::DebugError),
}

fn proofsteps(p: &Proofsteps) -> Result<(), Error> {
    let project_root = project::directory::find_project_root(p.project.as_deref())?;
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root, &files)?;

    if p.proofstep.is_some() && p.proof.is_none() {
        return Err(IncompatibleArgumentsError(
            "Need to specify a proof when specifying a proofstep",
        )
        .into());
    }
    if p.claim.is_some() && p.oracle.is_none() {
        return Err(IncompatibleArgumentsError(
            "Need to specify an oracle when specifying a claim",
        )
        .into());
    }

    project.proofsteps(&p.proof, &p.proofstep, &p.oracle, &p.claim)?;
    Ok(())
}

fn prove(p: &Prove) -> Result<(), Error> {
    let project_root = project::directory::find_project_root(p.project.as_deref())?;
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root, &files)?;

    if p.proofstep.is_none() || p.proof.is_some() {
        let smtsolver =
            sspverif::util::smtsolver::process::ProcessSmtSolverBackend::new(p.smtsolver);
        project.prove(
            &smtsolver,
            p.transcript,
            p.parallel,
            &p.proof,
            &p.proofstep,
            &p.oracle,
            &p.claim,
        )?;
    } else {
        return Err(IncompatibleArgumentsError(
            "Need to specify a proof when specifying a proofstep",
        )
        .into());
    }
    Ok(())
}

fn model(m: &Model) -> Result<(), Error> {
    // Loading the project is best-effort here: the model parser/viewer is still useful without
    // one (it just can't resolve names back to package/oracle semantics), so a missing or
    // unparseable project is a warning, not a hard error.
    let root_and_files = project::directory::find_project_root(m.project.as_deref())
        .and_then(|root| {
            let files = project::DirectoryFiles::load(&root)?;
            Ok((root, files))
        })
        .inspect_err(|err| {
            eprintln!(
                "warning: could not load a Domino project ({err}); showing raw model values only"
            );
        })
        .ok();

    let project = root_and_files.as_ref().and_then(|(root, files)| {
        project::DirectoryProject::load(root.clone(), files)
            .inspect_err(|err| {
                eprintln!(
                    "warning: could not load a Domino project ({err}); showing raw model values only"
                );
            })
            .ok()
    });

    let content = std::fs::read_to_string(&m.model_file)?;
    let report = sspverif::modelview::analyze(project.as_ref(), &content)?;
    println!("{report}");

    Ok(())
}

#[cfg(feature = "cvc5-lib")]
fn debug(d: &Debug) -> Result<(), Error> {
    use std::io::IsTerminal;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::Arc;

    use sspverif::debug::driver::{render_tree, run_debug_command, DebugOptions};
    use sspverif::debug::progress::{BarObserver, DebugObserver, NopObserver, PlainObserver};

    let project_root = project::directory::find_project_root(d.path.as_deref())?;
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root, &files)?;

    let opts = DebugOptions {
        check_left: !d.no_check_left,
        check_right: !d.no_check_right,
        timeout_ms: d.timeout,
        max_paths: d.max_paths,
    };

    let backend = sspverif::util::smtsolver::cvc5lib::Cvc5LibBackend::new(true, d.timeout);

    let mut observer: Box<dyn DebugObserver> = match d.progress {
        ProgressMode::None => Box::new(NopObserver),
        ProgressMode::Plain => Box::new(PlainObserver::new()),
        ProgressMode::Bar => Box::new(BarObserver::new()),
        ProgressMode::Auto => {
            if std::io::stderr().is_terminal() {
                Box::new(BarObserver::new())
            } else {
                Box::new(PlainObserver::new())
            }
        }
    };

    // Best-effort Ctrl-C handling. The first press sets a flag the driver checks
    // at every fork (inside branch-pruning sweeps too) and at every pair
    // boundary; it then finishes the in-flight cvc5 query — which is a blocking
    // FFI call and cannot itself be cancelled, so `--timeout` bounds how long
    // that takes — and writes partial `trace.json` / `index.html`. A second
    // press exits immediately with 130. If a handler is already installed the
    // run just is not interruptible — not fatal.
    let stop = Arc::new(AtomicBool::new(false));
    {
        let stop = stop.clone();
        let hits = Arc::new(AtomicUsize::new(0));
        let _ = ctrlc::try_set_handler(move || {
            if hits.fetch_add(1, Ordering::Relaxed) == 0 {
                stop.store(true, Ordering::Relaxed);
                eprintln!(
                    "\ndebug: interrupt — finishing the current solver query, then writing \
                     partial results (Ctrl-C again to abort now)"
                );
            } else {
                std::process::exit(130);
            }
        });
    }

    let run = run_debug_command(
        &project,
        &d.proof,
        d.proofstep,
        &d.oracle,
        &d.claim,
        &opts,
        &backend,
        d.out.clone(),
        observer.as_mut(),
        Some(&stop),
    )?;

    print!("{}", render_tree(&run));
    if !run.admitted {
        println!("\nviewer: {}/index.html", run.out_dir);
    }

    if !run.is_ok() {
        return Err(DebugNotVerified.into());
    }
    Ok(())
}

#[cfg(not(feature = "cvc5-lib"))]
fn debug(_d: &Debug) -> Result<(), Error> {
    Err(Cvc5LibNotEnabled.into())
}

fn inline(i: &Inline) -> Result<(), Error> {
    let project_root = project::directory::find_project_root(i.path.as_deref())?;
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root, &files)?;

    let theorem = project
        .get_theorem(&i.proof)
        .ok_or_else(|| TheoremNotFound(i.proof.clone()))?;

    let listing = sspverif::debug::render::render_side_by_side(
        theorem,
        i.proofstep,
        &i.oracle,
        !i.no_line_numbers,
    )?;
    print!("{listing}");
    Ok(())
}

fn latex(l: &Latex) -> Result<(), Error> {
    let project_root = project::directory::find_project_root(l.project.as_deref())?;
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root, &files)?;

    let smtsolver = l
        .smtsolver
        .map(sspverif::util::smtsolver::process::ProcessSmtSolverBackend::new);
    project.latex(&smtsolver)?;
    Ok(())
}

fn format(f: &Format) -> Result<(), Error> {
    if let Some(input) = &f.input {
        sspverif::format::format_file(input)?;
    } else {
        let root = crate::project::directory::find_project_root(f.project.as_deref());
        sspverif::format::format_file(&root?)?;
    }
    Ok(())
}

fn main() -> miette::Result<()> {
    miette::set_hook(Box::new(|_| {
        Box::new(
            miette::MietteHandlerOpts::new()
                .show_related_errors_as_nested()
                .build(),
        )
    }))
    .unwrap();

    let cli = Cli::parse();

    let result = match &cli.command {
        Commands::Prove(p) => prove(p),
        Commands::Proofsteps(p) => proofsteps(p),
        Commands::Inline(i) => inline(i),
        Commands::Latex(l) => latex(l),
        Commands::Format(f) => format(f),
        Commands::Model(m) => model(m),
        Commands::Debug(d) => debug(d),
        Commands::Inline(i) => inline(i),
    };

    result.map_err(miette::Report::new)
}
