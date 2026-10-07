// SPDX-License-Identifier: MIT OR Apache-2.0

//! Result records and the debug indexes (story 22, ADR 0011).
//!
//! Each Domino-listing run writes a **result record**, `<strategy>_result.json`, next to its
//! viewer ([`write_result`]). A **debug index** (`index.html` and `summary.txt`) exists for the
//! project, for each theorem and for each equivalence proofstep. An index renders the result
//! records below its directory, and nothing else: [`refresh_indexes`] writes the index of a
//! level, the indexes below it, and rewrites each index above it that already exists.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use serde_derive::{Deserialize, Serialize};

use crate::debug::driver::StopReason;
use crate::debug::layout::{proofstep_dir, Layout};
use crate::debug::report::format_elapsed;
use crate::debug::sweep::{esc, href_attr, SweepEntry};

/// Schema version of a result record.
pub const RESULT_SCHEMA: u32 = 1;

/// The failures list of an index shows at most this many runs.
const FAILURES_SHOWN: usize = 50;

/// What one claim said over the pairs (or joint paths) of a run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckLine {
    pub check: String,
    pub verified: usize,
    pub unreachable: usize,
    pub goal_fails: usize,
    pub inconclusive: usize,
}

/// One pair a check failed on.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FailureLine {
    pub check: String,
    /// The claim that this check is a part of.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub part_of: Option<String>,
    pub pair: String,
    pub verdict: String,
}

/// `<strategy>_result.json`: what a row of an index needs, and nothing more. A run artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResultRecord {
    pub schema: u32,
    pub theorem: String,
    pub proofstep: usize,
    pub left: String,
    pub right: String,
    pub oracle: String,
    pub claim: String,
    pub strategy: String,
    pub listing: String,
    /// The viewer, relative to the directory of the record.
    pub viewer: String,
    pub unit: String,
    pub units: usize,
    pub checks: Vec<CheckLine>,
    pub failures: Vec<FailureLine>,
    pub ok: bool,
    /// `completed`, `max-paths` or `interrupted`.
    pub stop_reason: String,
    /// The limit, when `stop_reason` is `max-paths`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_paths: Option<usize>,
    pub elapsed_ms: u64,
    /// `YYYY-MM-DDTHH:MM:SSZ`.
    pub finished_at: String,
}

impl ResultRecord {
    pub fn of(entry: &SweepEntry) -> Self {
        let t = &entry.target;
        let (stop_reason, max_paths) = match entry.stop_reason {
            StopReason::Completed => ("completed", None),
            StopReason::MaxPaths { limit } => ("max-paths", Some(limit)),
            StopReason::Interrupted => ("interrupted", None),
        };
        Self {
            schema: RESULT_SCHEMA,
            theorem: t.theorem.clone(),
            proofstep: t.proofstep,
            left: t.left.clone(),
            right: t.right.clone(),
            oracle: t.oracle.clone(),
            claim: entry.claim.clone(),
            strategy: entry.strategy.to_string(),
            listing: entry.listing.to_string(),
            viewer: entry.viewer.clone(),
            unit: entry.unit.to_string(),
            units: entry.units,
            checks: entry
                .claims
                .iter()
                .map(|c| CheckLine {
                    check: c.claim.clone(),
                    verified: c.verified,
                    unreachable: c.unreachable,
                    goal_fails: c.goal_fails,
                    inconclusive: c.inconclusive,
                })
                .collect(),
            failures: entry
                .failures
                .iter()
                .map(|f| FailureLine {
                    check: f.check.clone(),
                    part_of: f.part_of.clone(),
                    pair: f.pair.clone(),
                    verdict: f.verdict.to_string(),
                })
                .collect(),
            ok: entry.ok,
            stop_reason: stop_reason.to_string(),
            max_paths,
            elapsed_ms: u64::try_from(entry.elapsed.as_millis()).unwrap_or(u64::MAX),
            finished_at: entry.finished_at.clone(),
        }
    }

    /// `ok`, `FAILS` or `stopped early (…)`.
    fn result(&self) -> String {
        let stop = match self.stop_reason.as_str() {
            "completed" => StopReason::Completed,
            "interrupted" => StopReason::Interrupted,
            _ => StopReason::MaxPaths {
                limit: self.max_paths.unwrap_or(0),
            },
        };
        if self.ok {
            "ok".to_string()
        } else if stop.is_partial() {
            format!("stopped early ({})", stop.phrase())
        } else {
            "FAILS".to_string()
        }
    }

    fn failing_checks(&self) -> impl Iterator<Item = &CheckLine> {
        self.checks
            .iter()
            .filter(|c| c.goal_fails > 0 || c.inconclusive > 0)
    }

    /// `T proofstep 3 (L == R) O [claim]`.
    fn label(&self) -> String {
        format!(
            "{} proofstep {} ({} == {}) {} [{}]",
            self.theorem, self.proofstep, self.left, self.right, self.oracle, self.claim
        )
    }

    /// One text for each distinct chain of failing checks, with the pairs it holds on:
    /// `invariant: goal-fails → state-relation rel_ctr: goal-fails (#1.1, #2.1)`.
    fn failure_chains(&self) -> Vec<String> {
        let mut by_pair: Vec<(String, String)> = Vec::new();
        for f in &self.failures {
            let step = format!("{}: {}", f.check, f.verdict);
            match by_pair.last_mut() {
                Some((pair, chain)) if f.part_of.is_some() && *pair == f.pair => {
                    chain.push_str(" → ");
                    chain.push_str(&step);
                }
                _ => by_pair.push((f.pair.clone(), step)),
            }
        }
        let mut chains: Vec<(String, Vec<String>)> = Vec::new();
        for (pair, chain) in by_pair {
            match chains.iter_mut().find(|(c, _)| *c == chain) {
                Some((_, pairs)) => pairs.push(pair),
                None => chains.push((chain, vec![pair])),
            }
        }
        chains
            .into_iter()
            .map(|(chain, pairs)| format!("{chain} ({})", pairs.join(", ")))
            .collect()
    }
}

/// Write the result record of `entry` into its run directory. Returns its path.
pub fn write_result(entry: &SweepEntry) -> std::io::Result<PathBuf> {
    let path = entry
        .out_dir
        .join(Layout::Strategy(entry.strategy).result());
    let json = serde_json::to_string_pretty(&ResultRecord::of(entry)).map_err(std::io::Error::other)?;
    std::fs::write(&path, json + "\n")?;
    Ok(path)
}

/// The time now, as `YYYY-MM-DDTHH:MM:SSZ`.
pub fn now_utc() -> String {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    utc_of(secs)
}

/// `secs` after the Unix epoch, as `YYYY-MM-DDTHH:MM:SSZ` (the civil-from-days algorithm).
fn utc_of(secs: u64) -> String {
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = yoe + era * 400 + i64::from(month <= 2);
    format!(
        "{year:04}-{month:02}-{day:02}T{:02}:{:02}:{:02}Z",
        rem / 3_600,
        rem % 3_600 / 60,
        rem % 60
    )
}

/// The level of a debug index.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Level {
    Project,
    Theorem { theorem: String },
    Proofstep { theorem: String, left: String, right: String },
}

impl Level {
    /// The level that the filters of `domino debug` select. `--oracle` and `--claim` do not
    /// change it.
    pub fn of_filters(proof: Option<&str>, proofstep: Option<(&str, &str)>) -> Self {
        match (proof, proofstep) {
            (None, _) => Level::Project,
            (Some(theorem), None) => Level::Theorem {
                theorem: theorem.to_string(),
            },
            (Some(theorem), Some((left, right))) => Level::Proofstep {
                theorem: theorem.to_string(),
                left: left.to_string(),
                right: right.to_string(),
            },
        }
    }

    /// The directory of the index of this level.
    pub fn dir(&self, root: &Path) -> PathBuf {
        match self {
            Level::Project => root.to_path_buf(),
            Level::Theorem { theorem } => root.join(theorem),
            Level::Proofstep { theorem, left, right } => proofstep_dir(root, theorem, left, right),
        }
    }

    fn parent(&self) -> Option<Level> {
        match self {
            Level::Project => None,
            Level::Theorem { .. } => Some(Level::Project),
            Level::Proofstep { theorem, .. } => Some(Level::Theorem {
                theorem: theorem.clone(),
            }),
        }
    }

    fn title(&self) -> String {
        match self {
            Level::Project => "domino debug — project".to_string(),
            Level::Theorem { theorem } => format!("domino debug — theorem {theorem}"),
            Level::Proofstep { theorem, left, right } => {
                format!("domino debug — {theorem}: {left} == {right}")
            }
        }
    }
}

/// One index that [`refresh_indexes`] wrote.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WrittenIndex {
    /// The `index.html`; `summary.txt` is next to it.
    pub path: PathBuf,
    /// The index existed before, above the selected level.
    pub updated: bool,
}

/// Rewrite the index of `level`, each index below it that a record needs, and each index above
/// it that already exists, all under `root`, from the result records on disk. Returns the
/// indexes written, the lowest first.
pub fn refresh_indexes(root: &Path, level: &Level) -> std::io::Result<Vec<WrittenIndex>> {
    let mut written = Vec::new();
    for below in levels_below(root, level) {
        written.push(write_index(root, &below, false)?);
    }
    written.push(write_index(root, level, false)?);
    if let Some(parent) = level.parent() {
        written.extend(update_indexes(root, &parent)?);
    }
    Ok(written)
}

/// Rewrite the index of `level` and each index above it, each only when it already exists.
pub fn update_indexes(root: &Path, level: &Level) -> std::io::Result<Vec<WrittenIndex>> {
    let mut written = Vec::new();
    let mut current = Some(level.clone());
    while let Some(level) = current {
        if level.dir(root).join("index.html").exists() {
            written.push(write_index(root, &level, true)?);
        }
        current = level.parent();
    }
    Ok(written)
}

/// The levels strictly below `level` that hold a record, the lowest first.
fn levels_below(root: &Path, level: &Level) -> Vec<Level> {
    let mut proofsteps = std::collections::BTreeSet::new();
    let mut theorems = std::collections::BTreeSet::new();
    for found in records_below(&level.dir(root)) {
        let r = found.record;
        proofsteps.insert(Level::Proofstep {
            theorem: r.theorem.clone(),
            left: r.left,
            right: r.right,
        });
        theorems.insert(Level::Theorem { theorem: r.theorem });
    }
    let mut levels: Vec<Level> = proofsteps.into_iter().collect();
    if *level == Level::Project {
        levels.extend(theorems);
    }
    levels.retain(|l| l != level);
    levels
}

fn write_index(root: &Path, level: &Level, updated: bool) -> std::io::Result<WrittenIndex> {
    let dir = level.dir(root);
    let found = records_below(&dir);
    std::fs::create_dir_all(&dir)?;
    let (html, text) = render(level, &dir, &found);
    let path = dir.join("index.html");
    std::fs::write(&path, html)?;
    std::fs::write(dir.join("summary.txt"), text)?;
    Ok(WrittenIndex { path, updated })
}

/// A result record and the directory it is in.
struct Found {
    record: ResultRecord,
    dir: PathBuf,
}

/// Every readable result record of the current schema below `dir`, in a fixed order.
fn records_below(dir: &Path) -> Vec<Found> {
    let mut found = Vec::new();
    collect_records(dir, &mut found);
    found.sort_by(|a, b| sort_key(&a.record).cmp(&sort_key(&b.record)));
    found
}

fn sort_key(r: &ResultRecord) -> (&str, usize, &str, &str, &str) {
    (&r.theorem, r.proofstep, &r.oracle, &r.claim, &r.strategy)
}

fn collect_records(dir: &Path, found: &mut Vec<Found>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_records(&path, found);
        } else if let Some(record) = read_record(&path) {
            found.push(Found {
                record,
                dir: dir.to_path_buf(),
            });
        }
    }
}

fn read_record(path: &Path) -> Option<ResultRecord> {
    let name = path.file_name()?.to_str()?;
    if !name.ends_with("_result.json") {
        return None;
    }
    let record: ResultRecord = serde_json::from_str(&std::fs::read_to_string(path).ok()?).ok()?;
    (record.schema == RESULT_SCHEMA).then_some(record)
}

/// One row of an index table, as plain text.
struct Row {
    cells: Vec<String>,
    ok: bool,
    link: Link,
}

enum Link {
    /// A relative `href` and its text.
    To(String, &'static str),
    /// No page to link; the text says how to make one.
    Hint(String),
}

fn header(level: &Level) -> &'static [&'static str] {
    match level {
        Level::Project => &["theorem", "runs", "runs not ok", "oldest run", ""],
        Level::Theorem { .. } => &["proofstep", "games", "runs", "runs not ok", "oldest run", ""],
        Level::Proofstep { .. } => &[
            "oracle",
            "claim",
            "strategy",
            "result",
            "checks not verified",
            "time",
            "finished at",
            "",
        ],
    }
}

fn rows(level: &Level, dir: &Path, found: &[Found]) -> Vec<Row> {
    match level {
        Level::Project => {
            let groups = group(found, |r| (r.theorem.clone(), 0, String::new()));
            groups
                .into_iter()
                .map(|((theorem, _, _), runs)| {
                    let hint = format!("no index; run `domino debug --proof {theorem}`");
                    child_row(vec![theorem.clone()], &runs, child_link(dir, &theorem, hint))
                })
                .collect()
        }
        Level::Theorem { theorem } => {
            let groups = group(found, |r| (r.left.clone(), r.proofstep, r.right.clone()));
            groups
                .into_iter()
                .map(|((left, step, right), runs)| {
                    let hint =
                        format!("no index; run `domino debug --proof {theorem} --proofstep {step}`");
                    let link = child_link(dir, &format!("{left}-{right}"), hint);
                    child_row(vec![step.to_string(), format!("{left} == {right}")], &runs, link)
                })
                .collect()
        }
        Level::Proofstep { .. } => found.iter().map(|f| run_row(dir, f)).collect(),
    }
}

type GroupKey = (String, usize, String);

/// The runs of `found` grouped by `key`, ordered by proofstep, then by key.
fn group(
    found: &[Found],
    key: impl Fn(&ResultRecord) -> GroupKey,
) -> Vec<(GroupKey, Vec<&ResultRecord>)> {
    let mut groups: BTreeMap<(usize, GroupKey), Vec<&ResultRecord>> = BTreeMap::new();
    for f in found {
        let k = key(&f.record);
        groups.entry((k.1, k)).or_default().push(&f.record);
    }
    groups.into_iter().map(|((_, k), runs)| (k, runs)).collect()
}

fn child_link(dir: &Path, child: &str, hint: String) -> Link {
    if dir.join(child).join("index.html").exists() {
        Link::To(format!("{}/index.html", href_attr(child)), "index")
    } else {
        Link::Hint(hint)
    }
}

fn child_row(mut cells: Vec<String>, runs: &[&ResultRecord], link: Link) -> Row {
    let not_ok = runs.iter().filter(|r| !r.ok).count();
    let oldest = runs.iter().map(|r| r.finished_at.as_str()).min().unwrap_or("");
    cells.extend([runs.len().to_string(), not_ok.to_string(), oldest.to_string()]);
    Row {
        cells,
        ok: not_ok == 0,
        link,
    }
}

fn run_row(dir: &Path, f: &Found) -> Row {
    let r = &f.record;
    let failing: Vec<String> = r
        .failing_checks()
        .map(|c| format!("{} ({} fail, {} inconclusive)", c.check, c.goal_fails, c.inconclusive))
        .collect();
    Row {
        cells: vec![
            r.oracle.clone(),
            r.claim.clone(),
            r.strategy.clone(),
            format!("{} {}, {}", r.units, r.unit, r.result()),
            failing.join("; "),
            format_elapsed(Duration::from_millis(r.elapsed_ms)),
            r.finished_at.clone(),
        ],
        ok: r.ok,
        link: Link::To(viewer_href(dir, f), "viewer"),
    }
}

/// The viewer of the run in `f`, relative to the index directory `dir`.
fn viewer_href(dir: &Path, f: &Found) -> String {
    let rel = f.dir.strip_prefix(dir).unwrap_or(&f.dir);
    href_attr(&format!("{}/{}", rel.display(), f.record.viewer))
}

/// The runs below the index with a failing or inconclusive check, as (label, href) lines.
fn failure_lines(dir: &Path, found: &[Found]) -> Vec<(String, String)> {
    found
        .iter()
        .filter(|f| f.record.failing_checks().next().is_some() || !f.record.failures.is_empty())
        .map(|f| {
            let r = &f.record;
            let line = format!("{} {}: {}", r.label(), r.strategy, r.failure_chains().join("; "));
            (line, viewer_href(dir, f))
        })
        .collect()
}

const STYLE: &str = "<style>\n\
:root{--bg:#fff;--fg:#1b1f24;--dim:#59636e;--ok:#1a7f37;--bad:#cf222e;--line:#d0d7de}\n\
@media (prefers-color-scheme:dark){:root{--bg:#0d1117;--fg:#e6edf3;--dim:#8d96a0;--ok:#3fb950;--bad:#f85149;--line:#30363d}}\n\
body{background:var(--bg);color:var(--fg);font:14px/1.5 system-ui,sans-serif;margin:0 auto;max-width:72rem;padding:1rem 16px}\n\
table{border-collapse:collapse;width:100%}th,td{border-bottom:1px solid var(--line);padding:.35rem .6rem;text-align:left;vertical-align:top}\n\
.ok{color:var(--ok)}.bad{color:var(--bad)}.dim{color:var(--dim)}a{color:inherit}\n\
.scroll{overflow-x:auto}li{margin:.25rem 0}\n</style>";

/// The `index.html` and `summary.txt` of `level`, whose directory is `dir`.
fn render(level: &Level, dir: &Path, found: &[Found]) -> (String, String) {
    let title = level.title();
    let rows = rows(level, dir, found);
    let failures = failure_lines(dir, found);
    let mut html = format!(
        "<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\">\n\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
         <title>{t}</title>\n{STYLE}</head><body>\n<h1>{t}</h1>\n",
        t = esc(&title)
    );
    let mut text = format!("{title}\n{}\n\n", "=".repeat(title.chars().count()));
    render_table(&mut html, &mut text, header(level), &rows);
    render_failures(&mut html, &mut text, &failures);
    html.push_str("</body></html>\n");
    (html, text)
}

fn render_table(html: &mut String, text: &mut String, header: &[&str], rows: &[Row]) {
    html.push_str("<div class=\"scroll\"><table><thead><tr>");
    for h in header {
        let _ = write!(html, "<th>{}</th>", esc(h));
    }
    html.push_str("</tr></thead><tbody>\n");
    for row in rows {
        let class = if row.ok { "ok" } else { "bad" };
        let _ = write!(html, "<tr class=\"{class}\">");
        for cell in &row.cells {
            let _ = write!(html, "<td>{}</td>", esc(cell));
        }
        let (cell, line) = match &row.link {
            Link::To(href, label) => (format!("<a href=\"{}\">{label}</a>", esc(href)), href.clone()),
            Link::Hint(hint) => (format!("<span class=\"dim\">{}</span>", esc(hint)), hint.clone()),
        };
        let _ = writeln!(html, "<td>{cell}</td></tr>");
        let _ = writeln!(text, "{}  {line}", row.cells.join("  "));
    }
    html.push_str("</tbody></table></div>\n");
}

fn render_failures(html: &mut String, text: &mut String, failures: &[(String, String)]) {
    if failures.is_empty() {
        return;
    }
    html.push_str("<h2>failures</h2>\n<ul>\n");
    text.push_str("\nfailures\n");
    for (line, href) in failures.iter().take(FAILURES_SHOWN) {
        let _ = writeln!(html, "<li><a href=\"{}\">{}</a></li>", esc(href), esc(line));
        let _ = writeln!(text, "  {line}\n      {href}");
    }
    let more = failures.len().saturating_sub(FAILURES_SHOWN);
    if more > 0 {
        let _ = writeln!(html, "<li class=\"dim\">… and {more} more</li>");
        let _ = writeln!(text, "  … and {more} more");
    }
    html.push_str("</ul>\n");
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(theorem: &str, step: usize, oracle: &str, strategy: &str, ok: bool) -> ResultRecord {
        ResultRecord {
            schema: RESULT_SCHEMA,
            theorem: theorem.into(),
            proofstep: step,
            left: format!("L{step}"),
            right: format!("R{step}"),
            oracle: oracle.into(),
            claim: "!all-claims!".into(),
            strategy: strategy.into(),
            listing: "domino".into(),
            viewer: format!("{strategy}_viewer.html"),
            unit: "pairs".into(),
            units: 4,
            checks: vec![CheckLine {
                check: "invariant".into(),
                verified: 3,
                unreachable: 0,
                goal_fails: usize::from(!ok),
                inconclusive: 0,
            }],
            failures: if ok {
                vec![]
            } else {
                vec![
                    FailureLine {
                        check: "invariant".into(),
                        part_of: None,
                        pair: "#1.1".into(),
                        verdict: "goal-fails".into(),
                    },
                    FailureLine {
                        check: "state-relation rel_ctr".into(),
                        part_of: Some("invariant".into()),
                        pair: "#1.1".into(),
                        verdict: "goal-fails".into(),
                    },
                ]
            },
            ok,
            stop_reason: "completed".into(),
            max_paths: None,
            elapsed_ms: 1200,
            finished_at: "2026-10-07T12:00:00Z".into(),
        }
    }

    /// Write `r` where a run of it would.
    fn put(root: &Path, r: &ResultRecord) {
        let dir = proofstep_dir(root, &r.theorem, &r.left, &r.right)
            .join(&r.oracle)
            .join(&r.claim);
        std::fs::create_dir_all(&dir).unwrap();
        let name = format!("{}_result.json", r.strategy);
        std::fs::write(dir.join(name), serde_json::to_string(r).unwrap()).unwrap();
    }

    fn step(theorem: &str, n: usize) -> Level {
        Level::Proofstep {
            theorem: theorem.into(),
            left: format!("L{n}"),
            right: format!("R{n}"),
        }
    }

    fn read(path: PathBuf) -> String {
        std::fs::read_to_string(path).unwrap()
    }

    #[test]
    fn a_time_is_written_in_utc() {
        assert_eq!(utc_of(0), "1970-01-01T00:00:00Z");
        assert_eq!(utc_of(1_791_374_400), "2026-10-07T12:00:00Z");
        assert_eq!(utc_of(951_782_400), "2000-02-29T00:00:00Z");
    }

    #[test]
    fn a_proofstep_run_writes_no_index_above_it_that_was_not_there() {
        let root = tempfile::tempdir().unwrap();
        put(root.path(), &record("T", 0, "O", "sequential", true));
        let written = refresh_indexes(root.path(), &step("T", 0)).unwrap();
        assert_eq!(
            written,
            vec![WrittenIndex {
                path: root.path().join("T/L0-R0/index.html"),
                updated: false
            }]
        );
        assert!(root.path().join("T/L0-R0/summary.txt").exists());
        assert!(!root.path().join("T/index.html").exists());
        assert!(!root.path().join("index.html").exists());
    }

    #[test]
    fn a_project_run_writes_every_level_below_it() {
        let root = tempfile::tempdir().unwrap();
        put(root.path(), &record("T", 0, "O", "sequential", true));
        put(root.path(), &record("U", 1, "O", "sequential", true));
        let written: Vec<PathBuf> = refresh_indexes(root.path(), &Level::Project)
            .unwrap()
            .into_iter()
            .map(|w| w.path)
            .collect();
        let p = |s: &str| root.path().join(s);
        assert_eq!(
            written,
            vec![
                p("T/L0-R0/index.html"),
                p("U/L1-R1/index.html"),
                p("T/index.html"),
                p("U/index.html"),
                p("index.html")
            ]
        );
    }

    #[test]
    fn an_index_above_is_updated_only_if_it_exists() {
        let root = tempfile::tempdir().unwrap();
        put(root.path(), &record("T", 0, "O", "sequential", true));
        put(root.path(), &record("T", 1, "O", "sequential", true));
        refresh_indexes(root.path(), &Level::Theorem { theorem: "T".into() }).unwrap();

        let mut newer = record("T", 0, "O", "sequential", false);
        newer.finished_at = "2026-10-08T09:00:00Z".into();
        put(root.path(), &newer);
        let written = refresh_indexes(root.path(), &step("T", 0)).unwrap();
        assert_eq!(written.len(), 2, "{written:?}");
        assert_eq!(
            written[1],
            WrittenIndex {
                path: root.path().join("T/index.html"),
                updated: true
            }
        );
        assert!(!root.path().join("index.html").exists());

        let theorem = read(root.path().join("T/summary.txt"));
        assert!(theorem.contains("0  L0 == R0  1  1  2026-10-08T09:00:00Z"), "{theorem}");
        assert!(theorem.contains("1  L1 == R1  1  0  2026-10-07T12:00:00Z"), "{theorem}");
    }

    #[test]
    fn a_parent_row_shows_the_oldest_run_below_it() {
        let root = tempfile::tempdir().unwrap();
        let mut old = record("T", 0, "A", "sequential", true);
        old.finished_at = "2026-01-01T00:00:00Z".into();
        put(root.path(), &old);
        put(root.path(), &record("T", 0, "B", "sequential", true));
        refresh_indexes(root.path(), &Level::Project).unwrap();
        let project = read(root.path().join("summary.txt"));
        assert!(project.contains("T  2  0  2026-01-01T00:00:00Z  T/index.html"), "{project}");
    }

    #[test]
    fn a_proofstep_index_lists_each_run_in_order() {
        let root = tempfile::tempdir().unwrap();
        put(root.path(), &record("T", 0, "B", "sequential", true));
        put(root.path(), &record("T", 0, "A", "lockstep", true));
        put(root.path(), &record("T", 0, "A", "sequential", true));
        let mut one_claim = record("T", 0, "A", "sequential", true);
        one_claim.claim = "invariant".into();
        put(root.path(), &one_claim);
        refresh_indexes(root.path(), &step("T", 0)).unwrap();
        let text = read(root.path().join("T/L0-R0/summary.txt"));
        let rows: Vec<&str> = text.lines().skip(3).take(4).collect();
        assert!(rows[0].starts_with("A  !all-claims!  lockstep"), "{text}");
        assert!(rows[1].starts_with("A  !all-claims!  sequential"), "{text}");
        assert!(rows[2].starts_with("A  invariant  sequential"), "{text}");
        assert!(rows[3].starts_with("B  !all-claims!  sequential"), "{text}");
        let html = read(root.path().join("T/L0-R0/index.html"));
        assert!(
            html.contains("href=\"A/!all-claims!/lockstep_viewer.html\""),
            "{html}"
        );
    }

    #[test]
    fn a_child_with_no_index_says_how_to_make_one() {
        let root = tempfile::tempdir().unwrap();
        put(root.path(), &record("T", 0, "O", "sequential", true));
        put(root.path(), &record("T", 1, "O", "sequential", true));
        refresh_indexes(root.path(), &step("T", 0)).unwrap();
        std::fs::write(root.path().join("T/index.html"), "").unwrap();
        update_indexes(root.path(), &Level::Theorem { theorem: "T".into() }).unwrap();
        let text = read(root.path().join("T/summary.txt"));
        assert!(text.contains("L0 == R0  1  0  2026-10-07T12:00:00Z  L0-R0/index.html"), "{text}");
        assert!(
            text.contains("no index; run `domino debug --proof T --proofstep 1`"),
            "{text}"
        );
    }

    #[test]
    fn the_failures_list_names_the_checks_and_links_the_viewer() {
        let root = tempfile::tempdir().unwrap();
        put(root.path(), &record("T", 0, "O", "sequential", false));
        refresh_indexes(root.path(), &Level::Theorem { theorem: "T".into() }).unwrap();
        let text = read(root.path().join("T/summary.txt"));
        assert!(
            text.contains(
                "T proofstep 0 (L0 == R0) O [!all-claims!] sequential: invariant: goal-fails \
                 → state-relation rel_ctr: goal-fails (#1.1)"
            ),
            "{text}"
        );
        let html = read(root.path().join("T/index.html"));
        assert!(
            html.contains("<a href=\"L0-R0/O/!all-claims!/sequential_viewer.html\">"),
            "{html}"
        );
    }

    #[test]
    fn the_failures_list_shows_at_most_fifty_runs() {
        let root = tempfile::tempdir().unwrap();
        for n in 0..53 {
            put(root.path(), &record("T", 0, &format!("O{n:02}"), "sequential", false));
        }
        refresh_indexes(root.path(), &step("T", 0)).unwrap();
        let text = read(root.path().join("T/L0-R0/summary.txt"));
        assert!(text.contains("… and 3 more"), "{text}");
    }

    #[test]
    fn a_record_of_another_schema_is_not_listed() {
        let root = tempfile::tempdir().unwrap();
        let mut old = record("T", 0, "O", "sequential", true);
        old.schema = 0;
        put(root.path(), &old);
        refresh_indexes(root.path(), &step("T", 0)).unwrap();
        let text = read(root.path().join("T/L0-R0/summary.txt"));
        assert!(!text.contains("sequential"), "{text}");
    }
}
