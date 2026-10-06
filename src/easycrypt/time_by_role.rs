//! Where the EasyCrypt time of one oracle went, by **Sentence role** (story 57): the "time by
//! role" table of the tactics report.
//!
//! The session adds to it at the place where it writes each transcript record, with the same
//! `ms` ([`super::session`]), so the table also exists when the transcript write failed. Its rows
//! then sum to the sum of the oracle's records, which story 56 makes equal to the oracle's
//! EasyCrypt time.

use std::fmt::Write as _;
use std::time::Duration;

use super::json::Timing;
use super::transcript::{Event, Role};

/// The roles in the order of the glossary (`CONTEXT.md`), which is the order of the rows.
const ROLES: [&str; 10] = [
    "quick close",
    "structure",
    "side-goal fallback",
    "leaf fallback",
    "reduce",
    "split",
    "part fallback",
    "admit",
    "undo",
    "resume",
];

/// The sums of one oracle's transcript records. Empty ([`TimeByRole::is_empty`]) until the
/// session has sent a sentence or written an event for the oracle.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TimeByRole(Box<Sums>);

/// Boxed in [`TimeByRole`]: the table rides in every oracle's stats, which move by value.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Sums {
    roles: [RoleRow; 10],
    interrupts: EventRow,
    respawns: EventRow,
    between_ms: u128,
    /// The sums of story 55's `timing`; `None` while no answer had one.
    easycrypt: Option<EcSums>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct RoleRow {
    count: usize,
    ms: u128,
    /// Refused by EasyCrypt, or interrupted.
    failed: usize,
    /// The largest `bytes` of the role's records.
    largest: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct EventRow {
    count: usize,
    ms: u128,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct EcSums {
    tactic_ms: u64,
    serialize_ms: u64,
    smt_calls: u64,
    translate_ms: u64,
    prepare_ms: u64,
    prover_ms: u64,
    valid: u64,
    timeout: u64,
    unknown: u64,
}

/// One sentence record as the table counts it.
pub struct Sentence<'a> {
    pub role: &'a Role,
    /// The record's `ms`.
    pub ms: u128,
    /// The record's `bytes`: the answer's length before the cap.
    pub bytes: usize,
    /// EasyCrypt refused the sentence, or it was interrupted.
    pub failed: bool,
    pub timing: Option<&'a Timing>,
}

impl TimeByRole {
    pub fn add_sentence(&mut self, sentence: &Sentence<'_>) {
        let row = &mut self.0.roles[row_of(sentence.role)];
        row.count += 1;
        row.ms += sentence.ms;
        row.failed += usize::from(sentence.failed);
        row.largest = row.largest.max(sentence.bytes);
        if let Some(timing) = sentence.timing {
            self.0.easycrypt.get_or_insert_with(EcSums::default).add(timing);
        }
    }

    /// An event record of `ms`.
    pub fn add_event(&mut self, event: Event, ms: u128) {
        let row = match event {
            Event::Interrupt { .. } => &mut self.0.interrupts,
            Event::Respawn => &mut self.0.respawns,
            Event::Between => {
                self.0.between_ms += ms;
                return;
            }
        };
        row.count += 1;
        row.ms += ms;
    }

    /// Adds `other`'s records: the records a respawned session wrote for the same oracle.
    pub fn merge(&mut self, other: &TimeByRole) {
        for (row, more) in self.0.roles.iter_mut().zip(other.0.roles.iter()) {
            row.count += more.count;
            row.ms += more.ms;
            row.failed += more.failed;
            row.largest = row.largest.max(more.largest);
        }
        for (row, more) in [
            (&mut self.0.interrupts, other.0.interrupts),
            (&mut self.0.respawns, other.0.respawns),
        ] {
            row.count += more.count;
            row.ms += more.ms;
        }
        self.0.between_ms += other.0.between_ms;
        if let Some(more) = &other.0.easycrypt {
            self.0.easycrypt.get_or_insert_with(EcSums::default).merge(more);
        }
    }

    pub fn is_empty(&self) -> bool {
        *self == TimeByRole::default()
    }

    /// The sum of all rows: the oracle's time as its records give it.
    pub fn total(&self) -> Duration {
        let ms = self.0.roles.iter().map(|r| r.ms).sum::<u128>()
            + self.0.interrupts.ms
            + self.0.respawns.ms
            + self.0.between_ms;
        Duration::from_millis(u64::try_from(ms).unwrap_or(u64::MAX))
    }

    /// The table, its lines indented by four spaces: one row per role that occurred, the
    /// event rows, the `EasyCrypt:` line, and a warning when the rows do not sum to
    /// `easycrypt_time` within 1 %.
    pub fn render(&self, easycrypt_time: Duration) -> String {
        let mut out = format!(
            "    {:<22}{:>6}{:>10}{:>9}{:>17}\n",
            "time by role", "count", "time", "failed", "largest answer"
        );
        for (name, row) in ROLES.iter().zip(self.0.roles.iter()).filter(|(_, r)| r.count > 0) {
            let _ = writeln!(
                out,
                "      {name:<19}{:>6}{:>10}{:>9}{:>17}",
                row.count,
                duration(row.ms),
                row.failed,
                size(row.largest)
            );
        }
        for (name, row) in [("interrupts", self.0.interrupts), ("respawns", self.0.respawns)] {
            let _ = writeln!(out, "      {name:<19}{:>6}{:>10}", row.count, duration(row.ms));
        }
        let _ = writeln!(
            out,
            "      {:<19}{:>6}{:>10}",
            "Domino between",
            "—",
            duration(self.0.between_ms)
        );
        out += &match &self.0.easycrypt {
            Some(sums) => sums.render(),
            None => "    EasyCrypt: no timing in the answers\n".to_string(),
        };
        let total = self.total();
        if total.abs_diff(easycrypt_time) > easycrypt_time / 100 {
            let _ = writeln!(
                out,
                "    warning: the rows sum to {}, not to the EasyCrypt time {}",
                duration(total.as_millis()),
                duration(easycrypt_time.as_millis())
            );
        }
        out
    }
}

impl EcSums {
    fn add(&mut self, timing: &Timing) {
        self.tactic_ms += timing.tactic_ms;
        self.serialize_ms += timing.serialize_ms;
        if let Some(smt) = &timing.smt {
            self.smt_calls += smt.calls;
            self.translate_ms += smt.translate_ms;
            self.prepare_ms += smt.prepare_ms;
            self.prover_ms += smt.prover_ms;
            self.valid += smt.valid;
            self.timeout += smt.timeout;
            self.unknown += smt.unknown;
        }
    }

    fn merge(&mut self, other: &EcSums) {
        self.tactic_ms += other.tactic_ms;
        self.serialize_ms += other.serialize_ms;
        self.smt_calls += other.smt_calls;
        self.translate_ms += other.translate_ms;
        self.prepare_ms += other.prepare_ms;
        self.prover_ms += other.prover_ms;
        self.valid += other.valid;
        self.timeout += other.timeout;
        self.unknown += other.unknown;
    }

    fn render(&self) -> String {
        let ms = |ms: u64| duration(u128::from(ms));
        format!(
            "    EasyCrypt: tactic {} (smt {}: translate {}, prepare {}, prover {};\n               \
             {} calls: {} valid, {} timeout, {} unknown), serialize {}\n",
            ms(self.tactic_ms),
            ms(self.translate_ms + self.prepare_ms + self.prover_ms),
            ms(self.translate_ms),
            ms(self.prepare_ms),
            ms(self.prover_ms),
            self.smt_calls,
            self.valid,
            self.timeout,
            self.unknown,
            ms(self.serialize_ms)
        )
    }
}

fn row_of(role: &Role) -> usize {
    match role {
        Role::QuickClose => 0,
        Role::Structure => 1,
        Role::SideGoalFallback(_) => 2,
        Role::LeafFallback(_) => 3,
        Role::Reduce => 4,
        Role::Split => 5,
        Role::PartFallback { .. } => 6,
        Role::Admit { .. } => 7,
        Role::Undo => 8,
        Role::Resume => 9,
    }
}

/// `0s`, `12.3s` under a minute, `7m 40s`, `1h 12m 03s`.
fn duration(ms: u128) -> String {
    let secs = ms / 1000;
    match secs {
        _ if ms == 0 => "0s".to_string(),
        0..=59 => format!("{:.1}s", ms as f64 / 1000.0),
        60..=3599 => format!("{}m {:02}s", secs / 60, secs % 60),
        _ => format!("{}h {:02}m {:02}s", secs / 3600, secs / 60 % 60, secs % 60),
    }
}

/// `850 B`, `12.0 kB`, `1.2 MB`.
fn size(bytes: usize) -> String {
    match bytes {
        0..=999 => format!("{bytes} B"),
        1_000..=99_999 => format!("{:.1} kB", bytes as f64 / 1e3),
        _ => format!("{:.1} MB", bytes as f64 / 1e6),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::easycrypt::json::SmtTiming;

    fn sentence(role: &Role, ms: u128, bytes: usize, failed: bool) -> Sentence<'_> {
        Sentence {
            role,
            ms,
            bytes,
            failed,
            timing: None,
        }
    }

    fn known() -> TimeByRole {
        let mut t = TimeByRole::default();
        t.add_sentence(&sentence(&Role::QuickClose, 460_000, 1_200_000, true));
        t.add_sentence(&sentence(&Role::QuickClose, 0, 10, false));
        t.add_sentence(&sentence(&Role::Structure, 242_000, 900_000, false));
        t.add_sentence(&sentence(&Role::LeafFallback(2), 1_875_000, 1_400_000, true));
        t.add_sentence(&sentence(&Role::Undo, 130_000, 850, false));
        t.add_event(Event::Interrupt { resends: 1 }, 270_000);
        t.add_event(Event::Between, 40_000);
        t.add_event(Event::Between, 25_000);
        t
    }

    #[test]
    fn the_table_has_a_row_per_role_that_occurred_in_glossary_order_then_the_events() {
        let t = known();
        assert_eq!(t.total(), Duration::from_millis(3_042_000));
        assert_eq!(
            t.render(Duration::from_millis(3_050_000)),
            "    time by role           count      time   failed   largest answer\n\
             \x20     quick close             2    7m 40s        1           1.2 MB\n\
             \x20     structure               1    4m 02s        0           0.9 MB\n\
             \x20     leaf fallback           1   31m 15s        1           1.4 MB\n\
             \x20     undo                    1    2m 10s        0            850 B\n\
             \x20     interrupts              1    4m 30s\n\
             \x20     respawns                0        0s\n\
             \x20     Domino between          —    1m 05s\n\
             \x20   EasyCrypt: no timing in the answers\n"
        );
    }

    #[test]
    fn rows_that_miss_the_easycrypt_time_by_more_than_one_percent_give_a_warning() {
        let text = known().render(Duration::from_secs(3_100));
        assert!(
            text.ends_with("    warning: the rows sum to 50m 42s, not to the EasyCrypt time 51m 40s\n"),
            "{text}"
        );
    }

    #[test]
    fn the_easycrypt_line_sums_the_timing_of_the_answers() {
        let smt = SmtTiming {
            calls: 3,
            translate_ms: 2_000,
            prepare_ms: 3_000,
            prover_ms: 40_000,
            valid: 1,
            timeout: 1,
            unknown: 1,
        };
        let with_smt = Timing {
            tactic_ms: 50_000,
            serialize_ms: 400,
            smt: Some(smt),
        };
        let without = Timing {
            tactic_ms: 2_000,
            serialize_ms: 400,
            smt: None,
        };
        let mut t = TimeByRole::default();
        for timing in [&with_smt, &without] {
            t.add_sentence(&Sentence {
                timing: Some(timing),
                ..sentence(&Role::Split, 26_000, 5, false)
            });
        }
        let text = t.render(Duration::from_secs(52));
        assert!(
            text.ends_with(
                "    EasyCrypt: tactic 52.0s (smt 45.0s: translate 2.0s, prepare 3.0s, prover 40.0s;\n\
                 \x20              3 calls: 1 valid, 1 timeout, 1 unknown), serialize 0.8s\n"
            ),
            "{text}"
        );
    }

    #[test]
    fn a_merged_table_adds_the_rows_and_keeps_the_largest_answer() {
        let mut t = known();
        let mut respawned = TimeByRole::default();
        respawned.add_event(Event::Respawn, 5_000);
        respawned.add_sentence(&sentence(&Role::Resume, 3_000, 2_000_000, false));
        respawned.add_sentence(&sentence(&Role::QuickClose, 1_000, 5, true));
        t.merge(&respawned);
        assert_eq!(t.total(), Duration::from_millis(3_051_000));
        let text = t.render(Duration::from_millis(3_051_000));
        assert!(text.contains("      quick close             3    7m 41s        2           1.2 MB\n"), "{text}");
        assert!(text.contains("      resume                  1      3.0s        0           2.0 MB\n"), "{text}");
        assert!(text.contains("      respawns                1      5.0s\n"), "{text}");
    }
}
