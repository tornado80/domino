// SPDX-License-Identifier: MIT OR Apache-2.0

use super::driver::{pair_view, Part, SmtOutcome};
use super::*;
use crate::debug::driver::{ClaimVerdict, PartVerdict, TerminalView, Verdict};
use crate::debug::lockstep::{PairRecord, PairSide, EQUAL_OUTPUT};
use crate::easycrypt::job::{session_dir, AdmitRecord};
use crate::easycrypt::session::split_sentences;

fn pair_view_for_tests(p: &PairRecord, part: &Part) -> &'static str {
    pair_view(p, part).slug()
}

fn side(is_abort: bool) -> PairSide {
    PairSide {
        steps: vec![],
        terminal: TerminalView {
            label: 1,
            line: String::new(),
            is_abort,
        },
        lines: vec![],
        effect: None,
    }
}

fn pair(
    equal_output: Verdict,
    invariant: Verdict,
    relations: &[(&str, Verdict)],
    aborts: bool,
) -> PairRecord {
    PairRecord {
        id: "J1".into(),
        node: 0,
        left: side(aborts),
        right: side(false),
        claims: vec![
            ClaimVerdict {
                claim: EQUAL_OUTPUT.into(),
                verdict: equal_output,
                model: None,
                parts: Vec::new(),
            },
            ClaimVerdict {
                claim: "invariant".into(),
                verdict: invariant,
                model: None,
                parts: relations
                    .iter()
                    .map(|(name, verdict)| PartVerdict {
                        name: name.to_string(),
                        verdict: verdict.clone(),
                        model: None,
                    })
                    .collect(),
            },
        ],
    }
}

fn fails() -> Verdict {
    Verdict::GoalFails { model: "m".into() }
}

#[test]
fn smt_hints_come_from_the_easycrypt_table_of_ssp_toml() {
    assert_eq!(parse_smt_hints("").unwrap(), Vec::<String>::new());
    assert_eq!(
        parse_smt_hints("[other]\nx = 1\n").unwrap(),
        Vec::<String>::new()
    );
    assert_eq!(
        parse_smt_hints("[easycrypt]\nsmt_hints = [\"get_set_sameE\", \"Foo.bar_1\"]\n").unwrap(),
        vec!["get_set_sameE".to_string(), "Foo.bar_1".to_string()]
    );
    // a hint ends up in a tactic: only lemma names are accepted
    assert!(parse_smt_hints("[easycrypt]\nsmt_hints = [\"a). admit\"]\n").is_err());
    assert!(parse_smt_hints("[easycrypt]\nsmt_hints = \"x\"\n").is_err());
    assert!(parse_smt_hints("[easycrypt]\nsmt_hints = [1]\n").is_err());
    assert!(parse_smt_hints("not toml [").is_err());
}

#[test]
fn a_missing_ssp_toml_means_no_hints() {
    let dir = tempfile::tempdir().unwrap();
    assert!(read_smt_hints(dir.path()).unwrap().is_empty());
    std::fs::write(
        dir.path().join("ssp.toml"),
        "[easycrypt]\nsmt_hints = [\"mem_set\"]\n",
    )
    .unwrap();
    assert_eq!(
        read_smt_hints(dir.path()).unwrap(),
        vec!["mem_set".to_string()]
    );
}

#[test]
fn an_admit_label_names_the_id_the_claim_the_reason_and_dominos_verdict() {
    let admit = Admit {
        reason: AdmitReason::DominoVerifiedEcFailed,
        id: "J7".into(),
        claim: "invariant/StateRelation_rel_keys".into(),
        domino: DominoView::Verified,
        goal: String::new(),
        smt: None,
    };
    assert_eq!(
        admit.label(),
        "(* domino: J7 StateRelation_rel_keys; domino-verified-ec-failed *)"
    );
    // a sentence with such a comment is still one sentence for the session
    let sentences = split_sentences(&format!("admit. {}\nauto.", admit.label()));
    assert_eq!(sentences, vec!["admit.", "auto."]);
    // every slug is distinct
    let mut slugs: Vec<_> = AdmitReason::ALL.iter().map(|r| r.slug()).collect();
    slugs.sort_unstable();
    slugs.dedup();
    assert_eq!(slugs.len(), AdmitReason::ALL.len());
}

#[test]
fn dominos_verdicts_steer_per_claim_and_per_relation() {
    // equal-output fails, the invariant holds
    let p = pair(fails(), Verdict::Verified, &[], false);
    assert_eq!(pair_view_for_tests(&p, &Part::EqualOutput), "fails");
    assert_eq!(pair_view_for_tests(&p, &Part::Invariant), "verified");
    assert_eq!(pair_view_for_tests(&p, &Part::Whole), "fails");

    // one relation fails: only it does
    let p = pair(
        Verdict::Verified,
        fails(),
        &[
            ("StateRelation_a", Verdict::Verified),
            ("StateRelation_b", fails()),
        ],
        false,
    );
    assert_eq!(
        pair_view_for_tests(&p, &Part::Relation("a".into())),
        "verified"
    );
    assert_eq!(
        pair_view_for_tests(&p, &Part::Relation("b".into())),
        "fails"
    );
    // a part with no verdict where `invariant` failed is inconclusive, never the invariant's
    // verdict
    assert_eq!(
        pair_view_for_tests(&p, &Part::Relation("c".into())),
        "inconclusive"
    );

    // unreachable pairs count as verified; inconclusive stays inconclusive
    let p = pair(
        Verdict::pair_infeasible(),
        Verdict::Inconclusive { model: None },
        &[],
        false,
    );
    assert_eq!(pair_view_for_tests(&p, &Part::EqualOutput), "verified");
    assert_eq!(pair_view_for_tests(&p, &Part::Invariant), "inconclusive");
}

/// An ambient goal whose conclusion is `concl` (formula JSON).
fn ambient_goal(concl: &str) -> crate::easycrypt::json::Goal {
    serde_json::from_str(&format!(r#"{{"id":1,"concl":{concl}}}"#)).unwrap()
}

fn app(op: &str, args: &[&str]) -> String {
    format!(
        r#"{{"kind":"app","pp":"","op":"{op}","args":[{}]}}"#,
        args.join(",")
    )
}

/// Story 59 §3.3: a `StateRelation_` conjunct starts its state-relation part; a `Helper_`
/// conjunct is unfolded and stays in the part that contains it, never a part of its own.
#[test]
fn a_state_relation_starts_a_part_and_a_helper_stays_inside_one() {
    use super::driver::{ambient_step, Step};
    use crate::writers::easycrypt::invariant::InvariantOp;
    let op = |name: &str, relation: Option<&str>| InvariantOp {
        name: name.into(),
        claim: None,
        relation: relation.map(Into::into),
    };
    let part_ops = [op("StateRelation_a", Some("a")), op("Helper_h", None)];
    let var = r#"{"kind":"local","pp":"x"}"#;
    let relation = app("Top.Eq_L_R_Invariants.StateRelation_a", &[var, var]);
    let helper = app("Top.Eq_L_R_Invariants.Helper_h", &[var]);
    // JSON spells the operator `/\` with an escaped backslash
    let leaf = app(r"Top.Logic./\\", &[&relation, &helper]);

    let step = |concl: &str, part: Part| ambient_step(&ambient_goal(concl), &part, &part_ops);
    assert_eq!(step(&leaf, Part::Whole), (Step::Split, Part::Whole));
    assert_eq!(
        step(&relation, Part::Whole),
        (
            Step::Unfold("StateRelation_a".into()),
            Part::Relation("a".into())
        )
    );
    // the helper is unfolded in whatever part it is in
    for part in [Part::Whole, Part::Invariant, Part::Relation("a".into())] {
        assert_eq!(
            step(&helper, part.clone()),
            (Step::Unfold("Helper_h".into()), part)
        );
    }
    assert_eq!(
        Part::Relation("a".into()).claim_label(),
        "invariant/StateRelation_a"
    );
}

#[test]
fn an_invariant_failure_where_a_side_aborts_is_not_held_against_easycrypt() {
    // story 23: Domino's invariant verdict is stricter than EasyCrypt's `inv` at abort pairs
    let p = pair(
        Verdict::Verified,
        fails(),
        &[("StateRelation_a", fails())],
        true,
    );
    assert_eq!(pair_view_for_tests(&p, &Part::Invariant), "inconclusive");
    assert_eq!(
        pair_view_for_tests(&p, &Part::Relation("a".into())),
        "inconclusive"
    );
    // equal-output has no such exemption
    let p = pair(fails(), Verdict::Verified, &[], true);
    assert_eq!(pair_view_for_tests(&p, &Part::EqualOutput), "fails");
}

fn oracle_with(admits: Vec<Admit>) -> OracleTactics {
    OracleTactics {
        oracle: "O".into(),
        problem: None,
        stats: OracleStats {
            closed: 4,
            admits,
            fallbacks: 0,
            attempts_undone: 2,
            ..OracleStats::default()
        },
        alignment_mismatches: vec![],
        joint_paths: 2,
        nodes: 7,
        stuck_points: 1,
        lockstep_time: Duration::from_millis(100),
        easycrypt_time: Duration::from_secs(3),
        script: String::new(),
        closed: vec![],
        tree_id: None,
        resumed: false,
        resumed_at: None,
        transcript: None,
    }
}

fn equivalence_with(oracles: Vec<OracleTactics>) -> EquivalenceTactics {
    EquivalenceTactics {
        composition: None,
        proofstep: 0,
        proof_file: "Eq_A_B.ec".into(),
        left: "A".into(),
        right: "B".into(),
        oracles,
        elapsed: Duration::from_secs(4),
        report_file: "progress/Eq_A_B/report.txt".into(),
        interrupted: None,
        ended_early: None,
        unanswered: vec![],
        writes: 0,
    }
}

fn admit(reason: AdmitReason, id: &str) -> Admit {
    Admit {
        reason,
        id: id.into(),
        claim: "equal-output".into(),
        domino: DominoView::Verified,
        goal: "x = y".into(),
        smt: None,
    }
}

#[test]
fn the_report_counts_admits_by_reason_and_lists_the_verified_ones_with_their_goal() {
    let o = oracle_with(vec![
        admit(AdmitReason::Stuck, "S1"),
        admit(AdmitReason::DominoVerifiedEcFailed, "J2"),
        admit(AdmitReason::DominoVerifiedEcFailed, "J3"),
    ]);
    assert_eq!(
        o.admits_by_reason(),
        vec![
            (AdmitReason::Stuck, 1),
            (AdmitReason::DominoVerifiedEcFailed, 2)
        ]
    );
    let eq = equivalence_with(vec![o]);
    let report = eq.render();
    assert!(
        report.contains("3 admits (stuck 1, domino-verified-ec-failed 2)"),
        "{report}"
    );
    assert!(report.contains("goals closed: 4"), "{report}");
    assert!(
        report.contains("admit J2 equal-output; domino-verified-ec-failed"),
        "{report}"
    );
    // only that class carries the goal text
    assert_eq!(report.matches("goal: x = y").count(), 2, "{report}");
    assert!(
        report.contains("1 oracles, 4 goals closed, 3 admits"),
        "{report}"
    );
}

/// Story 57: the time by role table is under the oracle's `goals closed` line, and the
/// `EasyCrypt:` line follows it.
#[test]
fn the_report_shows_each_oracles_time_by_role_under_its_goals_closed_line() {
    use crate::easycrypt::time_by_role::Sentence;
    use crate::easycrypt::transcript::{Event, Role};
    let mut o = oracle_with(vec![]);
    let row = |role, ms, failed| Sentence {
        role,
        ms,
        parse_ms: 0,
        bytes: 1_300_000,
        failed,
        timing: None,
    };
    o.stats.time.add_sentence(&row(&Role::QuickClose, 1_200, true));
    o.stats.time.add_sentence(&row(&Role::Structure, 1_500, false));
    o.stats.time.add_event(Event::Between, 300);
    let report = equivalence_with(vec![o]).render();
    let expected = "
    goals closed: 4, no admit, fallbacks: 0, EasyCrypt time 3.0s (2 attempts undone)
    time by role           count      time   failed   largest answer
      quick close             1      1.2s        1           1.3 MB
      structure               1      1.5s        0           1.3 MB
      interrupts              0        0s
      respawns                0        0s
      Domino between          —      0.3s
    EasyCrypt: no timing in the answers
1 oracles";
    assert!(report.contains(expected), "{report}");
}

#[test]
fn an_oracle_without_records_has_no_time_by_role_table() {
    let report = equivalence_with(vec![oracle_with(vec![])]).render();
    assert!(!report.contains("time by role"), "{report}");
}

#[test]
fn the_admits_of_a_seal_have_their_own_reason_in_the_report() {
    assert_eq!(AdmitReason::ALL.last(), Some(&AdmitReason::Interrupted));
    assert_eq!(AdmitReason::Interrupted.slug(), "interrupted");
    let sealed = Admit {
        reason: AdmitReason::Interrupted,
        id: "N3".into(),
        claim: "open-goal".into(),
        domino: DominoView::NotApplicable,
        goal: String::new(),
        smt: None,
    };
    assert_eq!(
        sealed.label(),
        "(* domino: N3 open-goal; interrupted *)"
    );
    let o = oracle_with(vec![
        admit(AdmitReason::Stuck, "S1"),
        sealed.clone(),
        sealed,
    ]);
    let eq = equivalence_with(vec![o]);
    let report = eq.render();
    assert!(
        report.contains("3 admits (stuck 1, interrupted 2)"),
        "{report}"
    );
    assert!(
        report.contains("admit N3 open-goal; interrupted"),
        "{report}"
    );
}

#[test]
fn a_resumed_oracle_reports_where_it_resumed_and_what_it_kept() {
    let mut o = oracle_with(vec![admit(AdmitReason::Stuck, "S1")]);
    o.oracle = "PKENC".into();
    o.resumed_at = Some(ResumedAt {
        node: "N7".into(),
        kept: 12,
        mode: ResumeMode::Trust,
        stale: vec![],
    });
    let report = equivalence_with(vec![o.clone()]).render();
    assert!(
        report.contains("  PKENC: resumed at N7 (12 closed nodes kept, trust)\n  PKENC: lockstep 2 joint paths"),
        "{report}"
    );
    assert!(!report.contains("stale"), "{report}");
    o.resumed_at = Some(ResumedAt {
        node: "N7".into(),
        kept: 1,
        mode: ResumeMode::Replay,
        stale: vec!["code", "invariants"],
    });
    let report = equivalence_with(vec![o]).render();
    assert!(
        report.contains(
            "  PKENC: resumed at N7 (1 closed node kept, replay); saved joint tree is stale (code, invariants)\n"
        ),
        "{report}"
    );
}

#[test]
fn an_interrupted_report_names_what_was_sealed() {
    let sealed = |oracle: &str| Interrupted::Sealed {
        oracle: oracle.into(),
        admits: 5,
        node: "N4".into(),
    };
    assert_eq!(
        sealed("PKENC").to_string(),
        "sealed PKENC with 5 admits at node N4"
    );
    assert_eq!(
        Interrupted::Lockstep {
            oracle: "PKDEC".into()
        }
        .to_string(),
        "during lockstep execution of PKDEC, nothing sealed"
    );
    let mut eq = equivalence_with(vec![oracle_with(vec![])]);
    assert!(!eq.render().contains("interrupted"));
    eq.interrupted = Some(sealed("PKENC"));
    let report = eq.render();
    assert!(
        report.contains("\ninterrupted: sealed PKENC with 5 admits at node N4\n"),
        "{report}"
    );
    let theorem = TheoremTactics {
        theorem: "T".into(),
        equivalences: vec![eq],
        side_invariants: vec![],
        unproved_side_invariants: vec![],
        elapsed: Duration::from_secs(4),
        swallowed_interrupt: None,
    };
    assert_eq!(theorem.interrupted(), Some(&sealed("PKENC")));
}

/// The `admit` sentences of a proof file with their labels' reasons.
fn labelled_admits(text: &str) -> Vec<String> {
    text.lines()
        .filter_map(|line| {
            let (_, label) = line.split_once("admit. (* domino: ")?;
            let reason = label.split_once("reason: ")?.1;
            Some(reason.split([';', ' ']).next().unwrap().to_string())
        })
        .collect()
}

// ----------------------------------------------------------------------
// Story 37: what a proof job does with a session record
// ----------------------------------------------------------------------

fn eq_report() -> EquivalenceReport {
    EquivalenceReport {
        proofstep: 0,
        left_name: "L".into(),
        right_name: "R".into(),
        invariants_file: "Invariants.ec".into(),
        proof_file: "Eq_L_R.ec".into(),
        oracle_files: ["A", "B", "C"]
            .map(|o| (o.to_string(), format!("Eq_L_R_{o}.ec")))
            .to_vec(),
        oracle_count: 3,
        admit_count: 0,
        oracle_set_mismatch: None,
        state_relations: vec!["invariant".into()],
        helpers: Vec::new(),
        side_compositions: Vec::new(),
    }
}

fn done(name: &str) -> OracleRecord {
    let mut o = OracleRecord::new(name, OracleStatus::Done);
    o.script = Some(format!("+ proc; inline.\n  auto. (* {name} *)\n"));
    o
}

/// The oracles of [`eq_report`].
fn names() -> Vec<String> {
    ["A", "B", "C"].map(String::from).to_vec()
}

fn record_of(out: &Path, oracle: &str) -> PathBuf {
    oracle_record_path(out, "Eq_L_R.ec", oracle)
}

/// Writes one record for each of `oracles` (story 68) and plans a job on them.
fn plan_of(oracles: Vec<OracleRecord>, options: &TacticsOptions) -> (JobPlan, tempfile::TempDir) {
    let out = tempfile::tempdir().unwrap();
    std::fs::create_dir_all(session_dir(out.path(), "Eq_L_R.ec")).unwrap();
    for o in oracles {
        let record = SessionRecord::new("T", "L", "R", vec![o.clone()]);
        std::fs::write(record_of(out.path(), &o.name), record.to_json()).unwrap();
    }
    let plan = plan_job(&eq_report(), out.path(), options, &names()).unwrap();
    (plan, out)
}

fn partial() -> Vec<OracleRecord> {
    vec![
        done("A"),
        OracleRecord::new("B", OracleStatus::Interrupted),
        OracleRecord::new("C", OracleStatus::Pending),
    ]
}

fn oracle_option(name: &str, force: bool) -> TacticsOptions {
    TacticsOptions {
        oracle: Some(name.into()),
        force,
        ..TacticsOptions::default()
    }
}

fn prior(plan: JobPlan) -> Option<SessionRecord> {
    match plan {
        JobPlan::Prove { prior } => prior,
        JobPlan::Skip => panic!("expected a job that proves"),
    }
}

#[test]
fn without_a_record_a_job_proves_everything() {
    let out = tempfile::tempdir().unwrap();
    let plan = plan_job(&eq_report(), out.path(), &TacticsOptions::default(), &names()).unwrap();
    assert!(prior(plan).is_none());
}

#[test]
fn an_oracle_without_a_record_makes_the_equivalence_partial() {
    let (plan, _out) = plan_of(vec![done("A"), done("B")], &TacticsOptions::default());
    let record = prior(plan).expect("resumed, not skipped");
    assert_eq!(record.oracle("C").unwrap().status, OracleStatus::Pending);
    assert!(!record.complete);
}

#[test]
fn a_job_resumes_from_an_old_whole_equivalence_record_split_on_first_use() {
    let out = tempfile::tempdir().unwrap();
    let whole = SessionRecord::new("T", "L", "R", partial());
    let path = crate::easycrypt::job::equivalence_record_path(out.path(), "Eq_L_R.ec");
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(&path, whole.to_json()).unwrap();
    let plan = plan_job(&eq_report(), out.path(), &TacticsOptions::default(), &names()).unwrap();
    let record = prior(plan).expect("resumed");
    assert!(record.oracle("A").unwrap().is_resumable());
    assert_eq!(record.oracle("B").unwrap().status, OracleStatus::Interrupted);
    // each oracle now has its own record; the old one stays
    for o in ["A", "B", "C"] {
        assert!(record_of(out.path(), o).exists(), "{o}");
    }
    assert!(path.exists());
}

#[test]
fn a_partial_record_is_resumed_with_its_entries() {
    let (plan, _out) = plan_of(partial(), &TacticsOptions::default());
    let record = prior(plan).expect("resumed");
    assert_eq!(record.oracles.len(), 3);
    assert!(OracleTactics::from_record(record.oracle("A").unwrap()).unwrap().resumed);
    assert!(OracleTactics::from_record(record.oracle("B").unwrap()).is_none());
}

#[test]
fn a_complete_record_skips_and_force_proves_from_scratch_and_deletes_it() {
    let all = vec![done("A"), done("B"), done("C")];
    let (skipped, _out) = plan_of(all.clone(), &TacticsOptions::default());
    assert!(matches!(skipped, JobPlan::Skip));
    let forced = TacticsOptions {
        force: true,
        ..TacticsOptions::default()
    };
    let (plan, out) = plan_of(all, &forced);
    assert!(prior(plan).is_none());
    for o in ["A", "B", "C"] {
        assert!(!record_of(out.path(), o).exists(), "{o}");
    }
}

#[test]
fn force_discards_a_partial_record_too() {
    let forced = TacticsOptions {
        force: true,
        ..TacticsOptions::default()
    };
    let (plan, _out) = plan_of(partial(), &forced);
    assert!(prior(plan).is_none());
}

#[test]
fn an_oracle_that_is_done_is_skipped_and_one_that_is_not_is_proved() {
    let (skipped, _out) = plan_of(partial(), &oracle_option("A", false));
    assert!(matches!(skipped, JobPlan::Skip));
    let (plan, _out) = plan_of(partial(), &oracle_option("B", false));
    let record = prior(plan).expect("the others keep their entries");
    assert!(record.oracle("A").unwrap().is_resumable());
    // a complete record with `--oracle O` skips as well
    let all = vec![done("A"), done("B"), done("C")];
    let (skipped, _out) = plan_of(all, &oracle_option("C", false));
    assert!(matches!(skipped, JobPlan::Skip));
}

#[test]
fn force_with_an_oracle_reproves_that_oracle_alone_and_keeps_the_rest() {
    let all = vec![done("A"), done("B"), done("C")];
    let (plan, out) = plan_of(all, &oracle_option("B", true));
    let record = prior(plan).expect("kept");
    assert_eq!(record.oracle("B").unwrap().status, OracleStatus::Pending);
    assert!(record.oracle("A").unwrap().is_resumable());
    assert!(record.oracle("C").unwrap().is_resumable());
    assert!(!record.complete);
    // its record goes, so a crash cannot leave a done record beside a restarted file
    assert!(!record_of(out.path(), "B").exists());
    assert!(record_of(out.path(), "A").exists());
}

#[test]
fn a_version_1_record_cannot_be_resumed_from() {
    let out = tempfile::tempdir().unwrap();
    std::fs::create_dir_all(session_dir(out.path(), "Eq_L_R.ec")).unwrap();
    std::fs::write(
        crate::easycrypt::job::equivalence_record_path(out.path(), "Eq_L_R.ec"),
        r#"{"version": 1, "theorem": "T", "left": "L", "right": "R", "complete": false,
            "oracles": [{"name": "A", "status": "done"}, {"name": "B", "status": "pending"}]}"#,
    )
    .unwrap();
    let plan = plan_job(&eq_report(), out.path(), &TacticsOptions::default(), &names()).unwrap();
    let record = prior(plan).expect("read");
    assert_eq!(record.version, 1);
    assert!(OracleTactics::from_record(record.oracle("A").unwrap()).is_none());
    // a done oracle without a script is not skipped by `--oracle` either: it is proved again
    let plan = plan_job(&eq_report(), out.path(), &oracle_option("A", false), &names()).unwrap();
    assert!(prior(plan).is_some());
}

#[test]
fn a_resumed_oracle_reads_back_its_admits_and_lockstep() {
    let mut record = done("A");
    record.admits = vec![AdmitRecord {
        node: "N7".into(),
        reason: "stuck".into(),
        claim: "invariant".into(),
        domino: "inconclusive".into(),
    }];
    record.lockstep = Some(LockstepRecord {
        joint_paths: 23,
        ms: 41200,
    });
    let o = OracleTactics::from_record(&record).unwrap();
    assert!(o.resumed);
    assert_eq!(o.admits_by_reason(), vec![(AdmitReason::Stuck, 1)]);
    assert_eq!(o.joint_paths, 23);
    assert_eq!(o.lockstep_time, Duration::from_millis(41200));
    assert_eq!(o.to_record().admits, record.admits);
    assert_eq!(o.to_record().script, record.script);
    // a reason this version does not know: not resumable, so proved again
    record.admits[0].reason = "from-the-future".into();
    assert!(OracleTactics::from_record(&record).is_none());
}

#[test]
fn labels_are_read_back_from_the_file() {
    let text = "  + admit. (* domino: J1 invariant; reason: stuck; Domino: verified *)\n\
                  admit. (* domino: N4 program; reason: program-mismatch; Domino: inconclusive *)\n\
                + proc; inline. admit.\n";
    assert_eq!(labelled_admits(text), vec!["stuck", "program-mismatch"]);
}

/// The EasyCrypt a test's proof jobs start instead of [`crate::easycrypt::session::locate_binary`]'s,
/// with its interrupt timing (story tactics-run-survives-an-unanswered-interrupt).
#[derive(Clone)]
pub(super) struct FakeEasyCrypt {
    pub binary: PathBuf,
    pub grace: Duration,
    pub resend: Duration,
}

thread_local! {
    /// Set by a test, read by `spawn_easycrypt` on the same thread (a run is single-threaded).
    pub(super) static TEST_EASYCRYPT: std::cell::RefCell<Option<FakeEasyCrypt>> =
        const { std::cell::RefCell::new(None) };
}

fn answer_with(messages: &[&str]) -> crate::easycrypt::json::Response {
    let messages: Vec<String> = messages
        .iter()
        .map(|m| format!(r#"{{"level":"warning","text":{}}}"#, serde_json::Value::from(*m)))
        .collect();
    crate::easycrypt::json::parse_response(&format!(
        r#"{{"version":"domino-json/3","state":3,"status":"error","messages":[{}]}}"#,
        messages.join(",")
    ))
    .unwrap()
}

#[test]
fn a_swallowed_interrupt_is_warned_about_once_per_run() {
    let swallowed = answer_with(&[
        "error when starting `Z3': Failure in transformation eliminate_builtin anomaly: Stdlib.Sys.Break",
    ]);
    let watch = SwallowWatch::default();
    // not a swallow: the goal re-read handles it
    assert_eq!(watch.see(&answer_with(&["cannot serialize the goals: Stdlib.Sys.Break"])), None);
    assert_eq!(watch.see(&answer_with(&["error when starting `Z3': not found"])), None);
    assert_eq!(watch.warning(), None);
    let warning = watch.see(&swallowed).expect("the first swallow is warned about");
    assert!(
        warning.starts_with(
            "EasyCrypt swallowed an interrupt (`error when starting `Z3': Failure in transformation \
             eliminate_builtin anomaly: Stdlib.Sys.Break`). Rebuild it from branch \
             `amir/domino-easycrypt-integration` (story `easycrypt-never-swallows-an-interrupt`)"
        ),
        "{warning}"
    );
    assert_eq!(watch.see(&swallowed), None, "once per run");
    assert_eq!(watch.clone().see(&swallowed), None, "the run shares one watch");
    assert_eq!(watch.warning(), Some(warning.clone()));
    // the answer is left as it is
    assert_eq!(swallowed.status, crate::easycrypt::json::Status::Error);
    // and the run's summary says it
    let run = TheoremTactics {
        theorem: "T".into(),
        equivalences: vec![],
        side_invariants: vec![],
        unproved_side_invariants: vec![],
        elapsed: Duration::ZERO,
        swallowed_interrupt: watch.warning(),
    };
    assert!(run.render().contains(&format!("warning: {warning}\n")), "{}", run.render());
}

#[test]
fn an_unanswered_interrupt_is_its_own_line_in_the_report() {
    let mut eq = equivalence_with(vec![oracle_with(vec![admit(AdmitReason::Interrupted, "N38")])]);
    let u = Unanswered {
        oracle: "O".into(),
        node: "N38".into(),
        signals: 6,
        waited: Duration::from_millis(30_200),
        ended_job: false,
    };
    eq.unanswered = vec![u.clone()];
    let report = eq.render();
    assert!(
        report.contains(
            "\n    EasyCrypt left an interrupt unanswered at N38 (6 signals over 30 s); oracle \
             sealed, EasyCrypt given up, the next oracle gets a fresh one\n"
        ),
        "{report}"
    );
    assert!(!report.contains("interrupted:"), "not a Ctrl-C: {report}");
    // the third one ends the job, which says why, and is not a Ctrl-C
    eq.unanswered = vec![u.clone(), u.clone(), Unanswered { ended_job: true, ..u }];
    eq.interrupted = Some(Interrupted::Sealed {
        oracle: "O".into(),
        admits: 1,
        node: "N38".into(),
    });
    eq.ended_early = Some("EasyCrypt left 3 interrupts unanswered".into());
    let report = eq.render();
    assert!(report.contains("oracle sealed, EasyCrypt not respawned, the job ends\n"), "{report}");
    assert!(
        report.contains(
            "ended early: sealed O with 1 admits at node N38: EasyCrypt left 3 interrupts unanswered\n"
        ),
        "{report}"
    );
    let run = TheoremTactics {
        theorem: "T".into(),
        equivalences: vec![eq],
        side_invariants: vec![],
        unproved_side_invariants: vec![],
        elapsed: Duration::ZERO,
        swallowed_interrupt: None,
    };
    assert_eq!(run.interrupted(), None, "no Ctrl-C");
    assert!(run.ended_early());
}

/// The live tests: they skip unless `DOMINO_EASYCRYPT` names a `-json` EasyCrypt. Lockstep
/// execution uses the native cvc5 with `cvc5-lib`, and the `cvc5` binary on `PATH` without it.
mod live {
    use std::path::PathBuf;

    use super::*;
    use crate::easycrypt::check::{ok_or_reject, sentences_until_call};
    use crate::easycrypt::session::{json_binary_configured, split_sentences, Session};
    use crate::project::{DirectoryFiles, DirectoryProject};

    #[cfg(feature = "cvc5-lib")]
    fn backend() -> crate::util::smtsolver::cvc5lib::Cvc5LibBackend {
        crate::util::smtsolver::cvc5lib::Cvc5LibBackend::new(true, None)
    }

    #[cfg(not(feature = "cvc5-lib"))]
    fn backend() -> crate::util::smtsolver::process::IncrementalCvc5Backend {
        crate::util::smtsolver::process::IncrementalCvc5Backend
    }
    use crate::writers::easycrypt::export::{export_theorem, write_files};

    /// The most `easycrypt compile` of one written file may take.
    const COMPILE_TIMEOUT: Duration = Duration::from_secs(30 * 60);

    /// `easycrypt compile -I <dir> <file>`; `Err` carries the tail of its output. Only tests
    /// compile: a tactics run never does (ADR 0005).
    fn compile(binary: &Path, dir: &Path, file: &str) -> Result<(), String> {
        use std::process::Command;
        let stderr = tempfile::tempfile().map_err(|e| e.to_string())?;
        let mut child = Command::new(binary)
            .args(["compile", "-I"])
            .arg(dir)
            .arg(file)
            .current_dir(dir)
            .stdout(std::process::Stdio::null())
            .stderr(stderr.try_clone().map_err(|e| e.to_string())?)
            .spawn()
            .map_err(|e| e.to_string())?;
        let began = Instant::now();
        let status = loop {
            match child.try_wait().map_err(|e| e.to_string())? {
                Some(status) => break status,
                None if began.elapsed() > COMPILE_TIMEOUT => {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(format!("timed out after {}s", COMPILE_TIMEOUT.as_secs()));
                }
                None => std::thread::sleep(Duration::from_millis(200)),
            }
        };
        if status.success() {
            return Ok(());
        }
        use std::io::{Read, Seek};
        let mut text = String::new();
        let mut stderr = stderr;
        let _ = stderr.rewind();
        let _ = stderr.read_to_string(&mut text);
        let tail: Vec<&str> = text.lines().rev().take(8).collect();
        Err(tail.into_iter().rev().collect::<Vec<_>>().join("\n"))
    }

    fn run(
        dir: &str,
        theorem: &str,
        options: &TacticsOptions,
    ) -> Option<(TheoremTactics, tempfile::TempDir)> {
        run_captured(dir, theorem, options).map(|(result, out, _)| (result, out))
    }

    /// The proof file and its report as they were on disk when the run reported an event.
    #[derive(Debug, Clone)]
    struct Capture {
        /// `item 2` (an oracle started), `goal N3` (a joint node's goal done), `finished`.
        event: String,
        ec: String,
        report: Option<String>,
    }

    /// Reads the first equivalence's proof file and report at every tactics event: what a
    /// reader of the files sees while the run goes on.
    struct Capturing {
        /// The theorem's output directory and the glue of the first equivalence.
        out: PathBuf,
        file: String,
        /// The equivalence's progress folder: [`oracle_reports`] reads the reports under it.
        report: PathBuf,
        captures: std::rc::Rc<std::cell::RefCell<Vec<Capture>>>,
        /// Sets the flag at the first event whose name starts so, as a Ctrl-C would (story 34).
        stop_at: Option<(String, Arc<AtomicBool>)>,
    }

    thread_local! {
        /// The `NodeStarted` and `SentenceSent` events of this test's run (story 40).
        static WALK: std::cell::RefCell<Vec<String>> = const { std::cell::RefCell::new(Vec::new()) };
    }

    impl ExportObserver for Capturing {
        fn on_event(&mut self, event: &crate::writers::easycrypt::progress::ExportEvent<'_>) {
            use crate::writers::easycrypt::progress::ExportEvent;
            match event {
                ExportEvent::NodeStarted { node, total, .. } => {
                    WALK.with(|w| w.borrow_mut().push(format!("node {node}/{total}")))
                }
                ExportEvent::SentenceSent { sentence } => {
                    WALK.with(|w| w.borrow_mut().push(format!("sentence {sentence}")))
                }
                _ => {}
            }
            let event = match event {
                ExportEvent::ItemStarted { index, .. } => format!("item {index}"),
                ExportEvent::GoalFinished { goal, .. } => format!("goal {goal}"),
                ExportEvent::PhaseFinished { .. } => "finished".to_string(),
                _ => return,
            };
            if let Some((at, stop)) = &self.stop_at {
                if event.starts_with(at.as_str()) {
                    stop.store(true, Ordering::Relaxed);
                }
            }
            self.captures.borrow_mut().push(Capture {
                event,
                ec: proof_text(&self.out, &self.file),
                report: oracle_reports(&self.report),
            });
        }
    }

    /// [`run`], capturing the first equivalence's files at every event.
    fn run_captured(
        dir: &str,
        theorem: &str,
        options: &TacticsOptions,
    ) -> Option<(TheoremTactics, tempfile::TempDir, Vec<Capture>)> {
        run_stopped_at(dir, theorem, options, None)
    }

    /// [`run_captured`], and the run is asked to stop at the first event whose name starts with
    /// `stop_at`.
    fn run_stopped_at(
        dir: &str,
        theorem: &str,
        options: &TacticsOptions,
        stop_at: Option<&str>,
    ) -> Option<(TheoremTactics, tempfile::TempDir, Vec<Capture>)> {
        if !json_binary_configured() {
            eprintln!("DOMINO_EASYCRYPT not set, skipping");
            return None;
        }
        let dir = PathBuf::from(dir);
        let files = DirectoryFiles::load(&dir).unwrap();
        let project = DirectoryProject::load(dir, &files).unwrap();
        let theorem = project.get_theorem(theorem).unwrap();
        let exported = export_theorem(theorem, &project).unwrap();
        let out = tempfile::tempdir().unwrap();
        write_files(out.path(), &exported.files).unwrap();
        let proof_file = &exported.equivalences[0].proof_file;
        let captures = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
        let mut observer: Option<Box<dyn ExportObserver>> = Some(Box::new(Capturing {
            out: out.path().to_path_buf(),
            file: proof_file.clone(),
            report: out
                .path()
                .join(format!("progress/{}", proof_file.trim_end_matches(".ec"))),
            captures: captures.clone(),
            stop_at: stop_at.map(|at| {
                let stop = options.stop.clone().expect("a run to stop has a stop flag");
                (at.to_string(), stop)
            }),
        }));
        let result = run_tactics_observed(
            theorem,
            &project,
            &exported,
            out.path(),
            &backend(),
            options,
            &mut || {
                observer
                    .take()
                    .unwrap_or_else(|| Box::new(NopExportObserver))
            },
        )
        .unwrap();
        let captures = captures.borrow().clone();
        Some((result, out, captures))
    }

    /// The live page of the first equivalence: beside its transcript (story 36).
    fn page_path(result: &TheoremTactics) -> PathBuf {
        result.equivalences[0]
            .oracles[0]
            .transcript
            .as_ref()
            .expect("a proved oracle")
            .with_file_name("index.html")
    }

    /// The oracle lemma files of the first equivalence, in oracle order, one after another:
    /// what the one proof file held before story 68.
    fn proof_file(result: &TheoremTactics, out: &Path) -> String {
        proof_text(out, &result.equivalences[0].proof_file)
    }

    /// The oracle lemma files the glue `file` joins, in its order.
    fn oracle_files(out: &Path, file: &str) -> Vec<PathBuf> {
        let glue = std::fs::read_to_string(out.join(file)).unwrap();
        glue.lines()
            .filter_map(|l| l.trim().strip_prefix("+ by conseq "))
            .map(|rest| out.join(format!("{}.ec", rest.split([' ', '.']).next().unwrap())))
            .collect()
    }

    /// The oracle files' text one after another; a file no job has created yet is its
    /// untouched proof.
    fn proof_text(out: &Path, file: &str) -> String {
        oracle_files(out, file)
            .iter()
            .map(|f| std::fs::read_to_string(f).unwrap_or_else(|_| UNTOUCHED.to_string()))
            .collect::<Vec<_>>()
            .join("\n")
    }

    impl EquivalenceTactics {
        /// The transcript of the equivalence's one proved oracle; with more, their transcripts
        /// one after another in a file beside them.
        fn transcript(&self) -> PathBuf {
            let paths: Vec<&PathBuf> =
                self.oracles.iter().filter_map(|o| o.transcript.as_ref()).collect();
            if let [one] = paths[..] {
                return one.clone();
            }
            let dir = paths[0].parent().unwrap().parent().unwrap();
            let all = dir.join("all-transcripts.jsonl");
            let text: String = paths
                .iter()
                .map(|p| std::fs::read_to_string(p).unwrap())
                .collect();
            std::fs::write(&all, text).unwrap();
            all
        }
    }

    /// The record of the one oracle of the equivalence `file` that has one.
    fn session_record_path(out: &Path, file: &str) -> PathBuf {
        let dir = session_dir(out, file);
        std::fs::read_dir(&dir)
            .unwrap()
            .map(|e| e.unwrap().path())
            .find(|p| p.to_string_lossy().ends_with(".record.json"))
            .expect("an oracle record")
    }

    /// Story 40: the run says which node it is in before every sentence, and the transcript
    /// holds the sentences it announced.
    #[test]
    fn the_walk_announces_its_node_before_every_sentence() {
        WALK.with(|w| w.borrow_mut().clear());
        let Some((result, _out, _)) = run_captured(
            "example-projects/hello-world",
            "Proof",
            &TacticsOptions::default(),
        ) else {
            return;
        };
        let walk = WALK.with(|w| w.borrow().clone());
        assert!(walk[0].starts_with("node router/"), "{walk:?}");
        assert!(walk[1].starts_with("sentence proc; inline."), "{walk:?}");
        assert!(walk.iter().any(|e| e.starts_with("node N")), "{walk:?}");
        let total = walk[0].rsplit('/').next().unwrap();
        assert!(walk.iter().filter(|e| e.starts_with("node")).all(|e| e.ends_with(&format!("/{total}"))));
        let sentences = walk.iter().filter(|e| e.starts_with("sentence")).count();
        let transcript = std::fs::read_to_string(result.equivalences[0].transcript()).unwrap();
        assert!(sentences >= result.equivalences[0].oracles[0].stats.closed);
        assert!(transcript.lines().count() >= 1);
    }

    #[test]
    fn hello_world_useful_oracle_closes_with_no_admit_and_compiles() {
        let Some((result, out)) = run(
            "example-projects/hello-world",
            "Proof",
            &TacticsOptions::default(),
        ) else {
            return;
        };
        let oracle = &result.equivalences[0].oracles[0];
        assert_eq!(oracle.oracle, "UsefulOracle");
        assert!(oracle.problem.is_none(), "{:?}", oracle.problem);
        assert!(oracle.stats.admits.is_empty(), "{}", result.render());
        let text = proof_file(&result, out.path());
        assert!(!text.contains("admit"), "{text}");
        assert!(compile(
            &crate::easycrypt::session::locate_binary(),
            out.path(),
            &result.equivalences[0].proof_file
        )
        .is_ok());
        // the report is written next to the file and is what stdout shows
        let report =
            std::fs::read_to_string(out.path().join(&result.equivalences[0].report_file)).unwrap();
        assert_eq!(report, result.equivalences[0].render());
        assert!(report.contains("no admit"));
        // the transcript holds every sentence with EasyCrypt's answer
        let transcript = std::fs::read_to_string(result.equivalences[0].transcript()).unwrap();
        assert!(transcript.lines().count() >= oracle.stats.closed);
        assert!(transcript.contains("\"sentence\":\"proc; inline.\""));
        // every sentence of the walk says which oracle and node it belongs to, and why
        assert!(transcript.contains(
            "\"ctx\":{\"oracle\":\"UsefulOracle\",\"node\":0,\"kind\":\"sampling-synchronized\""
        ));
        for line in transcript.lines() {
            let v: serde_json::Value = serde_json::from_str(line).unwrap();
            assert!(v["ctx"]["role"].is_string(), "{v}");
            if v.get("event").is_none() {
                assert!(v["response"]["version"] == "domino-json/3");
                assert!(v["bytes"].as_u64().unwrap() > 0);
            }
        }
        // the records of the oracle account for its EasyCrypt time
        let ms: u64 = transcript
            .lines()
            .map(|l| serde_json::from_str::<serde_json::Value>(l).unwrap())
            .filter(|v| v["ctx"]["oracle"] == "UsefulOracle")
            .map(|v| v["ms"].as_u64().unwrap())
            .sum();
        let time = oracle.easycrypt_time.as_millis() as u64;
        // each record's `ms` is cut from a total over all oracles: one oracle's sum can be 1 ms
        // over its own time
        assert!(ms <= time + 1 && ms * 100 >= time * 99, "records {ms} ms, report {time} ms");
        // the time by role sums the same records (story 57)
        assert_eq!(oracle.stats.time.total().as_millis() as u64, ms);
        assert!(report.contains("    time by role "), "{report}");
        assert!(!report.contains("warning: the rows sum"), "{report}");
    }

    #[test]
    fn the_walk_of_the_joint_tree_alone_closes_hello_world_too() {
        // the quick close closes hello-world in one step: turn it off to see the tactics per node
        let Some((result, out)) = run(
            "example-projects/hello-world",
            "Proof",
            &TacticsOptions {
                quick_close: false,
                ..TacticsOptions::default()
            },
        ) else {
            return;
        };
        let oracle = &result.equivalences[0].oracles[0];
        assert!(oracle.stats.admits.is_empty(), "{}", result.render());
        assert_eq!(oracle.stats.fallbacks, 0);
        let text = proof_file(&result, out.path());
        // the router prelude, a synchronized sampling, a determined branch, the leaf
        for tactic in [
            "sp 1 1.",
            "if.",
            "seq 1 1 : (#pre /\\ rand{1} = rand{2}); 1: auto => />.",
            "rcondt{1} ^if; 1: auto => /#.",
            // the leaf (story 64): the exit path, then `auto`, then the goal opened
            "auto => &1 &2 hpre.",
        ] {
            assert!(text.contains(tactic), "missing `{tactic}` in\n{text}");
        }
        // story 63: no `sp` right before `rcondt`/`rcondf` (a determined node)
        let sentences: Vec<&str> = text
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .collect();
        for (i, s) in sentences.iter().enumerate().skip(1) {
            if s.starts_with("rcondt") || s.starts_with("rcondf") {
                assert!(
                    !sentences[i - 1].starts_with("sp "),
                    "`sp` before `{s}` in\n{text}"
                );
            }
        }
        // no position from our listing: every `sp` count comes from EasyCrypt's JSON, and no
        // subgoal is picked by a number but the `1:` of a side goal
        assert!(!text.contains("swap"));
        assert!(compile(
            &crate::easycrypt::session::locate_binary(),
            out.path(),
            &result.equivalences[0].proof_file
        )
        .is_ok());
    }

    /// A session on hello-world's `UsefulOracle` goal, and the theorem's names for it.
    fn hello_world_oracle_goal(out: &Path) -> (Session, crate::debug::lockstep::LockstepOutcome) {
        let dir = PathBuf::from("example-projects/hello-world");
        let files = DirectoryFiles::load(&dir).unwrap();
        let project = DirectoryProject::load(dir, &files).unwrap();
        let theorem = project.get_theorem("Proof").unwrap();
        let exported = export_theorem(theorem, &project).unwrap();
        write_files(out, &exported.files).unwrap();
        let file = &exported.equivalences[0].proof_file;
        let mut session = Session::start(out).unwrap();
        let source = &exported.files[Path::new(file)];
        for sentence in sentences_until_call(file, source).unwrap() {
            ok_or_reject(session.send(&sentence, Want::Full).unwrap(), file, &sentence).unwrap();
        }
        // the base case, then the oracle's goal is in front
        let base = &split_sentences(source)[sentences_until_call(file, source).unwrap().len()];
        assert_eq!(
            session.send(base, Want::Status).unwrap().status,
            crate::easycrypt::json::Status::Ok
        );
        assert!(session.front().unwrap().concl.kind == "equivF");
        let empty = crate::debug::lockstep::LockstepOutcome {
            tree: Default::default(),
            pairs: vec![],
            stuck: vec![],
            stop_reason: crate::debug::driver::StopReason::Completed,
        };
        (session, empty)
    }

    #[test]
    fn the_fallback_proves_an_oracle_without_the_joint_tree() {
        if !json_binary_configured() {
            eprintln!("DOMINO_EASYCRYPT not set, skipping");
            return;
        }
        let out = tempfile::tempdir().unwrap();
        let (mut session, empty) = hello_world_oracle_goal(out.path());
        let tree = super::driver::OracleTree::new(&empty);
        let mut prover = super::driver::Prover {
            judgement: super::driver::Judgement::Equiv,
            session: &mut session,
            script: Default::default(),
            tree: &tree,
            hints: &[],
            unfold_ops: &["inv".to_string(), "params_inv".to_string()],
            part_ops: &[],
            timeouts: Timeouts {
                general: Duration::from_secs(60),
                quick_close: Duration::from_secs(2),
            },
            quick_close: false,
            oracle: "UsefulOracle",
            leaf_budget: None,
            deadline: None,
            stats: OracleStats::default(),
            live: None,
            checkpoint: None,
            per_sentence: false,
            node: None,
            mismatches: vec![],
            stopped: None,
            resume: None,
            premises: Vec::new(),
            binders: Vec::new(),
            last_smt: None,
            admit_smt: None,
        };
        // an alignment mismatch sends the whole oracle down the fallback
        prover
            .oracle(|_| vec!["kind-differs at top level".to_string()])
            .unwrap();
        assert_eq!(prover.mismatches.len(), 1);
        assert_eq!(prover.stats.fallbacks, 1);
        assert!(prover.stats.admits.is_empty(), "{:?}", prover.stats.admits);
        let script = prover.script.render();
        // the PDF's trial procedure: a decided condition, then the sampling, then the leaf
        assert!(script.contains("rcondt{1} ^if; 1: auto => /#."), "{script}");
        assert!(
            script.contains("seq 1 1 : (#pre /\\ rand{1} = rand{2}); 1: auto => /#."),
            "{script}"
        );
        assert_eq!(prover.script.admit_count(), 0);
        assert_eq!(session.count(), 0, "the oracle's goal is closed");
    }

    #[test]
    fn two_runs_on_an_unchanged_project_write_the_same_file() {
        let options = TacticsOptions {
            quick_close: false,
            ..TacticsOptions::default()
        };
        let Some((a, out_a)) = run("example-projects/hello-world", "Proof", &options) else {
            return;
        };
        let (b, out_b) = run("example-projects/hello-world", "Proof", &options).unwrap();
        assert_eq!(proof_file(&a, out_a.path()), proof_file(&b, out_b.path()));
        // and the same final page, but for its timings (story 28)
        let page = |t: &TheoremTactics| std::fs::read_to_string(page_path(t)).unwrap();
        let (page_a, page_b) = (page(&a), page(&b));
        assert!(page_a.contains("id=\"timings\""));
        assert_eq!(stable_page(&page_a), stable_page(&page_b));
    }

    /// The page without its timings and without its transcript record numbers: a Domino gap of
    /// 100 ms or more is a `between` record (story 56), so the numbers move with the load.
    fn stable_page(html: &str) -> String {
        let html = strip_timings(html);
        let mut out = String::with_capacity(html.len());
        let mut rest = html.as_str();
        while let Some(at) = rest.find("record ") {
            let (head, tail) = rest.split_at(at + "record ".len());
            out += head;
            rest = tail.trim_start_matches(|c: char| c.is_ascii_digit());
            out.push('#');
        }
        out + rest
    }

    /// Story 31: the capped transcript is smaller and the page cannot tell the difference.
    #[test]
    fn the_page_is_the_same_under_a_capped_and_a_full_transcript() {
        let with = |ec_transcript| TacticsOptions {
            quick_close: false,
            ec_transcript,
            ..TacticsOptions::default()
        };
        let Some((capped, _out_capped)) = run(
            "example-projects/hello-world",
            "Proof",
            &with(EcTranscriptMode::Capped),
        ) else {
            return;
        };
        let (full, _out_full) = run(
            "example-projects/hello-world",
            "Proof",
            &with(EcTranscriptMode::Full),
        )
        .unwrap();
        let page =
            |t: &TheoremTactics| stable_page(&std::fs::read_to_string(page_path(t)).unwrap());
        assert_eq!(page(&capped), page(&full));
        let size = |t: &TheoremTactics| {
            std::fs::metadata(t.equivalences[0].transcript())
                .unwrap()
                .len()
        };
        assert!(
            size(&capped) < size(&full),
            "{} vs {}",
            size(&capped),
            size(&full)
        );
        let text = std::fs::read_to_string(capped.equivalences[0].transcript()).unwrap();
        assert!(text.contains("\"concl_cut\":"));
        assert!(!std::fs::read_to_string(full.equivalences[0].transcript())
            .unwrap()
            .contains("\"concl_cut\":"));
    }

    #[test]
    fn the_live_page_shows_the_oracle_its_goals_and_ends_without_a_refresh_tag() {
        let Some((result, _out)) = run(
            "example-projects/hello-world",
            "Proof",
            &TacticsOptions {
                quick_close: false,
                ..TacticsOptions::default()
            },
        ) else {
            return;
        };
        let page = std::fs::read_to_string(page_path(&result)).unwrap();
        assert!(
            !page.contains("http-equiv"),
            "the final page does not refresh"
        );
        assert!(page.contains("tactics (done)"));
        assert!(page.contains("UsefulOracle") && page.contains("router prelude"));
        // the goals of the walk, with their sentences, and the lockstep page they belong to
        assert!(page.contains("sp 1 1."));
        assert!(page.contains("proc; inline."));
        assert!(page.contains("lockstep page of this oracle"));
        assert!(page.contains("/easycrypt/index.html#n=") || page.contains("index.html#n="));
        assert!(page.contains("0 admit(s)"), "the summary counts admits");
        // the last step of a goal has its goal text embedded, straight from EasyCrypt
        assert!(page.contains("Type variables"), "goal text is embedded");
        let _ = result;
    }

    #[test]
    fn an_oracle_that_was_not_asked_for_keeps_its_admit() {
        let Some((result, out)) = run(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            &TacticsOptions {
                oracle: Some("PKGEN".into()),
                ..TacticsOptions::default()
            },
        ) else {
            return;
        };
        let text = proof_file(&result, out.path());
        // only PKGEN got tactics; PKENC and PKDEC keep `+ proc; inline. admit.`
        assert_eq!(text.matches("+ proc; inline. admit.").count(), 2, "{text}");
        assert_eq!(result.equivalences[0].oracles.len(), 1);
        // the report's counts are the labelled admits of the file
        let labelled = labelled_admits(&text);
        assert_eq!(labelled.len(), result.admit_count(), "{}", result.render());
    }
    // ------------------------------------------------------------------
    // Story 33: the file on disk is what is proved
    // ------------------------------------------------------------------

    /// Two oracles, one with a `domino-fails` admit; a few seconds.
    const TWO_ORACLES: &str = "test-projects/test-oracle-rename";

    fn walk(write_granularity: WriteGranularity) -> TacticsOptions {
        TacticsOptions {
            quick_close: false,
            write_granularity,
            ..TacticsOptions::default()
        }
    }

    const UNTOUCHED: &str = "+ proc; inline. admit.";

    /// `admit.` sentences of a proof file (outside comments).
    fn admit_sentences(text: &str) -> usize {
        text.lines()
            .filter(|l| {
                let code = l.split("(*").next().unwrap_or("");
                code.split(|c: char| c.is_whitespace() || c == ';')
                    .any(|w| w == "admit.")
            })
            .count()
    }

    /// The reports of the oracles under the equivalence's progress folder `dir`, in oracle
    /// order (story 68: each oracle's report is written with its file); `None` when there is
    /// none yet.
    fn oracle_reports(dir: &Path) -> Option<String> {
        let mut reports: Vec<PathBuf> = std::fs::read_dir(dir)
            .ok()?
            .map(|e| e.unwrap().path().join("report.txt"))
            .filter(|p| p.exists())
            .collect();
        reports.sort();
        let text: String = reports.iter().map(|p| std::fs::read_to_string(p).unwrap()).collect();
        (!text.is_empty()).then_some(text)
    }

    /// The report's total of admits (over every total line: one for each oracle's report), and
    /// of those labelled `interrupted`.
    fn report_admits(report: &str) -> (usize, usize) {
        let total: usize = report
            .lines()
            .filter(|l| l.contains(" oracles, "))
            .map(|total_line| {
                total_line
                    .split(", ")
                    .find_map(|part| part.strip_suffix(" admits"))
                    .expect("an admit count")
                    .parse::<usize>()
                    .unwrap()
            })
            .sum();
        let interrupted = report
            .lines()
            .filter_map(|l| l.split("interrupted ").nth(1))
            .filter_map(|n| n.split([',', ')']).next()?.parse::<usize>().ok())
            .sum();
        (total, interrupted)
    }

    /// The sentences of the transcript; event records have none (story 56).
    fn sentences(transcript: &Path) -> Vec<String> {
        std::fs::read_to_string(transcript)
            .unwrap()
            .lines()
            .filter_map(|line| {
                let v: serde_json::Value = serde_json::from_str(line).unwrap();
                Some(v["sentence"].as_str()?.to_string())
            })
            .collect()
    }

    #[test]
    fn each_oracle_is_on_disk_as_soon_as_it_is_proved() {
        let Some((result, _out, captures)) =
            run_captured(TWO_ORACLES, "Proof", &walk(WriteGranularity::Oracle))
        else {
            return;
        };
        let oracles = &result.equivalences[0].oracles;
        assert_eq!(oracles.len(), 2);
        let second_started = captures
            .iter()
            .position(|c| c.event == "item 2")
            .expect("the second oracle started");
        // while the first oracle runs, nothing is written: no node writes at this granularity
        for c in &captures[..second_started] {
            assert_eq!(c.ec.matches(UNTOUCHED).count(), 2, "{}: {}", c.event, c.ec);
            assert!(c.report.is_none(), "{}", c.event);
        }
        // between the oracles: the first one's script is on disk, and its report with it
        let between = &captures[second_started];
        let written: Vec<&OracleTactics> = oracles
            .iter()
            .filter(|o| between.ec.contains(o.script.trim_end()))
            .collect();
        assert_eq!(written.len(), 1, "{}", between.ec);
        assert_eq!(between.ec.matches(UNTOUCHED).count(), 1, "{}", between.ec);
        let report = between
            .report
            .as_deref()
            .expect("a report next to the file");
        let other = oracles
            .iter()
            .find(|o| o.oracle != written[0].oracle)
            .unwrap();
        assert!(
            report.contains(&format!("  {}: lockstep", written[0].oracle)),
            "{report}"
        );
        assert!(!report.contains(&other.oracle), "{report}");
        assert_eq!(report_admits(report).0, labelled_admits(&between.ec).len());
        assert!(!between.ec.contains("interrupted"));
    }

    #[test]
    fn at_node_granularity_every_write_is_a_complete_sealed_proof_and_its_report() {
        let Some((result, out, captures)) =
            run_captured(TWO_ORACLES, "Proof", &walk(WriteGranularity::Node))
        else {
            return;
        };
        let file = &result.equivalences[0].proof_file;
        let mid_oracle: Vec<&Capture> = captures
            .iter()
            .filter(|c| c.event.starts_with("goal "))
            .collect();
        assert!(mid_oracle.len() >= 4, "{captures:?}");
        let mut sealed = Vec::new();
        for c in &mid_oracle {
            // the full bullet structure: both oracle bullets, then `qed.`
            let progress = crate::writers::easycrypt::overwrite::proof_progress(&c.ec);
            assert_eq!(progress.total, 2, "{}: {}", c.event, c.ec);
            assert!(c.ec.contains("\nqed."));
            // every admit is labelled, but an untouched oracle's
            let labelled = labelled_admits(&c.ec);
            assert_eq!(
                admit_sentences(&c.ec),
                labelled.len() + c.ec.matches(UNTOUCHED).count(),
                "{}: {}",
                c.event,
                c.ec
            );
            // the report next to it describes it, the interrupted admits too
            let report = c.report.as_deref().expect("a report with every write");
            let interrupted = labelled.iter().filter(|r| *r == "interrupted").count();
            assert_eq!(
                report_admits(report),
                (labelled.len(), interrupted),
                "{}: {report}\n{}",
                c.event,
                c.ec
            );
            if interrupted > 0 {
                sealed.push(c.ec.clone());
            }
        }
        assert!(!sealed.is_empty(), "some write sealed an oracle part way");
        // a sealed file compiles (the test compiles, never the run: ADR 0005)
        let binary = crate::easycrypt::session::locate_binary();
        for text in [sealed.first().unwrap(), sealed.last().unwrap()] {
            std::fs::write(out.path().join(file), text).unwrap();
            if let Err(e) = compile(&binary, out.path(), file) {
                panic!("a sealed file does not compile: {e}\n{text}");
            }
        }
    }

    #[test]
    fn at_tactic_granularity_every_accepted_sentence_is_written() {
        let Some((result, out, captures)) =
            run_captured(TWO_ORACLES, "Proof", &walk(WriteGranularity::Tactic))
        else {
            return;
        };
        let by_node = run(TWO_ORACLES, "Proof", &walk(WriteGranularity::Node))
            .unwrap()
            .0;
        let eq = &result.equivalences[0];
        // the walk's sentences carry a note; the ones EasyCrypt accepted are the ones written
        let transcript = std::fs::read_to_string(eq.transcript()).unwrap();
        let mut walked = 0;
        let mut rejected = 0;
        for line in transcript.lines() {
            let v: serde_json::Value = serde_json::from_str(line).unwrap();
            if v["ctx"]["oracle"].is_null() || v.get("event").is_some() {
                continue;
            }
            if v["response"]["status"] == "ok" {
                walked += 1;
            } else {
                rejected += 1;
            }
        }
        assert!(walked >= 10, "{transcript}");
        // one write per accepted sentence, one at the end of each oracle, one at the end
        assert_eq!(eq.writes, walked + eq.oracles.len() + 1, "{rejected} rejected");
        assert!(eq.writes > by_node.equivalences[0].writes);
        // the final file is whole, and compiles
        let final_file = proof_file(&result, out.path());
        assert!(!final_file.contains("interrupted"), "{final_file}");
        // every write in between was a whole proof too (the bullets and `qed.`)
        for c in &captures {
            assert!(c.ec.contains("\nqed."), "{}: {}", c.event, c.ec);
        }
        let binary = crate::easycrypt::session::locate_binary();
        compile(&binary, out.path(), &eq.proof_file).expect("the file compiles");
    }

    // ------------------------------------------------------------------
    // Story 34: Ctrl-C stops a tactics run and leaves a partial proof
    // ------------------------------------------------------------------

    fn stoppable(write_granularity: WriteGranularity) -> TacticsOptions {
        TacticsOptions {
            stop: Some(Arc::new(AtomicBool::new(false))),
            ..walk(write_granularity)
        }
    }

    #[test]
    fn a_stop_in_the_walk_seals_the_oracle_where_it_stands_and_the_file_compiles() {
        // the first joint node of the first oracle is done: the walk stops at its next sentence
        let Some((result, out, captures)) = run_stopped_at(
            TWO_ORACLES,
            "Proof",
            &stoppable(WriteGranularity::Oracle),
            Some("goal N"),
        ) else {
            return;
        };
        assert!(
            captures.iter().any(|c| c.event.starts_with("goal N")),
            "{captures:?}"
        );
        let eq = &result.equivalences[0];
        let Some(Interrupted::Sealed {
            oracle,
            admits,
            node,
        }) = &eq.interrupted
        else {
            panic!("sealed: {:?}\n{}", eq.interrupted, eq.render());
        };
        assert_eq!(result.interrupted(), eq.interrupted.as_ref());
        // the oracle in flight is the only one in the report; the other is not reached
        assert_eq!(eq.oracles.len(), 1);
        assert_eq!(&eq.oracles[0].oracle, oracle);
        let text = proof_file(&result, out.path());
        assert_eq!(text.matches(UNTOUCHED).count(), 1, "{text}");
        // its open goals are admitted `interrupted`, at the node the walk was in
        let labelled = labelled_admits(&text);
        let interrupted = labelled.iter().filter(|r| *r == "interrupted").count();
        assert!(*admits > 0 && interrupted == *admits, "{text}");
        assert!(
            text.contains(&format!("admit. (* domino: {node} open-goal; reason: interrupted")),
            "{text}"
        );
        // the report names what was sealed, and its admit counts are the file's
        let report = std::fs::read_to_string(out.path().join(&eq.report_file)).unwrap();
        assert_eq!(report, eq.render());
        assert!(
            report.contains(&format!(
                "interrupted: sealed {oracle} with {admits} admits at node {node}"
            )),
            "{report}"
        );
        assert_eq!(report_admits(&report), (labelled.len(), interrupted));
        // the page says interrupted, not failed
        let page = std::fs::read_to_string(page_path(&result)).unwrap();
        assert!(page.contains("tactics (interrupted)"));
        assert!(!page.contains("http-equiv"));
        // and the partial proof compiles
        if let Err(e) = compile(
            &crate::easycrypt::session::locate_binary(),
            out.path(),
            &eq.proof_file,
        ) {
            panic!("the partial proof does not compile: {e}\n{text}");
        }
    }

    #[test]
    fn a_stop_during_lockstep_execution_keeps_the_earlier_oracles_work() {
        // the second oracle has started: its lockstep execution sees the stop
        let Some((result, out, _)) = run_stopped_at(
            TWO_ORACLES,
            "Proof",
            &stoppable(WriteGranularity::Oracle),
            Some("item 2"),
        ) else {
            return;
        };
        let eq = &result.equivalences[0];
        let [first] = eq.oracles.as_slice() else {
            panic!("one oracle finished: {}", eq.render());
        };
        let Some(Interrupted::Lockstep { oracle }) = &eq.interrupted else {
            panic!("stopped in lockstep execution: {:?}", eq.interrupted);
        };
        assert_ne!(oracle, &first.oracle);
        // the finished oracle keeps its script, the stopped one its unlabelled admit
        let text = proof_file(&result, out.path());
        assert!(text.contains(first.script.trim_end()), "{text}");
        assert_eq!(text.matches(UNTOUCHED).count(), 1, "{text}");
        assert!(!text.contains("interrupted"), "{text}");
        let report = std::fs::read_to_string(out.path().join(&eq.report_file)).unwrap();
        assert!(
            report.contains(&format!(
                "interrupted: during lockstep execution of {oracle}, nothing sealed"
            )),
            "{report}"
        );
        // nothing was sent for the stopped oracle: one `proc; inline.` after the `call`
        let sent = sentences(&result.equivalences[0].transcript());
        let call = sent.iter().position(|s| s.starts_with("call (")).unwrap();
        assert_eq!(
            sent[call..].iter().filter(|s| *s == "proc; inline.").count(),
            1,
            "{sent:?}"
        );
    }

    // ------------------------------------------------------------------
    // Story 37: a session record lets a proof job resume an equivalence
    // ------------------------------------------------------------------

    /// Another proof job on the export in `out`, as `prove` starts one.
    fn run_again(out: &Path, options: &TacticsOptions) -> TheoremTactics {
        run_again_on(TWO_ORACLES, out, options)
    }

    /// Another proof job on the export of `project` (theorem `Proof`) in `out`.
    fn run_again_on(project: &str, out: &Path, options: &TacticsOptions) -> TheoremTactics {
        run_again_stopped(project, out, options, None)
    }

    /// [`run_again_on`], asked to stop where `stop` says.
    fn run_again_stopped(
        project: &str,
        out: &Path,
        options: &TacticsOptions,
        stop: Option<StopIn>,
    ) -> TheoremTactics {
        let mut watching = Some(Watching { stop });
        let dir = PathBuf::from(project);
        let files = DirectoryFiles::load(&dir).unwrap();
        let project = DirectoryProject::load(dir, &files).unwrap();
        let theorem = project.get_theorem("Proof").unwrap();
        let exported = export_theorem(theorem, &project).unwrap();
        run_tactics_observed(
            theorem,
            &project,
            &exported,
            out,
            &backend(),
            options,
            &mut || Box::new(watching.take().unwrap_or(Watching { stop: None })),
        )
        .unwrap()
    }

    /// Records the walk's nodes and sentences, and lockstep execution, in [`WALK`], and sets the
    /// stop flag where `stop` says.
    struct Watching {
        stop: Option<StopIn>,
    }

    /// The `nth` sentence sent after node `node` is entered sets `flag`, as a Ctrl-C would: that
    /// sentence runs to its end, and the walk stops before the next one.
    struct StopIn {
        node: &'static str,
        nth: usize,
        flag: Arc<AtomicBool>,
        sent: Option<usize>,
    }

    impl ExportObserver for Watching {
        fn on_event(&mut self, event: &crate::writers::easycrypt::progress::ExportEvent<'_>) {
            use crate::writers::easycrypt::progress::ExportEvent;
            let line = match event {
                ExportEvent::NodeStarted { node, total, .. } => format!("node {node}/{total}"),
                ExportEvent::SentenceSent { sentence } => format!("sentence {sentence}"),
                ExportEvent::LockstepStarted { oracle } => format!("lockstep {oracle}"),
                _ => return,
            };
            if let Some(stop) = &mut self.stop {
                if line.starts_with(&format!("node {}/", stop.node)) {
                    stop.sent = Some(0);
                } else if let (true, Some(sent)) = (line.starts_with("sentence "), &mut stop.sent) {
                    *sent += 1;
                    if *sent == stop.nth {
                        stop.flag.store(true, Ordering::Relaxed);
                    }
                }
            }
            WALK.with(|w| w.borrow_mut().push(line));
        }
    }

    /// The session folder of the first equivalence: [`read_record`] joins its oracles' records.
    fn record_path(result: &TheoremTactics, out: &Path) -> PathBuf {
        session_dir(out, &result.equivalences[0].proof_file)
    }

    /// The record at `path`; for a session folder, its oracles' records joined in the glue's
    /// order.
    fn read_record(path: &Path) -> SessionRecord {
        if !path.is_dir() {
            return SessionRecord::read(path).unwrap().expect("a record");
        }
        let stem = path.file_name().unwrap().to_string_lossy().into_owned();
        let out = path.parent().unwrap().parent().unwrap();
        let mut records = Vec::new();
        let mut names = Vec::new();
        for file in oracle_files(out, &format!("{stem}.ec")) {
            let oracle = file.file_stem().unwrap().to_string_lossy()[stem.len() + 1..].to_string();
            records.extend(SessionRecord::read(&path.join(format!("{oracle}.record.json"))).unwrap());
            names.push(oracle);
        }
        SessionRecord::join(&records, &names).expect("a record")
    }

    /// The first oracle proved, the second stopped in lockstep execution, as by Ctrl-C.
    fn stopped_after_the_first_oracle() -> Option<(TheoremTactics, tempfile::TempDir)> {
        let (result, out, _) = run_stopped_at(
            TWO_ORACLES,
            "Proof",
            &stoppable(WriteGranularity::Oracle),
            Some("item 2"),
        )?;
        Some((result, out))
    }

    #[test]
    fn a_resumed_job_does_not_walk_the_oracles_the_record_holds() {
        let Some((first_run, out)) = stopped_after_the_first_oracle() else {
            return;
        };
        let stopped = &first_run.equivalences[0];
        let first = stopped.oracles[0].clone();
        let path = record_path(&first_run, out.path());
        let record = read_record(&path);
        assert!(!record.complete);
        assert_eq!(record.done(), 1);
        let entry = record.oracle(&first.oracle).unwrap();
        assert_eq!(entry.script.as_deref(), Some(first.script.as_str()));
        // a done oracle keeps its script, not its closed nodes
        assert!(entry.closed.is_empty());
        assert_eq!(entry.lockstep.unwrap().joint_paths, first.joint_paths);
        let before = proof_file(&first_run, out.path());

        let result = run_again(out.path(), &walk(WriteGranularity::Oracle));
        let eq = &result.equivalences[0];
        assert!(eq.interrupted.is_none());
        let [a, b] = eq.oracles.as_slice() else {
            panic!("two oracles: {}", eq.render());
        };
        let (resumed, proved) = if a.oracle == first.oracle { (a, b) } else { (b, a) };
        assert!(resumed.resumed && !proved.resumed, "{}", eq.render());
        assert_eq!(resumed.script, first.script);
        assert_eq!(resumed.admits_by_reason().len(), first.admits_by_reason().len());
        // not walked: one `proc; inline.` after the call (the other oracle's), the resumed
        // oracle's goal only got `admit.`
        let sent = sentences(&eq.transcript());
        let call = sent.iter().position(|s| s.starts_with("call (")).unwrap();
        assert_eq!(
            sent[call..].iter().filter(|s| *s == "proc; inline.").count(),
            1,
            "{sent:?}"
        );
        // the file holds the first script byte for byte, and is complete now
        let text = proof_file(&result, out.path());
        assert!(before.contains(first.script.trim_end()));
        assert!(text.contains(first.script.trim_end()), "{text}");
        assert!(text.contains(proved.script.trim_end()), "{text}");
        assert_eq!(text.matches(UNTOUCHED).count(), 0, "{text}");
        // the report and the page say which oracle is not this run's
        let report = std::fs::read_to_string(out.path().join(&eq.report_file)).unwrap();
        assert!(
            report.contains(&format!("  {}: resumed from session record", first.oracle)),
            "{report}"
        );
        assert!(!report.contains(&format!("  {}: resumed", proved.oracle)), "{report}");
        let page = std::fs::read_to_string(page_path(&result)).unwrap();
        assert!(page.contains("resumed from session record"));
        // the record is complete and still holds both scripts
        let record = read_record(&path);
        assert!(record.complete);
        assert!(record.oracles.iter().all(OracleRecord::is_resumable));
        assert_eq!(
            record.oracle(&first.oracle).unwrap().script.as_deref(),
            Some(first.script.as_str())
        );
        if let Err(e) = compile(
            &crate::easycrypt::session::locate_binary(),
            out.path(),
            &eq.proof_file,
        ) {
            panic!("the resumed proof does not compile: {e}\n{text}");
        }

        // complete: skipped, and nothing changes
        let again = run_again(out.path(), &walk(WriteGranularity::Oracle));
        assert!(again.equivalences.is_empty());
        assert_eq!(proof_file(&result, out.path()), text);
        // --oracle O --force: only O is proved again, the other comes from the record
        let only = TacticsOptions {
            oracle: Some(proved.oracle.clone()),
            force: true,
            ..walk(WriteGranularity::Oracle)
        };
        let again = run_again(out.path(), &only);
        let eq = &again.equivalences[0];
        assert_eq!(eq.oracles.len(), 2, "{}", eq.render());
        for o in &eq.oracles {
            assert_eq!(o.resumed, o.oracle == first.oracle, "{}", eq.render());
        }
        assert_eq!(proof_file(&again, out.path()), text);
        assert!(read_record(&path).complete);
        // --force: from scratch, nothing resumed
        let forced = TacticsOptions {
            force: true,
            ..walk(WriteGranularity::Oracle)
        };
        let again = run_again(out.path(), &forced);
        assert!(again.equivalences[0].oracles.iter().all(|o| !o.resumed));
        assert_eq!(proof_file(&again, out.path()), text);
    }

    #[test]
    fn a_file_written_without_its_record_is_proved_again_from_the_skeleton() {
        // a kill between the file's write and the record's leaves the file ahead of the record
        let Some((first_run, out)) = stopped_after_the_first_oracle() else {
            return;
        };
        std::fs::remove_file(record_path(&first_run, out.path())).unwrap();
        assert_eq!(proof_file(&first_run, out.path()).matches(UNTOUCHED).count(), 1);
        let result = run_again(out.path(), &walk(WriteGranularity::Oracle));
        let eq = &result.equivalences[0];
        assert!(eq.oracles.iter().all(|o| !o.resumed));
        let text = proof_file(&result, out.path());
        assert_eq!(text.matches(UNTOUCHED).count(), 0, "{text}");
        assert!(read_record(&record_path(&result, out.path())).complete);
        if let Err(e) = compile(
            &crate::easycrypt::session::locate_binary(),
            out.path(),
            &eq.proof_file,
        ) {
            panic!("the proof does not compile: {e}\n{text}");
        }
    }

    #[test]
    fn a_version_1_record_re_proves_its_done_oracles() {
        let Some((first_run, out)) = stopped_after_the_first_oracle() else {
            return;
        };
        let path = record_path(&first_run, out.path());
        let record = read_record(&path);
        let statuses: Vec<String> = record
            .oracles
            .iter()
            .map(|o| format!(r#"{{"name": "{}", "status": "{:?}"}}"#, o.name, o.status).to_lowercase())
            .collect();
        std::fs::write(
            &path,
            format!(
                r#"{{"version": 1, "theorem": "Proof", "left": "{}", "right": "{}", "complete": false, "oracles": [{}]}}"#,
                record.left,
                record.right,
                statuses.join(",")
            ),
        )
        .unwrap();
        let result = run_again(out.path(), &walk(WriteGranularity::Oracle));
        let eq = &result.equivalences[0];
        assert_eq!(eq.oracles.len(), 2);
        assert!(eq.oracles.iter().all(|o| !o.resumed), "{}", eq.render());
        let record = read_record(&path);
        assert_eq!(record.version, SessionRecord::VERSION);
        assert!(record.complete);
    }

    // ------------------------------------------------------------------
    // A tactics run survives an unanswered interrupt
    // ------------------------------------------------------------------

    const FOUR_ORACLES: &str = "testdata/easycrypt/unanswered-interrupt/four-oracles";

    /// The real EasyCrypt behind a filter that leaves the first sentence at joint node N0 (the
    /// 4th after `proc; inline.`) of the oracles walked `hang`th unanswered, whatever interrupt
    /// comes: it is not passed on, and no answer is written. Oracles are counted over the whole
    /// run, respawns included (in `dir`). Every other sentence and interrupt is passed on.
    fn unanswering_easycrypt(dir: &Path, hang: &[usize]) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let real = crate::easycrypt::session::locate_binary();
        let walked = dir.join("walked");
        std::fs::write(&walked, "0").unwrap();
        let hang: Vec<String> = hang.iter().map(usize::to_string).collect();
        let script = dir.join("unanswering-easycrypt");
        std::fs::write(
            &script,
            format!(
                r#"#!/bin/sh
fifo="$(mktemp -u)"
mkfifo "$fifo"
'{real}' "$@" < "$fifo" &
ec=$!
exec 3> "$fifo"
rm -f "$fifo"
trap 'kill -INT $ec 2>/dev/null' INT
opened=0
after=-1
while :; do
  if IFS= read -r line; then :; else
    [ $? -gt 128 ] && continue
    break
  fi
  [ $after -ge 0 ] && after=$((after+1))
  s=$(printf '%s\n' "$line" | sed -e 's/^."sentence":"\(.*\)","want":"[a-z]*".$/\1/' -e 's/\\"/"/g' -e 's/\\\\/\\/g')
  case "$s" in "proof.") opened=1;; esac
  if [ $opened = 1 ] && [ "$s" = "proc; inline." ]; then
    n=$(($(cat '{walked}')+1))
    echo $n > '{walked}'
    case " {hang} " in *" $n "*) after=0;; *) after=-1;; esac
  fi
  if [ $after -eq 6 ]; then
    trap '' INT
    while :; do sleep 1; done
  fi
  printf '%s\n' "$line" >&3
done
exec 3>&-
wait $ec
"#,
                real = real.display(),
                walked = walked.display(),
                hang = hang.join(" ")
            ),
        )
        .unwrap();
        std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).unwrap();
        script
    }

    /// [`run_stopped_at`] on [`FOUR_ORACLES`] with [`unanswering_easycrypt`]`(hang)`. A sentence
    /// times out after 10 s: the project's take well under one, but the opening `require import`
    /// can take several under a loaded full suite. An interrupt goes unanswered after six signals
    /// over 1.5 s.
    fn run_unanswered(
        hang: &[usize],
        stop_at: Option<&str>,
    ) -> Option<(TheoremTactics, tempfile::TempDir, Vec<Capture>)> {
        if !json_binary_configured() {
            eprintln!("DOMINO_EASYCRYPT not set, skipping");
            return None;
        }
        let fake = tempfile::tempdir().unwrap();
        TEST_EASYCRYPT.with(|t| {
            *t.borrow_mut() = Some(FakeEasyCrypt {
                binary: unanswering_easycrypt(fake.path(), hang),
                grace: Duration::from_millis(1_500),
                resend: Duration::from_millis(250),
            })
        });
        let options = TacticsOptions {
            ec_timeout: Duration::from_secs(10),
            stop: Some(Arc::new(AtomicBool::new(false))),
            ..TacticsOptions::default()
        };
        let result = run_stopped_at(FOUR_ORACLES, "Proof", &options, stop_at);
        TEST_EASYCRYPT.with(|t| t.borrow_mut().take());
        result
    }

    // ------------------------------------------------------------------
    // Story 68: oracle lemmas, proved in parallel
    // ------------------------------------------------------------------

    /// `project` exported to a fresh directory, and the project to prove it with.
    fn exported_to(project: &str) -> (tempfile::TempDir, DirectoryFilesAndProject) {
        let dir = PathBuf::from(project);
        let files = Box::leak(Box::new(DirectoryFiles::load(&dir).unwrap()));
        let project = DirectoryProject::load(dir, files).unwrap();
        let out = tempfile::tempdir().unwrap();
        let exported = export_theorem(project.get_theorem("Proof").unwrap(), &project).unwrap();
        write_files(out.path(), &exported.files).unwrap();
        (out, DirectoryFilesAndProject { project, exported })
    }

    struct DirectoryFilesAndProject {
        project: DirectoryProject<'static>,
        exported: crate::writers::easycrypt::export::ExportedTheorem,
    }

    impl DirectoryFilesAndProject {
        fn prove(&self, out: &Path, options: &TacticsOptions) -> TheoremTactics {
            let theorem = self.project.get_theorem("Proof").unwrap();
            run_tactics(theorem, &self.project, &self.exported, out, &backend(), options).unwrap()
        }
    }

    /// Every file under `dir`, relative, sorted.
    fn files_under(dir: &Path) -> Vec<String> {
        fn walk(root: &Path, dir: &Path, out: &mut Vec<String>) {
            for entry in std::fs::read_dir(dir).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    walk(root, &path, out);
                } else {
                    out.push(path.strip_prefix(root).unwrap().display().to_string());
                }
            }
        }
        let mut out = Vec::new();
        walk(dir, dir, &mut out);
        out.sort();
        out
    }

    #[test]
    fn two_proof_jobs_on_different_oracles_of_one_equivalence_both_finish_with_their_own_files() {
        if !json_binary_configured() {
            eprintln!("DOMINO_EASYCRYPT not set, skipping");
            return;
        }
        let (out, p) = exported_to(FOUR_ORACLES);
        let eq = p.exported.equivalences[0].clone();
        let stem = eq.proof_file.trim_end_matches(".ec").to_string();
        let [(a, a_file), (b, b_file), ..] = &eq.oracle_files[..] else {
            panic!("four oracles: {:?}", eq.oracle_files);
        };
        let before = files_under(out.path());
        let glue = std::fs::read_to_string(out.path().join(&eq.proof_file)).unwrap();
        let (ra, rb) = std::thread::scope(|s| {
            let ja = s.spawn(|| p.prove(out.path(), &oracle_option(a, false)));
            let jb = s.spawn(|| p.prove(out.path(), &oracle_option(b, false)));
            (ja.join().unwrap(), jb.join().unwrap())
        });
        for (r, oracle) in [(&ra, a), (&rb, b)] {
            let names: Vec<&str> = r.oracles().map(|o| o.oracle.as_str()).collect();
            assert_eq!(names, [oracle.as_str()], "{}", r.render());
            assert_eq!(
                r.equivalences[0].report_file,
                format!("progress/{stem}/{oracle}/report.txt")
            );
        }
        // the glue is translation's, and no job touched it
        assert_eq!(std::fs::read_to_string(out.path().join(&eq.proof_file)).unwrap(), glue);
        // what is new: each oracle's record, tree and progress folder, and nothing else of the
        // equivalence (no report, no page, no lock left)
        let new: Vec<String> = files_under(out.path())
            .into_iter()
            .filter(|f| !before.contains(f) && !f.starts_with("!debug!"))
            .collect();
        for f in &new {
            let own = [a, b].iter().any(|o| {
                f == &format!("session/{stem}/{o}.record.json")
                    || f == &format!("session/{stem}/{o}.tree.json")
                    || f.starts_with(&format!("progress/{stem}/{o}/"))
            });
            assert!(own, "{f} is no oracle's own file: {new:?}");
        }
        for o in [a, b] {
            assert!(new.contains(&format!("session/{stem}/{o}.record.json")), "{new:?}");
        }
        // the oracle files are proved, and the whole compiles
        for f in [a_file, b_file] {
            let text = std::fs::read_to_string(out.path().join(f)).unwrap();
            assert!(!text.contains(UNTOUCHED), "{text}");
        }
        compile(&crate::easycrypt::session::locate_binary(), out.path(), &eq.proof_file).unwrap();
    }

    /// An EasyCrypt that logs `start` and `end` lines to `log` around the real one.
    fn logging_easycrypt(dir: &Path, log: &Path) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let real = crate::easycrypt::session::locate_binary();
        let script = dir.join("logging-easycrypt");
        std::fs::write(
            &script,
            format!(
                // a session kills this script when it is dropped: a watcher logs the end of
                // the real EasyCrypt, which exits when its input closes
                "#!/bin/sh\necho start >> '{log}'\n'{real}' \"$@\" <&0 &\nec=$!\n\
                 ( while kill -0 $ec 2>/dev/null; do sleep 0.05; done; echo end >> '{log}' ) \
                 </dev/null >/dev/null 2>&1 &\nwait $ec\n",
                log = log.display(),
                real = real.display()
            ),
        )
        .unwrap();
        std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).unwrap();
        script
    }

    #[test]
    fn three_jobs_prove_three_oracles_at_once_and_the_report_keeps_oracle_order() {
        if !json_binary_configured() {
            eprintln!("DOMINO_EASYCRYPT not set, skipping");
            return;
        }
        let fake = tempfile::tempdir().unwrap();
        let log = fake.path().join("log");
        let (out, p) = exported_to(FOUR_ORACLES);
        let options = TacticsOptions {
            jobs: 3,
            ..TacticsOptions::default()
        };
        TEST_EASYCRYPT.with(|t| {
            *t.borrow_mut() = Some(FakeEasyCrypt {
                binary: logging_easycrypt(fake.path(), &log),
                grace: Duration::from_millis(1_500),
                resend: Duration::from_millis(250),
            })
        });
        let result = p.prove(out.path(), &options);
        TEST_EASYCRYPT.with(|t| t.borrow_mut().take());
        // the watchers log each end within a moment
        let began = Instant::now();
        while began.elapsed() < Duration::from_secs(10) {
            let text = std::fs::read_to_string(&log).unwrap();
            if text.matches("start").count() == text.matches("end").count() {
                break;
            }
            std::thread::sleep(Duration::from_millis(100));
        }
        let (mut running, mut most, mut started) = (0, 0, 0);
        for line in std::fs::read_to_string(&log).unwrap().lines() {
            if line == "start" {
                running += 1;
                started += 1;
            } else {
                running -= 1;
            }
            most = most.max(running);
        }
        assert_eq!(started, 4, "one EasyCrypt for each oracle");
        assert_eq!(most, 3, "three at once");
        let eq = &result.equivalences[0];
        let names: Vec<&str> = eq.oracles.iter().map(|o| o.oracle.as_str()).collect();
        assert_eq!(names, ["First", "Second", "Third", "Fourth"]);
        let report = std::fs::read_to_string(out.path().join(&eq.report_file)).unwrap();
        let at = |o: &str| report.find(&format!("  {o}: lockstep")).expect(o);
        assert!(at("First") < at("Second") && at("Second") < at("Third") && at("Third") < at("Fourth"));
        // the page of the equivalence: one row for each oracle, none running any more
        let page = equivalence_page(&result, out.path());
        for o in names {
            assert!(page.contains(&format!("<a href=\"{o}/index.html\">{o}</a>")), "{page}");
        }
        assert!(!page.contains("running") && !page.contains("http-equiv"), "{page}");
        compile(&crate::easycrypt::session::locate_binary(), out.path(), &eq.proof_file).unwrap();
    }

    fn interrupted_admits(o: &OracleTactics) -> usize {
        o.stats
            .admits
            .iter()
            .filter(|a| a.reason == AdmitReason::Interrupted)
            .count()
    }

    fn statuses(record: &SessionRecord) -> Vec<(String, OracleStatus)> {
        record
            .oracles
            .iter()
            .map(|o| (o.name.clone(), o.status))
            .collect()
    }

    fn status_list(list: &[(&str, OracleStatus)]) -> Vec<(String, OracleStatus)> {
        list.iter().map(|(n, s)| (n.to_string(), *s)).collect()
    }

    /// The transcript's sentence records as `(file tag, sentence)`; event records have no
    /// sentence (story 56).
    fn tagged_sentences(transcript: &Path) -> Vec<(String, String)> {
        std::fs::read_to_string(transcript)
            .unwrap()
            .lines()
            .filter_map(|line| {
                let v: serde_json::Value = serde_json::from_str(line).unwrap();
                Some((
                    v["file"].as_str().unwrap().to_string(),
                    v["sentence"].as_str()?.to_string(),
                ))
            })
            .collect()
    }

    /// The page of the equivalence (story 68): one row for each oracle.
    fn equivalence_page(result: &TheoremTactics, out: &Path) -> String {
        let stem = result.equivalences[0].proof_file.trim_end_matches(".ec").to_string();
        std::fs::read_to_string(out.join(format!("progress/{stem}/index.html"))).unwrap()
    }

    #[test]
    fn an_unanswered_interrupt_seals_the_oracle_and_the_next_oracle_has_a_fresh_easycrypt() {
        // the second oracle's first sentence at N0 goes unanswered
        let Some((result, out, _)) = run_unanswered(&[2], None) else {
            return;
        };
        let eq = &result.equivalences[0];
        assert_eq!(eq.interrupted, None, "the job finishes: {}", eq.render());
        assert_eq!(eq.ended_early, None);
        let names: Vec<&str> = eq.oracles.iter().map(|o| o.oracle.as_str()).collect();
        assert_eq!(names, ["First", "Second", "Third", "Fourth"]);
        assert_eq!(eq.oracles[0].stats.admits.len(), 0, "{}", eq.render());
        assert!(interrupted_admits(&eq.oracles[1]) > 0, "{}", eq.render());
        assert_eq!(eq.oracles[1].stats.admits.len(), interrupted_admits(&eq.oracles[1]));
        for o in &eq.oracles[2..] {
            assert_eq!(o.stats.admits.len(), 0, "proved after it: {}", eq.render());
            assert!(o.stats.closed > 0);
        }
        let [u] = eq.unanswered.as_slice() else {
            panic!("one unanswered interrupt: {}", eq.render());
        };
        assert_eq!((u.oracle.as_str(), u.signals), ("Second", 6));
        assert!(!u.ended_job);
        let report = std::fs::read_to_string(out.path().join(&eq.report_file)).unwrap();
        assert!(
            report.contains(&format!(
                "    EasyCrypt left an interrupt unanswered at {} (6 signals over 1 s); oracle \
                 sealed, EasyCrypt given up, the next oracle gets a fresh one",
                u.node
            )),
            "{report}"
        );
        assert!(!report.contains("interrupted:"), "not a Ctrl-C: {report}");
        let second_page = eq.oracles[1]
            .transcript
            .as_ref()
            .unwrap()
            .with_file_name("index.html");
        let page = std::fs::read_to_string(second_page).unwrap();
        assert!(page.contains("EasyCrypt left an interrupt unanswered at "), "{page}");
        // the record: the sealed oracle is not done, so the next job resumes it
        let record = read_record(&record_path(&result, out.path()));
        assert!(!record.complete);
        use OracleStatus::{Done, Interrupted as Sealed};
        assert_eq!(
            statuses(&record),
            status_list(&[("First", Done), ("Second", Sealed), ("Third", Done), ("Fourth", Done)])
        );
        // each oracle has its own EasyCrypt: its transcript opens its own lemma
        for o in &eq.oracles {
            let sent = tagged_sentences(o.transcript.as_ref().unwrap());
            assert!(sent.iter().all(|(tag, _)| tag.ends_with(&format!("_{}.ec", o.oracle))));
        }
        // the partial proof compiles (the test compiles, never the run: ADR 0005)
        let text = proof_file(&result, out.path());
        assert_eq!(text.matches(UNTOUCHED).count(), 0, "{text}");
        if let Err(e) = compile(
            &crate::easycrypt::session::locate_binary(),
            out.path(),
            &eq.proof_file,
        ) {
            panic!("the proof does not compile: {e}\n{text}");
        }
    }

    #[test]
    fn the_third_unanswered_interrupt_ends_the_job_and_leaves_the_rest_pending() {
        // every oracle walked is left unanswered at N0
        let Some((result, out, _)) = run_unanswered(&[1, 2, 3, 4], None) else {
            return;
        };
        let eq = &result.equivalences[0];
        let names: Vec<&str> = eq.oracles.iter().map(|o| o.oracle.as_str()).collect();
        assert_eq!(names, ["First", "Second", "Third"], "{}", eq.render());
        assert!(eq.oracles.iter().all(|o| interrupted_admits(o) > 0));
        let ended: Vec<bool> = eq.unanswered.iter().map(|u| u.ended_job).collect();
        assert_eq!(ended, [false, false, true]);
        let Some(Interrupted::Sealed { oracle, node, .. }) = &eq.interrupted else {
            panic!("sealed: {:?}", eq.interrupted);
        };
        assert_eq!((oracle.as_str(), node.as_str()), ("Third", "N0"));
        let why = eq.ended_early.as_deref().expect("why the job ended");
        assert!(why.contains("3 interrupts unanswered"), "{why}");
        // not a Ctrl-C: the run is not interrupted
        assert_eq!(result.interrupted(), None);
        assert!(result.ended_early());
        let report = std::fs::read_to_string(out.path().join(&eq.report_file)).unwrap();
        assert!(
            report.contains("\nended early: sealed Third with "),
            "{report}"
        );
        assert!(report.contains(why), "{report}");
        let page = equivalence_page(&result, out.path());
        assert!(page.contains("ended early: "), "{page}");
        assert!(!page.contains("Ctrl-C"));
        let record = read_record(&record_path(&result, out.path()));
        use OracleStatus::{Interrupted as Sealed, Pending};
        assert_eq!(
            statuses(&record),
            status_list(&[
                ("First", Sealed),
                ("Second", Sealed),
                ("Third", Sealed),
                ("Fourth", Pending)
            ])
        );
        let text = proof_file(&result, out.path());
        assert_eq!(text.matches(UNTOUCHED).count(), 1, "{text}");
    }

    #[test]
    fn a_ctrl_c_after_an_unanswered_interrupt_stops_the_job_as_a_ctrl_c() {
        // the first goal left is the walk unwinding from the unanswered sentence at N0 of the
        // first oracle: the stop comes after the seal, before the next oracle starts
        let Some((result, out, _)) = run_unanswered(&[1], Some("goal N0")) else {
            return;
        };
        let eq = &result.equivalences[0];
        assert_eq!(eq.interrupted, Some(Interrupted::NoOracleInFlight), "{}", eq.render());
        assert_eq!(eq.ended_early, None);
        assert_eq!(result.interrupted(), Some(&Interrupted::NoOracleInFlight));
        let [first] = eq.oracles.as_slice() else {
            panic!("one oracle sealed: {}", eq.render());
        };
        assert!(interrupted_admits(first) > 0);
        // nothing of a fresh EasyCrypt was sent
        let sent = tagged_sentences(&eq.transcript());
        assert!(sent.iter().all(|(tag, _)| !tag.contains("respawn")), "{sent:?}");
        let record = read_record(&record_path(&result, out.path()));
        use OracleStatus::{Interrupted as Sealed, Pending};
        assert_eq!(
            statuses(&record),
            status_list(&[
                ("First", Sealed),
                ("Second", Pending),
                ("Third", Pending),
                ("Fourth", Pending)
            ])
        );
        let page = equivalence_page(&result, out.path());
        assert!(page.contains("interrupted: no oracle was in flight"), "{page}");
    }

    // ------------------------------------------------------------------
    // Resume an oracle from its saved joint tree (ADR 0008)
    // ------------------------------------------------------------------

    /// One oracle whose joint tree branches: `N0` (`if`) with `N1` → `N2` (a sampling, then a
    /// leaf) under `then` and `N3` → `N4` under `else`.
    const TWO_BRANCHES: &str = "testdata/easycrypt/resume/two-branches";

    /// The oracle of [`TWO_BRANCHES`] stopped once its `then` branch has closed, at `tactic`
    /// granularity, quick close off: in flight at `N3`, below `N0`, with `N1` closed.
    fn stopped_mid_oracle() -> Option<(TheoremTactics, tempfile::TempDir)> {
        let (result, out, _) = run_stopped_at(
            TWO_BRANCHES,
            "Proof",
            &stoppable(WriteGranularity::Tactic),
            Some("goal N1"),
        )?;
        Some((result, out))
    }

    /// A copy of the export directory `from`, so two jobs can resume the same record.
    fn copy_export(from: &Path) -> tempfile::TempDir {
        fn copy(from: &Path, to: &Path) {
            std::fs::create_dir_all(to).unwrap();
            for entry in std::fs::read_dir(from).unwrap() {
                let entry = entry.unwrap();
                let target = to.join(entry.file_name());
                if entry.file_type().unwrap().is_dir() {
                    copy(&entry.path(), &target);
                } else {
                    std::fs::copy(entry.path(), target).unwrap();
                }
            }
        }
        let to = tempfile::tempdir().unwrap();
        copy(from, to.path());
        to
    }

    fn walk_events() -> Vec<String> {
        WALK.with(|w| std::mem::take(&mut *w.borrow_mut()))
    }

    /// The lines of `text` that are `closed`'s script, as written there: found by their
    /// sentences and comments, whatever their indentation.
    fn block_of(text: &str, closed: &ClosedNode) -> Option<String> {
        let want: Vec<String> = closed
            .script
            .iter()
            .map(|l| match &l.comment {
                Some(c) => format!("{} {c}", l.sentence),
                None => l.sentence.clone(),
            })
            .collect();
        let lines: Vec<&str> = text.lines().collect();
        let bare = |l: &str| l.trim_start().trim_start_matches("+ ").to_string();
        (0..lines.len().saturating_sub(want.len() - 1))
            .find(|&i| (0..want.len()).all(|k| bare(lines[i + k]) == want[k]))
            .map(|i| lines[i..i + want.len()].join("\n"))
    }

    #[test]
    fn a_resumed_oracle_keeps_its_closed_nodes_under_trust_and_replay_alike() {
        let Some((first_run, out)) = stopped_mid_oracle() else {
            return;
        };
        let stopped = &first_run.equivalences[0];
        let Some(Interrupted::Sealed { oracle, node, .. }) = &stopped.interrupted else {
            panic!("sealed in the walk: {}", stopped.render());
        };
        let record = read_record(&record_path(&first_run, out.path()));
        let entry = record.oracle(oracle).unwrap();
        assert_eq!(entry.status, OracleStatus::Interrupted);
        assert_eq!(entry.in_flight(), Some(node.as_str()));
        assert!(!entry.closed.is_empty(), "{record:?}");
        let tree = saved_tree_path(out.path(), &stopped.proof_file, oracle);
        assert!(SavedTree::read(&tree).unwrap().is_some());
        let checkpoint = proof_file(&first_run, out.path());
        let blocks: Vec<String> = entry
            .closed
            .iter()
            .map(|c| block_of(&checkpoint, c).unwrap_or_else(|| panic!("{c:?} in\n{checkpoint}")))
            .collect();
        let closed: Vec<&str> = entry.closed.iter().map(|c| c.id.as_str()).collect();
        assert_eq!((node.as_str(), closed), ("N3", vec!["N1"]), "{record:?}");

        let replay_out = copy_export(out.path());
        walk_events();
        // trust, quick close on: the in-flight node's ancestors skip it
        let trust = run_again_on(
            TWO_BRANCHES,
            out.path(),
            &TacticsOptions {
                write_granularity: WriteGranularity::Tactic,
                ..TacticsOptions::default()
            },
        );
        let events = walk_events();
        let first_after = |node: &str| {
            let at = events.iter().position(|e| e.starts_with(&format!("node {node}/")))?;
            events[at..].iter().find(|e| e.starts_with("sentence ")).cloned()
        };
        // N0, above the in-flight node, starts with its structural step; N3 from the quick close
        assert_eq!(first_after("N0").as_deref(), Some("sentence sp 2 2."), "{events:#?}");
        assert_eq!(first_after("N1").as_deref(), Some("sentence kept"), "{events:#?}");
        assert_eq!(first_after("N3").as_deref(), Some("sentence auto => /#."), "{events:#?}");
        let eq = &trust.equivalences[0];
        assert!(eq.interrupted.is_none(), "{}", eq.render());
        let resumed = eq.oracles.iter().find(|o| &o.oracle == oracle).unwrap();
        assert_eq!(
            resumed.resumed_at,
            Some(ResumedAt {
                node: node.clone(),
                kept: entry.closed.len(),
                mode: ResumeMode::Trust,
                stale: vec![],
            }),
            "{}",
            eq.render()
        );
        // no lockstep execution for it; one `admit.` per closed node
        assert!(!events.contains(&format!("lockstep {oracle}")), "{events:?}");
        assert_eq!(
            events.iter().filter(|e| *e == "sentence kept").count(),
            entry.closed.len()
        );
        // the transcript says which node each `admit.` keeps
        let transcript = std::fs::read_to_string(trust.equivalences[0].transcript()).unwrap();
        let kept_in: Vec<String> = transcript
            .lines()
            .map(|l| serde_json::from_str::<serde_json::Value>(l).unwrap())
            .filter(|r| r["ctx"]["role"] == "resume")
            // the pragma that makes the next answer carry every goal (story 61) is no kept node
            // and event records (an interrupt under load) have no sentence
            .filter(|r| !r["sentence"].as_str().unwrap_or("pragma ").starts_with("pragma "))
            .map(|r| {
                let c = &r["ctx"];
                let sentence = r["sentence"].as_str().unwrap();
                format!("{} N{} {sentence}", c["oracle"].as_str().unwrap(), c["node"])
            })
            .collect();
        assert_eq!(kept_in.len(), entry.closed.len(), "{kept_in:?}");
        assert!(kept_in[0].starts_with("Branch N1 ") && kept_in[0].ends_with(" admit."), "{kept_in:?}");
        let text = proof_file(&trust, out.path());
        for block in &blocks {
            assert!(text.contains(block.as_str()), "{block}\nnot in\n{text}");
        }
        let report = std::fs::read_to_string(out.path().join(&eq.report_file)).unwrap();
        assert!(
            report.contains(&format!(
                "{oracle}: resumed at {node} ({} closed node",
                entry.closed.len()
            )),
            "{report}"
        );

        let page = std::fs::read_to_string(page_path(&trust)).unwrap();
        assert!(page.contains("resumed at N3 (trust)"), "{page}");
        assert!(page.contains("kept from session record"), "{page}");

        // replay: the closed nodes' sentences are sent again, and the file is the same
        let replayed = run_again_on(
            TWO_BRANCHES,
            replay_out.path(),
            &TacticsOptions {
                write_granularity: WriteGranularity::Tactic,
                resume: ResumeMode::Replay,
                ..TacticsOptions::default()
            },
        );
        let events = walk_events();
        assert!(!events.contains(&"sentence kept".to_string()), "{events:?}");
        // N1's recorded sentences, sent again right after it is entered
        let n1 = events.iter().position(|e| e == "node N1/5").unwrap();
        let recorded: Vec<String> = entry.closed[0]
            .script
            .iter()
            .map(|l| format!("sentence {}", l.sentence))
            .collect();
        assert_eq!(
            events[n1 + 1..n1 + 1 + recorded.len()],
            recorded[..],
            "{events:#?}"
        );
        assert_eq!(
            replayed.equivalences[0].oracles.iter().find(|o| &o.oracle == oracle).unwrap().resumed_at.as_ref().map(|r| r.kept),
            Some(entry.closed.len())
        );
        assert_eq!(proof_file(&replayed, replay_out.path()), text);
        if let Err(e) = compile(
            &crate::easycrypt::session::locate_binary(),
            out.path(),
            &eq.proof_file,
        ) {
            panic!("the resumed proof does not compile: {e}\n{text}");
        }
    }

    #[test]
    fn a_stop_while_a_closed_node_is_replayed_keeps_it_closed_and_seals_its_goal() {
        let Some((first_run, out)) = stopped_mid_oracle() else {
            return;
        };
        let file = first_run.equivalences[0].proof_file.clone();
        let record = session_record_path(out.path(), &file);
        // N1's script as two sentences, the first of which closes its goal: a stop between them
        // finds one goal fewer in the session than the script, which has neither, accounts for
        edit_json(&record, |r| {
            r["oracles"][0]["closed"][0]["script"] =
                serde_json::json!([{"depth": 0, "sentence": "admit."}, {"depth": 0, "sentence": "idtac."}]);
        });
        let n1 = read_record(&record).oracles[0].closed[0].clone();
        assert_eq!(n1.id, "N1");
        let flag = Arc::new(AtomicBool::new(false));
        let stopped = run_again_stopped(
            TWO_BRANCHES,
            out.path(),
            &TacticsOptions {
                stop: Some(flag.clone()),
                ..resume_with(ResumeMode::Replay)
            },
            Some(StopIn {
                node: "N1",
                nth: 1,
                flag,
                sent: None,
            }),
        );
        let eq = &stopped.equivalences[0];
        assert!(
            matches!(&eq.interrupted, Some(Interrupted::Sealed { node, .. }) if node == "N1"),
            "{}",
            eq.render()
        );
        // N1 is still closed, as recorded, and the checkpoint admits its goal
        let entry = read_record(&record).oracles[0].clone();
        assert_eq!(entry.status, OracleStatus::Interrupted);
        assert_eq!(entry.closed, vec![n1]);
        assert_eq!(entry.in_flight(), Some("N1"));
        let text = proof_file(&stopped, out.path());
        if let Err(e) = compile(&crate::easycrypt::session::locate_binary(), out.path(), &file) {
            panic!("the checkpoint does not compile: {e}\n{text}");
        }
        // and the next job keeps it
        let resumed = run_again_on(TWO_BRANCHES, out.path(), &resume_with(ResumeMode::Trust));
        assert_eq!(the_oracle(&resumed).resumed_at.as_ref().map(|r| r.kept), Some(1));
        assert!(read_record(&record).complete);
    }

    /// Rewrites the JSON file at `path` with `edit`.
    fn edit_json(path: &Path, edit: impl FnOnce(&mut serde_json::Value)) {
        let mut value: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
        edit(&mut value);
        std::fs::write(path, value.to_string()).unwrap();
    }

    fn resume_with(mode: ResumeMode) -> TacticsOptions {
        TacticsOptions {
            write_granularity: WriteGranularity::Tactic,
            resume: mode,
            ..TacticsOptions::default()
        }
    }

    /// Story 67: the record and the trees are in `session/<Eq>/`, the report in
    /// `progress/<Eq>/`; the top level holds none of them.
    #[test]
    fn a_job_writes_its_record_and_trees_under_session_and_its_report_under_progress() {
        let Some((first_run, out)) = stopped_mid_oracle() else {
            return;
        };
        let eq = &first_run.equivalences[0];
        let stem = eq.proof_file.trim_end_matches(".ec");
        let session = out.path().join("session").join(stem);
        // story 68: one record for each oracle
        assert!(session.join("Branch.record.json").exists());
        assert!(!session.join("record.json").exists());
        assert!(session.join("Branch.tree.json").exists());
        assert_eq!(eq.report_file, format!("progress/{stem}/report.txt"));
        assert!(out.path().join(&eq.report_file).exists());
        for entry in std::fs::read_dir(out.path()).unwrap() {
            let name = entry.unwrap().file_name().to_string_lossy().into_owned();
            assert!(
                !name.ends_with(".session.json")
                    && !name.ends_with(".tree.json")
                    && !name.ends_with(".report.txt"),
                "{name} at the top level"
            );
        }
    }

    /// Story 67: a record and a tree at the paths before story 67 are resumed from; the job
    /// writes the new paths and leaves the old files.
    #[test]
    fn a_job_resumes_from_a_record_and_a_tree_at_the_old_paths() {
        let Some((first_run, out)) = stopped_mid_oracle() else {
            return;
        };
        let file = first_run.equivalences[0].proof_file.clone();
        let old_record = old_session_record_path(out.path(), &file);
        let old_tree = old_saved_tree_path(out.path(), &file, "Branch");
        std::fs::rename(session_record_path(out.path(), &file), &old_record).unwrap();
        std::fs::rename(saved_tree_path(out.path(), &file, "Branch"), &old_tree).unwrap();
        walk_events();
        let result = run_again_on(TWO_BRANCHES, out.path(), &resume_with(ResumeMode::Trust));
        assert!(!walk_events().contains(&"lockstep Branch".to_string()));
        assert!(the_oracle(&result).resumed_at.is_some());
        assert!(read_record(&session_record_path(out.path(), &file)).complete);
        assert!(old_record.exists() && old_tree.exists());
    }

    fn the_oracle(result: &TheoremTactics) -> &OracleTactics {
        &result.equivalences[0].oracles[0]
    }

    #[test]
    fn restart_runs_lockstep_execution_again_and_rewrites_the_tree() {
        let Some((first_run, out)) = stopped_mid_oracle() else {
            return;
        };
        let tree = saved_tree_path(out.path(), &first_run.equivalences[0].proof_file, "Branch");
        let saved = SavedTree::read(&tree).unwrap().unwrap().fingerprint;
        edit_json(&tree, |t| t["fingerprint"] = "from another project".into());
        walk_events();
        let result = run_again_on(TWO_BRANCHES, out.path(), &resume_with(ResumeMode::Restart));
        let events = walk_events();
        assert!(events.contains(&"lockstep Branch".to_string()), "{events:?}");
        assert!(!events.contains(&"sentence kept".to_string()), "{events:?}");
        assert_eq!(the_oracle(&result).resumed_at, None);
        assert_eq!(SavedTree::read(&tree).unwrap().unwrap().fingerprint, saved);
        assert!(read_record(&record_path(&result, out.path())).complete);
    }

    #[test]
    fn an_oracle_without_its_tree_or_from_a_version_2_record_is_proved_from_the_start() {
        let Some((first_run, out)) = stopped_mid_oracle() else {
            return;
        };
        let other = copy_export(out.path());
        let third = copy_export(out.path());
        // no tree file
        let file = &first_run.equivalences[0].proof_file;
        std::fs::remove_file(saved_tree_path(out.path(), file, "Branch")).unwrap();
        walk_events();
        let result = run_again_on(TWO_BRANCHES, out.path(), &resume_with(ResumeMode::Trust));
        assert!(walk_events().contains(&"lockstep Branch".to_string()));
        assert_eq!(the_oracle(&result).resumed_at, None);
        assert!(saved_tree_path(out.path(), file, "Branch").exists());
        // a version 2 record has no closed nodes
        edit_json(&session_record_path(other.path(), file), |r| {
            r["version"] = 2.into();
            for o in r["oracles"].as_array_mut().unwrap() {
                o.as_object_mut().unwrap().remove("closed");
            }
        });
        let result = run_again_on(TWO_BRANCHES, other.path(), &resume_with(ResumeMode::Trust));
        assert!(walk_events().contains(&"lockstep Branch".to_string()));
        assert_eq!(the_oracle(&result).resumed_at, None);
        let record = read_record(&record_path(&result, other.path()));
        assert_eq!(record.version, SessionRecord::VERSION);
        assert!(record.complete);
        // a tree written by a later lockstep execution than the closed nodes were proved on (a
        // job killed between writing the tree and the record)
        let record = session_record_path(third.path(), file);
        let saved = SavedTree::read(&saved_tree_path(third.path(), file, "Branch"))
            .unwrap()
            .expect("a tree");
        assert_eq!(read_record(&record).oracles[0].tree_id.as_ref(), Some(&saved.id));
        edit_json(&record, |r| r["oracles"][0]["tree_id"] = "another".into());
        let result = run_again_on(TWO_BRANCHES, third.path(), &resume_with(ResumeMode::Trust));
        assert!(walk_events().contains(&"lockstep Branch".to_string()));
        assert_eq!(the_oracle(&result).resumed_at, None);
    }

    #[test]
    fn a_stale_tree_is_walked_and_said_to_be_stale() {
        let Some((first_run, out)) = stopped_mid_oracle() else {
            return;
        };
        let tree = saved_tree_path(out.path(), &first_run.equivalences[0].proof_file, "Branch");
        // as if the oracle's code had changed since the tree was saved
        edit_json(&tree, |t| {
            t["fingerprint"] = "0".into();
            t["fingerprint_parts"]["code"] = "0".into();
        });
        walk_events();
        let result = run_again_on(TWO_BRANCHES, out.path(), &resume_with(ResumeMode::Trust));
        assert!(!walk_events().contains(&"lockstep Branch".to_string()));
        let at = the_oracle(&result).resumed_at.clone().expect("resumed");
        assert_eq!((at.kept, at.stale), (1, vec!["code"]));
        let report = result.equivalences[0].render();
        assert!(
            report.contains("Branch: resumed at N3 (1 closed node kept, trust); saved joint tree is stale (code)"),
            "{report}"
        );
    }

    /// Story 58: a tree saved before the `claims` part existed is stale, and it is still used.
    #[test]
    fn a_tree_saved_without_the_claims_part_is_stale_and_still_used() {
        let Some((first_run, out)) = stopped_mid_oracle() else {
            return;
        };
        let tree = saved_tree_path(out.path(), &first_run.equivalences[0].proof_file, "Branch");
        edit_json(&tree, |t| {
            t["fingerprint"] = "0".into();
            t["fingerprint_parts"].as_object_mut().unwrap().remove("claims");
        });
        walk_events();
        let result = run_again_on(TWO_BRANCHES, out.path(), &resume_with(ResumeMode::Trust));
        assert!(!walk_events().contains(&"lockstep Branch".to_string()));
        let at = the_oracle(&result).resumed_at.clone().expect("resumed");
        assert_eq!(at.stale, vec!["claims"]);
        assert_eq!(
            crate::debug::lockstep_fingerprint::describe_part("claims"),
            "the claims checked"
        );
    }

    /// Story 59: a tree saved before the `StateRelation_` names (its `claims` part hashes the
    /// old names, and it has no `helpers`) is stale, and it is still used (ADR 0008).
    #[test]
    fn a_tree_saved_before_the_state_relation_names_is_stale_and_still_used() {
        let Some((first_run, out)) = stopped_mid_oracle() else {
            return;
        };
        let tree = saved_tree_path(out.path(), &first_run.equivalences[0].proof_file, "Branch");
        edit_json(&tree, |t| {
            t["fingerprint"] = "0".into();
            t["fingerprint_parts"]["claims"] = "0".into();
            t.as_object_mut().unwrap().remove("helpers");
        });
        walk_events();
        let result = run_again_on(TWO_BRANCHES, out.path(), &resume_with(ResumeMode::Trust));
        assert!(!walk_events().contains(&"lockstep Branch".to_string()));
        let at = the_oracle(&result).resumed_at.clone().expect("resumed");
        assert_eq!(at.stale, vec!["claims"]);
    }

    #[test]
    fn a_closed_node_whose_replay_is_rejected_is_proved_again() {
        let Some((first_run, out)) = stopped_mid_oracle() else {
            return;
        };
        let file = &first_run.equivalences[0].proof_file;
        edit_json(&session_record_path(out.path(), file), |r| {
            r["oracles"][0]["closed"][0]["script"][0]["sentence"] = "sp 9 9.".into();
        });
        walk_events();
        let result = run_again_on(TWO_BRANCHES, out.path(), &resume_with(ResumeMode::Replay));
        let events = walk_events();
        let n1 = events.iter().position(|e| e == "node N1/5").unwrap();
        // rejected at once, undone, and N1 proved from its first fallback
        assert_eq!(
            events[n1 + 1..n1 + 3],
            ["sentence sp 9 9.", "sentence auto => /#."],
            "{events:#?}"
        );
        let eq = &result.equivalences[0];
        assert!(eq.interrupted.is_none(), "{}", eq.render());
        assert_eq!(the_oracle(&result).resumed_at.as_ref().map(|r| r.kept), Some(0));
        let text = proof_file(&result, out.path());
        assert!(!text.contains("sp 9 9."), "{text}");
        assert!(labelled_admits(&text).iter().all(|r| r != "interrupted"), "{text}");
        if let Err(e) = compile(
            &crate::easycrypt::session::locate_binary(),
            out.path(),
            &eq.proof_file,
        ) {
            panic!("the resumed proof does not compile: {e}\n{text}");
        }
    }

    #[test]
    fn an_oracle_sealed_by_an_unanswered_interrupt_is_resumed_by_the_next_job() {
        // the second oracle's first sentence at N0 goes unanswered: sealed, left behind
        let Some((first_run, out, _)) = run_unanswered(&[2], None) else {
            return;
        };
        let record = read_record(&record_path(&first_run, out.path()));
        let entry = record.oracle("Second").unwrap();
        assert_eq!((entry.status, entry.in_flight()), (OracleStatus::Interrupted, Some("N0")));
        walk_events();
        let result = run_again_on(FOUR_ORACLES, out.path(), &resume_with(ResumeMode::Trust));
        let events = walk_events();
        // the done oracles are resumed as story 37 resumes them, the sealed one on its tree
        assert!(!events.iter().any(|e| e.starts_with("lockstep ")), "{events:?}");
        let eq = &result.equivalences[0];
        let second = eq.oracles.iter().find(|o| o.oracle == "Second").unwrap();
        assert_eq!(
            second.resumed_at.as_ref().map(|r| (r.node.as_str(), r.kept)),
            Some(("N0", 0)),
            "{}",
            eq.render()
        );
        assert_eq!(interrupted_admits(second), 0, "{}", eq.render());
        assert!(read_record(&record_path(&result, out.path())).complete);
    }
}

#[test]
fn the_translation_files_line_names_few_files_and_counts_many() {
    let names = |n: usize| (0..n).map(|i| format!("F{i}.ec")).collect::<Vec<_>>();
    assert_eq!(
        translation_files_line("Eq_A_B", &[]),
        "easycrypt prove: Eq_A_B — translation files already on disk"
    );
    assert_eq!(
        translation_files_line("Eq_A_B", &names(2)),
        "easycrypt prove: Eq_A_B — wrote missing translation files: F0.ec, F1.ec"
    );
    assert!(translation_files_line("Eq_A_B", &names(5)).ends_with("F3.ec, F4.ec"));
    assert_eq!(
        translation_files_line("Eq_A_B", &names(6)),
        "easycrypt prove: Eq_A_B — wrote 6 missing translation files"
    );
}

#[test]
fn a_leaf_has_no_deadline_unless_a_budget_is_given() {
    let now = std::time::Instant::now();
    assert_eq!(super::driver::leaf_deadline(None, now), None);
    let budget = Duration::from_secs(5);
    assert_eq!(
        super::driver::leaf_deadline(Some(budget), now),
        Some(now + budget)
    );
    // `0` has no special meaning: the deadline is now, so every part is admitted at once.
    assert_eq!(
        super::driver::leaf_deadline(Some(Duration::ZERO), now),
        Some(now)
    );
}

#[test]
fn the_leaf_budget_is_off_by_default() {
    assert_eq!(TacticsOptions::default().leaf_budget, None);
}

/// Story 56: each sentence's record says why the driver sent it. A fake EasyCrypt refuses every
/// closing tactic, so the walk goes through every role: N0 (unreachable) through its quick close
/// to an admit, N1 (a leaf) through the reduction to a formula, the split and the part fallbacks of
/// each conjunct to an admit of each part.
#[test]
fn each_record_says_why_the_driver_sent_its_sentence() {
    use crate::debug::lockstep::JointTree;
    use crate::easycrypt::session::tests::TestSink;
    use crate::easycrypt::session::Session;
    use std::os::unix::fs::PermissionsExt;

    let dir = tempfile::tempdir().unwrap();
    let prog = r#"{"id":1,"concl":{"kind":"equivS","pp":"p"},"text":"p"}"#;
    let atom = r#"{"id":1,"concl":{"kind":"app","pp":"a","op":"Top.a"},"text":"a"}"#;
    let conj = format!(
        r#"{{"id":1,"concl":{{"kind":"app","pp":"a /\\ a","op":"Top.Logic./\\","args":[{a},{a}]}},"text":"a /\\ a"}}"#,
        a = r#"{"kind":"app","pp":"a","op":"Top.a"}"#
    );
    let proofs = [
        ("two", format!(r#"{{"front":{prog},"kinds":["program","program"]}}"#)),
        ("prog", format!(r#"{{"front":{prog},"kinds":["program"]}}"#)),
        ("conj", format!(r#"{{"front":{conj},"kinds":["formula"]}}"#)),
        ("two_atoms", format!(r#"{{"front":{atom},"kinds":["formula","formula"]}}"#)),
        ("one_atom", format!(r#"{{"front":{atom},"kinds":["formula"]}}"#)),
        ("none", r#"{"front":null,"kinds":[]}"#.to_string()),
    ];
    for (name, proof) in &proofs {
        std::fs::write(dir.path().join(format!("{name}.json")), proof).unwrap();
    }
    let script = dir.path().join("fake-easycrypt");
    std::fs::write(
        &script,
        format!(
            r#"#!/bin/sh
d='{}'; n=0; g=none
ans() {{ n=$((n+1)); printf '{{"version":"domino-json/3","state":%s,"status":"ok","messages":[],"proof":%s}}\n' $n "$(cat $d/$g.json)"; }}
err() {{ printf '{{"version":"domino-json/3","state":%s,"status":"error","messages":[],"error":{{"msg":"no"}},"proof":%s}}\n' $n "$(cat $d/$g.json)"; }}
while IFS= read -r req; do
  line=$(printf '%s\n' "$req" | sed -e 's/^."sentence":"\(.*\)","want":"[a-z]*".$/\1/' -e 's/\\"/"/g' -e 's/\\\\/\\/g')
  case "$line" in
    start.) g=two; ans;;
    admit.) case $g in two) g=prog;; prog) g=none;; two_atoms) g=one_atom;; *) g=none;; esac; ans;;
    "auto => &1 &2 hpre.") g=conj; ans;;
    "do split.") case $g in conj) g=two_atoms; ans;; *) err;; esac;;
    *) err;;
  esac
done
"#,
            dir.path().display()
        ),
    )
    .unwrap();
    std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).unwrap();

    let side = serde_json::json!({"head": {"kind": "return", "label": 1}, "consumed": []});
    let nodes: Vec<_> = ["unreachable", "terminal-pair"]
        .iter()
        .enumerate()
        .map(|(index, kind)| {
            serde_json::json!({"index": index, "kind": kind, "left": side, "right": side,
                               "answers": [], "children": []})
        })
        .collect();
    let tree: JointTree = serde_json::from_value(serde_json::json!({ "nodes": nodes })).unwrap();
    let outcome = crate::debug::lockstep::LockstepOutcome {
        tree,
        pairs: vec![],
        stuck: vec![],
        stop_reason: crate::debug::driver::StopReason::Completed,
    };
    let tree = super::driver::OracleTree::new(&outcome);
    let mut session = Session::start_with(&script, dir.path()).unwrap();
    let sink = TestSink::new(usize::MAX);
    session.set_transcript_sink(
        Box::new(sink.clone()),
        &dir.path().join("ec-transcript.jsonl"),
        EcTranscriptMode::Capped,
        "Eq.ec",
    );
    assert_eq!(session.send("start.", Want::Full).unwrap().status, crate::easycrypt::json::Status::Ok);
    let mut prover = super::driver::Prover {
        judgement: super::driver::Judgement::Equiv,
        session: &mut session,
        script: Default::default(),
        tree: &tree,
        hints: &[],
        unfold_ops: &["inv".to_string()],
        part_ops: &[],
        timeouts: Timeouts {
            general: Duration::from_secs(10),
            quick_close: Duration::from_secs(10),
        },
        quick_close: true,
        oracle: "O",
        leaf_budget: None,
        deadline: None,
        stats: OracleStats::default(),
        live: None,
        checkpoint: None,
        per_sentence: false,
        node: None,
        mismatches: vec![],
        stopped: None,
        resume: None,
        premises: Vec::new(),
        binders: Vec::new(),
        last_smt: None,
        admit_smt: None,
    };
    prover.prove_node(0).unwrap();
    prover.prove_node(1).unwrap();
    assert_eq!(prover.stats.admits.len(), 3);

    let said: Vec<String> = sink
        .text()
        .lines()
        .map(|l| serde_json::from_str::<serde_json::Value>(l).unwrap())
        .filter(|r| r["ctx"]["oracle"] == "O" && r.get("sentence").is_some())
        .map(|r| {
            let c = &r["ctx"];
            assert!(r["bytes"].as_u64().unwrap() > 0, "{r}");
            let sentence = r["sentence"].as_str().unwrap();
            let mut s = format!("N{} {} {sentence}", c["node"], c["role"].as_str().unwrap());
            if let Some(n) = c.get("n") {
                s += &format!(" #{n}");
            }
            if let Some(part) = c.get("part") {
                s += &format!(" [{}]", part.as_str().unwrap());
            }
            s
        })
        .collect();
    let hints = "smt(get_setE mem_set remE mem_rem emptyE).";
    let expected = [
        "N0 quick-close auto => /#.".to_string(),
        "N0 structure exfalso; smt().".to_string(),
        "N0 admit admit.".to_string(),
        "N1 reduce auto => &1 &2 hpre.".to_string(),
        "N1 split do split.".to_string(),
        "N1 split do split.".to_string(),
        "N1 part-fallback smt(). #1 [equal-output+invariant]".to_string(),
        format!("N1 part-fallback {hints} #2 [equal-output+invariant]"),
        format!("N1 part-fallback move: hpre => />; {hints} #3 [equal-output+invariant]"),
        // story 61: the key scan reads the goal in full; it was read at `head` by `do split.`
        "N1 split pragma Goals:printall.".to_string(),
        "N1 admit admit.".to_string(),
        "N1 split do split.".to_string(),
        "N1 part-fallback smt(). #1 [equal-output+invariant]".to_string(),
        format!("N1 part-fallback {hints} #2 [equal-output+invariant]"),
        format!("N1 part-fallback move: hpre => />; {hints} #3 [equal-output+invariant]"),
        "N1 admit admit.".to_string(),
    ];
    assert_eq!(said, expected);
}

/// Story 58 and symbolic-execution story 21: each one-sided invariant part has the view of
/// its own part verdict where `invariant` is not verified.
#[test]
fn a_one_sided_invariant_part_has_the_view_of_its_own_part_verdict() {
    let part = |op: &str, owner: &str| Part::SideInvariant {
        op: op.into(),
        claim: format!("package-invariant!main!{owner}-Prf!"),
    };
    let left = part("PkgInv_l_Prf", "Real_Hybrid3");
    let right = part("PkgInv_r_Prf", "Ideal_Hybrid3");
    let p = pair(
        Verdict::Verified,
        fails(),
        &[("PkgInv_l_Prf", fails()), ("PkgInv_r_Prf", Verdict::Verified)],
        false,
    );
    assert_eq!(pair_view_for_tests(&p, &left), "fails");
    assert_eq!(pair_view_for_tests(&p, &right), "verified");

    // a pair where a side aborts: a failure counts as inconclusive
    let aborting = pair(Verdict::Verified, fails(), &[("PkgInv_l_Prf", fails())], true);
    assert_eq!(pair_view_for_tests(&aborting, &left), "inconclusive");

    // a part verdict that is not there (a tree saved before story 21)
    let old = pair(Verdict::Verified, fails(), &[], false);
    assert_eq!(pair_view_for_tests(&old, &left), "inconclusive");
}

/// Symbolic-execution story 21: a verified `invariant` holds every part, so a part on that
/// pair is verified with no part verdict of its own.
#[test]
fn a_part_on_a_pair_with_invariant_verified_is_verified() {
    let p = pair(Verdict::Verified, Verdict::Verified, &[], false);
    assert_eq!(pair_view_for_tests(&p, &Part::Relation("a".into())), "verified");
    let side = Part::SideInvariant {
        op: "GameInv_G".into(),
        claim: "game-invariant!main!G!".into(),
    };
    assert_eq!(pair_view_for_tests(&p, &side), "verified");
    let unreachable = pair(Verdict::Verified, Verdict::pair_infeasible(), &[], false);
    assert_eq!(pair_view_for_tests(&unreachable, &side), "verified");
}

#[test]
fn the_exit_decision_that_domino_predicts_comes_first() {
    use super::driver::exit_decisions;
    let tail = "ec_result = None<:int * bits_n>";
    assert_eq!(exit_decisions(tail, Some(true)), ["rcondt", "rcondf"]);
    assert_eq!(exit_decisions(tail, Some(false)), ["rcondf", "rcondt"]);
    assert_eq!(exit_decisions(" (ec_result = None)", Some(true)), ["rcondt", "rcondf"]);
    // a done-flag guard comes after the side's terminal: it does not hold
    assert_eq!(exit_decisions("!ec_done", Some(true)), ["rcondf", "rcondt"]);
    // no prediction: `rcondf` first
    assert_eq!(exit_decisions("ec_r1 <> None", Some(true)), ["rcondf", "rcondt"]);
    assert_eq!(exit_decisions(tail, None), ["rcondf", "rcondt"]);
}

/// A leaf proved against a fake EasyCrypt (story 64): what was sent, and what was admitted.
struct LeafRun {
    /// `<role> <sentence>`, and ` [part]` where the record has one.
    said: Vec<String>,
    admits: Vec<Admit>,
    /// The script the leaf left.
    script: String,
    /// `<want> <sentence>` of every request the fake EasyCrypt read (ADR 0012).
    requests: Vec<String>,
}

/// Proves joint node 0, a terminal pair, against a fake EasyCrypt. `goals` are the proof
/// states by name (the JSON of `"proof"`); `start` is the state after `start.`; `arms` are the
/// shell `case` arms that answer the sentences (`g=<name>; ans` accepts and moves to a state;
/// anything else is refused). `undo k.` goes back to the state of answer `k`.
fn run_leaf(
    goals: &[(&str, String)],
    start: &str,
    arms: &str,
    pairs: Vec<PairRecord>,
    part_ops: &[crate::writers::easycrypt::invariant::InvariantOp],
) -> LeafRun {
    use crate::debug::lockstep::JointTree;
    use crate::easycrypt::session::tests::TestSink;
    use crate::easycrypt::session::Session;
    use std::os::unix::fs::PermissionsExt;

    let dir = tempfile::tempdir().unwrap();
    let none = ("none", r#"{"front":null,"kinds":[]}"#.to_string());
    for (name, proof) in goals.iter().chain([&none]) {
        std::fs::write(dir.path().join(format!("{name}.json")), proof).unwrap();
    }
    let script = dir.path().join("fake-easycrypt");
    std::fs::write(
        &script,
        format!(
            r#"#!/bin/sh
d='{}'; n=0; g=none
ans() {{ n=$((n+1)); eval "g_$n=$g"; printf '{{"version":"domino-json/3","state":%s,"status":"ok","messages":[],"proof":%s}}\n' $n "$(cat $d/$g.json)"; }}
err() {{ printf '{{"version":"domino-json/3","state":%s,"status":"error","messages":[],"error":{{"msg":"no"}},"proof":%s}}\n' $n "$(cat $d/$g.json)"; }}
while IFS= read -r req; do
  printf '%s\n' "$req" >> "$d/requests"
  line=$(printf '%s\n' "$req" | sed -e 's/^."sentence":"\(.*\)","want":"[a-z]*".$/\1/' -e 's/\\"/"/g' -e 's/\\\\/\\/g')
  case "$line" in
    start.) g={start}; ans;;
    "undo "*) k=${{line#undo }}; k=${{k%.}}; eval "g=\$g_$k"; n=$((k-1)); ans;;
{arms}
    *) err;;
  esac
done
"#,
            dir.path().display()
        ),
    )
    .unwrap();
    std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).unwrap();

    let side = serde_json::json!({"head": {"kind": "return", "label": 1}, "consumed": []});
    let tree: JointTree = serde_json::from_value(serde_json::json!({ "nodes": [
        {"index": 0, "kind": "terminal-pair", "left": side, "right": side,
         "answers": [], "children": []}
    ]}))
    .unwrap();
    let outcome = crate::debug::lockstep::LockstepOutcome {
        tree,
        pairs,
        stuck: vec![],
        stop_reason: crate::debug::driver::StopReason::Completed,
    };
    let tree = super::driver::OracleTree::new(&outcome);
    let mut session = Session::start_with(&script, dir.path()).unwrap();
    let sink = TestSink::new(usize::MAX);
    session.set_transcript_sink(
        Box::new(sink.clone()),
        &dir.path().join("ec-transcript.jsonl"),
        EcTranscriptMode::Capped,
        "Eq.ec",
    );
    assert_eq!(session.send("start.", Want::Full).unwrap().status, crate::easycrypt::json::Status::Ok);
    let mut prover = super::driver::Prover {
        judgement: super::driver::Judgement::Equiv,
        session: &mut session,
        script: Default::default(),
        tree: &tree,
        hints: &[],
        unfold_ops: &["inv".to_string()],
        part_ops,
        timeouts: Timeouts {
            general: Duration::from_secs(10),
            quick_close: Duration::from_secs(10),
        },
        quick_close: true,
        oracle: "O",
        leaf_budget: None,
        deadline: None,
        stats: OracleStats::default(),
        live: None,
        checkpoint: None,
        per_sentence: false,
        node: None,
        mismatches: vec![],
        stopped: None,
        resume: None,
        premises: Vec::new(),
        binders: Vec::new(),
        last_smt: None,
        admit_smt: None,
    };
    prover.prove_node(0).unwrap();
    assert_eq!(prover.count(), 0, "the leaf is closed");
    let admits = prover.stats.admits.clone();
    let script = prover.script.render();
    let said = sink
        .text()
        .lines()
        .map(|l| serde_json::from_str::<serde_json::Value>(l).unwrap())
        .filter(|r| r["ctx"]["oracle"] == "O" && r.get("sentence").is_some())
        .map(|r| {
            let c = &r["ctx"];
            let role = c["role"].as_str().unwrap();
            let mut s = format!("{role} {}", r["sentence"].as_str().unwrap());
            if let Some(part) = c.get("part") {
                s += &format!(" [{}]", part.as_str().unwrap());
            }
            s
        })
        .collect();
    let requests = std::fs::read_to_string(dir.path().join("requests"))
        .unwrap()
        .lines()
        .filter_map(|l| serde_json::from_str::<serde_json::Value>(l).ok())
        .map(|r| format!("{} {}", r["want"].as_str().unwrap(), r["sentence"].as_str().unwrap()))
        .collect();
    LeafRun {
        said,
        admits,
        script,
        requests,
    }
}

/// Story 61: each sentence asks for what its caller reads. The part fallbacks and the admit ask
/// for no goal (`status`), the reduction to a formula for its head; the key case split reads the
/// goal in full first, with the probe.
#[test]
fn fallbacks_and_admits_ask_for_status_and_the_opening_for_the_head() {
    let goals = [
        ("start", proof_of(&program_with_ifs(&[], &[]), 1)),
        ("atom", proof_of(&formula(r#"{"kind":"app","pp":"a","op":"Top.a"}"#), 1)),
    ];
    let arms = r#"
    "auto => &1 &2 hpre.") g=atom; ans;;
    "pragma Goals:printall.") n=$((n-1)); ans;;
    admit.) g=none; ans;;"#;
    let run = run_leaf(&goals, "start", arms, vec![leaf_pair(false, Verdict::Verified, &[])], &[]);
    let hints = "smt(get_setE mem_set remE mem_rem emptyE).";
    assert_eq!(
        run.requests,
        [
            "full start.".to_string(),
            "head auto => &1 &2 hpre.".to_string(),
            "head do split.".to_string(),
            "status smt().".to_string(),
            format!("status {hints}"),
            format!("status move: hpre => />; {hints}"),
            "full pragma Goals:printall.".to_string(),
            "status admit.".to_string(),
        ]
    );
    assert_eq!(run.admits.len(), 1);
}

/// A proof state whose front goal is `front` (goal JSON), with `open` goals of its kind.
fn proof_of(front: &str, open: usize) -> String {
    let kind = if front.contains(r#""kind":"equivS""#) {
        "program"
    } else {
        "formula"
    };
    let kinds = vec![format!("\"{kind}\""); open].join(",");
    format!(r#"{{"front":{front},"kinds":[{kinds}]}}"#)
}

/// A program goal whose sides hold `if`s with these conditions.
fn program_with_ifs(left: &[&str], right: &[&str]) -> String {
    let side = |conds: &[&str]| {
        let stmt: Vec<String> = conds
            .iter()
            .map(|c| {
                format!(r#"{{"kind":"if","pp":"if ({c}) {{}}","cond":{{"kind":"app","pp":"{c}"}}}}"#)
            })
            .collect();
        format!(r#"{{"stmt":[{}]}}"#, stmt.join(","))
    };
    format!(
        r#"{{"id":1,"concl":{{"kind":"equivS","pp":"p","left":{},"right":{}}},"text":"p"}}"#,
        side(left),
        side(right)
    )
}

fn formula(concl: &str) -> String {
    format!(r#"{{"id":1,"concl":{concl},"text":"f"}}"#)
}

fn leaf_pair(left_aborts: bool, invariant: Verdict, relations: &[(&str, Verdict)]) -> PairRecord {
    let mut p = pair(Verdict::Verified, invariant, relations, left_aborts);
    p.node = 0;
    p
}

#[test]
fn the_exit_path_tries_the_predicted_decision_first_then_the_other_one() {
    let goals = [
        ("start", proof_of(&program_with_ifs(&["ec_result = None"], &["!ec_done"]), 1)),
        ("right_only", proof_of(&program_with_ifs(&[], &["!ec_done"]), 1)),
        ("no_ifs", proof_of(&program_with_ifs(&[], &[]), 1)),
    ];
    let arms = r#"
    "rcondt{1} ^if; 1: by auto.") g=right_only; ans;;
    "rcondf{2} ^if; 1: by auto.") g=no_ifs; ans;;
    "auto => &1 &2 hpre.") g=none; ans;;"#;
    // side 1 does not abort: `rcondf` is predicted and refused, then `rcondt` is accepted
    let run = run_leaf(&goals, "start", arms, vec![leaf_pair(false, Verdict::Verified, &[])], &[]);
    assert_eq!(
        run.said,
        [
            "exit-path rcondf{1} ^if; 1: by auto.",
            "exit-path rcondt{1} ^if; 1: by auto.",
            "exit-path rcondf{2} ^if; 1: by auto.",
            "reduce auto => &1 &2 hpre.",
        ]
    );
    assert!(run.admits.is_empty());

    // side 1 aborts: `rcondt` on the router's tail is predicted, and accepted at once
    let run = run_leaf(&goals, "start", arms, vec![leaf_pair(true, Verdict::Verified, &[])], &[]);
    assert_eq!(run.said[0], "exit-path rcondt{1} ^if; 1: by auto.");
    assert_eq!(run.said[1], "exit-path rcondf{2} ^if; 1: by auto.");
}

#[test]
fn an_if_that_no_decision_takes_stops_the_exit_path_and_a_program_after_auto_is_a_whole_admit() {
    let goals = [("start", proof_of(&program_with_ifs(&["c", "d"], &["e"]), 1))];
    // `auto` is accepted but leaves the program goal: undone, and the leaf admitted whole
    let arms = r#"
    "auto => &1 &2 hpre.") ans;;
    admit.) g=none; ans;;"#;
    let run = run_leaf(&goals, "start", arms, vec![leaf_pair(false, fails(), &[])], &[]);
    assert_eq!(
        run.said,
        [
            "exit-path rcondf{1} ^if; 1: by auto.",
            "exit-path rcondt{1} ^if; 1: by auto.",
            "reduce auto => &1 &2 hpre.",
            "undo undo 1.",
            "admit admit.",
        ]
    );
    let [admit] = run.admits.as_slice() else {
        panic!("{:?}", run.admits)
    };
    assert_eq!(admit.claim, "equal-output+invariant");
}

fn relation_op(name: &str, relation: &str) -> crate::writers::easycrypt::invariant::InvariantOp {
    crate::writers::easycrypt::invariant::InvariantOp {
        name: name.into(),
        claim: None,
        relation: Some(relation.into()),
    }
}

/// `forall x, a => StateRelation_r x`, opened: the binder, the premise, the claim operator,
/// then `do split` into three goals that nothing opens. Each one is a part of the claim.
#[test]
fn the_leaf_is_opened_until_only_parts_are_left_and_no_split_is_sent() {
    let atom = r#"{"kind":"app","pp":"a","op":"Top.a"}"#;
    let rel = r#"{"kind":"app","pp":"","op":"Top.Eq_Invariants.StateRelation_r","args":[{"kind":"local","pp":"x"}]}"#;
    let imp = format!(r#"{{"kind":"app","pp":"","op":"Top.Logic.=>","args":[{atom},{rel}]}}"#);
    let binder = r#"{"name":"x","ident":{"name":"x","tag":1},"kind":"var","type":{"pp":"int"}}"#;
    let all = format!(
        r#"{{"kind":"quant","pp":"","quantifier":"forall","binders":[{binder}],"body":{imp}}}"#
    );
    let conj = format!(r#"{{"kind":"app","pp":"","op":"Top.Logic./\\","args":[{atom},{atom}]}}"#);
    let goals = [
        ("start", proof_of(&program_with_ifs(&[], &[]), 1)),
        ("all", proof_of(&formula(&all), 1)),
        ("imp", proof_of(&formula(&imp), 1)),
        ("rel", proof_of(&formula(rel), 1)),
        ("conj", proof_of(&formula(&conj), 1)),
        ("three", proof_of(&formula(atom), 3)),
        ("two", proof_of(&formula(atom), 2)),
        ("one", proof_of(&formula(atom), 1)),
    ];
    let arms = r#"
    "auto => &1 &2 hpre.") g=all; ans;;
    "move => x /=.") g=imp; ans;;
    "move => hpre /=.") g=rel; ans;;
    "rewrite /StateRelation_r /=.") g=conj; ans;;
    "do split.") case $g in conj) g=three; ans;; *) err;; esac;;
    admit.) case $g in three) g=two;; two) g=one;; *) g=none;; esac; ans;;"#;
    let ops = [relation_op("StateRelation_r", "r")];
    let pair = leaf_pair(false, fails(), &[("StateRelation_r", Verdict::Verified)]);
    let run = run_leaf(&goals, "start", arms, vec![pair], &ops);

    let part = "invariant/StateRelation_r";
    let mut expected: Vec<String> = [
        "reduce auto => &1 &2 hpre.",
        "split move => x /=.",
        "split move => hpre /=.",
        "split rewrite /StateRelation_r /=.",
        "split do split.",
    ]
    .map(String::from)
    .to_vec();
    for i in 0..3 {
        expected.push("split do split.".into());
        // story 65: the part fallback sequence, the premises in the order of introduction
        for f in [
            "smt().",
            "smt(get_setE mem_set remE mem_rem emptyE).",
            "move: hpre hpre => />; smt(get_setE mem_set remE mem_rem emptyE).",
        ] {
            expected.push(format!("part-fallback {f} [{part}]"));
        }
        // story 61: the key scan reads in full the goal `do split.` read at `head` (the fake
        // sends the next ones in full with the admit)
        if i == 0 {
            expected.push("split pragma Goals:printall.".into());
        }
        expected.push(format!("admit admit. [{part}]"));
    }
    assert_eq!(run.said, expected);
    assert!(!run.said.iter().any(|s| s.contains("get_set_neqE")));
    assert!(!run.said.iter().any(|s| s.ends_with(" split.") && !s.ends_with("do split.")));
    assert!(!run.said.iter().any(|s| s.starts_with("leaf-fallback")));
    assert_eq!(run.admits.len(), 3);
    for admit in &run.admits {
        assert_eq!(admit.claim, part);
        // the relation's own verdict, not the failing invariant's
        assert_eq!(admit.domino, DominoView::Verified);
        // the last fallback was refused with no prover outcome
        assert_eq!(admit.smt, Some(SmtOutcome::Error));
        assert!(admit.label().ends_with("; smt: error *)"), "{}", admit.label());
    }
}

/// Story 65: the outcome of the last fallback's answer, from its `timing.smt`.
#[test]
fn the_smt_outcome_is_timeout_then_unknown_then_error() {
    let answer = |status: &str, smt: &str| -> crate::easycrypt::json::Response {
        serde_json::from_str(&format!(
            r#"{{"version":"domino-json/3","state":1,"status":"{status}","messages":[],
               "timing":{{"tactic_ms":1,"serialize_ms":0{smt}}}}}"#
        ))
        .unwrap()
    };
    let calls = |valid: u64, timeout: u64, unknown: u64| {
        format!(
            r#","smt":{{"calls":{},"translate_ms":0,"prepare_ms":0,"prover_ms":0,"valid":{valid},"timeout":{timeout},"unknown":{unknown}}}"#,
            valid + timeout + unknown
        )
    };
    let of = |r| SmtOutcome::of_answer(&r);
    assert_eq!(of(answer("error", &calls(0, 1, 2))), Some(SmtOutcome::Timeout));
    assert_eq!(of(answer("error", &calls(1, 0, 2))), Some(SmtOutcome::Unknown));
    assert_eq!(of(answer("error", &calls(0, 0, 0))), Some(SmtOutcome::Error));
    assert_eq!(of(answer("error", "")), Some(SmtOutcome::Error));
    assert_eq!(of(answer("ok", &calls(1, 0, 0))), None);
}

/// Story 65: `Domino: <view>` only where the reason does not say it, and `smt:` when a fallback
/// ran.
#[test]
fn the_admit_label_says_dominos_view_only_where_the_reason_does_not() {
    for reason in AdmitReason::ALL {
        let admit = Admit {
            reason,
            id: "J1".into(),
            claim: "invariant/StateRelation_s".into(),
            domino: DominoView::Verified,
            goal: String::new(),
            smt: Some(SmtOutcome::Timeout),
        };
        let says = matches!(
            reason,
            AdmitReason::Router
                | AdmitReason::Stuck
                | AdmitReason::SeqPost
                | AdmitReason::ProgramMismatch
        );
        let domino = if says { "; Domino: verified" } else { "" };
        assert_eq!(
            admit.label(),
            format!(
                "(* domino: J1 StateRelation_s; {}{domino}; smt: timeout *)",
                reason.slug()
            )
        );
    }
    let whole = Admit {
        reason: AdmitReason::DominoVerifiedEcFailed,
        id: "J2".into(),
        claim: "equal-output+invariant".into(),
        domino: DominoView::Verified,
        goal: String::new(),
        smt: None,
    };
    assert_eq!(whole.label(), "(* domino: J2; domino-verified-ec-failed *)");

    // a session record written before story 65 reads back without change: `domino` is kept
    let old = AdmitRecord {
        node: "J1".into(),
        reason: "domino-verified-ec-failed".into(),
        claim: "invariant/StateRelation_s".into(),
        domino: "verified".into(),
    };
    let back = Admit::from_record(&old).unwrap().to_record();
    assert_eq!(
        (back.node, back.reason, back.claim, back.domino),
        (old.node, old.reason, old.claim, old.domino)
    );
}

/// §3.6 for a claim: the part is admitted as soon as the loop sees its operator. A part with no
/// claim operator has the whole leaf's verdict.
#[test]
fn a_claim_that_fails_in_domino_is_admitted_at_once_and_a_part_without_a_claim_is_the_leafs() {
    let atom = r#"{"kind":"app","pp":"a","op":"Top.a"}"#;
    let rel = r#"{"kind":"app","pp":"","op":"Top.Eq_Invariants.StateRelation_r","args":[]}"#;
    let conj = format!(r#"{{"kind":"app","pp":"","op":"Top.Logic./\\","args":[{rel},{atom}]}}"#);
    let goals = [
        ("start", proof_of(&program_with_ifs(&[], &[]), 1)),
        ("conj", proof_of(&formula(&conj), 1)),
        ("rel_first", proof_of(&formula(rel), 2)),
        ("atom_last", proof_of(&formula(atom), 1)),
    ];
    let arms = r#"
    "auto => &1 &2 hpre.") g=conj; ans;;
    "do split.") case $g in conj) g=rel_first; ans;; *) err;; esac;;
    admit.) case $g in rel_first) g=atom_last;; *) g=none;; esac; ans;;"#;
    let ops = [relation_op("StateRelation_r", "r")];
    let pair = leaf_pair(false, fails(), &[("StateRelation_r", fails())]);
    let run = run_leaf(&goals, "start", arms, vec![pair], &ops);
    assert!(!run.said.iter().any(|s| s.contains("rewrite /StateRelation_r")), "{:?}", run.said);
    assert_eq!(run.said[2], "admit admit. [invariant/StateRelation_r]");
    let [rel_admit, whole] = run.admits.as_slice() else {
        panic!("{:?}", run.admits)
    };
    assert_eq!(rel_admit.claim, "invariant/StateRelation_r");
    assert_eq!(rel_admit.reason, AdmitReason::DominoFails);
    assert_eq!(whole.claim, "equal-output+invariant");
    // the worse of equal-output (verified) and invariant (fails)
    assert_eq!(whole.domino, DominoView::Fails);
}

/// Story 66: `forall c d, P (m.[k{2} <- v]).[c] (m.[j{2} <- v]).[d]` after `auto`, with a fake
/// EasyCrypt in which only the key cases close (`p1` is the part, `nK` is K goals after a
/// `case`). `last_closes` says whether the last case's `smt` closes.
fn run_key_split(last_closes: bool) -> LeafRun {
    let local = |n: &str| format!(r#"{{"kind":"local","name":"{n}"}}"#);
    let key = |n: &str| {
        format!(r#"{{"kind":"pvar","scope":"global","path":"Top.Comp_H3.M./{n}","mem":"&2"}}"#)
    };
    let read = |k: &str, b: &str| {
        let set = format!(
            r#"{{"kind":"app","op":"Top.FMap._.[_<-_]","args":[{},{},{}]}}"#,
            local("m"),
            key(k),
            local("v")
        );
        format!(r#"{{"kind":"app","op":"Top.FMap._.[_]","args":[{set},{}]}}"#, local(b))
    };
    let body = format!(
        r#"{{"kind":"app","pp":"","op":"Top.P","args":[{},{}]}}"#,
        read("k", "c"),
        read("j", "d")
    );
    let binder = |n: &str| format!(r#"{{"name":"{n}","kind":"var","type":{{"pp":"int"}}}}"#);
    let all = format!(
        r#"{{"kind":"quant","pp":"","quantifier":"forall","binders":[{},{}],"body":{body}}}"#,
        binder("c"),
        binder("d")
    );
    let goals = [
        ("start", proof_of(&program_with_ifs(&[], &[]), 1)),
        ("all", proof_of(&formula(&all), 1)),
        ("p1", proof_of(&formula(&body), 1)),
        ("n1", proof_of(&formula(&body), 1)),
        ("n2", proof_of(&formula(&body), 2)),
        ("n3", proof_of(&formula(&body), 3)),
    ];
    let last = if last_closes { "g=none; ans" } else { "err" };
    let arms = format!(
        r#"
    "auto => &1 &2 hpre.") g=all; ans;;
    "move => c d /=.") g=p1; ans;;
    "case ("*) case $g in p1) g=n2; ans;; n2) g=n3; ans;; n1) g=n2; ans;; *) err;; esac;;
    "smt(get_setE mem_set remE mem_rem emptyE).") case $g in n3) g=n2; ans;; n2) g=n1; ans;; n1) {last};; *) err;; esac;;
    admit.) g=none; ans;;"#
    );
    run_leaf(&goals, "start", &arms, vec![], &[])
}

const KEY_SPLIT: [&str; 7] = [
    "case (c = Comp_H3.M.k{2}) => [->|?].",
    "case (d = Comp_H3.M.j{2}) => [->|?].",
    "smt(get_setE mem_set remE mem_rem emptyE).",
    "smt(get_setE mem_set remE mem_rem emptyE).",
    "case (d = Comp_H3.M.j{2}) => [->|?].",
    "smt(get_setE mem_set remE mem_rem emptyE).",
    "smt(get_setE mem_set remE mem_rem emptyE).",
];

/// Story 66: two pairs give four cases, in order, each a bullet, and the part is closed.
#[test]
fn two_key_pairs_split_into_four_cases_each_a_bullet() {
    let run = run_key_split(true);
    let split: Vec<_> = run
        .said
        .iter()
        .filter_map(|s| s.strip_prefix("part-fallback "))
        .filter_map(|s| s.strip_suffix(" [equal-output+invariant]"))
        .skip(3)
        .collect();
    assert_eq!(split, KEY_SPLIT, "{:?}", run.said);
    assert!(run.admits.is_empty(), "{:?}", run.admits);
    let script: Vec<_> = run
        .script
        .lines()
        .map(str::trim)
        .filter(|l| l.contains("case (") || l.contains("smt(get"))
        .collect();
    assert_eq!(
        script,
        [
            "case (c = Comp_H3.M.k{2}) => [->|?].",
            "+ case (d = Comp_H3.M.j{2}) => [->|?].",
            "+ smt(get_setE mem_set remE mem_rem emptyE).",
            "+ smt(get_setE mem_set remE mem_rem emptyE).",
            "+ case (d = Comp_H3.M.j{2}) => [->|?].",
            "+ smt(get_setE mem_set remE mem_rem emptyE).",
            "+ smt(get_setE mem_set remE mem_rem emptyE).",
        ],
        "{}",
        run.script
    );
}

/// Story 66: when the last case does not close, the whole split is undone and the part is
/// admitted with the outcome of that last `smt`.
#[test]
fn one_failing_case_undoes_the_whole_split() {
    let run = run_key_split(false);
    let n = run.said.len();
    assert!(run.said[n - 3].starts_with("part-fallback smt("), "{:?}", run.said);
    assert!(run.said[n - 2].starts_with("undo undo "), "{:?}", run.said);
    assert!(run.said[n - 1].starts_with("admit admit."), "{:?}", run.said);
    assert!(!run.script.contains("case ("), "{}", run.script);
    let [admit] = run.admits.as_slice() else {
        panic!("{:?}", run.admits)
    };
    assert_eq!(admit.smt, Some(SmtOutcome::Error));
}

/// Story 66: more than six pairs, and fallback 4 does not run.
#[test]
fn seven_key_pairs_give_no_split() {
    let local = |n: &str| format!(r#"{{"kind":"local","name":"{n}"}}"#);
    let reads: Vec<String> = (0..7)
        .map(|i| {
            let key = format!(r#"{{"kind":"pvar","scope":"local","name":"k{i}","mem":"&1"}}"#);
            let set = format!(
                r#"{{"kind":"app","op":"Top.FMap._.[_<-_]","args":[{},{key},{}]}}"#,
                local("m"),
                local("v")
            );
            format!(r#"{{"kind":"app","op":"Top.FMap._.[_]","args":[{set},{}]}}"#, local("c"))
        })
        .collect();
    let body = format!(r#"{{"kind":"app","pp":"","op":"Top.P","args":[{}]}}"#, reads.join(","));
    let binder = r#"{"name":"c","kind":"var","type":{"pp":"int"}}"#;
    let all = format!(
        r#"{{"kind":"quant","pp":"","quantifier":"forall","binders":[{binder}],"body":{body}}}"#
    );
    let goals = [
        ("start", proof_of(&program_with_ifs(&[], &[]), 1)),
        ("all", proof_of(&formula(&all), 1)),
        ("p1", proof_of(&formula(&body), 1)),
    ];
    let arms = r#"
    "auto => &1 &2 hpre.") g=all; ans;;
    "move => c /=.") g=p1; ans;;
    admit.) g=none; ans;;"#;
    let run = run_leaf(&goals, "start", arms, vec![], &[]);
    assert!(!run.said.iter().any(|s| s.contains("case (")), "{:?}", run.said);
    assert_eq!(run.admits.len(), 1);
}

/// Story 69: the side-invariant jobs, and what `--proofstep`, `--side-inv` and a whole-theorem
/// run start.
mod side_invariant_jobs {
    use std::path::PathBuf;

    use super::*;
    use crate::easycrypt::session::{json_binary_configured, locate_binary};
    use crate::project::{DirectoryFiles, DirectoryProject};
    use crate::writers::easycrypt::export::{export_theorem, write_files, ExportedTheorem};

    const STORY58: &str = "testdata/easycrypt/story58";

    fn project() -> DirectoryProject<'static> {
        let dir = PathBuf::from(STORY58);
        let files = Box::leak(Box::new(DirectoryFiles::load(&dir).unwrap()));
        DirectoryProject::load(dir, files).unwrap()
    }

    fn exported(project: &DirectoryProject<'static>) -> ExportedTheorem {
        export_theorem(project.get_theorem("OneSided").unwrap(), project).unwrap()
    }

    #[test]
    fn a_proofstep_whose_side_invariant_files_are_missing_does_not_start_and_warns() {
        let exported = exported(&project());
        let out = tempfile::tempdir().unwrap();
        let options = TacticsOptions {
            proofstep: Some(0),
            ..TacticsOptions::default()
        };
        let plan = plan_run(&exported, out.path(), &options).unwrap();
        assert!(plan.equivalences.is_empty(), "the equivalence does not start");
        assert!(plan.side.is_empty(), "a proof job never proves side invariants");
        assert_eq!(plan.unproved, ["Game"]);
        assert_eq!(
            unproved_side_invariants_line("Game"),
            "warning: side invariants of Game are not proved: run prove --side-inv Game first"
        );
        // one file missing is enough
        write_files(out.path(), &exported.files).unwrap();
        std::fs::remove_file(out.path().join("SideInv_Game_Inc.ec")).unwrap();
        let plan = plan_run(&exported, out.path(), &options).unwrap();
        assert!(plan.equivalences.is_empty());
        assert_eq!(plan.unproved, ["Game"]);
        // on disk, with admits (a partial proof): the equivalence starts
        write_files(out.path(), &exported.files).unwrap();
        let plan = plan_run(&exported, out.path(), &options).unwrap();
        assert_eq!(plan.equivalences.len(), 1);
        assert!(plan.unproved.is_empty());
    }

    /// No EasyCrypt runs: the plan starts nothing, and the result says why.
    #[test]
    fn a_proofstep_run_without_side_invariant_files_starts_no_job_and_its_report_says_why() {
        let project = project();
        let exported = exported(&project);
        let out = tempfile::tempdir().unwrap();
        let options = TacticsOptions {
            proofstep: Some(0),
            ..TacticsOptions::default()
        };
        let result = run_tactics(
            project.get_theorem("OneSided").unwrap(),
            &project,
            &exported,
            out.path(),
            &crate::util::smtsolver::process::IncrementalCvc5Backend,
            &options,
        )
        .unwrap();
        assert!(result.equivalences.is_empty() && result.side_invariants.is_empty());
        assert_eq!(result.unproved_side_invariants, ["Game"]);
        assert!(
            result
                .render()
                .contains("side invariants of Game are not proved: run prove --side-inv Game first"),
            "{}",
            result.render()
        );
        assert!(!out.path().join("progress").exists(), "no job started");
    }

    #[test]
    fn side_inv_plans_only_its_job_and_a_whole_theorem_run_plans_both_kinds() {
        let exported = exported(&project());
        let out = tempfile::tempdir().unwrap();
        let only = TacticsOptions {
            side_inv: Some("Game".into()),
            ..TacticsOptions::default()
        };
        let plan = plan_run(&exported, out.path(), &only).unwrap();
        assert!(plan.equivalences.is_empty());
        let [(report, composition)] = plan.side.as_slice() else {
            panic!("one side-invariant job");
        };
        assert_eq!(composition, "Game");
        // its records, trees and locks are under `SideInv_<C>`
        assert_eq!(report.proof_file, "SideInv_Game.ec");
        assert_eq!(
            report.oracle_files,
            [("Inc".to_string(), "SideInv_Game_Inc.ec".to_string())]
        );
        let whole = plan_run(&exported, out.path(), &TacticsOptions::default()).unwrap();
        assert_eq!(whole.equivalences.len(), 1);
        assert_eq!(whole.side.len(), 1);
        let none = TacticsOptions {
            side_inv: Some("Nothing".into()),
            ..TacticsOptions::default()
        };
        assert!(matches!(
            plan_run(&exported, out.path(), &none),
            Err(TacticsError::NoSideInvariants { composition }) if composition == "Nothing"
        ));
    }

    /// The side-invariant lemma files belong to the side-invariant job: a proof job does not
    /// create them, and `SideInv_<C>.ec` is a translation file.
    #[test]
    fn only_the_side_invariant_lemma_files_are_owned_by_the_side_invariant_job() {
        let exported = exported(&project());
        use crate::easycrypt::job::is_oracle_file;
        assert!(is_oracle_file(&exported, Path::new("SideInv_Game_Inc.ec")));
        assert!(!is_oracle_file(&exported, Path::new("SideInv_Game.ec")));
        assert!(is_oracle_file(&exported, Path::new("Eq_L_R_Inc.ec")));
    }

    // ------------------------------------------------------------------
    // Live: a `-json` EasyCrypt (`DOMINO_EASYCRYPT`) and `cvc5` on `PATH`
    // ------------------------------------------------------------------

    fn backend() -> crate::util::smtsolver::process::IncrementalCvc5Backend {
        crate::util::smtsolver::process::IncrementalCvc5Backend
    }

    fn prove(
        project: &DirectoryProject<'static>,
        exported: &ExportedTheorem,
        out: &Path,
        options: &TacticsOptions,
    ) -> TheoremTactics {
        let theorem = project.get_theorem("OneSided").unwrap();
        run_tactics(theorem, project, exported, out, &backend(), options).unwrap()
    }

    fn compiles(dir: &Path, file: &str) -> Result<(), String> {
        let output = std::process::Command::new(locate_binary())
            .args(["compile", "-I"])
            .arg(dir)
            .arg(file)
            .current_dir(dir)
            .output()
            .map_err(|e| e.to_string())?;
        if output.status.success() {
            Ok(())
        } else {
            Err(String::from_utf8_lossy(&output.stderr).into_owned())
        }
    }

    /// Symbolic-execution story 25's composition `S`: a branch on the free parameter `n`, then
    /// one on the argument `x`, where `x < 0` breaks the package invariant `k >= 0`. Each branch
    /// is an `if.` with a bullet for each arm, and the two terminals where the invariant breaks
    /// are admitted with Domino's verdict, without EasyCrypt time spent on them.
    #[test]
    fn a_side_tree_with_branches_is_walked_with_if_and_its_failing_claim_is_admitted() {
        if !json_binary_configured() {
            eprintln!("DOMINO_EASYCRYPT not set, skipping");
            return;
        }
        let dir = PathBuf::from("testdata/debug/se25");
        let files = Box::leak(Box::new(DirectoryFiles::load(&dir).unwrap()));
        let project = DirectoryProject::load(dir, files).unwrap();
        let theorem = project.get_theorem("T").unwrap();
        let exported = export_theorem(theorem, &project).unwrap();
        let out = tempfile::tempdir().unwrap();
        write_files(out.path(), &exported.files).unwrap();
        let options = TacticsOptions {
            side_inv: Some("S".into()),
            quick_close: false,
            ..TacticsOptions::default()
        };
        let result = run_tactics(theorem, &project, &exported, out.path(), &backend(), &options)
            .unwrap();
        let [job] = result.side_invariants.as_slice() else {
            panic!("one side-invariant job: {}", result.render());
        };
        let [o] = job.oracles.as_slice() else {
            panic!("one oracle: {}", result.render());
        };
        assert_eq!(o.joint_paths, 4, "{}", result.render());
        let lemma = std::fs::read_to_string(out.path().join("SideInv_S_O.ec")).unwrap();
        // the router prelude's `if.`, and one for each branch of the side tree
        assert!(lemma.matches("if.").count() >= 3, "{lemma}");
        assert!(!o.stats.admits.is_empty(), "{}", result.render());
        for a in &o.stats.admits {
            assert_eq!(a.reason, AdmitReason::DominoFails, "{}", result.render());
            assert_eq!(a.claim, "invariant/PkgInv_main_of_p_in_S", "{}", result.render());
        }
        compiles(out.path(), "SideInv_S_O.ec").unwrap();
    }

    /// Story 73: a package with two named invariants, where a path breaks only `nonneg`: only
    /// the leaf parts of `nonneg` are admitted, with Domino's verdict.
    #[test]
    fn a_path_that_breaks_one_named_invariant_admits_only_its_leaf_part() {
        if !json_binary_configured() {
            eprintln!("DOMINO_EASYCRYPT not set, skipping");
            return;
        }
        let dir = PathBuf::from("testdata/debug/ec73");
        let files = Box::leak(Box::new(DirectoryFiles::load(&dir).unwrap()));
        let project = DirectoryProject::load(dir, files).unwrap();
        let theorem = project.get_theorem("T").unwrap();
        let exported = export_theorem(theorem, &project).unwrap();
        let out = tempfile::tempdir().unwrap();
        write_files(out.path(), &exported.files).unwrap();
        let options = TacticsOptions {
            side_inv: Some("S".into()),
            quick_close: false,
            ..TacticsOptions::default()
        };
        let result = run_tactics(theorem, &project, &exported, out.path(), &backend(), &options)
            .unwrap();
        let [job] = result.side_invariants.as_slice() else {
            panic!("one side-invariant job: {}", result.render());
        };
        let [o] = job.oracles.as_slice() else {
            panic!("one oracle: {}", result.render());
        };
        assert!(!o.stats.admits.is_empty(), "{}", result.render());
        for a in &o.stats.admits {
            assert_eq!(a.reason, AdmitReason::DominoFails, "{}", result.render());
            assert_eq!(a.claim, "invariant/PkgInv_nonneg_of_p_in_S", "{}", result.render());
        }
        compiles(out.path(), "SideInv_S_O.ec").unwrap();
    }

    /// `prove --side-inv Game`: one-sided execution of `Inc`, then its `hoare` lemma proved
    /// along the side tree, with no admit; then the equivalence, and the glue joins them.
    #[test]
    fn side_inv_proves_the_hoare_lemma_along_the_side_tree_and_the_glue_compiles() {
        if !json_binary_configured() {
            eprintln!("DOMINO_EASYCRYPT not set, skipping");
            return;
        }
        let project = project();
        let exported = exported(&project);
        let out = tempfile::tempdir().unwrap();
        write_files(out.path(), &exported.files).unwrap();
        let options = TacticsOptions {
            side_inv: Some("Game".into()),
            quick_close: false,
            ..TacticsOptions::default()
        };
        let result = prove(&project, &exported, out.path(), &options);
        assert!(result.equivalences.is_empty());
        let [job] = result.side_invariants.as_slice() else {
            panic!("one side-invariant job: {}", result.render());
        };
        assert_eq!(job.composition.as_deref(), Some("Game"));
        let [inc] = job.oracles.as_slice() else {
            panic!("one oracle: {}", result.render());
        };
        assert!(inc.problem.is_none(), "{}", result.render());
        assert!(inc.joint_paths > 0, "the walk followed a side tree: {}", result.render());
        assert!(inc.stats.admits.is_empty(), "{}", result.render());
        assert!(result.render().contains("tactics for SideInv_Game.ec (side invariants of Game)"));
        let lemma = std::fs::read_to_string(out.path().join("SideInv_Game_Inc.ec")).unwrap();
        assert!(!lemma.contains("proc; inline. admit."), "{lemma}");
        // the router prelude, then the leaf of the one terminal, opened by claim
        for step in ["sp 1.", "if.", "auto => &hr hpre /=.", "rewrite /Comp_Game.PkgInv_main_of_C_in_Game /=."] {
            assert!(lemma.contains(step), "{step} in:\n{lemma}");
        }
        for f in ["session/SideInv_Game/Inc.record.json", "session/SideInv_Game/Inc.tree.json"] {
            assert!(out.path().join(f).is_file(), "{f}");
        }
        assert!(!out.path().join("progress/SideInv_Game/Inc.lock").exists(), "the lock is released");
        compiles(out.path(), "SideInv_Game_Inc.ec").unwrap();

        // the equivalence: its oracle lemma assumes the side invariants
        let options = TacticsOptions {
            proofstep: Some(0),
            ..TacticsOptions::default()
        };
        let result = prove(&project, &exported, out.path(), &options);
        assert!(result.unproved_side_invariants.is_empty());
        assert_eq!(result.equivalences.len(), 1, "{}", result.render());
        assert_eq!(result.admit_count(), 0, "{}", result.render());
        compiles(out.path(), "Eq_L_R.ec").unwrap();
    }

    /// An EasyCrypt that logs `start` and `end` lines to `log` around the real one.
    fn logging_easycrypt(dir: &Path, log: &Path) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let script = dir.join("logging-easycrypt");
        std::fs::write(
            &script,
            format!(
                "#!/bin/sh\necho start >> '{log}'\n'{real}' \"$@\" <&0 &\nec=$!\n\
                 ( while kill -0 $ec 2>/dev/null; do sleep 0.05; done; echo end >> '{log}' ) \
                 </dev/null >/dev/null 2>&1 &\nwait $ec\n",
                log = log.display(),
                real = locate_binary().display()
            ),
        )
        .unwrap();
        std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).unwrap();
        script
    }

    /// Story 69 §3.3: a whole-theorem run starts the side-invariant job beside the proof job.
    #[test]
    fn a_whole_theorem_prove_runs_a_side_invariant_job_and_a_proof_job_at_the_same_time() {
        if !json_binary_configured() {
            eprintln!("DOMINO_EASYCRYPT not set, skipping");
            return;
        }
        let project = project();
        let exported = exported(&project);
        let out = tempfile::tempdir().unwrap();
        write_files(out.path(), &exported.files).unwrap();
        let fake = tempfile::tempdir().unwrap();
        let log = fake.path().join("log");
        TEST_EASYCRYPT.with(|t| {
            *t.borrow_mut() = Some(FakeEasyCrypt {
                binary: logging_easycrypt(fake.path(), &log),
                grace: Duration::from_millis(1_500),
                resend: Duration::from_millis(250),
            })
        });
        let result = prove(&project, &exported, out.path(), &TacticsOptions::default());
        TEST_EASYCRYPT.with(|t| t.borrow_mut().take());
        let began = Instant::now();
        while began.elapsed() < Duration::from_secs(10) {
            let text = std::fs::read_to_string(&log).unwrap();
            if text.matches("start").count() == text.matches("end").count() {
                break;
            }
            std::thread::sleep(Duration::from_millis(100));
        }
        let (mut running, mut most, mut started) = (0, 0, 0);
        for line in std::fs::read_to_string(&log).unwrap().lines() {
            if line == "start" {
                running += 1;
                started += 1;
            } else {
                running -= 1;
            }
            most = most.max(running);
        }
        assert_eq!(started, 2, "one EasyCrypt for each job's oracle");
        assert_eq!(most, 2, "the two jobs at the same time");
        assert_eq!(result.equivalences.len(), 1, "{}", result.render());
        assert_eq!(result.side_invariants.len(), 1, "{}", result.render());
    }
}
