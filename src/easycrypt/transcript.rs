// SPDX-License-Identifier: MIT OR Apache-2.0

//! The records of the EasyCrypt transcript, `progress/ec-transcript.jsonl` (story 27 §3.7,
//! bounded by story 31).
//!
//! One record per sentence sent, one JSON object per line:
//! `{"file": <tag>, "ctx": <the caller's note>, "sentence": …, "ms": …, "response": …}`, with
//! `"interrupts": <n>` before `response` when the sentence took `n` > 0 interrupts to stop.
//! [`EcTranscriptMode::Full`] writes EasyCrypt's answer verbatim as `response`, which prints
//! every open goal in full, 100–700 kB per record. [`EcTranscriptMode::Capped`] (the default)
//! writes the same answer with its goals cut to what the live page embeds ([`cap_response`]):
//! the first goal only, split into its conclusion (cut at [`GOAL_CONCL_CAP`] characters) and its
//! hypotheses (cut at [`GOAL_HYPS_CAP`]), so at most ~5 kB of goal text per record (story 51;
//! story 41 kept ~2 kB of the goal's start, story 31 3 goals of 12 000).
//!
//! **The byte offsets constraint.** The live page (`tactics::live`) remembers where each record
//! starts in the file (byte offset and length) and reads goal text back from there. Anything that
//! rewrites, compacts, reorders, rotates or compresses the file after it is written invalidates
//! every offset it holds. The transcript is bounded by making each record small *as it is
//! written*, never by post-processing the file: if the capped size is ever too large, cap harder
//! here.

use serde::de::{MapAccess, Visitor};
use serde::Deserialize as _;
use serde_derive::{Deserialize, Serialize};
use serde_json::value::RawValue;

/// The most goals of one answer kept in a capped record, and embedded per step in the live page.
///
/// A contract between the transcript and the page: a capped record holds exactly what the page
/// shows, so the page renders the same from either mode. Defined here and nowhere else.
pub const GOALS_PER_STEP: usize = 1;
/// The most characters of one goal's conclusion kept in a capped record, and embedded in the page
/// (see [`GOALS_PER_STEP`]). A longer conclusion keeps its head and its tail.
pub const GOAL_CONCL_CAP: usize = 4_000;
/// How much of a cut conclusion is its head; the rest of [`GOAL_CONCL_CAP`] is its tail (the
/// post-condition). The page finds the cut from it.
pub const GOAL_CONCL_HEAD: usize = GOAL_CONCL_CAP * 3 / 5;
/// The most characters of one goal's hypotheses kept in a capped record, cut at the end.
pub const GOAL_HYPS_CAP: usize = 1_000;

/// One goal as the page shows it: what `cli` prints below the separator rule (the conclusion),
/// and above it (the hypotheses, one per line), each cut to its cap with the characters cut.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct GoalParts {
    pub concl: String,
    pub concl_cut: usize,
    pub hyps: String,
    pub hyps_cut: usize,
}

impl GoalParts {
    /// The parts of a goal's `text`, cut to the caps. A text without the rule is all conclusion.
    pub fn of_text(text: &str) -> GoalParts {
        let (hyps, concl) = split_at_rule(text);
        let (concl, concl_cut) = cut_middle(concl.trim_matches('\n'));
        let hyps = hyps.trim_matches('\n');
        let hyps_chars = hyps.chars().count();
        GoalParts {
            concl,
            concl_cut,
            hyps: hyps.chars().take(GOAL_HYPS_CAP).collect(),
            hyps_cut: hyps_chars.saturating_sub(GOAL_HYPS_CAP),
        }
    }

    /// The conclusion around its cut: the whole conclusion and `""` when nothing was cut.
    pub fn concl_head_tail(&self) -> (&str, &str) {
        if self.concl_cut == 0 {
            return (&self.concl, "");
        }
        let at = self
            .concl
            .char_indices()
            .nth(GOAL_CONCL_HEAD)
            .map_or(self.concl.len(), |(i, _)| i);
        self.concl.split_at(at)
    }
}

/// `(hypotheses, conclusion)`: the text above and below the first line made only of `-`.
fn split_at_rule(text: &str) -> (&str, &str) {
    let mut start = 0;
    for line in text.split_inclusive('\n') {
        let rule = line.trim_end();
        if rule.len() >= 10 && rule.bytes().all(|b| b == b'-') {
            return (&text[..start], &text[start + line.len()..]);
        }
        start += line.len();
    }
    ("", text)
}

/// `text` cut to [`GOAL_CONCL_CAP`] characters by dropping its middle, and how many were cut.
fn cut_middle(text: &str) -> (String, usize) {
    let chars = text.chars().count();
    if chars <= GOAL_CONCL_CAP {
        return (text.to_string(), 0);
    }
    let tail = GOAL_CONCL_CAP - GOAL_CONCL_HEAD;
    let mut kept: String = text.chars().take(GOAL_CONCL_HEAD).collect();
    kept.extend(text.chars().skip(chars - tail));
    (kept, chars - GOAL_CONCL_CAP)
}

/// What `ec-transcript.jsonl` holds of EasyCrypt's answers (`--ec-transcript`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum EcTranscriptMode {
    /// Goals cut to the page's limits ([`cap_response`]). A failed write drops the transcript
    /// with a warning and the run goes on.
    #[default]
    Capped,
    /// EasyCrypt's answers verbatim (story 27). A failed write fails the run.
    Full,
}

/// One transcript record, with its line break. `answer` is the line EasyCrypt answered with.
pub fn record(
    mode: EcTranscriptMode,
    tag: &str,
    context: &str,
    sentence: &str,
    ms: u128,
    interrupts: usize,
    answer: &str,
) -> String {
    let answer = answer.trim_end();
    let capped = match mode {
        EcTranscriptMode::Full => None,
        EcTranscriptMode::Capped => cap_response(answer),
    };
    // how hard the sentence was to stop: only on a sentence that was interrupted
    let interrupts = match interrupts {
        0 => String::new(),
        n => format!("\"interrupts\":{n},"),
    };
    format!(
        "{{\"file\":{},\"ctx\":{},\"sentence\":{},\"ms\":{ms},{interrupts}\"response\":{}}}\n",
        serde_json::Value::from(tag),
        serde_json::Value::from(context),
        serde_json::Value::from(sentence),
        capped.as_deref().unwrap_or(answer)
    )
}

/// EasyCrypt's answer with its goals cut to the page's limits, or `None` if it is not a JSON
/// object (the caller then writes it verbatim).
///
/// Every field but `proof` is kept verbatim and in order: `status`, `state`, `error` and
/// `messages` are small and the page shows them all. `proof.goals` keeps its first
/// [`GOALS_PER_STEP`] goals, each reduced to its `id` and the [`GoalParts`] of its `text`, and
/// says what was cut:
///
/// ```json
/// "proof": {"goals_dropped": 7, "goals": [{"id": 1, "concl": "…", "concl_cut": 41000,
///                                          "hyps": "…", "hyps_cut": 3000}]}
/// ```
///
/// The structured goal (`hyps`, `concl`, …) is what makes an answer large, and nothing reads it
/// back from the transcript. Its `concl.pp` prints the programs as `{...}`, so the conclusion is
/// taken from `text`. `goals_dropped` is always written, so a capped record is told from a full
/// one by its presence.
pub fn cap_response(answer: &str) -> Option<String> {
    let fields = serde_json::from_str::<Fields>(answer).ok()?.0;
    let mut out = String::with_capacity(
        answer
            .len()
            .min(4 * (GOAL_CONCL_CAP + GOAL_HYPS_CAP) * GOALS_PER_STEP),
    );
    out.push('{');
    for (i, (key, value)) in fields.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&serde_json::Value::from(key.as_str()).to_string());
        out.push(':');
        match (key.as_str(), capped_proof(value)) {
            ("proof", Some(proof)) => out.push_str(&proof),
            _ => out.push_str(value.get()),
        }
    }
    out.push('}');
    Some(out)
}

/// The top-level fields of an answer, in order, each kept as the text it was written as.
/// Scanning a [`RawValue`] does not recurse, so a deeply nested goal needs no extra stack.
struct Fields(Vec<(String, Box<RawValue>)>);

impl<'de> serde::Deserialize<'de> for Fields {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct FieldsVisitor;
        impl<'de> Visitor<'de> for FieldsVisitor {
            type Value = Fields;
            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                f.write_str("a JSON object")
            }
            fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Fields, A::Error> {
                let mut fields = Vec::new();
                while let Some(entry) = map.next_entry::<String, Box<RawValue>>()? {
                    fields.push(entry);
                }
                Ok(Fields(fields))
            }
        }
        deserializer.deserialize_map(FieldsVisitor)
    }
}

#[derive(Deserialize)]
struct ProofText {
    goals: Vec<GoalText>,
}

#[derive(Deserialize)]
struct GoalText {
    id: Box<RawValue>,
    #[serde(default)]
    text: String,
}

/// `proof` cut as [`cap_response`] says, or `None` if it is not a proof with goals (`null`).
fn capped_proof(proof: &RawValue) -> Option<String> {
    // unknown fields are skipped without recursing, like `RawValue`
    let proof: ProofText =
        ProofText::deserialize(&mut serde_json::Deserializer::from_str(proof.get())).ok()?;
    let goals_dropped = proof.goals.len().saturating_sub(GOALS_PER_STEP);
    let goals: Vec<String> = proof
        .goals
        .into_iter()
        .take(GOALS_PER_STEP)
        .map(|goal| {
            let parts = serde_json::to_string(&GoalParts::of_text(&goal.text)).ok()?;
            Some(format!("{{\"id\":{},{}", goal.id.get(), &parts[1..]))
        })
        .collect::<Option<_>>()?;
    Some(format!(
        "{{\"goals_dropped\":{goals_dropped},\"goals\":[{}]}}",
        goals.join(",")
    ))
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    /// An answer as `easycrypt cli -json` writes it, with `n` goals of `chars` characters each.
    pub(crate) fn answer_with_goals(n: usize, chars: usize) -> String {
        let goals: Vec<String> = (1..=n)
            .map(|id| {
                format!(
                    "{{\"id\":{id},\"tvars\":[],\"hyps\":[{{\"name\":\"x\",\"kind\":\"var\"}}],\"concl\":{{\"kind\":\"app\",\"pp\":\"c\",\"args\":[{{\"kind\":\"local\",\"pp\":\"x\"}}]}},\"text\":{}}}",
                    serde_json::Value::from("é".repeat(chars))
                )
            })
            .collect();
        format!(
            "{{\"version\":\"domino-json/1\",\"state\":7,\"status\":\"error\",\"error\":{{\"loc\":{{\"start\":0,\"end\":4}},\"msg\":\"no\"}},\"messages\":[{{\"level\":\"warning\",\"text\":\"careful\"}}],\"proof\":{{\"goals\":[{}]}}}}",
            goals.join(",")
        )
    }

    #[test]
    fn a_capped_answer_keeps_the_first_goal_cut_to_the_caps_and_says_what_it_cut() {
        let answer = answer_with_goals(10, 50_000);
        let capped = cap_response(&answer).unwrap();
        let v: serde_json::Value = serde_json::from_str(&capped).unwrap();
        let goals = v["proof"]["goals"].as_array().unwrap();
        assert_eq!(goals.len(), GOALS_PER_STEP);
        assert_eq!(goals.len(), 1);
        assert_eq!(v["proof"]["goals_dropped"], 9);
        for (i, goal) in goals.iter().enumerate() {
            assert_eq!(goal["id"], i + 1);
            assert_eq!(
                goal["concl"].as_str().unwrap().chars().count(),
                GOAL_CONCL_CAP
            );
            assert_eq!(goal["concl_cut"], 50_000 - GOAL_CONCL_CAP);
            assert_eq!(goal["hyps"], "");
            assert_eq!(goal["hyps_cut"], 0);
            assert!(goal.get("text").is_none());
        }
        // everything else is intact, in order
        let full: serde_json::Value = serde_json::from_str(&answer).unwrap();
        for key in ["version", "state", "status", "error", "messages"] {
            assert_eq!(v[key], full[key], "{key}");
        }
        assert!(capped.starts_with("{\"version\":\"domino-json/1\",\"state\":7,\"status\":\"error\",\"error\":{\"loc\":{\"start\":0,\"end\":4},\"msg\":\"no\"},\"messages\":[{\"level\":\"warning\",\"text\":\"careful\"}],\"proof\":"));
        assert!(
            capped.len() < (GOAL_CONCL_CAP + GOAL_HYPS_CAP) * 2 + 1_000,
            "{}",
            capped.len()
        );
    }

    #[test]
    fn a_five_goal_answer_holds_one_goal_and_says_four_were_dropped() {
        let v: serde_json::Value =
            serde_json::from_str(&cap_response(&answer_with_goals(5, 10)).unwrap()).unwrap();
        assert_eq!(v["proof"]["goals"].as_array().unwrap().len(), 1);
        assert_eq!(v["proof"]["goals"][0]["id"], 1);
        assert_eq!(v["proof"]["goals_dropped"], 4);
    }

    #[test]
    fn short_goals_and_answers_without_a_proof_are_kept_whole() {
        let answer = answer_with_goals(1, 10);
        let v: serde_json::Value = serde_json::from_str(&cap_response(&answer).unwrap()).unwrap();
        assert_eq!(v["proof"]["goals_dropped"], 0);
        assert_eq!(v["proof"]["goals"][0]["concl"], "é".repeat(10));
        assert_eq!(v["proof"]["goals"][0]["concl_cut"], 0);
        let no_proof = "{\"version\":\"domino-json/1\",\"state\":0,\"status\":\"ok\",\"messages\":[],\"proof\":null}";
        assert_eq!(cap_response(no_proof).unwrap(), no_proof);
        assert_eq!(cap_response("not json"), None);
    }

    #[test]
    fn a_full_record_is_the_story_27_record_byte_for_byte() {
        let answer =
            std::fs::read_to_string("testdata/easycrypt/story31/answer-two-goals.json").unwrap();
        let record = record(
            EcTranscriptMode::Full,
            "Eq.ec",
            "O N0",
            "split.",
            12,
            0,
            &answer,
        );
        assert_eq!(
            record,
            format!(
                "{{\"file\":\"Eq.ec\",\"ctx\":\"O N0\",\"sentence\":\"split.\",\"ms\":12,\"response\":{}}}\n",
                answer.trim_end()
            )
        );
    }

    #[test]
    fn a_capped_record_of_a_real_answer_holds_its_goal_texts() {
        let answer =
            std::fs::read_to_string("testdata/easycrypt/story31/answer-two-goals.json").unwrap();
        let record = record(EcTranscriptMode::Capped, "Eq.ec", "", "split.", 12, 0, &answer);
        assert!(record.ends_with("}\n") && record.lines().count() == 1);
        let v: serde_json::Value = serde_json::from_str(&record).unwrap();
        let full: serde_json::Value = serde_json::from_str(&answer).unwrap();
        let goals = full["proof"]["goals"].as_array().unwrap();
        assert_eq!(goals.len(), 2);
        for (capped, full) in v["response"]["proof"]["goals"]
            .as_array()
            .unwrap()
            .iter()
            .zip(goals)
        {
            let parts = GoalParts::of_text(full["text"].as_str().unwrap());
            assert_eq!(capped["concl"], parts.concl.as_str());
            assert_eq!(capped["hyps"], parts.hyps.as_str());
            assert_eq!(capped["id"], full["id"]);
        }
        assert!(record.len() < answer.len());
    }

    const RULE: &str = "--------------------------------------------------------------------------";

    #[test]
    fn a_goal_splits_at_the_rule_into_hypotheses_and_conclusion() {
        let parts = GoalParts::of_text(&format!(
            "Type variables: <none>\n\nx: int\ny: int\n{RULE}\nx + y = y + x\n"
        ));
        assert_eq!(parts.hyps, "Type variables: <none>\n\nx: int\ny: int");
        assert_eq!(parts.concl, "x + y = y + x");
        assert_eq!((parts.concl_cut, parts.hyps_cut), (0, 0));
        assert_eq!(parts.concl_head_tail(), ("x + y = y + x", ""));
    }

    #[test]
    fn a_goal_without_hypotheses_is_all_conclusion() {
        let parts = GoalParts::of_text("x = x\n");
        assert_eq!(parts.concl, "x = x");
        assert_eq!(parts.hyps, "");
        let parts = GoalParts::of_text(&format!("{RULE}\nx = x\n"));
        assert_eq!((parts.hyps.as_str(), parts.concl.as_str()), ("", "x = x"));
    }

    #[test]
    fn a_long_conclusion_keeps_its_head_and_tail_and_counts_the_middle() {
        let concl = format!(
            "{}{}{}",
            "h".repeat(GOAL_CONCL_HEAD),
            "m".repeat(3_412),
            "t".repeat(GOAL_CONCL_CAP - GOAL_CONCL_HEAD)
        );
        let parts = GoalParts::of_text(&format!("x: int\n{RULE}\n{concl}"));
        assert_eq!(parts.concl_cut, 3_412);
        assert_eq!(parts.concl.chars().count(), GOAL_CONCL_CAP);
        let (head, tail) = parts.concl_head_tail();
        assert_eq!(head, "h".repeat(GOAL_CONCL_HEAD));
        assert_eq!(tail, "t".repeat(GOAL_CONCL_CAP - GOAL_CONCL_HEAD));
    }

    #[test]
    fn long_hypotheses_are_cut_at_the_end_and_counted() {
        let hyps = "é".repeat(GOAL_HYPS_CAP + 77);
        let parts = GoalParts::of_text(&format!("{hyps}\n{RULE}\npost"));
        assert_eq!(parts.hyps, "é".repeat(GOAL_HYPS_CAP));
        assert_eq!(parts.hyps_cut, 77);
        assert_eq!(parts.concl, "post");
    }

    #[test]
    fn a_real_program_goal_keeps_the_judgment_with_its_post_condition() {
        let answer = std::fs::read_to_string(
            "testdata/easycrypt/story25/hello_world_useful_oracle_after_inline.json",
        )
        .unwrap();
        let capped: serde_json::Value =
            serde_json::from_str(&cap_response(&answer).unwrap()).unwrap();
        let goal = &capped["proof"]["goals"][0];
        let concl = goal["concl"].as_str().unwrap();
        assert!(concl.starts_with("&1 (left ) : {"), "{concl}");
        assert!(concl.contains("pre =") && concl.contains("post ="), "{concl}");
        assert_eq!(goal["hyps"], "Type variables: <none>\n\n&m: {}");
    }
}
