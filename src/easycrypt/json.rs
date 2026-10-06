// SPDX-License-Identifier: MIT OR Apache-2.0

//! The Rust mirror of `easycrypt cli -json` (format `domino-json/2`, specified in
//! `easycrypt/doc/json-output.md`).
//!
//! The mirror is lenient on purpose: every field a consumer does not read is left out, every
//! optional field defaults, and node kinds are kept as strings, because the format may gain
//! fields and kinds without a version change ("readers must ignore what they do not know").
//! [`Form`] therefore is one struct carrying the union of the fields of the kinds this crate
//! reads, not an enum.

use serde::Deserialize as _;
use serde_derive::Deserialize;

/// The only format version this module understands.
pub const FORMAT_VERSION: &str = "domino-json/2";

/// The answer to one sentence.
#[derive(Debug, Clone, Deserialize)]
pub struct Response {
    pub version: String,
    /// The undo depth after the sentence: `undo <state>.` returns to this state.
    pub state: u64,
    pub status: Status,
    #[serde(default)]
    pub error: Option<EcError>,
    #[serde(default)]
    pub messages: Vec<Message>,
    /// `None` when there is no active proof.
    #[serde(default)]
    pub proof: Option<Proof>,
    /// Where EasyCrypt spent the time of the sentence. `None` from a binary older than story 55. Boxed, as
    /// `Proof::front`, to keep `session::Wait` small.
    #[serde(default)]
    pub timing: Option<Box<Timing>>,
}

impl Response {
    /// Whether the answer lost its goals: an interrupt that lands while EasyCrypt prints them
    /// leaves the answer without them, with a `critical` message saying so (story 34). The
    /// sentence's effect on the state stands.
    pub fn goals_lost(&self) -> bool {
        self.proof.is_none()
            && self
                .messages
                .iter()
                .any(|m| m.text.starts_with("cannot serialize the goals"))
    }

    /// The head of the message that shows EasyCrypt swallowed an interrupt: a prover dropped
    /// with `error when starting …` because of `Sys.Break`, the sentence carrying on as if no
    /// interrupt had come (story `easycrypt-never-swallows-an-interrupt`). The status is still
    /// truthful. `cannot serialize the goals: …Sys.Break` is not a swallow ([`Self::goals_lost`]).
    pub fn swallowed_interrupt(&self) -> Option<String> {
        /// Enough of the message to recognise it in a one-line warning.
        const HEAD_CHARS: usize = 160;
        let text = &self
            .messages
            .iter()
            .find(|m| m.text.contains("error when starting") && m.text.contains("Sys.Break"))?
            .text;
        let line = text.lines().next().unwrap_or_default();
        Some(line.chars().take(HEAD_CHARS).collect())
    }
}

/// `timing` of an answer, in milliseconds of a monotonic clock (see EasyCrypt's
/// `doc/json-output.md`). `tactic_ms + serialize_ms` is at most the wall time of the sentence.
#[derive(Debug, Clone, Copy, Deserialize)]
pub struct Timing {
    /// The run of the sentence, `smt` included, serialization excluded.
    pub tactic_ms: u64,
    /// The build of `proof`; the write of the line is not in it.
    pub serialize_ms: u64,
    /// `None` when the sentence called no prover.
    #[serde(default)]
    pub smt: Option<SmtTiming>,
}

/// The prover calls of one sentence, summed. `valid + timeout + unknown == calls`.
#[derive(Debug, Clone, Copy, Deserialize)]
pub struct SmtTiming {
    pub calls: u64,
    pub translate_ms: u64,
    /// Why3's preparation of each task; outside the prover's time limit.
    pub prepare_ms: u64,
    pub prover_ms: u64,
    pub valid: u64,
    pub timeout: u64,
    pub unknown: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Status {
    Ok,
    Error,
    Interrupted,
}

#[derive(Debug, Clone, Deserialize)]
pub struct EcError {
    /// Character offsets inside the sentence; `None` if the error has no location.
    #[serde(default)]
    pub loc: Option<Loc>,
    pub msg: String,
}

#[derive(Debug, Clone, Copy, Deserialize)]
pub struct Loc {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Message {
    pub level: String,
    pub text: String,
}

/// The open goals of a proof: the front goal in full, and the kind of each open goal (ADR 0009).
#[derive(Debug, Clone, Deserialize)]
pub struct Proof {
    /// The first open goal; `None` when no goal is open and `qed.` is due.
    pub front: Option<Box<Goal>>,
    /// One entry for each open goal, in order, the front goal included.
    pub kinds: Vec<GoalKind>,
}

/// What [`Proof::kinds`] tells of a goal that is not printed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum GoalKind {
    /// A judgement over two programs (`equivS`).
    Program,
    /// Every other goal.
    Formula,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Goal {
    /// The ordinal of the goal among the open goals, from 1: always 1 for the front goal.
    pub id: u64,
    #[serde(default)]
    pub tvars: Vec<String>,
    #[serde(default)]
    pub hyps: Vec<Hyp>,
    pub concl: Form,
    /// The goal as `cli` prints it.
    #[serde(default)]
    pub text: String,
}

/// A hypothesis. `kind` is `var`, `mem`, `modty`, `hyp` or `abs_st`.
#[derive(Debug, Clone, Deserialize)]
pub struct Hyp {
    pub name: String,
    pub kind: String,
    #[serde(default)]
    pub ident: Option<Ident>,
    #[serde(default, rename = "type")]
    pub ty: Option<Node>,
    #[serde(default)]
    pub form: Option<Form>,
}

/// A binder identity: two binders called `x` have different tags.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Ident {
    pub name: String,
    pub tag: u64,
}

/// A node about which only `kind` and `pp` are read (types, expressions).
#[derive(Debug, Clone, Deserialize)]
pub struct Node {
    #[serde(default)]
    pub kind: String,
    #[serde(default)]
    pub pp: String,
}

/// A formula. Which fields are present depends on `kind` (`equivS`, `equivF`, `app`, `quant`, …);
/// see `json-output.md`. Only a root formula (a conclusion, a hypothesis) has `pp`; a subnode's
/// `pp` is empty.
#[derive(Debug, Clone, Deserialize)]
pub struct Form {
    pub kind: String,
    #[serde(default)]
    pub pp: String,
    /// `app`: the operator path if the head is an operator.
    #[serde(default)]
    pub op: Option<String>,
    #[serde(default)]
    pub head: Option<Box<Form>>,
    /// `app`: the arguments. A `pr` has a single formula (its argument tuple), read as one.
    #[serde(default, deserialize_with = "one_or_many")]
    pub args: Vec<Form>,
    /// `quant`: `forall`, `exists` or `lambda`.
    #[serde(default)]
    pub quantifier: Option<String>,
    #[serde(default)]
    pub binders: Vec<Binder>,
    #[serde(default)]
    pub body: Option<Box<Form>>,
    /// `equivS`: the two programs.
    #[serde(default)]
    pub left: Option<Side>,
    #[serde(default)]
    pub right: Option<Side>,
    #[serde(default)]
    pub pre: Option<Box<Form>>,
    #[serde(default)]
    pub post: Option<Box<Form>>,
}

impl Form {
    /// The two procedures of an `equivF`, `(left, right)`.
    pub fn equiv_procs(&self) -> Option<(&Proc, &Proc)> {
        if self.kind != "equivF" {
            return None;
        }
        Some((self.left.as_ref()?.proc.as_ref()?, self.right.as_ref()?.proc.as_ref()?))
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct Binder {
    pub name: String,
    #[serde(default)]
    pub kind: String,
    #[serde(default)]
    pub ident: Option<Ident>,
}

/// One side of an `equivS` (`stmt` is the program) or `equivF` (`proc`).
#[derive(Debug, Clone, Deserialize)]
pub struct Side {
    #[serde(default)]
    pub mem: String,
    #[serde(default)]
    pub stmt: Vec<Instr>,
    #[serde(default)]
    pub stmt_pp: String,
    #[serde(default)]
    pub proc: Option<Proc>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Proc {
    pub path: String,
    /// The module, `Top.Comp_X.Game_X`.
    pub top: String,
    /// The procedure name.
    pub name: String,
    #[serde(default)]
    pub pp: String,
}

/// A program instruction. `kind` is `asgn`, `rnd`, `call`, `if`, `while`, `match`, `raise` or
/// `abstract`.
#[derive(Debug, Clone, Deserialize)]
pub struct Instr {
    pub kind: String,
    #[serde(default)]
    pub pp: String,
    /// `if`, `while`.
    #[serde(default)]
    pub cond: Option<Node>,
    #[serde(default, rename = "then")]
    pub then_block: Vec<Instr>,
    #[serde(default, rename = "else")]
    pub else_block: Vec<Instr>,
    /// `asgn`, `rnd`, `call`.
    #[serde(default)]
    pub lvalue: Option<LValue>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct LValue {
    #[serde(default)]
    pub pp: String,
}

/// Parses one line of an EasyCrypt answer.
///
/// The recursion limit is off: after a few `sp`s the goals nest a formula deeper than serde's
/// default of 128, and the answer is still well-formed. The caller must have stack for it (the
/// session parses on a thread with a large one).
pub fn parse_response(line: &str) -> Result<Response, serde_json::Error> {
    let mut deserializer = serde_json::Deserializer::from_str(line);
    deserializer.disable_recursion_limit();
    let response = Response::deserialize(&mut deserializer)?;
    deserializer.end()?;
    Ok(response)
}

/// A list of formulas, or a single formula (`pr`'s `args`) as a list of one.
fn one_or_many<'de, D>(deserializer: D) -> Result<Vec<Form>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum OneOrMany {
        Many(Vec<Form>),
        One(Box<Form>),
    }
    Ok(match OneOrMany::deserialize(deserializer)? {
        OneOrMany::Many(v) => v,
        OneOrMany::One(f) => vec![*f],
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const HEAD: &str = r#""version":"domino-json/2","state":1,"status":"ok","messages":[],"proof":null"#;

    #[test]
    fn an_answer_without_timing_parses() {
        let r: Response = serde_json::from_str(&format!("{{{HEAD}}}")).unwrap();
        assert!(r.timing.is_none());
    }

    #[test]
    fn an_answer_with_timing_parses_with_and_without_smt() {
        let smt = r#""smt":{"calls":2,"translate_ms":140,"prepare_ms":95,"prover_ms":6120,"valid":1,"timeout":1,"unknown":0}"#;
        let r: Response = serde_json::from_str(&format!(
            "{{{HEAD},\"timing\":{{\"tactic_ms\":812,\"serialize_ms\":3,{smt}}}}}"
        ))
        .unwrap();
        let t = r.timing.unwrap();
        assert_eq!((t.tactic_ms, t.serialize_ms), (812, 3));
        let s = t.smt.unwrap();
        assert_eq!(
            (s.calls, s.translate_ms, s.prepare_ms, s.prover_ms),
            (2, 140, 95, 6120)
        );
        assert_eq!((s.valid, s.timeout, s.unknown), (1, 1, 0));

        let r: Response = serde_json::from_str(&format!(
            "{{{HEAD},\"timing\":{{\"tactic_ms\":0,\"serialize_ms\":1}}}}"
        ))
        .unwrap();
        assert!(r.timing.unwrap().smt.is_none());
    }
}
