# Story 67 — Resume files go to `session/`, the report to `progress/`

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 35, 36, 37 (the session record, the run-artifact directories, resume), ADR 0008
(saved joint trees).
**Blocks:** 68.

A **layout** story, Rust only. The proof files and the tactics do not change.

---

## 1. Why this story exists

The owner: the session files and the report files make the export directory crowded. Next to each
`Eq_X.ec` today there are `Eq_X.session.json`, one `Eq_X.<Oracle>.tree.json` for each oracle, and
`Eq_X.report.txt`. For Full4WHS that is about 9 × (1 + 12 + 1) = 126 files between the `.ec` files.

The files are of two kinds (`CONTEXT.md`):

- the **session record** and the **saved joint trees** must be protected: losing them loses
  resume;
- the report is a **run artifact**: it is written again on each run and may be overwritten without
  asking.

The code already keeps run artifacts in directories (`RUN_ARTIFACT_DIRS = ["progress", "!debug!"]`,
`src/writers/easycrypt/overwrite.rs:25`), one sub-directory for each equivalence.

Vocabulary (`CONTEXT.md`): **Session record**, **Saved joint tree**, **Run artifact**.

## 2. Inherited from earlier stories

- `session_record_name` and `saved_tree_name` (`src/easycrypt/job.rs:93`, `:99`) are the one owner of
  those names. `progress_dir` (`job.rs:493`) is the owner of `progress/<Eq>/`.
- The report's name: `tactics/mod.rs:867` (`Eq_<L>_<R>.report.txt`).
- `names.rs:120` reserves `progress` as a name that nothing in the export may take.
- `--force` removes session records and saved trees (`job.rs:388`, story 37).

## 3. Work to do

- The session record: `<theorem_out>/session/<Eq>/record.json`.
- Each saved joint tree: `<theorem_out>/session/<Eq>/<Oracle>.tree.json`.
- The report: `<theorem_out>/progress/<Eq>/report.txt`.
- `session` becomes a reserved name next to `progress`. It is **not** a run-artifact directory: the
  overwrite rule protects it, as it protects the record today.
- **Old paths:** when the new record (or tree) is missing and the old one exists, the proof job reads
  the old one, says so on one line, and writes only the new path. It never deletes the old file;
  `--force` removes both.
- The `prove` stage messages (story 44) name the new paths.

### Rejected alternatives

- **One hidden `.domino/` for all of it.** The protected and the overwritable files would be
  mixed, so the overwrite rule would have to look at each file name. A hidden directory also hides
  the report.
- **All into `progress/<Eq>/`.** `progress/` is overwritten without asking, so the session record
  would need an exception inside a run-artifact directory.

## 4. Acceptance criteria

- [ ] A test runs a proof job on a small project and checks that the record and the trees are under
      `session/<Eq>/` and the report under `progress/<Eq>/`, and that the top level has no
      `.session.json`, `.tree.json` or `.report.txt`.
- [ ] A test resumes from a record and trees at the old paths, and writes the new paths.
- [ ] A test: the export refuses an equivalence or a file that would be called `session`.
- [ ] `--force` removes the old and the new record files; the overwrite check does not treat
      `session/` as a run artifact.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt prove --theorem Simple4WHS --tactics
ls <out>/session/*/ <out>/progress/*/report.txt
```
