# Story 67 — Implementation report: resume files in their own directory

Rust only. The proof files and the tactics do not change.

## What changed

- **`job.rs`**: `session_record_name` and `saved_tree_name` are replaced by path functions, the
  one owner of the layout:
  - `session_dir` → `<theorem_out>/session/<Eq>/`;
  - `session_record_path` → `session/<Eq>/record.json`;
  - `saved_tree_path` → `session/<Eq>/<Oracle>.tree.json`;
  - `old_session_record_path`, `old_saved_tree_path`: the paths before story 67 (read only);
  - `path_to_read(new, old)`: the new path if it exists, else the old one if it exists (with one
    `note:` line on stderr), else the new one. The old file is never deleted.
  - `remove_records_and_trees` (`--force`) removes every file under `session/` and every old
    `*.session.json` / `*.tree.json`.
- **`tactics/mod.rs`**: `plan_job` and the tree read of a resumed oracle use `path_to_read`; the
  record and the trees are always written to the new paths. `--force` without `--oracle` removes
  the old and the new record. The report is `progress/<Eq>/report.txt` (`report_file` is that
  relative path, so the live page and the stage messages name it). `write_atomically` creates
  the parent directory.
- **`overwrite.rs`**: `SESSION_DIR = "session"`, and `takes_reserved_dir_name`: an exported file
  whose first component (stem, any case) is `session`, `progress` or `!debug!`. `session/` is
  not in `RUN_ARTIFACT_DIRS`, so the overwrite check stops on it as it did on the record.
- **`export.rs` / `mod.rs`**: `export_theorem` refuses such a file with the new
  `EcExportError::ReservedFileName`.
- **CLI doc** of `--force` names `session/`.

### Deviation

`names.rs:120` does not reserve `progress` as a file name; it is only an EasyCrypt keyword. All
exported files have a prefix (`Pkg_`, `Comp_`, `Eq_`) or a fixed name, so no file can be called
`session` today. The guard is a check in `export_theorem` (defensive); its test is on
`takes_reserved_dir_name`, because no project can make the export produce such a name.

### Rejected shape

Keep `*_name` functions that return a relative name and let each caller join. Rejected: the
callers would know that the name has a directory, and the old-path fallback would be in each
caller.

## Tests

- `job.rs`: `a_saved_joint_tree_reads_back_as_it_was_written` (new paths),
  `the_old_path_is_read_only_when_the_new_one_is_missing`,
  `removing_records_deletes_…` (old and new paths go, `progress/…/report.txt` stays).
- `overwrite.rs`: `an_exported_file_never_takes_a_reserved_directory_name` (also: `session/…`
  is not a run artifact).
- `tactics/tests.rs` (plan tests updated to the new path);
  live, `cvc5-lib` only: `a_job_writes_its_record_and_trees_under_session_and_its_report_under_progress`,
  `a_job_resumes_from_a_record_and_a_tree_at_the_old_paths`.
- `crates/domino/tests`: `easycrypt_overwrite` (record and tree at the new paths block
  translation, `--force` removes them), and the `cvc5-lib` tests `easycrypt_prove`,
  `easycrypt_ctrl_c`, `easycrypt_tactics_writes` updated to the new paths.

## Results

- `cargo test --lib`: 699 passed, 0 failed, 5 ignored.
- `cargo test -p domino --test easycrypt_overwrite`: 9 passed.
- `cargo clippy --workspace --all-targets`: no new warnings in the changed files.
- `cargo build --release --workspace`: OK.
- `--features cvc5-lib`: cannot build here (no cmake). The live tests above and the updated
  integration tests are not compiled or run. **Open.**
- Complexity: the sdlc cognitive gate does not score Rust (NotApplicable); CC is UNMEASURED.
  The changed functions are small; `plan_job` gets one loop with one `match`.
