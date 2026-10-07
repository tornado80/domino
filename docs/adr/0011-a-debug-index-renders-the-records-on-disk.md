# A debug index renders the records on disk

**Status:** accepted. Implemented by `docs/stories/symbolic-execution/22-debug-indexes-and-out.md`.

`domino debug` used to write one project index from the entries of the run that had just
finished. A run of one proofstep then deleted every other row. We now write an index for each
proofstep, theorem and project, and each index is a **pure renderer over the result records on
disk** (`<strategy>_result.json`, one for each oracle run). It is not a report of the last run.
After a run, Domino rewrites the index of the level the run selected and each index above it that
already exists. It never creates an index above the selected level. Thus there is no project index
until the user runs the debugger on the whole project.

## Considered options

- **Each run writes the indexes of its level from its own entries.** This is simpler, and an
  index never shows a run older than the last one. Rejected: a narrower rerun leaves stale rows in
  the indexes above it with no warning, a filtered run (`--oracle`, `--claim`) writes a partial
  index over a full one, and a lockstep run replaces the sequential index of the same proofstep.

## Consequences

- An index can show runs that are days old. Each row therefore shows when its run finished, and
  each parent row shows the oldest run below it.
- Runs from before story 22 have no record and are not listed until they run again.
- To remove a run from the indexes, delete its directory.
