# Local wayfinder tracker

- A map is `map.md` (label `wayfinder:map`). Its tickets are files in `tickets/`.
- Ticket identity: the file name number (`01`, `02`, ...). Refer to tickets by **title**.
- Frontmatter fields: `title`, `type` (`wayfinder:research|prototype|grilling|task`),
  `status` (`open|closed`), `assignee` (empty = unclaimed), `blocked_by` (list of ticket ids).
- Claim: set `assignee` before you do work.
- Resolve: add a `## Resolution` section, set `status: closed`, add a line to the map's
  "Decisions so far".
- Frontier: `status: open`, `assignee` empty, and every id in `blocked_by` is closed.
- Assets: put them in `assets/` and link them from the ticket.
