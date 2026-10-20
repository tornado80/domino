; `main` holds on every state; `nonneg` breaks on the path with `x < 0` (the side run checks only
; game invariants, story 77)
(define-game-invariant main
  (or (>= game.p.k 0) (< game.p.k 0)))
(define-game-invariant nonneg
  (>= game.p.k 0))
