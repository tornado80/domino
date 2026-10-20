; the side run checks only game invariants (story 77): the path with `x < 0` breaks this one
(define-game-invariant main
  (>= game.p.k 0))
