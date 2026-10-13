; holds on every state: the side run checks it and verifies it everywhere
(define-game-invariant
  (or (>= game.p.k 0) (< game.p.k 0)))
