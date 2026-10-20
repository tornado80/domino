(define-game-invariant main
  (and
    (=> (not game.c) (= game.P.ctr 0))
    (or game.u (not game.u))))
