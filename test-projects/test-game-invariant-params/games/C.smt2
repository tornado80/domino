(define-game-invariant main
  (and
    (=> (>= game.P.b 0) (>= game.P.ctr 0))
    (= (game.P.f game.P.ctr) (game.P.f game.P.ctr))
    (= (game.f game.P.ctr) (game.P.f game.P.ctr))))
