(define-game-invariant bounded
  (<= game.wrap.calls (+ game.wrap.calls game.cnt.ctr)))
