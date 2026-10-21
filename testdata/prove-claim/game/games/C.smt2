; story 31: `main` needs `other` as an assumption; `bad` (on `c`, which no oracle writes) is false at the start; the three do not contradict
(define-game-invariant main
  (>= game.q.a 0))
(define-game-invariant other
  (>= game.q.b 0))
(define-game-invariant bad
  (< game.q.c 0))
