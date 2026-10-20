(define-state-relation invariant (left right)
  (and
    (= left.P.ctr right.P.ctr)
    (= left.q.n right.q.n)))
