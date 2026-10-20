(define-state-relation invariant (left right)
  (and
    (= left.ctr.ctr right.ctr.ctr)
    (= left.src.k right.src.k)))
