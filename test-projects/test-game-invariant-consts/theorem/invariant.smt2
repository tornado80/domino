(define-state-relation invariant (left right)
  (and
    (= left.P.ctr right.P.ctr)
    left.c
    (= (right.f 0) (left.P.f 0))))
