(define-state-relation invariant (left right)
  (and
    (= left.flag.differed right.flag.differed)
    (= left.det.k right.det.k)))
