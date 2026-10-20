(define-state-relation invariant (left right)
  (and
    (= left.cnt.ctr right.cnt.ctr)
    (= left.wrap.calls right.wrap.calls)))
