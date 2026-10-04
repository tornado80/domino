(define-state-relation trivial (left right)
  true)

(define-state-relation invariant (left right)
  (trivial left right))
