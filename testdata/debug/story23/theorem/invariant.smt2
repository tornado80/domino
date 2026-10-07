; `invariant` holds after `O` only where `x > 0`: there both sides store `x`.
(define-state-relation invariant
  (left right)
  (= left.p.ctr right.p.ctr))
