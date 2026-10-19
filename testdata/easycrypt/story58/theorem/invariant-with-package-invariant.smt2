(define-state-relation invariant (left right)
  (= left.C.ctr right.C.ctr))

(define-package-invariant main
  (>= pkg.ctr 0))
