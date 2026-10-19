(define-fun nonneg ((x Int)) Bool (>= x 0))

(define-package-invariant main
  (>= pkg.ctr 0))
