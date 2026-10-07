(define-fun nonneg ((x Int)) Bool (>= x 0))

(define-package-invariant
  (>= pkg.ctr 0))
