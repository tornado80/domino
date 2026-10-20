; `main` holds on every state; `nonneg` breaks on the path with `x < 0`
(define-package-invariant main
  (or (>= pkg.k 0) (< pkg.k 0)))
(define-package-invariant nonneg
  (>= pkg.k 0))
