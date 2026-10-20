(define-package-invariant main
  (and
    (=> (>= pkg.k 0) (>= pkg.ctr 0))
    (or pkg.b (not pkg.b))
    (= (pkg.f pkg.ctr) (pkg.f pkg.ctr))))
