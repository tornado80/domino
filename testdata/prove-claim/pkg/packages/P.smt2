(define-package-invariant main
  (and
    (=> (>= pkg.k 0) (>= pkg.ctr 0))
    (or pkg.b (not pkg.b))
    (= (pkg.f pkg.ctr) (pkg.f pkg.ctr))))

; story 31: a second, false invariant
(define-package-invariant bad
  (< pkg.ctr 0))
