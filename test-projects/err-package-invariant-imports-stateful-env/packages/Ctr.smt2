(define-package-invariant nonneg
  (>= pkg.ctr 0))

(define-package-invariant same
  (not pkg.differed))

(define-package-invariant unseen
  (forall ((i Int))
    (=> (or (< i 0) (>= i pkg.ctr))
        (is-mk-none (select pkg.seen i)))))
