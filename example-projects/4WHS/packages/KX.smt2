; state-machine-properties
(define-package-invariant state-machine-properties
  (forall ((ctr Int))
      (let ((state (select pkg.State ctr)))
         (=> (not (is-mk-none state))
            (let  ((U    (el11-1  (maybe-get state)))
                     (role (el11-2  (maybe-get state)))
                     (V    (el11-3  (maybe-get state)))
                     (ltk  (el11-4  (maybe-get state)))
                     (acc  (el11-5  (maybe-get state)))
                     (k    (el11-6  (maybe-get state)))
                     (ni   (el11-7  (maybe-get state)))
                     (nr   (el11-8  (maybe-get state)))
                     (kmac (el11-9  (maybe-get state)))
                     (sid  (el11-10 (maybe-get state)))
                     (mess (el11-11 (maybe-get state))))
               (and
               (=>
                  (or
                  (and role (> mess 0))
                  (and (not role) (> mess 1)))
                  (= k (mk-some (<<func-prf>> ltk
                                                (mk-tuple5 U V
                                                         (maybe-get ni)
                                                         (maybe-get nr)
                                                         true)))))
               (=>
                  (not (is-mk-none acc))
                  (or
                  (and role (> mess 1))
                  (and (not role) (> mess 2))))
               (=>
                  (and (not role) (> mess 0))
                  (not (is-mk-none ni)))
               (=>
                  (and (not role) (> mess 1))
                  (not (is-mk-none nr)))
               (=>
                  (and role (> mess 0))
                  (and
                  (not (is-mk-none ni))
                  (not (is-mk-none nr))))
               (=> ; needed for sid Unwraps in Send3 and Send4
                  (or
                  (and role (> mess 0))
                  (and (not role) (> mess 1)))
                  (not (is-mk-none sid)))))))))