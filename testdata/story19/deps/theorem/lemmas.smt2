; `positive` is a dependency that only the solver can see is false: on the path of `Branch`
; where `x <= 0` it is unsatisfiable, and no terminal says so.
(define-lemma positive Branch
    (old-state-left old-state-right return-left return-right (x Int))
    (> x 0))

(define-lemma needs-positive Branch
    (old-state-left old-state-right return-left return-right (x Int))
    (= return-left.value return-right.value))

(define-lemma skipped Admitted
    (old-state-left old-state-right return-left return-right (x Int))
    false)
