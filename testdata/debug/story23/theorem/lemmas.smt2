; `my-lemma` is the project lemma `invariant` and `same-output` depend on. It is not provable
; on its own; the core claim set must neither check nor assume it.
(define-lemma <relation-my-lemma-gl-gr-O>
    (old-state-left old-state-right return-left return-right (x Int))
    (> x 0))
