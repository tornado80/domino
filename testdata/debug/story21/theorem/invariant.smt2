; rel_ctr fails where the left side bumps its counter; rel_seen holds on every pair.
(define-state-relation rel_ctr
  (left right)
  (= left.p.ctr right.p.ctr))

(define-state-relation rel_seen
  (left right)
  (= left.p.seen right.p.seen))

(define-state-relation invariant
  (left right)
  (and (rel_ctr left right)
       (rel_seen left right)))
