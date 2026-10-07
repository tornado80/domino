; Story 59: one helper `define-fun` and one state relation.

(define-fun same-bit ((a Bool) (b Bool)) Bool
  (= a b))

(define-state-relation invariant (left right)
  (same-bit left.Front.b right.Front.b))
