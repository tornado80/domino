; Story 62: `invariant` calls two relations, one relation calls a helper, and one helper
; calls the other. Each definition comes after the ones that it calls (SMT-LIB order).

(define-fun inner-bit ((a Bool) (b Bool)) Bool
  (= a b))

(define-fun outer-bit ((a Bool) (b Bool)) Bool
  (inner-bit a b))

(define-state-relation plain-rel (left right)
  true)

(define-state-relation bit-rel (left right)
  (outer-bit left.Front.b right.Front.b))

(define-state-relation invariant (left right)
  (and (plain-rel left right) (bit-rel left right)))
