;; Twocpa (direct) == TwocpaViaCpa (via), uniformly in the real/ideal bit.
;;
;; In the direct game the two keys of a wire h live side by side in
;; keys_top.WireKey[h].  In TwocpaViaCpa they are split: the active one is held
;; by the reduction (reduction.ActiveKey[h]) and the secret one by the CPA game
;; (cpa.Key[h]).
;;
;; The old Keys package tracked "the active bit is set and the keys have been
;; generated" in a dedicated table.  That flag is gone; keys are generated
;; exactly by GenerateWireKeys, which is also the only oracle writing WireKey in
;; this game, so `WireKey[h] != None` now plays the role of the flag and matches
;; `reduction.Generated[h] == Some(true)`.

(define-state-relation generated (direct via)
  (forall ((h Int))
    (= (not (is-mk-none (select direct.keys_top.WireKey h)))
       (= (select via.reduction.Generated h) (mk-some true)))))

(define-state-relation control-state (direct via)
  (and
    (= direct.keys_top.ActiveBit via.reduction.ActiveBit)
    (generated direct via)))

(define-state-relation key-state (direct via)
  (forall ((h Int))
    (ite (not (is-mk-none (select direct.keys_top.WireKey h)))
      (let ((active (maybe-get (select direct.keys_top.ActiveBit h)))
            (wire-keys (maybe-get (select direct.keys_top.WireKey h))))
        (and
          ;; GenerateWireKeys only generates the keys of h after SetActiveBit(h, .)
          (not (is-mk-none (select direct.keys_top.ActiveBit h)))
          (not (is-mk-none (select via.reduction.ActiveKey h)))
          (not (is-mk-none (select via.cpa.Key h)))
          (= (select wire-keys active)
             (select via.reduction.ActiveKey h))
          (= (select wire-keys (not active))
             (select via.cpa.Key h))))
      (and
        (is-mk-none (select via.reduction.ActiveKey h))
        (is-mk-none (select via.cpa.Key h))))))

(define-state-relation invariant (direct via)
  (and
    (control-state direct via)
    (key-state direct via)))
