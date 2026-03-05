
(define-fun state=
    ((left-State (Array Int (Maybe (Tuple10 Int Bool Int Bits_n (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (right-State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (right-Ltk (Array Int (Maybe Bits_n))))
  Bool
  (forall ((ctr Int))
          (and (= (is-mk-none (select left-State ctr))
                  (is-mk-none (select right-State ctr)))
               (let ((state (select right-State ctr)))
                 (=> (not (is-mk-none state))
                  (let  ((U    (el10-1  (maybe-get state)))
                         (u    (el10-2  (maybe-get state)))
                         (V    (el10-3  (maybe-get state)))
                         (kid  (el10-4  (maybe-get state)))
                         (acc  (el10-5  (maybe-get state)))
                         (ni   (el10-6  (maybe-get state)))
                         (nr   (el10-7  (maybe-get state)))
                         (kmac (el10-8  (maybe-get state)))
                         (sid  (el10-9  (maybe-get state)))
                         (mess (el10-10 (maybe-get state))))
                    (let ((ltk (select right-Ltk kid)))
                      (and (not (is-mk-none ltk))
                           (= (select left-State ctr)
                              (mk-some (mk-tuple10 U u V (maybe-get ltk) acc ni nr kmac sid mess)))))))))))


(define-fun LTK-table-empty-above-max
    ((max-kid Int)
     (Ltk (Array Int (Maybe Bits_n))))
  Bool
  (forall ((kid Int))
          (=> (> kid max-kid)
              (is-mk-none (select Ltk kid)))))


(define-fun ltk-and-h-set-together
    ((Ltk (Array Int (Maybe Bits_n)))
     (H (Array Int (Maybe Bool))))
  Bool
  (forall ((kid Int))
          (= (is-mk-none (select Ltk kid))
             (is-mk-none (select H kid)))))


(define-state-relation invariant
    ((left-game <GameState_Hybrid1_<$<!n!>$>>)
     (right-game <GameState_Hybrid2_<$<!n!>$>>))
  (and
   (= left-game.KX.kid_ right-game.Prf.kid_)
   (= left-game.KX.ctr_ right-game.KX.ctr_)
   (= left-game.KX.LTK right-game.Prf.LTK)
   (= left-game.KX.H right-game.Prf.H)
   (= left-game.KX.Fresh right-game.KX.Fresh)
   (= left-game.KX.RevTested right-game.KX.RevTested)
   (state= left-game.KX.State right-game.KX.State right-game.Prf.LTK)

   (LTK-table-empty-above-max right-game.Prf.kid_ right-game.Prf.LTK)
   (ltk-and-h-set-together right-game.Prf.LTK right-game.Prf.H)))
