(define-fun state=
    ((left-State (Array Int (Maybe (Tuple11 Int Bool Int Bits_n (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (right-State (Array Int (Maybe (Tuple10 Int Bool Int Bits_n (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (and (= (is-mk-none (select left-State ctr))
                  (is-mk-none (select right-State ctr)))
               (let ((state (select left-State ctr)))
                 (=> (not (is-mk-none state))
                  (let  ((U    (el11-1  (maybe-get state)))
                         (u    (el11-2  (maybe-get state)))
                         (V    (el11-3  (maybe-get state)))
                         (ltk  (el11-4  (maybe-get state)))
                         (acc  (el11-5  (maybe-get state)))
                         (k    (el11-6  (maybe-get state)))
                         (ni   (el11-7  (maybe-get state)))
                         (nr   (el11-8  (maybe-get state)))
                         (kmac (el11-9  (maybe-get state)))
                         (sid  (el11-10 (maybe-get state)))
                         (mess (el11-11 (maybe-get state))))
                    (= (select right-State ctr)
                       (mk-some (mk-tuple10 U u V ltk acc ni nr kmac sid mess)))))))))


(define-fun keys-computed-correctly
    ((left-State (Array Int (Maybe (Tuple11 Int Bool Int Bits_n (Maybe Bool) (Maybe Bits_n)
                                            (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                            (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select left-State ctr)))
            (=> (not (is-mk-none state))
                (let  ((U    (el11-1  (maybe-get state)))
                       (u    (el11-2  (maybe-get state)))
                       (V    (el11-3  (maybe-get state)))
                       (ltk  (el11-4  (maybe-get state)))
                       (acc  (el11-5  (maybe-get state)))
                       (k    (el11-6  (maybe-get state)))
                       (ni   (el11-7  (maybe-get state)))
                       (nr   (el11-8  (maybe-get state)))
                       (kmac (el11-9  (maybe-get state)))
                       (sid  (el11-10 (maybe-get state)))
                       (mess (el11-11 (maybe-get state))))
                  (ite (or (and u (> mess 0))
                           (and (not u) (> mess 1)))
                       (= k (mk-some (<<func-prf>> ltk (mk-tuple5 U V (maybe-get ni) (maybe-get nr) true))))
                       (= k (as mk-none (Maybe Bits_n)))))))))


(define-fun time-of-acceptance
    ((left-State (Array Int (Maybe (Tuple11 Int Bool Int Bits_n (Maybe Bool) (Maybe Bits_n)
                                            (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                            (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select left-State ctr)))
            (=> (not (is-mk-none state))
                (let  ((u    (el11-2  (maybe-get state)))
                       (acc  (el11-5  (maybe-get state)))
                       (mess (el11-11 (maybe-get state))))
                  (=> (not (is-mk-none acc))
                      (ite u (> mess 1) (> mess 2))))))))


(define-fun time-of-nonces
    ((left-State (Array Int (Maybe (Tuple11 Int Bool Int Bits_n (Maybe Bool) (Maybe Bits_n)
                                            (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                            (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select left-State ctr)))
            (=> (not (is-mk-none state))
                (let  ((u    (el11-2  (maybe-get state)))
                       (ni   (el11-7  (maybe-get state)))
                       (nr   (el11-8  (maybe-get state)))
                       (mess (el11-11 (maybe-get state))))
                  (and
                   ;; ni
                   (=> (> mess 0)
                       (not (is-mk-none ni)))
                   (=> (or (and (> mess 0) u)
                           (and (> mess 1) (not u)))
                       (not (is-mk-none nr)))))))))

(define-fun time-of-sid
    ((left-State (Array Int (Maybe (Tuple11 Int Bool Int Bits_n (Maybe Bool) (Maybe Bits_n)
                                            (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                            (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select left-State ctr)))
            (=> (not (is-mk-none state))
                (let  ((u    (el11-2  (maybe-get state)))
                       (sid  (el11-10 (maybe-get state)))
                       (mess (el11-11 (maybe-get state))))
                  (=> (or (and (> mess 0) u)
                          (and (> mess 1) (not u)))
                      (not (is-mk-none sid))))))))


(define-state-relation invariant
    ((left-game <GameState_Hybrid0_<$<!n!>$>>)
     (right-game <GameState_Hybrid1_<$<!n!>$>>))
  (and
   (= left-game.KX.kid_ right-game.KX.kid_)
   (= left-game.KX.ctr_ right-game.KX.ctr_)
   (= left-game.KX.LTK right-game.KX.LTK)
   (= left-game.KX.H right-game.KX.H)
   (= left-game.KX.Fresh right-game.KX.Fresh)
   (= left-game.KX.RevTested right-game.KX.RevTested)

   (state= left-game.KX.State right-game.KX.State)

   (keys-computed-correctly left-game.KX.State)

   (time-of-nonces left-game.KX.State)
   (time-of-sid left-game.KX.State)
   (time-of-acceptance left-game.KX.State)))
