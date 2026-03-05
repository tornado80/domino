(define-fun =prf
    ((left-prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (right-prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (hon (Array Int (Maybe Bool))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
          (let ((kmac-index (mk-tuple2 kid (mk-tuple5 U V ni nr false)))
                (k-index (mk-tuple2 kid (mk-tuple5 U V ni nr true))))
            (and
             ;; (is-mk-none (select right-prf k-index))
             (=> (not (is-mk-none (select right-prf k-index)))
                 (= (select left-prf k-index)
                    (select right-prf k-index)))
             (= (select left-prf kmac-index)
                (select right-prf kmac-index))))))


(define-fun no-overwriting-state
    ((max-ctr Int)
     (State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (=> (> ctr max-ctr)
              (is-mk-none (select State ctr)))))


(define-fun H-LTK-tables-empty-above-max
    ((max-kid Int)
     (H (Array Int (Maybe Bool)))
     (Ltk (Array Int (Maybe Bits_n))))
  Bool
  (forall ((kid Int))
          (=> (> kid max-kid)
              (and (is-mk-none (select H kid))
                   (is-mk-none (select Ltk kid))))))


(define-fun kmac-before-sid
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
                 (=> (not (is-mk-none state))
                  (let  ((kmac (el10-8  (maybe-get state)))
                         (sid  (el10-9  (maybe-get state))))
                    (=> (is-mk-none kmac)
                        (is-mk-none sid)))))))


(define-fun referenced-kid-exist
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (Ltk (Array Int (Maybe Bits_n))))
  Bool
  (and
   (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n) (flag Bool))
           (=> (is-mk-none (select Ltk kid))
               (is-mk-none (select Prf (mk-tuple2 kid (mk-tuple5 U V ni nr flag))))))

  (forall ((ctr Int))
          (let ((state (select State ctr)))
                 (=> (not (is-mk-none state))
                  (let  ((kid  (el10-4  (maybe-get state))))
                    (not (is-mk-none (select Ltk kid)))))))))


(define-fun ltk-and-h-set-together
    ((Ltk (Array Int (Maybe Bits_n)))
     (H (Array Int (Maybe Bool))))
  Bool
  (forall ((kid Int))
          (= (is-mk-none (select Ltk kid))
             (is-mk-none (select H kid)))))


(define-fun k-prf-implies-rev-tested-sid
    ((Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (RevTested (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Bool))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
          (=> (not (is-mk-none (select Prf (mk-tuple2 kid (mk-tuple5 U V ni nr true)))))
              (let ((kmac (maybe-get (select Prf (mk-tuple2 kid (mk-tuple5 U V ni nr false))))))
                (let ((tau (<<func-mac>> kmac nr 2)))
                  (not (is-mk-none (select RevTested (mk-tuple5 U V ni nr tau)))))))))


(define-fun h-and-fresh-match
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Fresh (Array Int (Maybe Bool)))
     (H (Array Int (Maybe Bool))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((kid  (el10-4  (maybe-get state))))
                  (and (not (is-mk-none (select Fresh ctr)))
                       (not (is-mk-none (select H kid)))
                       (= (select Fresh ctr) (select H kid))))))))


(define-fun sid-is-wellformed
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (H (Array Int (Maybe Bool)))
     (Ltk (Array Int (Maybe Bits_n)))
     (Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
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
                  (=> (not (is-mk-none sid))
                      (= sid (mk-some (mk-tuple5 U V
                                                 (maybe-get ni) (maybe-get nr)
                                                 (<<func-mac>> (maybe-get kmac) (maybe-get nr) 2))))))))))

(define-fun kmac-requires-nonces
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((ni   (el10-6  (maybe-get state)))
                       (nr   (el10-7  (maybe-get state)))
                       (kmac (el10-8  (maybe-get state))))
                  (=> (not (is-mk-none kmac))
                      (and (not (is-mk-none ni))
                           (not (is-mk-none nr)))))))))


(define-fun sid-requires-nonces
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((ni   (el10-6  (maybe-get state)))
                       (nr   (el10-7  (maybe-get state)))
                       (sid  (el10-9  (maybe-get state))))
                  (=> (not (is-mk-none sid))
                      (and (not (is-mk-none ni))
                           (not (is-mk-none nr)))))))))


(define-fun no-sid-in-send1
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((sid  (el10-9  (maybe-get state)))
                       (mess (el10-10 (maybe-get state))))
                  (=> (= mess 0) (is-mk-none sid)))))))


(define-fun no-kmac-in-send1
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((kmac (el10-8  (maybe-get state)))
                       (mess (el10-10 (maybe-get state))))
                  (=> (= mess 0) (is-mk-none kmac)))))))


(define-fun kmac-is-wellformed
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Fresh (Array Int (Maybe Bool)))
     (Ltk (Array Int (Maybe Bits_n)))
     (Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
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
                  (=> (not (is-mk-none kmac))
                      (= (maybe-get kmac)
                         (ite (= (select Fresh ctr) (mk-some true))
                              (maybe-get (select Prf (mk-tuple2 kid (mk-tuple5
                                                                U V
                                                                (maybe-get ni)
                                                                (maybe-get nr)
                                                                false))))
                              (<<func-prf>> (maybe-get (select Ltk kid))
                                            (mk-tuple5 U V
                                            (maybe-get ni)
                                            (maybe-get nr)
                                            false))))))))))


(define-fun honest-kmac
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (Fresh (Array Int (Maybe Bool)))
     (H (Array Int (Maybe Bool))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
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
                  (=> (= (select Fresh ctr)
                         (mk-some true))
                      (and
                       (= (select H kid) (mk-some true))
                       (=> (not (is-mk-none kmac))
                           (not (is-mk-none (select Prf (mk-tuple2 kid (mk-tuple5 U V
                                                                   (maybe-get ni) (maybe-get nr)
 
                                                                   false)))))))))))))


(define-fun kmac-before-k
    ((Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) 
                 (Maybe Bits_n))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
          (=> (is-mk-none (select Prf (mk-tuple2 kid (mk-tuple5 U V ni nr false))))
              (is-mk-none (select Prf (mk-tuple2 kid (mk-tuple5 U V ni nr true)))))))


(define-state-relation invariant
    ((left-game <GameState_Hybrid2_<$<!n!>$>>)
     (right-game <GameState_Hybrid2_<$<!n!>$>>))
  (and
   (= left-game.Prf.kid_ right-game.Prf.kid_)
   (= left-game.KX.ctr_ right-game.KX.ctr_)
   (= left-game.Prf.LTK right-game.Prf.LTK)
   (=prf left-game.Prf.PRF right-game.Prf.PRF left-game.Prf.H)
   (= left-game.Prf.H right-game.Prf.H)
   (= left-game.KX.Fresh right-game.KX.Fresh)
   (= left-game.KX.RevTested right-game.KX.RevTested)
   (= left-game.KX.State right-game.KX.State)

   (no-overwriting-state left-game.KX.ctr_ left-game.KX.State)
   (H-LTK-tables-empty-above-max left-game.Prf.kid_ left-game.Prf.H left-game.Prf.LTK)
   (H-LTK-tables-empty-above-max right-game.Prf.kid_ right-game.Prf.H right-game.Prf.LTK)

   (kmac-requires-nonces left-game.KX.State)
   (kmac-is-wellformed left-game.KX.State left-game.KX.Fresh left-game.Prf.LTK left-game.Prf.PRF)
   (no-kmac-in-send1 left-game.KX.State)

   (sid-requires-nonces left-game.KX.State)
   (sid-is-wellformed left-game.KX.State left-game.Prf.H left-game.Prf.LTK left-game.Prf.PRF)
   (no-sid-in-send1 left-game.KX.State)

   (kmac-before-sid left-game.KX.State)
   (kmac-before-k left-game.Prf.PRF)
   (kmac-before-k right-game.Prf.PRF)

   (referenced-kid-exist left-game.KX.State left-game.Prf.PRF left-game.Prf.LTK)

   (ltk-and-h-set-together left-game.Prf.LTK left-game.Prf.H)
   (h-and-fresh-match left-game.KX.State left-game.KX.Fresh left-game.Prf.H)
   (k-prf-implies-rev-tested-sid left-game.Prf.PRF left-game.KX.RevTested)

   (honest-kmac left-game.KX.State left-game.Prf.PRF left-game.KX.Fresh left-game.Prf.H)))
