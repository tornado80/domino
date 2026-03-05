(define-fun randomness-mapping-PKGEN
    ( 
        (sample-ctr-old-monolithic_pke_cca_game Int)
        (sample-ctr-old-modular_pke_cca_game_with_real_kem Int)
        (sample-id-monolithic_pke_cca_game SampleId)
        (sample-id-modular_pke_cca_game_with_real_kem SampleId)
        (sample-ctr-monolithic_pke_cca_game Int)
        (sample-ctr-modular_pke_cca_game_with_real_kem Int)
    )
    Bool
    (or
        (and
            (= sample-ctr-monolithic_pke_cca_game sample-ctr-old-monolithic_pke_cca_game)
            (= sample-ctr-modular_pke_cca_game_with_real_kem sample-ctr-old-modular_pke_cca_game_with_real_kem)
            (= sample-id-monolithic_pke_cca_game (sample-id "pkg_KemScheme" "KEM_GEN" "kem_gen"))
            (= sample-id-modular_pke_cca_game_with_real_kem (sample-id "pkg_KemScheme" "KEM_GEN" "kem_gen"))
        )
    )
)

(define-fun randomness-mapping-PKENC
    ( 
        (sample-ctr-old-monolithic_pke_cca_game Int)
        (sample-ctr-old-modular_pke_cca_game_with_real_kem Int)
        (sample-id-monolithic_pke_cca_game SampleId)
        (sample-id-modular_pke_cca_game_with_real_kem SampleId)
        (sample-ctr-monolithic_pke_cca_game Int)
        (sample-ctr-modular_pke_cca_game_with_real_kem Int)
    )
    Bool
    (or
        (and
            (= sample-ctr-monolithic_pke_cca_game sample-ctr-old-monolithic_pke_cca_game)
            (= sample-ctr-modular_pke_cca_game_with_real_kem sample-ctr-old-modular_pke_cca_game_with_real_kem)
            (= sample-id-monolithic_pke_cca_game (sample-id "pkg_DemScheme" "DEM_ENC" "dem_enc"))
            (= sample-id-modular_pke_cca_game_with_real_kem (sample-id "pkg_DemScheme" "DEM_ENC" "dem_enc"))
        )
        (and
            (= sample-ctr-monolithic_pke_cca_game sample-ctr-old-monolithic_pke_cca_game)
            (= sample-ctr-modular_pke_cca_game_with_real_kem sample-ctr-old-modular_pke_cca_game_with_real_kem)
            (= sample-id-monolithic_pke_cca_game (sample-id "pkg_KemScheme" "KEM_ENCAPS" "kem_encaps"))
            (= sample-id-modular_pke_cca_game_with_real_kem (sample-id "pkg_KemScheme" "KEM_ENCAPS" "kem_encaps"))
        )
    )
)

(define-fun randomness-mapping-PKDEC
    ( 
        (sample-ctr-old-monolithic_pke_cca_game Int)
        (sample-ctr-old-modular_pke_cca_game_with_real_kem Int)
        (sample-id-monolithic_pke_cca_game SampleId)
        (sample-id-modular_pke_cca_game_with_real_kem SampleId)
        (sample-ctr-monolithic_pke_cca_game Int)
        (sample-ctr-modular_pke_cca_game_with_real_kem Int)
    )
    Bool
    false
)

(define-state-relation invariant
    (
        (left-game <GameState_MonolithicPkeCcaGame>)
        (right-game <GameState_ModularPkeCcaGame>)
    )
    (and
        (= left-game.pkg_MON_CCA.pk right-game.pkg_MOD_CCA.pk right-game.pkg_KEM.pk) ; left_pk = right_pk
        (= ((_ is mk-none) left-game.pkg_MON_CCA.pk) ((_ is mk-none) left-game.pkg_MON_CCA.sk) ((_ is mk-none) right-game.pkg_MOD_CCA.pk) ((_ is mk-none) right-game.pkg_KEM.pk) ((_ is mk-none) right-game.pkg_KEM.sk)) ; left_pk = None iff right_pk = None
        (= left-game.pkg_MON_CCA.c right-game.pkg_MOD_CCA.c) ; left_challenge_ciphertext = right_challenge_ciphertext
        (= ((_ is mk-none) left-game.pkg_MON_CCA.c) ((_ is mk-none) right-game.pkg_MOD_CCA.c) ((_ is mk-none) right-game.pkg_KEM.ek) ((_ is mk-none) right-game.pkg_MOD_CCA.ek) ((_ is mk-none) right-game.pkg_MOD_CCA.em) ((_ is mk-none) right-game.pkg_Key.k)) ; left_challenge_ciphertext = None iff right_challenge_ciphertext = None iff right_encapsulation_challenge = None iff right_dem_challenge = None iff right_key_k = None
        (= left-game.pkg_MON_CCA.sk right-game.pkg_KEM.sk) ; left_sk = right_sk
        (= right-game.pkg_MOD_CCA.ek right-game.pkg_KEM.ek) ; right encapsulated keys
        (=> ((_ is mk-none) right-game.pkg_KEM.pk) ((_ is mk-none) right-game.pkg_MOD_CCA.c)) ; if PKGEN is not called, PKENC can not be called
        (=>
            (not ((_ is mk-none) right-game.pkg_MOD_CCA.c))
            (= (maybe-get right-game.pkg_MOD_CCA.c) (mk-tuple2 (maybe-get right-game.pkg_MOD_CCA.ek) (maybe-get right-game.pkg_MOD_CCA.em)))
        )
        (=>
            (not ((_ is mk-none) right-game.pkg_Key.k))
            (and
                (= (maybe-get right-game.pkg_Key.k) (el2-1 (<<func-kem_encaps>> (maybe-get right-game.pkg_KEM.encaps_randomness) (maybe-get right-game.pkg_KEM.pk))))
                (= (maybe-get right-game.pkg_KEM.ek) (el2-2 (<<func-kem_encaps>> (maybe-get right-game.pkg_KEM.encaps_randomness) (maybe-get right-game.pkg_KEM.pk))))
            )
        )
        (forall 
            (
                (x Bits_*)
            )
            (and 
                (=> 
                    ((_ is mk-none) right-game.pkg_MOD_CCA.c)
                    ((_ is mk-none) (select right-game.pkg_DEM.T x))
                )
                (=> 
                    (not ((_ is mk-none) right-game.pkg_MOD_CCA.c))
                    (= (= x (maybe-get right-game.pkg_MOD_CCA.em)) (not ((_ is mk-none) (select right-game.pkg_DEM.T x))))
                )
            )
        )
    )
)

; The following axiom gives unknown when checking satisfiability of only invariants
;(assert
;    (forall 
;        (
;            (gen-r Bits_2000)
;            (encaps-r Bits_3000)
;        )
;        (let 
;            (
;                (pk (el2-1 (<<func-kem_gen>> gen-r)))
;                (sk (el2-2 (<<func-kem_gen>> gen-r)))
;            )
;            (let
;                (
;                    (k (el2-1 (<<func-kem_encaps>> encaps-r pk)))
;                    (ek (el2-2 (<<func-kem_encaps>> encaps-r pk)))
;                )
;                (= k (<<func-kem_decaps>> sk ek))
;            )
;        )
;    )
;)

(define-fun <relation-lemma-kem-correctness-monolithic_pke_cca_game-modular_pke_cca_game_with_real_kem-PKDEC>
    (
        (old-state-left <GameState_MonolithicPkeCcaGame>)
        (old-state-right <GameState_ModularPkeCcaGame>)
        (return-left <OracleReturn_MonolithicPkeCcaGame_MON_CCA_PKDEC>)
        (return-right <OracleReturn_ModularPkeCcaGame_MOD_CCA_PKDEC>)
        (ek_ctxt (Tuple2 Bits_400 Bits_*))
    )
    Bool
    (let
        (
            (pk (<pkg-state-KEM-pk> (<game-ModularPkeCcaGame-pkgstate-pkg_KEM> old-state-right)))
            (sk (<pkg-state-KEM-sk> (<game-ModularPkeCcaGame-pkgstate-pkg_KEM> old-state-right)))
        )
        (=>
            (not ((_ is mk-none) pk))
            (forall 
                (
                    (r Bits_3000)
                )
                (let
                    (
                        (k (el2-1 (<<func-kem_encaps>> r (maybe-get pk))))
                        (ek (el2-2 (<<func-kem_encaps>> r (maybe-get pk))))
                    )
                    (= k (<<func-kem_decaps>> (maybe-get sk) ek))
                )
            )
        )
    )
)

(define-fun <relation-lemma-rand-is-eq-monolithic_pke_cca_game-modular_pke_cca_game_with_real_kem-PKENC>
    (
        (old-state-left <GameState_MonolithicPkeCcaGame>)
        (old-state-right <GameState_ModularPkeCcaGame>)
        (return-left <OracleReturn_MonolithicPkeCcaGame_MON_CCA_PKENC>)
        (return-right <OracleReturn_ModularPkeCcaGame_MOD_CCA_PKENC>)
        (m Bits_*)
    )
    Bool 
    (let 
        (
            (dem_mapping_id (sample-id "pkg_DemScheme" "DEM_ENC" "dem_enc"))
            (kem_mapping_id (sample-id "pkg_KemScheme" "KEM_ENCAPS" "kem_encaps"))
        )
        (and
            (rand-is-eq dem_mapping_id dem_mapping_id (<game-MonolithicPkeCcaGame-rand-pkg_DemScheme-DEM_ENC-dem_enc> old-state-left) (<game-ModularPkeCcaGame-rand-pkg_DemScheme-DEM_ENC-dem_enc> old-state-right))
            (rand-is-eq kem_mapping_id kem_mapping_id (<game-MonolithicPkeCcaGame-rand-pkg_KemScheme-KEM_ENCAPS-kem_encaps> old-state-left) (<game-ModularPkeCcaGame-rand-pkg_KemScheme-KEM_ENCAPS-kem_encaps> old-state-right))
        )
    )
)