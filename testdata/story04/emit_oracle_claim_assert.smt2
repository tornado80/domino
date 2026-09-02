(assert (not (=> (and (forall ((randmap-sample-id-left SampleId)
                               (randmap-sample-offset-left Int)
                               (randmap-sample-id-right SampleId)
                               (randmap-sample-offset-right Int))
                              (=> (randomness-mapping-PKENC randmap-sample-id-left
                                                            randmap-sample-id-right
                                                            randmap-sample-offset-left
                                                            randmap-sample-offset-right)
                                  (rand-is-eq randmap-sample-id-left
                                              randmap-sample-id-right
                                              randmap-sample-offset-left
                                              randmap-sample-offset-right)))
                      (<domino-invariant> <<game-state-Game_MON_CCA_PKE-old>>
                                          <<game-state-Game_MOD_CCA_PKE_Real_KEM-old>>)
                      (relation-no-abort <<game-state-Game_MON_CCA_PKE-new-PKENC>>
                                         <<game-state-Game_MOD_CCA_PKE_Real_KEM-new-PKENC>>)
                      (<relation-lemma-kem-correctness-Game_MON_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM-PKENC> <<game-state-Game_MON_CCA_PKE-old>>
                                                                                                         <<game-state-Game_MOD_CCA_PKE_Real_KEM-old>>
                                                                                                         <return-Game_MON_CCA_PKE-PKENC>
                                                                                                         <return-Game_MOD_CCA_PKE_Real_KEM-PKENC>
                                                                                                         <arg-Game_MON_CCA_PKE-PKENC-m0>
                                                                                                         <arg-Game_MON_CCA_PKE-PKENC-m1>))
                 (<relation-same-output-Game_MON_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM-PKENC> <<game-state-Game_MON_CCA_PKE-old>>
                                                                                          <<game-state-Game_MOD_CCA_PKE_Real_KEM-old>>
                                                                                          <return-Game_MON_CCA_PKE-PKENC>
                                                                                          <return-Game_MOD_CCA_PKE_Real_KEM-PKENC>
                                                                                          <arg-Game_MON_CCA_PKE-PKENC-m0>
                                                                                          <arg-Game_MON_CCA_PKE-PKENC-m1>))))
