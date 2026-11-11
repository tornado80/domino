(* Red_big_composition_medium_composition_more_oracles_UselessOracle.ec for theorem `Proof`: the oracle lemmas of `UselessOracle`, one for each side (the sides use different compositions) — hand-written prototype of story 101 (ADR 0023). *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Comp_BigComposition Comp_MediumCompositionMoreOracles Comp_MediumComposition Comp_SmallComposition.
require import Red_big_composition_medium_composition_more_oracles_Router.

lemma Red_big_composition_medium_composition_more_oracles_UselessOracle_L : equiv[Comp_BigComposition.Game_BigComposition.d_UselessOracle ~ Red_big_composition_medium_composition_more_oracles(Comp_MediumComposition.Game_MediumComposition).d_UselessOracle :
      ={arg} /\ inv_big_composition_medium_composition_more_oracles_L
                  Comp_BigComposition.Game_BigComposition.abort_flag{1}
                  Red_big_composition_medium_composition_more_oracles.abort_flag{2}
                  Comp_MediumComposition.Game_MediumComposition.abort_flag{2}
                  (glob Comp_BigComposition.Cloned_Pkg_Fwd2.Fwd){1}
                  (glob Cloned_Pkg_Fwd2.Fwd){2}
                  (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1}
                  (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}
                  (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1}
                  (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2}
      ==> ={res} /\ inv_big_composition_medium_composition_more_oracles_L
                      Comp_BigComposition.Game_BigComposition.abort_flag{1}
                      Red_big_composition_medium_composition_more_oracles.abort_flag{2}
                      Comp_MediumComposition.Game_MediumComposition.abort_flag{2}
                      (glob Comp_BigComposition.Cloned_Pkg_Fwd2.Fwd){1}
                      (glob Cloned_Pkg_Fwd2.Fwd){2}
                      (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1}
                      (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}
                      (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1}
                      (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2}].
proof.
proc; inline *.
auto => /#.
qed.

lemma Red_big_composition_medium_composition_more_oracles_UselessOracle_R : equiv[Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles.d_UselessOracle ~ Red_big_composition_medium_composition_more_oracles(Comp_SmallComposition.Game_SmallComposition).d_UselessOracle :
      ={arg} /\ inv_big_composition_medium_composition_more_oracles_R
                  Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles.abort_flag{1}
                  Red_big_composition_medium_composition_more_oracles.abort_flag{2}
                  Comp_SmallComposition.Game_SmallComposition.abort_flag{2}
                  (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Fwd.Fwd){1}
                  (glob Cloned_Pkg_Fwd2.Fwd){2}
                  (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1}
                  (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}
      ==> ={res} /\ inv_big_composition_medium_composition_more_oracles_R
                      Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles.abort_flag{1}
                      Red_big_composition_medium_composition_more_oracles.abort_flag{2}
                      Comp_SmallComposition.Game_SmallComposition.abort_flag{2}
                      (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Fwd.Fwd){1}
                      (glob Cloned_Pkg_Fwd2.Fwd){2}
                      (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1}
                      (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}].
proof.
proc; inline *.
auto => /#.
qed.
