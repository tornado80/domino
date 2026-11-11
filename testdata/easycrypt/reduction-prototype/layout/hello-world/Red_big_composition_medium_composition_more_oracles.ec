(* Red_big_composition_medium_composition_more_oracles.ec for theorem `Proof`, the reduction `big_composition ~ medium_composition_more_oracles` to assumption `Assumption`: the run lemmas — hand-written prototype of story 101 (ADR 0023). *)
(* The two sides use different compositions, so there is one run lemma for each side. *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Comp_BigComposition Comp_MediumCompositionMoreOracles Comp_MediumComposition Comp_SmallComposition.
require import Red_big_composition_medium_composition_more_oracles_Router.
require import Red_big_composition_medium_composition_more_oracles_UsefulOracle Red_big_composition_medium_composition_more_oracles_UselessOracle.

section.

declare module A <: Interfaces.Adv_MediumCompositionMoreOracles { -Comp_BigComposition.Game_BigComposition, -Comp_BigComposition.Cloned_Pkg_Rand.Rand, -Comp_BigComposition.Cloned_Pkg_Fwd.Fwd, -Comp_BigComposition.Cloned_Pkg_Fwd2.Fwd, -Comp_MediumComposition.Game_MediumComposition, -Comp_MediumComposition.Cloned_Pkg_Rand.Rand, -Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd, -Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles, -Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand, -Comp_MediumCompositionMoreOracles.Cloned_Pkg_Fwd.Fwd, -Comp_SmallComposition.Game_SmallComposition, -Comp_SmallComposition.Cloned_Pkg_Rand.Rand, -Red_big_composition_medium_composition_more_oracles, -Cloned_Pkg_Fwd2.Fwd }.

lemma run_big_composition_medium_composition_more_oracles_L : equiv[A(Comp_BigComposition.Game_BigComposition).run ~ A(Red_big_composition_medium_composition_more_oracles(Comp_MediumComposition.Game_MediumComposition)).run :
      ={glob A} /\ inv_big_composition_medium_composition_more_oracles_L
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
proc (inv_big_composition_medium_composition_more_oracles_L
                  Comp_BigComposition.Game_BigComposition.abort_flag{1}
                  Red_big_composition_medium_composition_more_oracles.abort_flag{2}
                  Comp_MediumComposition.Game_MediumComposition.abort_flag{2}
                  (glob Comp_BigComposition.Cloned_Pkg_Fwd2.Fwd){1}
                  (glob Cloned_Pkg_Fwd2.Fwd){2}
                  (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1}
                  (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}
                  (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1}
                  (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2}) => //.
(* d_UsefulOracle *)
+ by conseq Red_big_composition_medium_composition_more_oracles_UsefulOracle_L => /#.
(* d_UselessOracle *)
+ by conseq Red_big_composition_medium_composition_more_oracles_UselessOracle_L => /#.
qed.

lemma run_big_composition_medium_composition_more_oracles_R : equiv[A(Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles).run ~ A(Red_big_composition_medium_composition_more_oracles(Comp_SmallComposition.Game_SmallComposition)).run :
      ={glob A} /\ inv_big_composition_medium_composition_more_oracles_R
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
proc (inv_big_composition_medium_composition_more_oracles_R
                  Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles.abort_flag{1}
                  Red_big_composition_medium_composition_more_oracles.abort_flag{2}
                  Comp_SmallComposition.Game_SmallComposition.abort_flag{2}
                  (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Fwd.Fwd){1}
                  (glob Cloned_Pkg_Fwd2.Fwd){2}
                  (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1}
                  (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}) => //.
(* d_UsefulOracle *)
+ by conseq Red_big_composition_medium_composition_more_oracles_UsefulOracle_R => /#.
(* d_UselessOracle *)
+ by conseq Red_big_composition_medium_composition_more_oracles_UselessOracle_R => /#.
qed.

end section.
