(* Prop_BigToMedium.ec for theorem `Proof` — hand-written prototype of story 101 (ADR 0023). *)
(* hello-world has no proposition. This file stands for the one-step proposition *)
(*   BigToMedium: big_composition ~ medium_composition_more_oracles *)
(* on its reduction. The reduction packages read no theorem constant (`n` is a type parameter), so the hop has one adversary with an empty suffix. *)
(* The two sides use different game compositions (and different assumption compositions), so the merge rule does not apply: *)
(* one `_L` and one `_R` equivalence lemma, with literals (here: no arguments). *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Red_big_composition_medium_composition_more_oracles Red_big_composition_medium_composition_more_oracles_Router Comp_BigComposition Comp_MediumCompositionMoreOracles Comp_MediumComposition Comp_SmallComposition.

module B_big_composition_medium_composition_more_oracles (A : Interfaces.Adv_MediumCompositionMoreOracles) (O : Interfaces.Iface_SmallComposition) = {
  proc run() : bool = {
    var b' : bool;
    Red_big_composition_medium_composition_more_oracles_Router.Red_big_composition_medium_composition_more_oracles(O).init();
    b' <@ A(Red_big_composition_medium_composition_more_oracles_Router.Red_big_composition_medium_composition_more_oracles(O)).run();
    return b';
  }
}.

section.

declare module A <: Interfaces.Adv_MediumCompositionMoreOracles { -Comp_BigComposition.Game_BigComposition, -Comp_BigComposition.Cloned_Pkg_Rand.Rand, -Comp_BigComposition.Cloned_Pkg_Fwd.Fwd, -Comp_BigComposition.Cloned_Pkg_Fwd2.Fwd, -Comp_MediumComposition.Game_MediumComposition, -Comp_MediumComposition.Cloned_Pkg_Rand.Rand, -Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd, -Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles, -Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand, -Comp_MediumCompositionMoreOracles.Cloned_Pkg_Fwd.Fwd, -Comp_SmallComposition.Game_SmallComposition, -Comp_SmallComposition.Cloned_Pkg_Rand.Rand, -Red_big_composition_medium_composition_more_oracles_Router.Red_big_composition_medium_composition_more_oracles, -Red_big_composition_medium_composition_more_oracles_Router.Cloned_Pkg_Fwd2.Fwd }.

lemma equiv_big_composition_medium_composition_more_oracles_L &m : Pr[Comp_BigComposition.Exp_BigComposition(A).run() @ &m : res] = Pr[Comp_MediumComposition.Exp_MediumComposition(B_big_composition_medium_composition_more_oracles(A)).run() @ &m : res].
proof.
byequiv (: ={glob A} ==> ={res}) => //.
proc; inline *; wp.
call (Red_big_composition_medium_composition_more_oracles.run_big_composition_medium_composition_more_oracles_L A).
by auto => /#.
qed.

lemma equiv_big_composition_medium_composition_more_oracles_R &m : Pr[Comp_MediumCompositionMoreOracles.Exp_MediumCompositionMoreOracles(A).run() @ &m : res] = Pr[Comp_SmallComposition.Exp_SmallComposition(B_big_composition_medium_composition_more_oracles(A)).run() @ &m : res].
proof.
byequiv (: ={glob A} ==> ={res}) => //.
proc; inline *; wp.
call (Red_big_composition_medium_composition_more_oracles.run_big_composition_medium_composition_more_oracles_R A).
by auto => /#.
qed.

lemma bound_big_composition_medium_composition_more_oracles &m : `|Pr[Comp_BigComposition.Exp_BigComposition(A).run() @ &m : res] - Pr[Comp_MediumCompositionMoreOracles.Exp_MediumCompositionMoreOracles(A).run() @ &m : res]| = `|Pr[Comp_MediumComposition.Exp_MediumComposition(B_big_composition_medium_composition_more_oracles(A)).run() @ &m : res] - Pr[Comp_SmallComposition.Exp_SmallComposition(B_big_composition_medium_composition_more_oracles(A)).run() @ &m : res]|.
proof.
by rewrite (equiv_big_composition_medium_composition_more_oracles_L &m) (equiv_big_composition_medium_composition_more_oracles_R &m).
qed.

lemma BigToMedium &m : `|Pr[Comp_BigComposition.Exp_BigComposition(A).run() @ &m : res] - Pr[Comp_MediumCompositionMoreOracles.Exp_MediumCompositionMoreOracles(A).run() @ &m : res]| <= `|Pr[Comp_MediumComposition.Exp_MediumComposition(B_big_composition_medium_composition_more_oracles(A)).run() @ &m : res] - Pr[Comp_SmallComposition.Exp_SmallComposition(B_big_composition_medium_composition_more_oracles(A)).run() @ &m : res]|.
proof.
have h0 := bound_big_composition_medium_composition_more_oracles &m.
smt().
qed.

end section.
