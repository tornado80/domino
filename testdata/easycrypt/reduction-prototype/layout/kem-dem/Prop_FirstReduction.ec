(* Prop_FirstReduction.ec for theorem `kem_dem_cca_ssp` — hand-written prototype of story 101 (ADR 0023). *)
(* The theorem's proposition `Main` has three reductions. This file stands for the one-step proposition *)
(*   FirstReduction: Game_MOD_CCA_PKE_Real_KEM_Real_DEM ~ Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM *)
(* on the first one. Its reduction packages read no free theorem constant, so the hop has one adversary with an empty suffix. *)
(* Both sides use the same game composition and the same assumption composition, and the game's differing pairs, *)
(* {(false, true)} at `key_idealization`, equal the assumption's, {(false, true)} at `b`: one merged lemma, binder `key_idealization`. *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_Router Comp_Game_MOD_CCA_PKE Comp_Game_CCA_KEM.

module B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM (A : Interfaces.Adv_Game_MON_CCA_PKE) (O : Interfaces.Iface_Game_CCA_KEM) = {
  proc run() : bool = {
    var b' : bool;
    Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_Router.Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(O).init(false);
    b' <@ A(Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_Router.Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(O)).run();
    return b';
  }
}.

section.

declare module A <: Interfaces.Adv_Game_MON_CCA_PKE { -Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_DEM.Scheme_DEM, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE, -Comp_Game_CCA_KEM.Game_Game_CCA_KEM, -Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM, -Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key, -Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM, -Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_Router.Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM, -Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_Router.Cloned_Pkg_Scheme_DEM.Scheme_DEM, -Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_Router.Cloned_Pkg_DEM.DEM, -Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_Router.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE }.

lemma equiv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM &m (key_idealization : bool) : Pr[Comp_Game_MOD_CCA_PKE.Exp_Game_MOD_CCA_PKE(A).run(false, key_idealization) @ &m : res] = Pr[Comp_Game_CCA_KEM.Exp_Game_CCA_KEM(B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(A)).run(key_idealization) @ &m : res].
proof.
byequiv (: ={glob A} /\ arg{1} = (false, key_idealization) /\ arg{2} = key_idealization ==> ={res}) => //.
proc; inline *; wp.
call (Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.run_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM A).
by auto => /#.
qed.

lemma bound_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM &m : `|Pr[Comp_Game_MOD_CCA_PKE.Exp_Game_MOD_CCA_PKE(A).run(false, false) @ &m : res] - Pr[Comp_Game_MOD_CCA_PKE.Exp_Game_MOD_CCA_PKE(A).run(false, true) @ &m : res]| = `|Pr[Comp_Game_CCA_KEM.Exp_Game_CCA_KEM(B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(A)).run(false) @ &m : res] - Pr[Comp_Game_CCA_KEM.Exp_Game_CCA_KEM(B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(A)).run(true) @ &m : res]|.
proof.
by rewrite !(equiv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM &m).
qed.

lemma FirstReduction &m : `|Pr[Comp_Game_MOD_CCA_PKE.Exp_Game_MOD_CCA_PKE(A).run(false, false) @ &m : res] - Pr[Comp_Game_MOD_CCA_PKE.Exp_Game_MOD_CCA_PKE(A).run(false, true) @ &m : res]| <= `|Pr[Comp_Game_CCA_KEM.Exp_Game_CCA_KEM(B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(A)).run(false) @ &m : res] - Pr[Comp_Game_CCA_KEM.Exp_Game_CCA_KEM(B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(A)).run(true) @ &m : res]|.
proof.
have h0 := bound_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM &m.
smt().
qed.

end section.
