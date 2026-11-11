(* Prop_RedConsts.ec for theorem `RedConsts` — hand-written prototype of story 101 (ADR 0023). *)
(* The fixture has no proposition. This file stands for the proposition `FlipBound` on the path *)
(*   mod_real[b := false] ~ mod_ideal[b := false] ~ mod_ideal[b := true] ~ mod_real[b := true], *)
(* which uses the reduction `mod_real ~ mod_ideal` twice (the second time in reverse) and has an open hop in the middle. *)
(* The two steps give two different values to `b`, which the reduction package `mod` reads (as `flip`), so the hop gets two adversaries. *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Red_mod_real_mod_ideal Red_mod_real_mod_ideal_Router Comp_ModGame Comp_KeyGame.

module B_mod_real_mod_ideal_b_false (A : Interfaces.Adv_ModGame) (O : Interfaces.Iface_KeyGame) = {
  proc run() : bool = {
    var b' : bool;
    Red_mod_real_mod_ideal_Router.Red_mod_real_mod_ideal(O).init(false);
    b' <@ A(Red_mod_real_mod_ideal_Router.Red_mod_real_mod_ideal(O)).run();
    return b';
  }
}.

module B_mod_real_mod_ideal_b_true (A : Interfaces.Adv_ModGame) (O : Interfaces.Iface_KeyGame) = {
  proc run() : bool = {
    var b' : bool;
    Red_mod_real_mod_ideal_Router.Red_mod_real_mod_ideal(O).init(true);
    b' <@ A(Red_mod_real_mod_ideal_Router.Red_mod_real_mod_ideal(O)).run();
    return b';
  }
}.

section.

declare module A <: Interfaces.Adv_ModGame { -Comp_ModGame.Game_ModGame, -Comp_ModGame.Cloned_Pkg_Key.Key, -Comp_ModGame.Cloned_Pkg_Mod.Mod, -Comp_KeyGame.Game_KeyGame, -Comp_KeyGame.Cloned_Pkg_Key.Key, -Red_mod_real_mod_ideal_Router.Red_mod_real_mod_ideal, -Red_mod_real_mod_ideal_Router.Cloned_Pkg_Mod.Mod }.

lemma equiv_mod_real_mod_ideal_b_false &m (ideal : bool) : Pr[Comp_ModGame.Exp_ModGame(A).run(false, ideal) @ &m : res] = Pr[Comp_KeyGame.Exp_KeyGame(B_mod_real_mod_ideal_b_false(A)).run(ideal) @ &m : res].
proof.
byequiv (: ={glob A} /\ arg{1} = (false, ideal) /\ arg{2} = ideal ==> ={res}) => //.
proc; inline *; wp.
call (Red_mod_real_mod_ideal.run_mod_real_mod_ideal A).
by auto => /#.
qed.

lemma bound_mod_real_mod_ideal_b_false &m : `|Pr[Comp_ModGame.Exp_ModGame(A).run(false, false) @ &m : res] - Pr[Comp_ModGame.Exp_ModGame(A).run(false, true) @ &m : res]| = `|Pr[Comp_KeyGame.Exp_KeyGame(B_mod_real_mod_ideal_b_false(A)).run(false) @ &m : res] - Pr[Comp_KeyGame.Exp_KeyGame(B_mod_real_mod_ideal_b_false(A)).run(true) @ &m : res]|.
proof.
by rewrite !(equiv_mod_real_mod_ideal_b_false &m).
qed.

lemma equiv_mod_real_mod_ideal_b_true &m (ideal : bool) : Pr[Comp_ModGame.Exp_ModGame(A).run(true, ideal) @ &m : res] = Pr[Comp_KeyGame.Exp_KeyGame(B_mod_real_mod_ideal_b_true(A)).run(ideal) @ &m : res].
proof.
byequiv (: ={glob A} /\ arg{1} = (true, ideal) /\ arg{2} = ideal ==> ={res}) => //.
proc; inline *; wp.
call (Red_mod_real_mod_ideal.run_mod_real_mod_ideal A).
by auto => /#.
qed.

lemma bound_mod_real_mod_ideal_b_true &m : `|Pr[Comp_ModGame.Exp_ModGame(A).run(true, false) @ &m : res] - Pr[Comp_ModGame.Exp_ModGame(A).run(true, true) @ &m : res]| = `|Pr[Comp_KeyGame.Exp_KeyGame(B_mod_real_mod_ideal_b_true(A)).run(false) @ &m : res] - Pr[Comp_KeyGame.Exp_KeyGame(B_mod_real_mod_ideal_b_true(A)).run(true) @ &m : res]|.
proof.
by rewrite !(equiv_mod_real_mod_ideal_b_true &m).
qed.

(* The proposition lemma of the path, with the open hop `mod_ideal[b := false] ~ mod_ideal[b := true]` as its own term. *)
lemma FlipBound &m : `|Pr[Comp_ModGame.Exp_ModGame(A).run(false, false) @ &m : res] - Pr[Comp_ModGame.Exp_ModGame(A).run(true, false) @ &m : res]| <= `|Pr[Comp_KeyGame.Exp_KeyGame(B_mod_real_mod_ideal_b_false(A)).run(false) @ &m : res] - Pr[Comp_KeyGame.Exp_KeyGame(B_mod_real_mod_ideal_b_false(A)).run(true) @ &m : res]| + (`|Pr[Comp_ModGame.Exp_ModGame(A).run(false, true) @ &m : res] - Pr[Comp_ModGame.Exp_ModGame(A).run(true, true) @ &m : res]| + `|Pr[Comp_KeyGame.Exp_KeyGame(B_mod_real_mod_ideal_b_true(A)).run(false) @ &m : res] - Pr[Comp_KeyGame.Exp_KeyGame(B_mod_real_mod_ideal_b_true(A)).run(true) @ &m : res]|).
proof.
have h0 := bound_mod_real_mod_ideal_b_false &m.
have h1 := bound_mod_real_mod_ideal_b_true &m.
smt().
qed.

end section.
