(* Story 97 prototype: the reduction `big_composition ~ medium_composition_more_oracles`
   of theorem `Proof` (example-projects/hello-world), written by hand against the
   exported tree. Story 98/99 generate this file; see docs/research/reduction-proof-script.md.

   Assumption: medium_composition ~ small_composition (two different compositions, so two
   reduction experiments, ADR 0022 decision 3).
   Map (left)  medium_composition -> big_composition                 { rand: rand, fwd: fwd }
   Map (right) small_composition  -> medium_composition_more_oracles { rand: rand }
   Reduction packages: fwd2 (left) paired with fwd (right). The router uses the left names. *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Pkg_Fwd.
require Comp_BigComposition Comp_MediumCompositionMoreOracles.
require Comp_MediumComposition Comp_SmallComposition.

(* ---- 1. The reduction router ------------------------------------------------ *)

clone Pkg_Fwd as Cloned_Pkg_Fwd2.

module Pkg_Imports_Fwd2 (O : Interfaces.Iface_SmallComposition) : Pkg_Fwd.Fwd_Imports = {
  proc d_UsefulOracle() : (int * bits_n) option = {
    var r : (int * bits_n) option;
    r <@ O.d_UsefulOracle();
    return r;
  }
}.

module Pkg_Inst_Fwd2 (O : Interfaces.Iface_SmallComposition) = Cloned_Pkg_Fwd2.Fwd(Pkg_Imports_Fwd2(O)).

module Red_big_composition_medium_composition_more_oracles (O : Interfaces.Iface_SmallComposition) : Interfaces.Iface_MediumCompositionMoreOracles = {
  var abort_flag : bool

  proc init() : unit = {
    abort_flag <- false;
    Pkg_Inst_Fwd2(O).init();
  }

  proc d_UsefulOracle() : (int * bits_n) option = {
    var ec_result : (int * bits_n) option <- None;
    if (!abort_flag) {
      ec_result <@ Pkg_Inst_Fwd2(O).d_UsefulOracle();
      if (ec_result = None) {
        abort_flag <- true;
      }
    }
    return ec_result;
  }

  proc d_UselessOracle(x : int) : int option = {
    var ec_result : int option <- None;
    if (!abort_flag) {
      ec_result <@ Pkg_Inst_Fwd2(O).d_UselessOracle(x);
      if (ec_result = None) {
        abort_flag <- true;
      }
    }
    return ec_result;
  }
}.

(* ---- 2. The reduction adversary ---------------------------------------------- *)

module B_big_composition_medium_composition_more_oracles (A : Interfaces.Adv_MediumCompositionMoreOracles) (O : Interfaces.Iface_SmallComposition) = {
  proc setup() : unit = { }

  proc run() : bool = {
    var b' : bool;
    Red_big_composition_medium_composition_more_oracles(O).init();
    b' <@ A(Red_big_composition_medium_composition_more_oracles(O)).run();
    return b';
  }
}.

(* ---- 3. The reduction experiments (one for each side: the assumption's games are
        different compositions) ------------------------------------------------- *)

module RedExp_big_composition_medium_composition_more_oracles_L (A : Interfaces.Adv_MediumCompositionMoreOracles) = {
  proc run() : bool = {
    var b' : bool;
    B_big_composition_medium_composition_more_oracles(A, Comp_MediumComposition.Game_MediumComposition).setup();
    b' <@ Comp_MediumComposition.Exp_MediumComposition(B_big_composition_medium_composition_more_oracles(A)).run();
    return b';
  }
}.

module RedExp_big_composition_medium_composition_more_oracles_R (A : Interfaces.Adv_MediumCompositionMoreOracles) = {
  proc run() : bool = {
    var b' : bool;
    B_big_composition_medium_composition_more_oracles(A, Comp_SmallComposition.Game_SmallComposition).setup();
    b' <@ Comp_SmallComposition.Exp_SmallComposition(B_big_composition_medium_composition_more_oracles(A)).run();
    return b';
  }
}.
(* ---- 4. The proof ------------------------------------------------------------ *)

(* The invariant of the left reduction equivalence, from the map: the game's abort flag is
   the router's, the assumption game's abort flag implies the router's, and each package
   state equals its partner's (reduction package fwd2 ~ router fwd2; mapped fwd, rand). *)
op inv_big_composition_medium_composition_more_oracles_L
  (game_abort red_abort assm_abort : bool)
  (fwd2_l : glob Comp_BigComposition.Cloned_Pkg_Fwd2.Fwd) (fwd2_r : glob Cloned_Pkg_Fwd2.Fwd)
  (fwd_l  : glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd)  (fwd_r  : glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd)
  (rand_l : glob Comp_BigComposition.Cloned_Pkg_Rand.Rand) (rand_r : glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand) : bool =
     game_abort = red_abort
  /\ (assm_abort => red_abort)
  /\ fwd2_l = fwd2_r
  /\ fwd_l = fwd_r
  /\ rand_l = rand_r.

(* The invariant of the right reduction equivalence (reduction package fwd ~ router fwd2;
   mapped rand). *)
op inv_big_composition_medium_composition_more_oracles_R
  (game_abort red_abort assm_abort : bool)
  (fwd_l  : glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Fwd.Fwd)  (fwd2_r : glob Cloned_Pkg_Fwd2.Fwd)
  (rand_l : glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand) (rand_r : glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand) : bool =
     game_abort = red_abort
  /\ (assm_abort => red_abort)
  /\ fwd_l = fwd2_r
  /\ rand_l = rand_r.

section.

declare module A <: Interfaces.Adv_MediumCompositionMoreOracles {
  -Comp_BigComposition.Game_BigComposition, -Comp_BigComposition.Cloned_Pkg_Rand.Rand,
  -Comp_BigComposition.Cloned_Pkg_Fwd.Fwd, -Comp_BigComposition.Cloned_Pkg_Fwd2.Fwd,
  -Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles, -Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand,
  -Comp_MediumCompositionMoreOracles.Cloned_Pkg_Fwd.Fwd,
  -Comp_MediumComposition.Game_MediumComposition, -Comp_MediumComposition.Cloned_Pkg_Rand.Rand, -Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd,
  -Comp_SmallComposition.Game_SmallComposition, -Comp_SmallComposition.Cloned_Pkg_Rand.Rand,
  -Red_big_composition_medium_composition_more_oracles, -B_big_composition_medium_composition_more_oracles, -Cloned_Pkg_Fwd2.Fwd }.
local equiv big_composition_medium_composition_more_oracles_L_d_UsefulOracle :
  Comp_BigComposition.Game_BigComposition.d_UsefulOracle ~ Red_big_composition_medium_composition_more_oracles(Comp_MediumComposition.Game_MediumComposition).d_UsefulOracle :
  ={arg} /\ inv_big_composition_medium_composition_more_oracles_L
    Comp_BigComposition.Game_BigComposition.abort_flag{1} Red_big_composition_medium_composition_more_oracles.abort_flag{2} Comp_MediumComposition.Game_MediumComposition.abort_flag{2} (glob Comp_BigComposition.Cloned_Pkg_Fwd2.Fwd){1} (glob Cloned_Pkg_Fwd2.Fwd){2} (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1} (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2} (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1} (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}
  ==> ={res} /\ inv_big_composition_medium_composition_more_oracles_L
    Comp_BigComposition.Game_BigComposition.abort_flag{1} Red_big_composition_medium_composition_more_oracles.abort_flag{2} Comp_MediumComposition.Game_MediumComposition.abort_flag{2} (glob Comp_BigComposition.Cloned_Pkg_Fwd2.Fwd){1} (glob Cloned_Pkg_Fwd2.Fwd){2} (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1} (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2} (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1} (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}.
proof.
proc; inline *
  -Comp_BigComposition.Pkg_Inst_Fwd
  -Comp_BigComposition.Cloned_Pkg_Fwd.Fwd
  -Comp_BigComposition.Pkg_Inst_Rand
  -Comp_BigComposition.Cloned_Pkg_Rand.Rand
  -Comp_MediumComposition.Pkg_Inst_Fwd
  -Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd
  -Comp_MediumComposition.Pkg_Inst_Rand
  -Comp_MediumComposition.Cloned_Pkg_Rand.Rand.
do ? (sp; (
     (if; first by move=> /#)
  || (rcondt{2} 1; first by auto => /#)
  || (rcondf{2} 1; first by auto => /#)
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd2});
      first by (call (: (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1} = (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2}
  /\ (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1} = (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd1});
      first by (call (: (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1} = (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2}
  /\ (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1} = (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd0});
      first by (call (: (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1} = (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2}
  /\ (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1} = (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd});
      first by (call (: (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1} = (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2}
  /\ (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1} = (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || if{2})); auto => /#.
qed.
local equiv big_composition_medium_composition_more_oracles_L_d_UselessOracle :
  Comp_BigComposition.Game_BigComposition.d_UselessOracle ~ Red_big_composition_medium_composition_more_oracles(Comp_MediumComposition.Game_MediumComposition).d_UselessOracle :
  ={arg} /\ inv_big_composition_medium_composition_more_oracles_L
    Comp_BigComposition.Game_BigComposition.abort_flag{1} Red_big_composition_medium_composition_more_oracles.abort_flag{2} Comp_MediumComposition.Game_MediumComposition.abort_flag{2} (glob Comp_BigComposition.Cloned_Pkg_Fwd2.Fwd){1} (glob Cloned_Pkg_Fwd2.Fwd){2} (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1} (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2} (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1} (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}
  ==> ={res} /\ inv_big_composition_medium_composition_more_oracles_L
    Comp_BigComposition.Game_BigComposition.abort_flag{1} Red_big_composition_medium_composition_more_oracles.abort_flag{2} Comp_MediumComposition.Game_MediumComposition.abort_flag{2} (glob Comp_BigComposition.Cloned_Pkg_Fwd2.Fwd){1} (glob Cloned_Pkg_Fwd2.Fwd){2} (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1} (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2} (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1} (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}.
proof.
proc; inline *
  -Comp_BigComposition.Pkg_Inst_Fwd
  -Comp_BigComposition.Cloned_Pkg_Fwd.Fwd
  -Comp_BigComposition.Pkg_Inst_Rand
  -Comp_BigComposition.Cloned_Pkg_Rand.Rand
  -Comp_MediumComposition.Pkg_Inst_Fwd
  -Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd
  -Comp_MediumComposition.Pkg_Inst_Rand
  -Comp_MediumComposition.Cloned_Pkg_Rand.Rand.
do ? (sp; (
     (if; first by move=> /#)
  || (rcondt{2} 1; first by auto => /#)
  || (rcondf{2} 1; first by auto => /#)
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd2});
      first by (call (: (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1} = (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2}
  /\ (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1} = (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd1});
      first by (call (: (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1} = (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2}
  /\ (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1} = (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd0});
      first by (call (: (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1} = (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2}
  /\ (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1} = (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd});
      first by (call (: (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1} = (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2}
  /\ (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1} = (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || if{2})); auto => /#.
qed.
local equiv big_composition_medium_composition_more_oracles_R_d_UsefulOracle :
  Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles.d_UsefulOracle ~ Red_big_composition_medium_composition_more_oracles(Comp_SmallComposition.Game_SmallComposition).d_UsefulOracle :
  ={arg} /\ inv_big_composition_medium_composition_more_oracles_R
    Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles.abort_flag{1} Red_big_composition_medium_composition_more_oracles.abort_flag{2} Comp_SmallComposition.Game_SmallComposition.abort_flag{2} (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Fwd.Fwd){1} (glob Cloned_Pkg_Fwd2.Fwd){2} (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1} (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}
  ==> ={res} /\ inv_big_composition_medium_composition_more_oracles_R
    Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles.abort_flag{1} Red_big_composition_medium_composition_more_oracles.abort_flag{2} Comp_SmallComposition.Game_SmallComposition.abort_flag{2} (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Fwd.Fwd){1} (glob Cloned_Pkg_Fwd2.Fwd){2} (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1} (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}.
proof.
proc; inline *
  -Comp_MediumCompositionMoreOracles.Pkg_Inst_Rand
  -Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand
  -Comp_SmallComposition.Pkg_Inst_Rand
  -Comp_SmallComposition.Cloned_Pkg_Rand.Rand.
do ? (sp; (
     (if; first by move=> /#)
  || (rcondt{2} 1; first by auto => /#)
  || (rcondf{2} 1; first by auto => /#)
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd2});
      first by (call (: (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1} = (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd1});
      first by (call (: (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1} = (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd0});
      first by (call (: (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1} = (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd});
      first by (call (: (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1} = (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || if{2})); auto => /#.
qed.
local equiv big_composition_medium_composition_more_oracles_R_d_UselessOracle :
  Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles.d_UselessOracle ~ Red_big_composition_medium_composition_more_oracles(Comp_SmallComposition.Game_SmallComposition).d_UselessOracle :
  ={arg} /\ inv_big_composition_medium_composition_more_oracles_R
    Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles.abort_flag{1} Red_big_composition_medium_composition_more_oracles.abort_flag{2} Comp_SmallComposition.Game_SmallComposition.abort_flag{2} (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Fwd.Fwd){1} (glob Cloned_Pkg_Fwd2.Fwd){2} (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1} (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}
  ==> ={res} /\ inv_big_composition_medium_composition_more_oracles_R
    Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles.abort_flag{1} Red_big_composition_medium_composition_more_oracles.abort_flag{2} Comp_SmallComposition.Game_SmallComposition.abort_flag{2} (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Fwd.Fwd){1} (glob Cloned_Pkg_Fwd2.Fwd){2} (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1} (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}.
proof.
proc; inline *
  -Comp_MediumCompositionMoreOracles.Pkg_Inst_Rand
  -Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand
  -Comp_SmallComposition.Pkg_Inst_Rand
  -Comp_SmallComposition.Cloned_Pkg_Rand.Rand.
do ? (sp; (
     (if; first by move=> /#)
  || (rcondt{2} 1; first by auto => /#)
  || (rcondf{2} 1; first by auto => /#)
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd2});
      first by (call (: (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1} = (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd1});
      first by (call (: (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1} = (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd0});
      first by (call (: (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1} = (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd});
      first by (call (: (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1} = (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}); [by sim | by auto => /#]) || (auto => /#))
  || if{2})); auto => /#.
qed.
lemma big_composition_medium_composition_more_oracles_equiv_L &m :
  Pr[Comp_BigComposition.Exp_BigComposition(A).run() @ &m : res]
  = Pr[RedExp_big_composition_medium_composition_more_oracles_L(A).run() @ &m : res].
proof.
byequiv (: ={glob A} ==> ={res}) => //.
proc; inline *; wp.
call (: inv_big_composition_medium_composition_more_oracles_L
    Comp_BigComposition.Game_BigComposition.abort_flag{1} Red_big_composition_medium_composition_more_oracles.abort_flag{2} Comp_MediumComposition.Game_MediumComposition.abort_flag{2} (glob Comp_BigComposition.Cloned_Pkg_Fwd2.Fwd){1} (glob Cloned_Pkg_Fwd2.Fwd){2} (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd){1} (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd){2} (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand){1} (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand){2}).
+ by conseq big_composition_medium_composition_more_oracles_L_d_UsefulOracle => /#.
+ by conseq big_composition_medium_composition_more_oracles_L_d_UselessOracle => /#.
by auto => /#.
qed.

lemma big_composition_medium_composition_more_oracles_equiv_R &m :
  Pr[Comp_MediumCompositionMoreOracles.Exp_MediumCompositionMoreOracles(A).run() @ &m : res]
  = Pr[RedExp_big_composition_medium_composition_more_oracles_R(A).run() @ &m : res].
proof.
byequiv (: ={glob A} ==> ={res}) => //.
proc; inline *; wp.
call (: inv_big_composition_medium_composition_more_oracles_R
    Comp_MediumCompositionMoreOracles.Game_MediumCompositionMoreOracles.abort_flag{1} Red_big_composition_medium_composition_more_oracles.abort_flag{2} Comp_SmallComposition.Game_SmallComposition.abort_flag{2} (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Fwd.Fwd){1} (glob Cloned_Pkg_Fwd2.Fwd){2} (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand){1} (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand){2}).
+ by conseq big_composition_medium_composition_more_oracles_R_d_UsefulOracle => /#.
+ by conseq big_composition_medium_composition_more_oracles_R_d_UselessOracle => /#.
by auto => /#.
qed.

lemma big_composition_medium_composition_more_oracles_bound &m :
  `|Pr[Comp_BigComposition.Exp_BigComposition(A).run() @ &m : res]
    - Pr[Comp_MediumCompositionMoreOracles.Exp_MediumCompositionMoreOracles(A).run() @ &m : res]|
  = `|Pr[RedExp_big_composition_medium_composition_more_oracles_L(A).run() @ &m : res] - Pr[RedExp_big_composition_medium_composition_more_oracles_R(A).run() @ &m : res]|.
proof. by rewrite (big_composition_medium_composition_more_oracles_equiv_L &m) (big_composition_medium_composition_more_oracles_equiv_R &m). qed.

end section.
