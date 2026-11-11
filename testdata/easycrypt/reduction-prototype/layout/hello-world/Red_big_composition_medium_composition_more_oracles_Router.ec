(* Red_big_composition_medium_composition_more_oracles_Router.ec for theorem `Proof`, the reduction to assumption `Assumption`: the router and the invariant — hand-written prototype of story 101 (ADR 0023). *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Pkg_Fwd Comp_BigComposition Comp_MediumCompositionMoreOracles Comp_MediumComposition Comp_SmallComposition.

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


op inv_big_composition_medium_composition_more_oracles_L (game_abort : bool) (red_abort : bool) (assm_abort : bool) (x0_l : (glob Comp_BigComposition.Cloned_Pkg_Fwd2.Fwd)) (x0_r : (glob Cloned_Pkg_Fwd2.Fwd)) (x1_l : (glob Comp_BigComposition.Cloned_Pkg_Rand.Rand)) (x1_r : (glob Comp_MediumComposition.Cloned_Pkg_Rand.Rand)) (x2_l : (glob Comp_BigComposition.Cloned_Pkg_Fwd.Fwd)) (x2_r : (glob Comp_MediumComposition.Cloned_Pkg_Fwd.Fwd)) : bool =
     game_abort = red_abort
  /\ (   assm_abort
      => red_abort)
  /\ x0_l = x0_r
  /\ x1_l = x1_r
  /\ x2_l = x2_r.

op inv_big_composition_medium_composition_more_oracles_R (game_abort : bool) (red_abort : bool) (assm_abort : bool) (x0_l : (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Fwd.Fwd)) (x0_r : (glob Cloned_Pkg_Fwd2.Fwd)) (x1_l : (glob Comp_MediumCompositionMoreOracles.Cloned_Pkg_Rand.Rand)) (x1_r : (glob Comp_SmallComposition.Cloned_Pkg_Rand.Rand)) : bool =
     game_abort = red_abort
  /\ (   assm_abort
      => red_abort)
  /\ x0_l = x0_r
  /\ x1_l = x1_r.
