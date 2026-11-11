(* Red_mod_real_mod_ideal_Router.ec for theorem `RedConsts`, the reduction `mod_real ~ mod_ideal` to assumption `KeyAssumption`: the router and the invariant — hand-written prototype of story 101 (ADR 0023). *)
(* Reduction packages (left ~ right): mod ~ mod. The router uses the left names. *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Pkg_Mod Comp_ModGame Comp_KeyGame.

clone Pkg_Mod as Cloned_Pkg_Mod.

module Pkg_Imports_Mod (O : Interfaces.Iface_KeyGame) : Pkg_Mod.Mod_Imports = {
  proc d_Get() : bool option = {
    var r : bool option;
    r <@ O.d_Get();
    return r;
  }
}.

module Pkg_Inst_Mod (O : Interfaces.Iface_KeyGame) = Cloned_Pkg_Mod.Mod(Pkg_Imports_Mod(O)).

module Red_mod_real_mod_ideal (O : Interfaces.Iface_KeyGame) : Interfaces.Iface_ModGame = {
  var abort_flag : bool

  proc init(flip : bool) : unit = {
    abort_flag <- false;
    Pkg_Inst_Mod(O).init(flip);
  }

  proc d_Query() : bool option = {
    var ec_result : bool option <- None;
    if (!abort_flag) {
      ec_result <@ Pkg_Inst_Mod(O).d_Query();
      if (ec_result = None) {
        abort_flag <- true;
      }
    }
    return ec_result;
  }
}.

op inv_mod_real_mod_ideal (game_abort : bool) (red_abort : bool) (assm_abort : bool) (x0_l : (glob Comp_ModGame.Cloned_Pkg_Mod.Mod)) (x0_r : (glob Cloned_Pkg_Mod.Mod)) (x1_l : (glob Comp_ModGame.Cloned_Pkg_Key.Key)) (x1_r : (glob Comp_KeyGame.Cloned_Pkg_Key.Key)) : bool =
     game_abort = red_abort
  /\ (   assm_abort
      => red_abort)
  /\ x0_l = x0_r
  /\ x1_l = x1_r.
