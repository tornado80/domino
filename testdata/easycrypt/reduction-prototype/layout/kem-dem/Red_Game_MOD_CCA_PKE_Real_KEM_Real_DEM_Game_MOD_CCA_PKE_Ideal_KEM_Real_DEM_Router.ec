(* Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_Router.ec for theorem `kem_dem_cca_ssp`, the reduction to assumption `KEM_CCA_Security`: the router and the invariant — hand-written prototype of story 101 (ADR 0023). *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Pkg_Scheme_DEM Pkg_DEM Pkg_MOD_CCA_PKE Comp_Game_MOD_CCA_PKE Comp_Game_CCA_KEM.

clone Pkg_Scheme_DEM as Cloned_Pkg_Scheme_DEM.

clone Pkg_DEM as Cloned_Pkg_DEM.

clone Pkg_MOD_CCA_PKE as Cloned_Pkg_MOD_CCA_PKE.

module Pkg_Inst_Scheme_DEM = Cloned_Pkg_Scheme_DEM.Scheme_DEM.

module Pkg_Imports_DEM (O : Interfaces.Iface_Game_CCA_KEM) : Pkg_DEM.DEM_Imports = {
  proc d_DEM_DEC(k : bits_dkeyl, c : bits_dctl) : bits_ptl option = {
    var r : bits_ptl option;
    r <@ Pkg_Inst_Scheme_DEM.d_DEM_DEC(k, c);
    return r;
  }

  proc d_DEM_ENC(k : bits_dkeyl, m : bits_ptl) : bits_dctl option = {
    var r : bits_dctl option;
    r <@ Pkg_Inst_Scheme_DEM.d_DEM_ENC(k, m);
    return r;
  }

  proc d_GET() : bits_dkeyl option = {
    var r : bits_dkeyl option;
    r <@ O.d_GET();
    return r;
  }
}.

module Pkg_Inst_DEM (O : Interfaces.Iface_Game_CCA_KEM) = Cloned_Pkg_DEM.DEM(Pkg_Imports_DEM(O)).

module Pkg_Imports_MOD_CCA_PKE (O : Interfaces.Iface_Game_CCA_KEM) : Pkg_MOD_CCA_PKE.MOD_CCA_PKE_Imports = {
  proc d_DEC(c : bits_dctl) : bits_ptl option = {
    var r : bits_ptl option;
    r <@ Pkg_Inst_DEM(O).d_DEC(c);
    return r;
  }

  proc d_DECAPS(c_kem : bits_kctl) : bits_dkeyl option = {
    var r : bits_dkeyl option;
    r <@ O.d_DECAPS(c_kem);
    return r;
  }

  proc d_DEM_DEC(k : bits_dkeyl, c : bits_dctl) : bits_ptl option = {
    var r : bits_ptl option;
    r <@ Pkg_Inst_Scheme_DEM.d_DEM_DEC(k, c);
    return r;
  }

  proc d_ENC(m0 : bits_ptl, m1 : bits_ptl) : bits_dctl option = {
    var r : bits_dctl option;
    r <@ Pkg_Inst_DEM(O).d_ENC(m0, m1);
    return r;
  }

  proc d_ENCAPS() : bits_kctl option = {
    var r : bits_kctl option;
    r <@ O.d_ENCAPS();
    return r;
  }

  proc d_KEMGEN() : bits_pkeyl option = {
    var r : bits_pkeyl option;
    r <@ O.d_KEMGEN();
    return r;
  }
}.

module Pkg_Inst_MOD_CCA_PKE (O : Interfaces.Iface_Game_CCA_KEM) = Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE(Pkg_Imports_MOD_CCA_PKE(O)).

module Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM (O : Interfaces.Iface_Game_CCA_KEM) : Interfaces.Iface_Game_MON_CCA_PKE = {
  var abort_flag : bool

  proc init(dem_idealization : bool) : unit = {
    abort_flag <- false;
    Pkg_Inst_DEM(O).init(dem_idealization);
    Pkg_Inst_MOD_CCA_PKE(O).init();
  }

  proc d_PKGEN() : bits_pkeyl option = {
    var ec_result : bits_pkeyl option <- None;
    if (!abort_flag) {
      ec_result <@ Pkg_Inst_MOD_CCA_PKE(O).d_PKGEN();
      if (ec_result = None) {
        abort_flag <- true;
      }
    }
    return ec_result;
  }

  proc d_PKENC(m0 : bits_ptl, m1 : bits_ptl) : (bits_kctl * bits_dctl) option = {
    var ec_result : (bits_kctl * bits_dctl) option <- None;
    if (!abort_flag) {
      ec_result <@ Pkg_Inst_MOD_CCA_PKE(O).d_PKENC(m0, m1);
      if (ec_result = None) {
        abort_flag <- true;
      }
    }
    return ec_result;
  }

  proc d_PKDEC(c_ : (bits_kctl * bits_dctl)) : bits_ptl option = {
    var ec_result : bits_ptl option <- None;
    if (!abort_flag) {
      ec_result <@ Pkg_Inst_MOD_CCA_PKE(O).d_PKDEC(c_);
      if (ec_result = None) {
        abort_flag <- true;
      }
    }
    return ec_result;
  }
}.


op inv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM (game_abort : bool) (red_abort : bool) (assm_abort : bool) (x0_l : (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_DEM.Scheme_DEM)) (x0_r : (glob Cloned_Pkg_Scheme_DEM.Scheme_DEM)) (x1_l : (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM)) (x1_r : (glob Cloned_Pkg_DEM.DEM)) (x2_l : (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE)) (x2_r : (glob Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE)) (x3_l : (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM)) (x3_r : (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM)) (x4_l : (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key)) (x4_r : (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key)) (x5_l : (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM)) (x5_r : (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM)) : bool =
     game_abort = red_abort
  /\ (   assm_abort
      => red_abort)
  /\ x0_l = x0_r
  /\ x1_l = x1_r
  /\ x2_l = x2_r
  /\ x3_l = x3_r
  /\ x4_l = x4_r
  /\ x5_l = x5_r.
