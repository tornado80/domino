(* Story 97 prototype: the first reduction of theorem `kem_dem_cca_ssp`
   (example-projects/kem-dem/kem-dem-cca-ssp),
   `Game_MOD_CCA_PKE_Real_KEM_Real_DEM ~ Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM`,
   written by hand against the exported tree. Story 98/99 generate this file; see
   docs/research/reduction-proof-script.md.

   Assumption KEM_CCA_Security: Game_CCA_KEM(b = false) ~ Game_CCA_KEM(b = true). The two
   assumption games are the same composition, so one reduction experiment.
   Mapped packages: Scheme_KEM, Key, KEM. Reduction packages: Scheme_DEM, DEM, MOD_CCA_PKE
   (same instance names on both sides). DEM imports Key.GET: a reduction package that calls
   a mapped package, so its import adapter is a functor over the assumption interface.

   `dem_idealization` is the literal `false` in this hop. The prototype treats it as if it
   were a theorem constant (story 97 section 3): B stores it with `setup`, the reduction
   experiment takes it, and the lemmas quantify it. *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Pkg_Scheme_DEM Pkg_DEM Pkg_MOD_CCA_PKE.
require Comp_Game_MOD_CCA_PKE Comp_Game_CCA_KEM.

(* ---- 1. The reduction router ------------------------------------------------ *)

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

(* ---- 2. The reduction adversary ---------------------------------------------- *)

module B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM (A : Interfaces.Adv_Game_MON_CCA_PKE) (O : Interfaces.Iface_Game_CCA_KEM) = {
  var dem_idealization : bool

  proc setup(dem_idealization_ : bool) : unit = {
    dem_idealization <- dem_idealization_;
  }

  proc run() : bool = {
    var b' : bool;
    Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(O).init(dem_idealization);
    b' <@ A(Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(O)).run();
    return b';
  }
}.

(* ---- 3. The reduction experiment (one: the assumption's two games are the same
        composition) ---------------------------------------------------------------- *)

module RedExp_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM (A : Interfaces.Adv_Game_MON_CCA_PKE) = {
  proc run(dem_idealization : bool, b : bool) : bool = {
    var b' : bool;
    B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(A, Comp_Game_CCA_KEM.Game_Game_CCA_KEM).setup(dem_idealization);
    b' <@ Comp_Game_CCA_KEM.Exp_Game_CCA_KEM(B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(A)).run(b);
    return b';
  }
}.

(* ---- 4. The proof ------------------------------------------------------------ *)

(* The invariant of both reduction equivalences (the two assumption games are the same
   composition, so one invariant and one set of oracle lemmas serve both sides), from the
   map: the game's abort flag is the router's, the assumption game's abort flag implies the
   router's, the constant stored by the adversary is the game's, and each package state
   equals its partner's (mapped Key, KEM; reduction packages DEM, MOD_CCA_PKE; Scheme_KEM
   and Scheme_DEM have no state). *)
op inv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM
  (game_abort red_abort assm_abort : bool)
  (const_l const_r : bool)
  (key_l : glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key) (key_r : glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key)
  (kem_l : glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM) (kem_r : glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM)
  (dem_l : glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM) (dem_r : glob Cloned_Pkg_DEM.DEM)
  (mod_l : glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE)
  (mod_r : glob Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE) : bool =
     game_abort = red_abort
  /\ (assm_abort => red_abort)
  /\ const_l = const_r
  /\ key_l = key_r
  /\ kem_l = kem_r
  /\ dem_l = dem_r
  /\ mod_l = mod_r.

section.

declare module A <: Interfaces.Adv_Game_MON_CCA_PKE {
  -Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_DEM.Scheme_DEM,
  -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM,
  -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE,
  -Comp_Game_CCA_KEM.Game_Game_CCA_KEM, -Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key, -Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM, -Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM,
  -Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM, -B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM, -Cloned_Pkg_Scheme_DEM.Scheme_DEM, -Cloned_Pkg_DEM.DEM,
  -Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE }.
local equiv Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_d_PKGEN :
  Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE.d_PKGEN ~ Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(Comp_Game_CCA_KEM.Game_Game_CCA_KEM).d_PKGEN :
  ={arg} /\ inv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM
    Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE.abort_flag{1} Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.abort_flag{2} Comp_Game_CCA_KEM.Game_Game_CCA_KEM.abort_flag{2} Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM.b{1} B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.dem_idealization{2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM){1} (glob Cloned_Pkg_DEM.DEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){1} (glob Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){2}
  ==> ={res} /\ inv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM
    Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE.abort_flag{1} Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.abort_flag{2} Comp_Game_CCA_KEM.Game_Game_CCA_KEM.abort_flag{2} Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM.b{1} B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.dem_idealization{2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM){1} (glob Cloned_Pkg_DEM.DEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){1} (glob Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){2}.
proof.
proc; inline *
  -Comp_Game_MOD_CCA_PKE.Pkg_Inst_Key
  -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key
  -Comp_Game_MOD_CCA_PKE.Pkg_Inst_KEM
  -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM
  -Comp_Game_MOD_CCA_PKE.Pkg_Inst_Scheme_KEM
  -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM
  -Comp_Game_CCA_KEM.Pkg_Inst_Key
  -Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key
  -Comp_Game_CCA_KEM.Pkg_Inst_KEM
  -Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM
  -Comp_Game_CCA_KEM.Pkg_Inst_Scheme_KEM
  -Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM.
do ? (sp; (
     (if; first by move=> /#)
  || (rcondt{2} 1; first by auto => /#)
  || (rcondf{2} 1; first by auto => /#)
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd2});
      first by (call (: (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd1});
      first by (call (: (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd0});
      first by (call (: (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd});
      first by (call (: (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM){2}); [by sim | by auto => /#]) || (auto => /#))
  || if{2})); auto => /#.
qed.
local equiv Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_d_PKENC :
  Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE.d_PKENC ~ Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(Comp_Game_CCA_KEM.Game_Game_CCA_KEM).d_PKENC :
  ={arg} /\ inv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM
    Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE.abort_flag{1} Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.abort_flag{2} Comp_Game_CCA_KEM.Game_Game_CCA_KEM.abort_flag{2} Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM.b{1} B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.dem_idealization{2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM){1} (glob Cloned_Pkg_DEM.DEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){1} (glob Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){2}
  ==> ={res} /\ inv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM
    Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE.abort_flag{1} Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.abort_flag{2} Comp_Game_CCA_KEM.Game_Game_CCA_KEM.abort_flag{2} Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM.b{1} B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.dem_idealization{2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM){1} (glob Cloned_Pkg_DEM.DEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){1} (glob Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){2}.
proof.
proc; inline *
  -Comp_Game_MOD_CCA_PKE.Pkg_Inst_Key
  -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key
  -Comp_Game_MOD_CCA_PKE.Pkg_Inst_KEM
  -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM
  -Comp_Game_MOD_CCA_PKE.Pkg_Inst_Scheme_KEM
  -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM
  -Comp_Game_CCA_KEM.Pkg_Inst_Key
  -Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key
  -Comp_Game_CCA_KEM.Pkg_Inst_KEM
  -Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM
  -Comp_Game_CCA_KEM.Pkg_Inst_Scheme_KEM
  -Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM.
do ? (sp; (
     (if; first by move=> /#)
  || (rcondt{2} 1; first by auto => /#)
  || (rcondf{2} 1; first by auto => /#)
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd2});
      first by (call (: (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd1});
      first by (call (: (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd0});
      first by (call (: (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd});
      first by (call (: (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM){2}); [by sim | by auto => /#]) || (auto => /#))
  || if{2})); auto => /#.
qed.
local equiv Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_d_PKDEC :
  Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE.d_PKDEC ~ Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(Comp_Game_CCA_KEM.Game_Game_CCA_KEM).d_PKDEC :
  ={arg} /\ inv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM
    Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE.abort_flag{1} Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.abort_flag{2} Comp_Game_CCA_KEM.Game_Game_CCA_KEM.abort_flag{2} Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM.b{1} B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.dem_idealization{2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM){1} (glob Cloned_Pkg_DEM.DEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){1} (glob Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){2}
  ==> ={res} /\ inv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM
    Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE.abort_flag{1} Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.abort_flag{2} Comp_Game_CCA_KEM.Game_Game_CCA_KEM.abort_flag{2} Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM.b{1} B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.dem_idealization{2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM){1} (glob Cloned_Pkg_DEM.DEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){1} (glob Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){2}.
proof.
proc; inline *
  -Comp_Game_MOD_CCA_PKE.Pkg_Inst_Key
  -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key
  -Comp_Game_MOD_CCA_PKE.Pkg_Inst_KEM
  -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM
  -Comp_Game_MOD_CCA_PKE.Pkg_Inst_Scheme_KEM
  -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM
  -Comp_Game_CCA_KEM.Pkg_Inst_Key
  -Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key
  -Comp_Game_CCA_KEM.Pkg_Inst_KEM
  -Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM
  -Comp_Game_CCA_KEM.Pkg_Inst_Scheme_KEM
  -Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM.
do ? (sp; (
     (if; first by move=> /#)
  || (rcondt{2} 1; first by auto => /#)
  || (rcondf{2} 1; first by auto => /#)
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd2});
      first by (call (: (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd1});
      first by (call (: (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd0});
      first by (call (: (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM){2}); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd});
      first by (call (: (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}
  /\ (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM){1} = (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM){2}); [by sim | by auto => /#]) || (auto => /#))
  || if{2})); auto => /#.
qed.
lemma Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_equiv_L &m (dem : bool) :
  Pr[Comp_Game_MOD_CCA_PKE.Exp_Game_MOD_CCA_PKE(A).run(dem, false) @ &m : res]
  = Pr[RedExp_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(A).run(dem, false) @ &m : res].
proof.
byequiv (: ={glob A} /\ arg{1} = (dem, false) /\ arg{2} = (dem, false) ==> ={res}) => //.
proc; inline *; wp.
call (: inv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM
    Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE.abort_flag{1} Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.abort_flag{2} Comp_Game_CCA_KEM.Game_Game_CCA_KEM.abort_flag{2} Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM.b{1} B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.dem_idealization{2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM){1} (glob Cloned_Pkg_DEM.DEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){1} (glob Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){2}).
+ by conseq Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_d_PKGEN => /#.
+ by conseq Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_d_PKENC => /#.
+ by conseq Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_d_PKDEC => /#.
by auto => /#.
qed.

lemma Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_equiv_R &m (dem : bool) :
  Pr[Comp_Game_MOD_CCA_PKE.Exp_Game_MOD_CCA_PKE(A).run(dem, true) @ &m : res]
  = Pr[RedExp_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(A).run(dem, true) @ &m : res].
proof.
byequiv (: ={glob A} /\ arg{1} = (dem, true) /\ arg{2} = (dem, true) ==> ={res}) => //.
proc; inline *; wp.
call (: inv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM
    Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE.abort_flag{1} Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.abort_flag{2} Comp_Game_CCA_KEM.Game_Game_CCA_KEM.abort_flag{2} Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM.b{1} B_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.dem_idealization{2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1} (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM){1} (glob Cloned_Pkg_DEM.DEM){2} (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){1} (glob Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){2}).
+ by conseq Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_d_PKGEN => /#.
+ by conseq Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_d_PKENC => /#.
+ by conseq Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_d_PKDEC => /#.
by auto => /#.
qed.

lemma Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_bound &m (dem : bool) :
  `|Pr[Comp_Game_MOD_CCA_PKE.Exp_Game_MOD_CCA_PKE(A).run(dem, false) @ &m : res]
    - Pr[Comp_Game_MOD_CCA_PKE.Exp_Game_MOD_CCA_PKE(A).run(dem, true) @ &m : res]|
  = `|Pr[RedExp_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(A).run(dem, false) @ &m : res] - Pr[RedExp_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(A).run(dem, true) @ &m : res]|.
proof. by rewrite (Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_equiv_L &m dem) (Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_equiv_R &m dem). qed.

end section.
