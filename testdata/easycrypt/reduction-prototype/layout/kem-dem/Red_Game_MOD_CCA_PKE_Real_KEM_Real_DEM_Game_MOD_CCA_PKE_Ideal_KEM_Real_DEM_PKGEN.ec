(* Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_PKGEN.ec for theorem `kem_dem_cca_ssp`: the oracle lemma of `PKGEN` — hand-written prototype of story 101 (ADR 0023). *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Comp_Game_MOD_CCA_PKE Comp_Game_CCA_KEM.
require import Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_Router.

lemma Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_PKGEN : equiv[Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE.d_PKGEN ~ Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(Comp_Game_CCA_KEM.Game_Game_CCA_KEM).d_PKGEN :
      ={arg} /\ inv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM
                  Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE.abort_flag{1}
                  Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.abort_flag{2}
                  Comp_Game_CCA_KEM.Game_Game_CCA_KEM.abort_flag{2}
                  (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_DEM.Scheme_DEM){1}
                  (glob Cloned_Pkg_Scheme_DEM.Scheme_DEM){2}
                  (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM){1}
                  (glob Cloned_Pkg_DEM.DEM){2}
                  (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){1}
                  (glob Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){2}
                  (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM){1}
                  (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM){2}
                  (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1}
                  (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2}
                  (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1}
                  (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}
      ==> ={res} /\ inv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM
                      Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE.abort_flag{1}
                      Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.abort_flag{2}
                      Comp_Game_CCA_KEM.Game_Game_CCA_KEM.abort_flag{2}
                      (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_DEM.Scheme_DEM){1}
                      (glob Cloned_Pkg_Scheme_DEM.Scheme_DEM){2}
                      (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM){1}
                      (glob Cloned_Pkg_DEM.DEM){2}
                      (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){1}
                      (glob Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE){2}
                      (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM){1}
                      (glob Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM){2}
                      (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key){1}
                      (glob Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key){2}
                      (glob Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM){1}
                      (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}].
proof.
proc; inline *.
sp 1 1.
if.
+ auto => /#.
+ sp 1 1.
  if.
  + auto => /#.
  + sp 1 1.
    rcondt{2} ^if; 1: auto => /#.
    sp 0 1.
    if.
    + auto => /#.
    + auto => /#.
    + auto => /#.
  + auto => /#.
+ auto => /#.
qed.
