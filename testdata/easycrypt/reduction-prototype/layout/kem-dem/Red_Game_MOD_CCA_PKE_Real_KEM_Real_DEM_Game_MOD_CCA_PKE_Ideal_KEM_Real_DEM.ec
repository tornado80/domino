(* Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.ec for theorem `kem_dem_cca_ssp`, the reduction `Game_MOD_CCA_PKE_Real_KEM_Real_DEM ~ Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM` to assumption `KEM_CCA_Security`: the run lemma — hand-written prototype of story 101 (ADR 0023). *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Comp_Game_MOD_CCA_PKE Comp_Game_CCA_KEM.
require import Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_Router.
require import Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_PKGEN Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_PKENC Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_PKDEC.

section.

declare module A <: Interfaces.Adv_Game_MON_CCA_PKE { -Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Key.Key, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_DEM.Scheme_DEM, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_Scheme_KEM.Scheme_KEM, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_DEM.DEM, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_KEM.KEM, -Comp_Game_MOD_CCA_PKE.Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE, -Comp_Game_CCA_KEM.Game_Game_CCA_KEM, -Comp_Game_CCA_KEM.Cloned_Pkg_Scheme_KEM.Scheme_KEM, -Comp_Game_CCA_KEM.Cloned_Pkg_Key.Key, -Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM, -Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM, -Cloned_Pkg_Scheme_DEM.Scheme_DEM, -Cloned_Pkg_DEM.DEM, -Cloned_Pkg_MOD_CCA_PKE.MOD_CCA_PKE }.

lemma run_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM : equiv[A(Comp_Game_MOD_CCA_PKE.Game_Game_MOD_CCA_PKE).run ~ A(Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM(Comp_Game_CCA_KEM.Game_Game_CCA_KEM)).run :
      ={glob A} /\ inv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM
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
proc (inv_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM
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
                  (glob Comp_Game_CCA_KEM.Cloned_Pkg_KEM.KEM){2}) => //.
(* d_PKGEN *)
+ by conseq Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_PKGEN => /#.
(* d_PKENC *)
+ by conseq Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_PKENC => /#.
(* d_PKDEC *)
+ by conseq Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM_PKDEC => /#.
qed.

end section.
