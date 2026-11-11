(* Red_mod_real_mod_ideal.ec for theorem `RedConsts`, the reduction `mod_real ~ mod_ideal` to assumption `KeyAssumption`: the run lemma — hand-written prototype of story 101 (ADR 0023). *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Comp_ModGame Comp_KeyGame.
require import Red_mod_real_mod_ideal_Router.
require import Red_mod_real_mod_ideal_Query.

section.

declare module A <: Interfaces.Adv_ModGame { -Comp_ModGame.Game_ModGame, -Comp_ModGame.Cloned_Pkg_Key.Key, -Comp_ModGame.Cloned_Pkg_Mod.Mod, -Comp_KeyGame.Game_KeyGame, -Comp_KeyGame.Cloned_Pkg_Key.Key, -Red_mod_real_mod_ideal, -Cloned_Pkg_Mod.Mod }.

lemma run_mod_real_mod_ideal : equiv[A(Comp_ModGame.Game_ModGame).run ~ A(Red_mod_real_mod_ideal(Comp_KeyGame.Game_KeyGame)).run :
      ={glob A} /\ inv_mod_real_mod_ideal
                     Comp_ModGame.Game_ModGame.abort_flag{1}
                     Red_mod_real_mod_ideal.abort_flag{2}
                     Comp_KeyGame.Game_KeyGame.abort_flag{2}
                     (glob Comp_ModGame.Cloned_Pkg_Mod.Mod){1}
                     (glob Cloned_Pkg_Mod.Mod){2}
                     (glob Comp_ModGame.Cloned_Pkg_Key.Key){1}
                     (glob Comp_KeyGame.Cloned_Pkg_Key.Key){2}
      ==> ={res} /\ inv_mod_real_mod_ideal
                      Comp_ModGame.Game_ModGame.abort_flag{1}
                      Red_mod_real_mod_ideal.abort_flag{2}
                      Comp_KeyGame.Game_KeyGame.abort_flag{2}
                      (glob Comp_ModGame.Cloned_Pkg_Mod.Mod){1}
                      (glob Cloned_Pkg_Mod.Mod){2}
                      (glob Comp_ModGame.Cloned_Pkg_Key.Key){1}
                      (glob Comp_KeyGame.Cloned_Pkg_Key.Key){2}].
proof.
proc (inv_mod_real_mod_ideal
        Comp_ModGame.Game_ModGame.abort_flag{1}
        Red_mod_real_mod_ideal.abort_flag{2}
        Comp_KeyGame.Game_KeyGame.abort_flag{2}
        (glob Comp_ModGame.Cloned_Pkg_Mod.Mod){1}
        (glob Cloned_Pkg_Mod.Mod){2}
        (glob Comp_ModGame.Cloned_Pkg_Key.Key){1}
        (glob Comp_KeyGame.Cloned_Pkg_Key.Key){2}) => //.
(* d_Query *)
by conseq Red_mod_real_mod_ideal_Query => /#.
qed.

end section.
