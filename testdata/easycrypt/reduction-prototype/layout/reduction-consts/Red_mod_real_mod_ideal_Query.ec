(* Red_mod_real_mod_ideal_Query.ec for theorem `RedConsts`: the oracle lemma of `Query` in the reduction `mod_real ~ mod_ideal` — hand-written prototype of story 101 (ADR 0023). *)

require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Comp_ModGame Comp_KeyGame.
require import Red_mod_real_mod_ideal_Router.

lemma Red_mod_real_mod_ideal_Query : equiv[Comp_ModGame.Game_ModGame.d_Query ~ Red_mod_real_mod_ideal(Comp_KeyGame.Game_KeyGame).d_Query :
      ={arg} /\ inv_mod_real_mod_ideal
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
proc; inline *.
auto => /#.
qed.
