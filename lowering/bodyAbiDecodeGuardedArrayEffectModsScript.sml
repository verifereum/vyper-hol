Theory bodyAbiDecodeGuardedArrayEffectMods
Ancestors
  bodyAbiDecodeGuardedWordStoreMods
  bodyAbiDecodeArrayPrepareSuffixEffectMods
  bodyAbiDecodeArrayPrepareEffectMods
  bodyAbiDecodeArrayScratchEffectMods
  bodyAbiDecodeGuardedArrayBindMods
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib bodyFullAbiDecodeCutArraySyntaxLib

val bulk_all =
  let val tm = bodyAbiDecodeGuardedEffectSyntaxLib.beta (guarded_effect_bulk_clause ())
  in list_mk_forall (free_vars tm, tm) end;
val array_effect_clause = guarded_effect_array_clause ();

(* Use exact closed contracts, with no matching across the phase interfaces. *)
fun discharge_phase fact rule =
  MP (BETA_RULE rule) (BETA_RULE fact);

Theorem abi_decode_array_guarded_effect_mods:
  (^array_mode ==> ^array_straight_rule) ==>
  (^array_mode ==> ^array_bind_rule) ==>
  (^array_mode ==> ^array_revert_rule) ==>
  ^bulk_all ==> ^array_effect_clause
Proof
  BETA_TAC >>
  ACCEPT_TAC
    (let
       val suffix = abi_decode_array_prepare_suffix_width_joint_effect_mods
         |> discharge_phase abi_decode_owned_word_store_effect_mods
       val prepare = abi_decode_array_prepare_width_joint_if_suffix_effect_mods
         |> discharge_phase suffix
     in
       abi_decode_array_guarded_bind_effect_mods
       |> discharge_phase prepare
       |> discharge_phase abi_decode_array_scratch_loop_entry_horizon_joint_effect_mods
     end)
QED
