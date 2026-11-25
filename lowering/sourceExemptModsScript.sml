Theory sourceExemptMods
Ancestors
  e2eDefs supportedProgram vyperContext vyperABI finite_map

(* A dynamic abi_decode may occur in an imported body or in the main
   module. Its type is interpreted in the linked unit's type environment. *)
Definition unspecified_behaviour_exempt_mods_def:
  unspecified_behaviour_exempt_mods mods e <=>
    (e = RuntimeError "abi_decode invalid" /\
     ?src tops ty. MEM (src, tops) mods /\
       occurs_abi_decode_target ty tops /\
       is_dynamic (vyper_to_abi_type (type_env_all_modules mods) ty)) \/
    e = RuntimeError "transfer_value recipient overflow"
End

Theorem unspecified_behaviour_exempt_mods_singleton:
  unspecified_behaviour_exempt_mods [(NONE, tops)] e <=>
    unspecified_behaviour_exempt tops e
Proof
  simp[unspecified_behaviour_exempt_mods_def, unspecified_behaviour_exempt_def,
       type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2]
QED
