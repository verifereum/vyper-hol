(* Public compatibility laws for the guarded decoder effect. *)
Theory bodyAbiDecodeGuardedEffectSyntaxMods
Ancestors
  bodyAbiDecodeGuardedEffectBaseMods
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib

Theorem abi_decode_guarded_effect_refl:
  abi_decode_guarded_effect s tn s tn
Proof
  ACCEPT_TAC abi_decode_guarded_effect_refl_core
QED

Theorem abi_decode_guarded_effect_compose:
  abi_decode_guarded_effect s tn u tu /\
  abi_decode_guarded_effect u tu t tf ==>
  abi_decode_guarded_effect s tn t tf
Proof
  ACCEPT_TAC abi_decode_guarded_effect_compose_core
QED
