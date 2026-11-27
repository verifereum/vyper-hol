(* Effects of one normal phase, on the same machine and taint witnesses. *)
Theory bodyAbiDecodeGuardedEffectBaseMods
Ancestors
  venomState ptrDiscipline pred_set arithmetic
  bodyFullAbiDecodeLoopObservedSyntax abiDecoderLoopSetup
  bodyFullAbiDecodeCutPath
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib

Definition abi_decode_guarded_effect_core_def:
  abi_decode_guarded_effect_core (s:venom_state) tn t tf <=>
    s.vs_alloca_next <= t.vs_alloca_next /\
    tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\
    tf.t_imm = tn.t_imm /\
    (!i. i < s.vs_alloca_next /\ i IN tf.t_mem ==> i IN tn.t_mem)
End

Theorem abi_decode_guarded_effect_refl_core:
  abi_decode_guarded_effect_core s tn s tn
Proof
  simp[abi_decode_guarded_effect_core_def]
QED

Theorem abi_decode_guarded_effect_compose_core:
  abi_decode_guarded_effect_core s tn u tu /\
  abi_decode_guarded_effect_core u tu t tf ==>
  abi_decode_guarded_effect_core s tn t tf
Proof
  rw[abi_decode_guarded_effect_core_def]
QED

val _ = check_guarded_effect_syntax ();
