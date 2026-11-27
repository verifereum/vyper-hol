(* Public compatibility laws for the guarded decoder effect. *)
Theory bodyAbiDecodeGuardedEffectSyntaxMods
Ancestors
  venomState ptrDiscipline pred_set arithmetic
  bodyAbiDecodeGuardedEffectBaseMods
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib

Definition abi_decode_guarded_effect_def:
  abi_decode_guarded_effect (s:venom_state) tn t tf <=>
    s.vs_alloca_next <= t.vs_alloca_next /\
    tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\
    tf.t_imm = tn.t_imm /\
    (!i. i < s.vs_alloca_next /\ i IN tf.t_mem ==> i IN tn.t_mem)
End

Theorem abi_decode_guarded_effect_refl:
  abi_decode_guarded_effect s tn s tn
Proof
  simp[abi_decode_guarded_effect_def]
QED

Theorem abi_decode_guarded_effect_compose:
  abi_decode_guarded_effect s tn u tu /\
  abi_decode_guarded_effect u tu t tf ==>
  abi_decode_guarded_effect s tn t tf
Proof
  rw[abi_decode_guarded_effect_def] >>
  strip_tac >>
  rpt conj_tac >>
  metis_tac[]
QED
