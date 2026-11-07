Theory bodyPtrBytestringBuiltinsImmutableFrame
Ancestors bodyPtrBytestringBuiltinsScratchState compileEnv exprLoweringProps

Theorem immutables_rel_nonctor_data_frame:
  ~cenv.ce_is_ctor /\
  immutables_rel cenv addr src cenv.ce_is_ctor es s /\
  t.vs_data_section = s.vs_data_section ==>
  immutables_rel cenv addr src cenv.ce_is_ctor es t
Proof
  strip_tac >> gvs[immutables_rel_def] >> gvs[]
QED

Theorem immutable_base_zero_reserved_frame:
  immutable_base_zero cenv s /\ local_ptrs_reserved cenv st /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
  t.vs_labels = s.vs_labels ==>
  immutable_base_zero cenv t
Proof
  strip_tac >> irule immutable_base_zero_frame >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[local_ptrs_reserved_imm_base]
QED
