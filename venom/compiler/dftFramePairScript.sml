(* Semantic classification and successful-pair boundaries for crossings. *)
Theory dftFramePair
Ancestors
  dftFramePrefix dftFrameSwap dftPermSim venomEffects dftDefs
  unitShapeDefs venomInst pred_set

Theorem dft_cross_effects:
  dft_cross a b ==> effects_independent a.inst_opcode b.inst_opcode
Proof
  simp[dft_cross_def, effects_independent_def, DISJOINT_UNION] >>
  metis_tac[DISJOINT_SYM]
QED

Theorem dft_cross_abort:
  dft_cross a b ==> abort_compatible a.inst_opcode b.inst_opcode
Proof
  simp[dft_cross_def, is_fallible_def] >> strip_tac >>
  gvs[abort_compatible_def, opcode_fail_class_def]
QED

Theorem dft_cross_not_two_invokes:
  dft_cross a b ==> ~(a.inst_opcode = INVOKE /\ b.inst_opcode = INVOKE)
Proof
  strip_tac >> drule dft_cross_effects >>
  rpt strip_tac >> gvs[effects_independent_def, read_effects_def, write_effects_def, all_effects_def]
QED

Theorem dft_cross_ext_independent:
  dft_cross a b /\ a.inst_opcode <> ALLOCA /\ b.inst_opcode <> ALLOCA /\
  ~is_ext_call_op a.inst_opcode /\ ~is_ext_call_op b.inst_opcode ==>
  ext_bi_independent a b
Proof
  strip_tac >> drule dft_cross_effects >> drule dft_cross_abort >>
  `~is_alloca_op a.inst_opcode /\ ~is_alloca_op b.inst_opcode` by
    (conj_tac >- (Cases_on `a.inst_opcode` >> gvs[is_alloca_op_def]) >>
     Cases_on `b.inst_opcode` >> gvs[is_alloca_op_def]) >>
  gvs[dft_cross_def, ext_bi_independent_def]
QED

Theorem dft_shape_external:
  inst_shape_ok e /\ is_ext_call_op e.inst_opcode ==>
  e.inst_opcode = CALL \/ e.inst_opcode = STATICCALL
Proof
  Cases_on `e.inst_opcode` >>
  simp[inst_shape_ok_def, is_ext_call_op_def]
QED

Theorem dft_external_observer:
  effects_independent e.inst_opcode p.inst_opcode /\
  (e.inst_opcode = CALL \/ e.inst_opcode = STATICCALL) ==>
  write_effects p.inst_opcode = {} /\
  p.inst_opcode <> INVOKE /\ ~is_ext_call_op p.inst_opcode /\
  DISJOINT (read_effects p.inst_opcode) (write_effects e.inst_opcode) /\
  (e.inst_opcode = CALL ==> read_effects p.inst_opcode = {})
Proof
  strip_tac >>
  gvs[effects_independent_def, DISJOINT_UNION, read_effects_def,
      write_effects_def] >>
  Cases_on `p.inst_opcode` >>
  fs[read_effects_def, write_effects_def, empty_effects_def,
     is_ext_call_op_def] >>
  fs[all_effects_def]
QED
