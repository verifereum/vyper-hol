Theory augAssignPtrScalarEmit
Ancestors augAssignPtrScalarCertificate exprLoweringProps emitHelperProps venomInst pred_set list

Theorem scalar_emit_op_code:
  emit_op opc ops s = (r,t) /\ EVERY (scalar_available A) ops /\
  ((scalar_binary opc /\ LENGTH ops = 2) \/
   (scalar_unary opc /\ LENGTH ops = 1)) ==>
  scalar_code A (emitted_insts s t)
Proof
  strip_tac >> drule emitted_insts_emit_op_local >> strip_tac >>
  simp[scalar_code_singleton, scalar_shape_def, mk_inst_def]
QED

Theorem scalar_emit_op_available:
  emit_op opc ops s = (r,t) ==>
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s t)))) r
Proof
  strip_tac >> drule emitted_insts_emit_op_local >> strip_tac >>
  simp[scalar_available_def, mk_inst_def]
QED

Theorem scalar_emit_assert_code:
  emit_void ASSERT [x] s = ((),t) /\ scalar_available A x ==>
  scalar_code A (emitted_insts s t)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  simp[scalar_code_singleton, scalar_shape_def, mk_inst_def]
QED

Theorem scalar_emitted_chain:
  u.cs_current_insts = s.cs_current_insts ++ emitted_insts s u /\
  t.cs_current_insts = u.cs_current_insts ++ emitted_insts u t /\
  scalar_code A (emitted_insts s u) /\
  scalar_code
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                 (emitted_insts s u))))
    (emitted_insts u t) ==>
  scalar_code A (emitted_insts s t)
Proof
  strip_tac >> drule_all emitted_insts_append >>
  disch_then SUBST1_TAC >> simp[scalar_code_append]
QED

Theorem scalar_emitted_available_union:
  u.cs_current_insts = s.cs_current_insts ++ emitted_insts s u /\
  t.cs_current_insts = u.cs_current_insts ++ emitted_insts u t ==>
  A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                              (emitted_insts s t))) =
  (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                               (emitted_insts s u)))) UNION
  BIGUNION (set (MAP (\i. set i.inst_outputs) (emitted_insts u t)))
Proof
  strip_tac >> drule_all emitted_insts_append >>
  disch_then SUBST1_TAC >> simp[UNION_ASSOC]
QED

Theorem scalar_available_after_code:
  scalar_available A x ==>
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) code))) x
Proof
  strip_tac >> irule scalar_available_mono >> qexists `A` >> simp[]
QED
