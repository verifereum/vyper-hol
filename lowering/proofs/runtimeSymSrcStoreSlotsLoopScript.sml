Theory runtimeSymSrcStoreSlotsLoop
Ancestors
  runtimeSymSrcContextCopy runtimeSymSrcEmission runtimeSymSrcContext
  runtimeSymSrcEmissionProbe context compileEnv emitHelper list venomInst stackPlanTypes

Theorem runtime_sym_copy_elements_to_slots_step:
  (!a b st u st'.
    ~is_label_operand a /\ ~is_label_operand b /\
    EVERY runtime_sym_inst (state_insts st) /\
    compile_store_slots cenv a b elem tr st = (u,st') ==>
    EVERY runtime_sym_inst (state_insts st')) ==>
  ~is_label_operand src /\ ~is_label_operand slot /\
  ~is_label_operand count_op /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_copy_elements_to_slots cenv src slot elem count_op tr s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  disch_tac >>
  simp[NoAsms, Once compile_store_slots_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  ntac 3 (qpat_x_assum `fresh_label _ _ = _`
    (mp_then Any mp_tac runtime_sym_fresh_label) >> strip_tac) >>
  qpat_x_assum `fresh_var _ = _`
    (mp_then Any mp_tac runtime_sym_fresh_var) >> strip_tac >> gvs[] >>
  qpat_x_assum `emit_inst ASSIGN [Lit 0w] _ _ = _`
    (mp_then Any mp_tac runtime_sym_assign) >>
  simp[is_label_operand_def] >> strip_tac >>
  last_x_assum (mp_then Any mp_tac runtime_sym_jump) >> simp[] >> strip_tac >>
  qpat_x_assum `new_block cond_lbl _ = _`
    (mp_then Any mp_tac runtime_sym_copy_new_block) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_op LT _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_op ISZERO _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_jnz) >> simp[] >> strip_tac >>
  qpat_x_assum `new_block body_lbl _ = _`
    (mp_then Any mp_tac runtime_sym_copy_new_block) >> simp[] >> strip_tac >>
  ntac 4 (last_x_assum (mp_then Any mp_tac runtime_sym_emit_op) >>
    simp[is_label_operand_def] >> strip_tac) >>
  qpat_x_assum `!a b st st'. _` (fn ih =>
    qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _`
      (mp_then Any mp_tac ih)) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_op ADD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_inst ASSIGN _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_assign) >> simp[] >> strip_tac >>
  last_x_assum (mp_then Any mp_tac runtime_sym_jump) >> simp[] >> strip_tac >>
  drule_all runtime_sym_copy_new_block >> simp[]
QED
