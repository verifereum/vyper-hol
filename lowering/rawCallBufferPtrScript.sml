Theory rawCallBufferPtr
Ancestors
  bodyPtrDefs representationCleanPtr exprSimProps oracleCallStepPtr
  finite_map pred_set

Theorem ptr_mem_ok_site:
  ptr_mem_ok cx ty v op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME w /\ val_footprint tv v <> 0 ==>
  ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
    b <= w2n w /\ w2n w + val_store_size tv v <= b + sz
Proof
  simp[ptr_mem_ok_def] >> metis_tac[]
QED

Theorem ptr_mem_ok_dynamic_bytes_site:
  ptr_mem_ok cx ty (BytesV bs) op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic n))) /\
  eval_operand op s = SOME w ==>
  ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
    b <= w2n w /\ w2n w + 32 + LENGTH bs <= b + sz
Proof
  strip_tac >>
  `val_footprint (BaseTV (BytesT (Dynamic n))) (BytesV bs) <> 0` by
    simp[loweringPostsTheory.val_footprint_def] >>
  drule_all ptr_mem_ok_site >> strip_tac >>
  qexistsl_tac [`x`, `b`, `sz`] >> simp[] >>
  mp_tac (Q.SPECL [`BaseTV (BytesT (Dynamic n))`, `BytesV bs`]
    val_footprint_le_store_size) >>
  simp[loweringPostsTheory.val_footprint_def] >> decide_tac
QED

Theorem ptr_mem_ok_dynamic_bytes_clean:
  ptr_mem_ok cx ty (BytesV bs) op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic n))) /\
  eval_operand op s = SOME w ==>
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
  (!i. w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) (w2n w) mem` by
    metis_tac[ptr_mem_ok_def] >>
  drule robust_val_in_memory_bytes_clean >> simp[]
QED


(* Opcode/operand interface, independent of instruction outputs and IDs. *)
Theorem revert_forward_pair_consecutive:
  get_instruction bb i = SOME copy /\
  get_instruction bb (SUC i) = SOME rev /\
  copy.inst_opcode = RETURNDATACOPY /\
  copy.inst_operands = [p; Lit 0w; rds] /\
  rev.inst_opcode = REVERT /\ rev.inst_operands = [p; rds] ==>
  revert_forward_pair bb i (SUC i)
Proof
  strip_tac >>
  simp[contextCodegenRelTheory.revert_forward_pair_def,
    contextCodegenRelTheory.resolve_block_assigns_def,
    contextCodegenRelPropsTheory.same_after_assigns_refl] >>
  rpt strip_tac >> fs[]
QED

Theorem revert_forward_access_taint:
  in_revert_forward fn s /\ about_to_revert fn inst s /\
  (inst.inst_opcode = RETURNDATACOPY \/ inst.inst_opcode = REVERT) /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands ==>
  access_ok lo G fn inst s /\ taint_ok fn tn inst s
Proof
  strip_tac >>
  fs[ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
    listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem ptr_inst_ok_forward_revert:
  inst.inst_opcode = REVERT /\ inst.inst_operands = [p; n] /\
  in_revert_forward fn s /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn inst s
Proof
  strip_tac >>
  `access_ok 0 G fn inst s /\ taint_ok fn tn inst s` by
    (irule revert_forward_access_taint >>
     simp[ptrDisciplineTheory.about_to_revert_def]) >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.allocas_from_def,
    venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_def, AllCaseEqs()]
QED

Theorem ptr_inst_ok_forward_copy:
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [p; src; n] /\
  in_revert_forward fn s /\ about_to_revert fn inst s /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn inst s
Proof
  strip_tac >>
  `access_ok 0 G fn inst s /\ taint_ok fn tn inst s` by
    (irule revert_forward_access_taint >> simp[]) >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.allocas_from_def,
    venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_def,
    venomStateTheory.write_memory_with_expansion_def,
    venomStateTheory.write_memory_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

(* Capacity and live-byte representation are independent: padding need not
   be clean. These folds work for output bytes and inline result tuples. *)
Theorem ptr_val_ok_from_covers:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ptr_covers G tn p s capacity /\ val_store_size tv v <= capacity /\
  (!w mem. lookup_var p s = SOME w /\
    mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem) ==>
  ptr_val_ok cx ty v (Var p) G tn s
Proof
  simp[ptr_covers_def, ptr_val_ok_def, ptr_mem_ok_def,
    venomStateTheory.eval_operand_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
    arithmeticTheory.LESS_EQ_MONO_ADD_EQ]
QED

Theorem ptr_buf_ok_from_covers:
  ptr_covers G tn p s capacity /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= capacity ==>
  ptr_buf_ok cenv e (Var p) G s
Proof
  simp[ptr_covers_def, ptr_buf_ok_def, venomStateTheory.eval_operand_def] >>
  rpt strip_tac >> gvs[] >>
  qexistsl_tac [`b`, `sz'`] >> simp[] >> decide_tac
QED
