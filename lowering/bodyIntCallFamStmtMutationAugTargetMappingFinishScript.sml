(* Allocating mapping hash suffix, with resources on the actual counted run. *)
Theory bodyIntCallFamStmtMutationAugTargetMappingFinish
Ancestors
  bodyIntCallFamStmtMutationAugTargetMappingCompose
  bodyIntCallFamStmtMutationAugTargetMappingOps bodyIntCallJointAggCore
  bodyIntCallJointContract exprSimMapKey loweringHalt loweringShapeRules
  emitHelperProps exprSimAccounts fragExec compileEnv exprLoweringProps
  vyperStorage byte venomState fragGasMode loweringStateRelDefs

Theorem intcall_mapping_suffix:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_mapping_subscript base_op key sa = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. base_op = Var x \/ key = Var x ==> not_fresh_at sa x) /\
  eval_operand base_op s = SOME w0 /\ eval_operand key s = SOME w1 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      intcall_expr_cont fp ce env es sa s es sb u /\
      eval_operand op u = SOME (hashmap_slot w0 w1)
Proof
  strip_tac >> drule compile_mapping_subscript_parts >> strip_tac >>
  imp_res_tac compile_alloc_buffer_extends >>
  imp_res_tac emit_op_extends_next_var >>
  `cs_extends sm sn /\ cs_extends sp sq` by
    (imp_res_tac emit_void_extends >>
     fs[cs_extends_def, same_blocks_def] >>
     conj_tac >> qexists `[]` >> simp[]) >>
  `cs_extends sa sn /\ cs_extends sa sp /\ cs_extends sa sq /\
   cs_extends sm sb /\ cs_extends sn sb /\ cs_extends sp sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sn fp.jc_func /\
   fn_has_code sn sp fp.jc_func /\ fn_has_code sp sq fp.jc_func /\
   fn_has_code sq sb fp.jc_func` by metis_tac[fn_has_code_mid, fn_has_code_split] >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) intcall_mapping_two_words >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_void MSTORE _ sm = _`)) >>
  disch_then (drule_at (Pat `emit_void MSTORE _ sp = _`)) >>
  disch_then drule_all >> strip_tac >>
  rename1 `intcall_expr_cont fp ce env es sa s es sq mid` >>
  `intcall_expr_res fp ce env es sq mid /\ ~mid.vs_halted /\
   mid.vs_current_bb = sq.cs_current_bb /\
   mid.vs_inst_idx = LENGTH sq.cs_current_insts` by fs[intcall_expr_cont_def] >>
  drule_at (Pat `emit_op SHA3 _ _ = _`) intcall_mapping_hash_run >>
  disch_then (drule_at (Pat `intcall_expr_res _ _ _ _ sq _`)) >>
  simp[eval_operand_def, wordsTheory.dimword_def] >> strip_tac >>
  rename1 `eval_operand op t = SOME _` >>
  qexists `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, hashmap_slot_def, word_of_bytes_be_def] >>
  conj_tac >- metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
  irule bodyIntCallJointAggCoreTheory.intcall_expr_cont_trans >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`es`, `sq`, `mid`] >> simp[] >>
  imp_res_tac compile_alloc_buffer_parts >>
  imp_res_tac emitted_insts_emit_void >>
  imp_res_tac emitted_insts_emit_op >> simp[]
QED
