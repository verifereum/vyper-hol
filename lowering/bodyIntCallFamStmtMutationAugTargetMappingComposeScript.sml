(* Construct the two scratch words on the resource-preserving path. *)
Theory bodyIntCallFamStmtMutationAugTargetMappingCompose
Ancestors
  bodyIntCallFamStmtMutationAugTargetMappingStore
  bodyIntCallFamStmtMutationAugTargetMapping
  bodyIntCallJointContract stmtSimAugAssignPlaceMemory exprSimMapKey
  emitHelperProps loweringShapeRules exprLoweringProps compileEnv
  valueEncodingProofs byte venomState fragGasMode loweringStateRelDefs

Theorem intcall_mapping_two_words:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_alloc_buffer 64 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; base_op] sm = ((),sn) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sn = (ptr_op,sp) /\
  emit_void MSTORE [ptr_op; key] sp = ((),sq) /\
  fn_has_code sa sm fp.jc_func /\ fn_has_code sm sn fp.jc_func /\
  fn_has_code sn sp fp.jc_func /\ fn_has_code sp sq fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  (!v. base_op = Var v \/ key = Var v ==> not_fresh_at sa v) /\
  eval_operand base_op s = SOME w0 /\ eval_operand key s = SOME w1 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      intcall_expr_cont fp ce env es sa s es sq u /\
      eval_operand buf.buf_operand u = SOME w /\
      mem_bytes_at (w2n w) 64 u.vs_memory =
        word_to_bytes_be w0 ++ word_to_bytes_be w1
Proof
  strip_tac >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) intcall_scratch_entry >>
  disch_then (drule_at (Pat `emit_void _ _ _ = _`)) >>
  disch_then (drule_at (Pat `intcall_expr_res _ _ _ _ _ _`)) >>
  simp[wordsTheory.dimword_def] >>
  strip_tac >>
  rename1 `mem_word_at (w2n w) first.vs_memory = w0` >>
  `eval_operand key first = SOME w1` by
    (irule aug_place_saved_operand >> goal_assum (drule_at Any) >>
     fs[intcall_expr_cont_def] >> metis_tac[]) >>
  `!v. key = Var v ==> not_fresh_at sn v` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  qpat_x_assum `emit_op ADD _ _ = _` mp_tac >> simp[] >> strip_tac >>
  drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ sn _`) intcall_scratch_second_word >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_void _ _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  simp[wordsTheory.dimword_def] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  rename1 `mem_word_at (w2n w+32) final.vs_memory = w1` >>
  qexistsl [`final`, `w`] >> simp[] >> conj_tac
  >- metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
  `mem_bytes_at (w2n w) 32 final.vs_memory =
   mem_bytes_at (w2n w) 32 first.vs_memory` by
    (first_x_assum irule >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  qspecl_then [`w2n w`, `32`, `32`, `final.vs_memory`] mp_tac
    mem_bytes_at_split_padded >>
  simp[mem_bytes_at_word, word_to_bytes_be_def]
QED
