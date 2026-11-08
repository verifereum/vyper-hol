(* Memory certificate for the allocating bytestring widening suffix. *)
Theory bodyMemTbConvertWidenCounted
Ancestors
  bodyMemTbConvertCopyMemory bodyLiteralBufferMemory exprSimConvertBytes
  exprSimAlloc bodyAllocMemory bodyCopyMemory fragExecMem exprLoweringProps
  compileEnv context emitHelperProps emitHelper venomState venomInst
  venomExecSemantics rich_list list words venomMemDefs instMemFrontier
  fragExec fragGasSeqMem fragGasMode allocaHistoryFragment bodyMemBiSha256Compose
  exprSimDefs loweringPosts varsExt freshWrites venomInstProofs valueCopyBytes
  exprSimBufferStore bodyMemEcArithPrefix

Theorem convert_alloc_copy_insts_split[local]:
  compile_alloc_buffer d sm = (buf,mid) /\
  emit_void MCOPY [buf.buf_operand; x; Lit (n2w k)] mid = ((),sb) ==>
  emitted_insts sm sb = emitted_insts sm mid ++ emitted_insts mid sb
Proof
  strip_tac >>
  gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, emit_op_def, emit_void_def, emit_inst_def,
      fresh_id_def, fresh_var_def, emit_def, emitted_insts_def,
      DROP_LENGTH_APPEND] >> simp[DROP_APPEND]
QED

Theorem convert_widen_copy_run_capacity[local]:
  compile_bytestring_widen_copy d x k sm = (op,sb) /\
  0 < k /\ k <= d /\ d < dimword (:256) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ eval_operand x s = SOME p /\
  run_inst_seq (emitted_insts sm sb) s = OK u ==>
  ?w. eval_operand op u = SOME w /\
    w2n w + d <= u.vs_alloca_next
Proof
  strip_tac >> drule_all convert_widen_copy_code >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule_all hash_alloc_buffer_labels >> strip_tac >>
  `eval_operand x t = SOME p` by
    (Cases_on `x` >> gvs[eval_operand_def]) >>
  `w2n w + d <= t.vs_alloca_next` by
    (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. FLOOKUP t.vs_allocas aid = SOME (base,sz) ==> _`
       drule >> simp[]) >>
  `run_inst_seq (emitted_insts mid sb) t =
     OK (mcopy (w2n w) (w2n p) (w2n (n2w k:256 word)) t)` by
    (irule buffer_emit_mcopy_run >>
     qexistsl_tac [`buf.buf_operand`, `x`, `Lit (n2w k)`] >>
     gvs[eval_operand_def]) >>
  `emitted_insts sm sb = emitted_insts sm mid ++ emitted_insts mid sb` by
    (irule convert_alloc_copy_insts_split >> metis_tac[]) >>
  qpat_assum `run_inst_seq (emitted_insts sm mid) s = OK t`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `emitted_insts mid sb` mp_tac) >>
  gvs[] >> strip_tac >> qexists_tac `w` >>
  gvs[mcopy_def, write_memory_with_expansion_def, eval_operand_def, lookup_var_def]
QED

Theorem convert_widen_copy_mem_ok:
  compile_bytestring_widen_copy d x k sm = (op,sb) /\
  0 < k /\ k <= d /\ d < dimword (:256) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  eval_operand x s = SOME p /\ w2n p + k <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  strip_tac >> drule_all convert_widen_copy_code >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (irule literal_alloca_frontier >>
     qexistsl_tac [`sm.cs_next_id`, `[Lit (n2w d)]`,
       `[STRING #"%" (toString sm.cs_next_var)]`] >>
     qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
     qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     drule emitted_insts_emit_op >> simp[]) >>
  drule_all hash_alloc_buffer_labels >> strip_tac >>
  `eval_operand x t = SOME p` by
    (Cases_on `x` >> gvs[eval_operand_def]) >>
  `w2n w + d <= t.vs_alloca_next` by
    (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. FLOOKUP t.vs_allocas aid = SOME (base,sz) ==> _`
       drule >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sm mid) s` by
    (irule ec_alloc_buffer_mem_ok >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts mid sb) t` by
    (drule emitted_insts_emit_void >> strip_tac >>
     gvs[run_inst_seq_mem_ok_last, below_frontier_MCOPY, eval_operand_def] >>
     decide_tac) >>
  `emitted_insts sm sb = emitted_insts sm mid ++ emitted_insts mid sb` by
    (irule convert_alloc_copy_insts_split >> metis_tac[]) >>
  simp[] >> irule run_inst_seq_mem_ok_append_run >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem convert_widen_copy_path_mem:
  compile_bytestring_widen_copy d x k sm = (op,sb) /\
  0 < k /\ k <= d /\ d < dimword (:256) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  alloca_history func s /\ alloca_inv s /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  eval_operand x s = SOME p /\ w2n p + k <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sb) s = OK t ==>
  gas_marked_path T ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) s` by
    (irule convert_widen_copy_mem_ok >> metis_tac[]) >>
  drule_all convert_widen_copy_opcodes >> strip_tac >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sb ++ rest` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND,
         emitted_insts_def] >> simp[DROP_APPEND]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts` by
    gvs[IS_PREFIX_APPEND, emitted_insts_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sb) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb) = []` by
    fs[EVERY_MEM, FILTER_EQ_NIL] >>
  reverse conj_tac
  >- (conj_tac
      >- (drule_all alloca_history_run_inst_seq >> simp[]) >>
      irule sha256_run_inst_seq_alloca_next_mono >> metis_tac[]) >>
  simp[gas_marked_path_def] >>
  drule run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then [`emitted_insts sm sb`, `t`, `ctx`, `func`, `bb`] mp_tac) >>
  simp[IS_PREFIX_APPEND]
QED

Theorem convert_widen_copy_owned_mem:
  compile_bytestring_widen_copy d x k sm = (op,sb) /\
  0 < k /\ k <= d /\ d < dimword (:256) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  alloca_history func s /\ alloca_inv s /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  eval_operand x s = SOME p /\ w2n p + k <= s.vs_alloca_next /\
  ~is_word_type (expr_type e) /\ post_value_type cenv e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ val_in_memory tv v (w2n p) s.vs_memory /\
  val_footprint tv v <= k /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    expr_post ctx func cenv cx e es sm sb s es v op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (?w. eval_operand op t = SOME w /\ w2n w + d <= t.vs_alloca_next)
Proof
  strip_tac >> drule_all convert_widen_copy_run >> strip_tac >>
  drule_all convert_widen_copy_run_capacity >> strip_tac >>
  drule_all convert_widen_copy_path_mem >> strip_tac >>
  drule_all convert_widen_copy_opcodes >> strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (SRULE [] run_inst_seq_preserves_field) >>
     qexists_tac `emitted_insts sm sb` >> simp[] >> rpt strip_tac >>
     `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
       (qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then drule >> simp[]) >>
     `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
     drule_all venomInstProofsTheory.step_preserves_control_flow >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[same_blocks_def] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `post_value_type _ _ = _` (fn th =>
    simp[th, expr_post_def, expr_val_rel_def, expr_val_at_def,
         stmt_state_rel_inst_idx, lookup_var_def, local_region_def,
         locals_kept_def, eval_operand_def]) >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem convert_widen_cont_mem:
  is_bytestring_type (expr_type e1) /\ is_bytestring_type (expr_type e) /\
  is_bytestring_type (lowered_value_type cenv e1) /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv2 /\
  value_has_type tv1 v /\
  val_footprint tv1 v <= type_memory_bytes cenv (lowered_value_type cenv e1) /\
  type_memory_bytes cenv (lowered_value_type cenv e1) <
    type_memory_bytes cenv (expr_type e) /\
  type_memory_bytes cenv (expr_type e) < dimword (:256) /\
  expr_post ctx func cenv cx e1 es sa sm s0 es1 v x s /\
  compile_bytestring_widen_copy (type_memory_bytes cenv (expr_type e)) x
    (type_memory_bytes cenv (lowered_value_type cenv e1)) sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ ~s.vs_halted /\
  alloca_history func s /\ alloca_inv s /\
  (!p. eval_operand x s = SOME p ==>
    w2n p + type_memory_bytes cenv (lowered_value_type cenv e1) <= s.vs_alloca_next) /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?tt v'. gas_marked_path T ctx func s 0 (OK tt) /\
    convert_result cx (expr_type e1) (expr_type e) v = INL v' /\
    expr_post ctx func cenv cx e es sa sb s0 es1 v' op tt /\
    tt.vs_current_bb = sb.cs_current_bb /\
    tt.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func tt /\ s.vs_alloca_next <= tt.vs_alloca_next /\
    (?w. eval_operand op tt = SOME w /\
      w2n w + type_memory_bytes cenv (expr_type e) <= tt.vs_alloca_next)
Proof
  strip_tac >>
  drule_all convert_bytestring_lowered_widen_success >> strip_tac >>
  drule_all convert_bytestring_wf >> strip_tac >>
  `post_value_type cenv e1 = expr_type e1` by
    (irule post_value_type_bytestring >> first_assum ACCEPT_TAC) >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> first_assum ACCEPT_TAC) >>
  `?p. eval_operand x s = SOME p /\
       val_in_memory tv1 v (w2n p) s.vs_memory` by
    (gvs[expr_post_def, expr_val_rel_def] >>
     `~is_word_type (expr_type e1)` by
       gvs[bytestring_type_cases, is_word_type_def] >> metis_tac[]) >>
  drule_all convert_bytestring_memory >>
  disch_then (qspecl_then [`w2n p`, `s.vs_memory`] strip_assume_tac) >>
  `~is_word_type (expr_type e)` by
    gvs[bytestring_type_cases, is_word_type_def] >>
  `0 < type_memory_bytes cenv (lowered_value_type cenv e1)` by
    metis_tac[bytestring_memory_bytes_positive] >>
  `stmt_state_rel ctx func cenv cx es1 s` by gvs[expr_post_def] >>
  `type_memory_bytes cenv (lowered_value_type cenv e1) <=
     type_memory_bytes cenv (expr_type e)` by decide_tac >>
  `val_in_memory tv2 v' (w2n p) s.vs_memory` by metis_tac[] >>
  `val_footprint tv2 v' <= type_memory_bytes cenv (lowered_value_type cenv e1)` by simp[] >>
  `w2n p + type_memory_bytes cenv (lowered_value_type cenv e1) <= s.vs_alloca_next` by
    metis_tac[] >>
  drule_all convert_widen_copy_owned_mem >> strip_tac >>
  qexistsl_tac [`t`, `v'`] >> simp[] >>
  qpat_assum `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac convert_expr_post_compose) >>
  disch_then drule_all >> simp[]
QED
