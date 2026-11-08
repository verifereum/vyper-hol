(* Memory safety of the external-code slice copy and length header. *)
Theory bodyMemSliceExtcode
Ancestors
  exprSimSliceExtcode builtinBytesMemory fragGasSeqMem
  emitHelper emitHelperProps compileEnv exprLoweringProps fragExecMem instMemFrontier
  venomExecSemantics venomInst venomState list exprSimSliceMemory memSafeRun loweringHalt
  exprSimSliceExtcodeContinue exprSimMemUnwrap venomMemDefs context

Theorem slice_extcode_copy_store_mem_ok:
  emit_void EXTCODECOPY [addr;dst;start;len] sa = ((),sm) /\
  emit_void MSTORE [out;len] sm = ((),sb) /\
  eval_operand addr s = SOME a /\ eval_operand dst s = SOME d /\
  eval_operand start s = SOME b /\ eval_operand len s = SOME n /\
  eval_operand out s = SOME p /\
  w2n d + w2n n <= s.vs_alloca_next /\
  w2n p + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >>
  qpat_x_assum `emit_void EXTCODECOPY _ _ = _` mp_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
  simp[emit_void_def, comp_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       rich_listTheory.DROP_APPEND2, run_inst_seq_mem_ok_cons,
       run_inst_seq_mem_ok_last, below_frontier_EXTCODECOPY] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  rewrite_tac[GSYM mk_inst_def, below_frontier_MSTORE] >>
  simp[write_memory_with_expansion_def, eval_operand_def]
QED

Theorem slice_extcode_tail_mem_ok:
  compile_slice_extcode addr start len out dst sa = (r,sb) /\
  eval_operand addr s = SOME a /\ eval_operand start s = SOME b /\
  eval_operand len s = SOME n /\ eval_operand out s = SOME p /\
  eval_operand dst s = SOME d /\
  (!x. MEM (Var x) [addr;start;len;out;dst] ==> not_fresh_at sa x) /\
  LENGTH (lookup_account (w2w a) s.vs_accounts).code < dimword (:256) /\
  w2n d + w2n n <= s.vs_alloca_next /\
  w2n p + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule slice_extcode_shape >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sc ++ emitted_insts sc sd) s` by
    (match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
     >- (drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
         simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges, mk_inst_def]) >>
     rpt strip_tac >> irule compile_assert_slice_bounds_mem_ok >>
     goal_assum (drule_at Any)) >>
  qpat_x_assum `emitted_insts sa sb = _` SUBST1_TAC >>
  pure_rewrite_tac[APPEND_ASSOC] >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac >- simp[] >>
  rpt strip_tac >>
  `!x. MEM (Var x) [addr;start;len] ==> not_fresh_at sa x` by
    (simp[] >> metis_tac[MEM]) >>
  drule_all slice_extcode_prefix_run >>
  Cases_on `LENGTH (lookup_account (w2w a) s.vs_accounts).code < w2n b + w2n n` >>
  simp[] >> strip_tac >> gvs[] >>
  irule slice_extcode_copy_store_mem_ok >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  `s'.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `s' = s with vs_vars := _` mp_tac >>
     disch_then (mp_tac o Q.AP_TERM `\t. t.vs_alloca_next`) >> simp[]) >>
  `!op. MEM op [addr;start;len;out;dst] ==>
        eval_operand op s' = eval_operand op s` by
    (rpt strip_tac >> first_x_assum irule >> rpt strip_tac >>
     gvs[] >> metis_tac[]) >>
  qexistsl_tac [`a`,`b`,`d`,`n`,`p`] >> simp[]
QED

Theorem slice_out_buf_mem_ok:
  compile_slice_out_buf sz sa = ((out,data),sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule slice_out_buf_decompose >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  qpat_x_assum `emitted_insts sa sb = _` SUBST1_TAC >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  irule run_inst_seq_mem_ok_every >>
  simp[below_frontier_no_ranges, mk_inst_def]
QED

Theorem slice_out_buf_path_mem:
  compile_slice_out_buf sz sa = ((out,data),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule slice_extcode_out_control >> strip_tac >>
  `same_blocks sa sb` by
    (qpat_x_assum `compile_slice_out_buf _ _ = _` mp_tac >>
     simp[builtinBytesTheory.compile_slice_out_buf_def,
          compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emit_op_def, fresh_var_def, fresh_id_def, emit_def,
          same_blocks_def] >> strip_tac >> gvs[]) >>
  irule straight_path_mem >> simp[] >> qexists_tac `sa` >> simp[] >>
  conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
  irule slice_out_buf_mem_ok >> goal_assum (drule_at Any)
QED
