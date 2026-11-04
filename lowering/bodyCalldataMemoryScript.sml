(* Actual CALLDATASIZE execution, prefix safety and body memory closure. *)
Theory bodyCalldataMemory
Ancestors
  exprSimSource exprSimMemoryValues fragGasPathMem fragGasSeqMem gasCount gasContext
  exprSimMemoryStack bodyMemoryDefs bodyMemoryPreds exprSimCalldata exprSimHypsDefs
  exprSimProps
  fragExecMem instMemFrontier allocaHistoryFragment emitHelperProps
  exprLoweringProps emitHelper venomInst venomState words list rich_list
  compileEnv fragExec exprSimDefs valueEncoding vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState vyperTyping vyperTypeSystem

Theorem body_calldatasize_prefix_mem_ok[local]:
  emit_op CALLDATASIZE [] sm = (dst,sn) ==>
  run_inst_seq_mem_ok (emitted_insts sm sn) s
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_mem_ok_last] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem body_calldatasize_run[local]:
  emit_op CALLDATASIZE [] sm = (dst,sn) ==>
  run_inst_seq (emitted_insts sm sn) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var))
                   (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, exec_read0_def, mk_inst_def]
QED

Theorem body_calldatasize_history[local]:
  emit_op CALLDATASIZE [] sm = (dst,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sn) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)
Proof
  rpt strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sn ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sm sn) = LENGTH sn.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         emitted_insts_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem body_calldatasize_state_post[local]:
  emit_op CALLDATASIZE [] sm = (dst,sn) /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx es s ==>
  ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
      stmt_state_rel ctx func cenv cx es q /\
      eval_operand dst q = SOME (val_to_w256 (IntV &LENGTH cx.txn.calldata)) /\
      (!z v. not_fresh_at sm z /\ lookup_var z s = SOME v ==>
             lookup_var z q = SOME v) /\
      q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
      q.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >> drule body_calldatasize_run >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qexists_tac `update_var out (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s` >>
  simp[Abbr `out`] >> conj_tac
  >- (irule stmt_state_rel_update_var >> simp[]) >>
  `dst = Var (STRING #"%" (toString sm.cs_next_var))` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  gvs[] >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac
  >- gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
         val_to_w256_def, integer_wordTheory.i2w_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

Theorem body_calldatasize_frag_mem[local]:
  emit_op CALLDATASIZE [] sm = (dst,sn) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
         alloca_history func s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (val_to_w256 (IntV &LENGTH cx.txn.calldata)) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R
Proof
  rpt strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `P = \s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
    alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  `frag_exec_mem ctx sm sn P
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (val_to_w256 (IntV &LENGTH cx.txn.calldata)) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R`
    suffices_by (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_mem_run_inst_seq >> fs[same_blocks_def] >>
  simp[IS_PREFIX_APPEND3, mk_inst_def, is_terminator_def] >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  conj_tac
  >- (simp[run_inst_seq_mem_ok_last] >>
      irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  disj1_tac >> drule_all body_calldatasize_state_post >> strip_tac >>
  `alloca_inv entry` by gvs[stmt_state_rel_def] >>
  drule_all body_calldatasize_history >> strip_tac >>
  qexists_tac `q` >>
  fs[GSYM mk_inst_def, stmt_state_rel_inst_idx, lookup_var_def] >>
  qpat_x_assum `run_inst_seq _ _ = OK q` mp_tac >>
  qpat_x_assum `alloca_history func (q with vs_inst_idx := _)` mp_tac >>
  simp[]
QED

Theorem compile_calldatasize_body_sim_mem:
  !ctx func cenv cx env ty ann args es.
    expr_body_pre cenv cx env (Builtin ann CalldataLen args) es ==>
    expr_sim_mem ctx func cenv cx ty (Builtin ann CalldataLen args) es
Proof
  rpt gen_tac >> strip_tac >>
  `args = [] /\ ann = BaseT (UintT 256)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >>
  `!st. eval_expr cx (Builtin (BaseT (UintT 256)) CalldataLen []) st =
        (INL (Value (IntV &LENGTH cx.txn.calldata)), st)` by
    (gen_tac >>
     Cases_on `eval_expr cx (Builtin (BaseT (UintT 256)) CalldataLen []) st` >>
     drule eval_expr_calldata_len >> simp[] >> strip_tac >> gvs[]) >>
  rw[expr_sim_mem_def] >>
  gvs[bind_def, read_result_def, return_def, lower_value_calldata_len] >>
  drule_all body_calldatasize_frag_mem >>
  disch_then (qspecl_then [`es`, `s0`, `cx`, `ctx`,
    `expr_exit (INL (IntV &LENGTH cx.txn.calldata))`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
  disch_then irule >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, is_word_type_def, typed_val_to_w256_word_value,
       word_value_def, locals_kept_mem] >> rpt strip_tac >> simp[]
QED

Theorem compile_calldatasize_body_vv_sim_mem:
  !ctx func cenv cx env ty ann args es.
    expr_body_pre cenv cx env (Builtin ann CalldataLen args) es ==>
    expr_vv_sim_mem ctx func cenv cx ty (Builtin ann CalldataLen args) es
Proof
  rpt gen_tac >> strip_tac >> irule body_expr_vv_sim_mem_stack >>
  conj_tac >- simp[compile_calldata_len_stack] >>
  conj_tac
  >- (`args = []` by
        gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
      gvs[] >> rpt strip_tac >> drule eval_expr_calldata_len >> simp[]) >>
  irule compile_calldatasize_body_sim_mem >> metis_tac[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_CALLDATASIZE_MEMORY_AUDIT OK\n"
     else raise Fail "calldatasize memory inherited admission"
  end) [body_calldatasize_prefix_mem_ok, body_calldatasize_run,
        body_calldatasize_history, body_calldatasize_state_post,
        body_calldatasize_frag_mem, compile_calldatasize_body_sim_mem,
        compile_calldatasize_body_vv_sim_mem];
