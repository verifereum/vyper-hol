(* The void external call's account-code guard, on the counted memory path. *)
Theory extcallPrecheckMemory
Ancestors
  bodyUnopFragMemory bodyDeclMemoryCounted bodyDeclMemoryCore exprSimSend exprSimConcatPath
  fragGasSeqAbort fragGasSeqMem fragGasMode fragGasPathMem
  fragExecMem fragExec exprLoweringProps exprLowering emitHelper emitHelperProps
  compileEnv instMemFrontier memSafeRun loweringStateRelDefs loweringPosts
  venomExecSemantics venomState venomInst words finite_map rich_list list

Theorem extcall_codecheck_run[local]:
  compile_extcodesize_check addr sa = ((),sb) /\
  eval_operand addr s = SOME aw /\
  w = n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id EXTCODESIZE [addr]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) ASSERT
       [Var (STRING #"%" (toString sa.cs_next_var))] []] /\
  sb.cs_current_bb = sa.cs_current_bb /\ same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 2 /\
  run_inst_seq (emitted_insts sa sb) s =
    if w = 0w then Abort Revert_abort
      (revert_state (set_returndata []
        (update_var (STRING #"%" (toString sa.cs_next_var)) w s)))
    else OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s)
Proof
  simp[compile_extcodesize_check_def, comp_bind_def, comp_ignore_bind_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
    comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, same_blocks_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
    exec_read1_def] >>
  Cases_on `n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) = (0w:bytes32)` >>
  simp[send_assert_ok, send_assert_fail, eval_operand_def, lookup_var_def,
    update_var_def, FLOOKUP_UPDATE] >> IF_CASES_TAC >> fs[n2w_11]
QED

Theorem extcall_codecheck_path_mem:
  compile_extcodesize_check addr sa = ((),sb) /\
  eval_operand addr s = SOME aw /\
  w = n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (?t. w <> 0w /\ gas_path_mem ctx func s 0 (OK t) /\
    t = (update_var (STRING #"%" (toString sa.cs_next_var)) w s
      with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    stmt_state_rel ctx func cenv cx es t /\ alloca_history func t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
  (?t. w = 0w /\ gas_path_mem ctx func s 0 (Abort Revert_abort t) /\
    t.vs_returndata = [])
Proof
  strip_tac >> drule_all extcall_codecheck_run >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[below_frontier_no_ranges, inst_dload_in_section_other, mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule concat_code_prefix >> simp[] >> metis_tac[]) >>
  Cases_on `w = 0w` >- suspend "reject" >>
  suspend "accept"
QED

Resume extcall_codecheck_path_mem[reject]:
  gvs[] >>
  drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_zero_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >> simp[] >>
  strip_tac >>
  qexists_tac `revert_state (set_returndata []
    (update_var (STRING #"%" (toString sa.cs_next_var)) 0w s))
    with vs_inst_idx := j` >>
  fs[gas_marked_path_def, revert_state_def, set_returndata_def]
QED

Resume extcall_codecheck_path_mem[accept]:
  `run_inst_seq (emitted_insts sa sb) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s)` by simp[] >>
  `gas_path_mem ctx func s 0
    (OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s
      with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (qspecl_then [`emitted_insts sa sb`, `s`,
       `update_var (STRING #"%" (toString sa.cs_next_var)) w s`,
       `ctx`, `func`, `bb`] mp_tac run_inst_seq_gas_path_mem >>
     simp[mk_inst_def, is_terminator_def]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func
    (update_var (STRING #"%" (toString sa.cs_next_var)) w s
      with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> simp[mk_inst_def, is_terminator_def]) >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es
    (update_var (STRING #"%" (toString sa.cs_next_var)) w s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  disj1_tac >>
  qexists_tac `update_var (STRING #"%" (toString sa.cs_next_var)) w s
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx] >> simp[update_var_def]
QED

Finalise extcall_codecheck_path_mem
