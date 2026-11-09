(* The constructor exit and epilogue with memory: every return from the
 * constructor body (a valueless Return, the only one it types) halts
 * memory-safely through the jump to the exit block, the unlock, and the
 * epilogue's ALLOCA, MCOPY of the immutables, CODECOPY of the runtime code
 * and RETURN.  The memory twin of constructor_frame_ret_ok, in a frame with
 * no caller return buffer.
 * TOP-LEVEL: constructor_frame_ret_ok_mem.
 *)
Theory ctorDeployMemoryRunMemFrameRet
Ancestors
  ctorDeployMemoryRunMemFallthrough ctorDeployLoweringFrameRet bodyMemoryDefs instMemFrontier fragGasSeqMem
  immutableDeployExecution allocaSiteResource venomExecSemantics venomState
  venomMemDefs words arithmetic finite_map exprLoweringProps moduleLowering venomInst
  fragExecMem memSafeRun fragGasPathMem fragExec gasCount instIdxIndep
  list rich_list entrySinkExtraction compileEnv loweringHalt ctorReturnFrame bodySim unitTransformDefs stmtSimDefs stmtSimProps
  stmtLowering gasOutcome gasSummary fragGasMode loweringPosts vyperInterpreter

Theorem constructor_mem_seq_split:
  !pre post s mid.
  run_inst_seq pre s = OK mid /\ run_inst_seq_mem_ok (pre ++ post) s ==>
  run_inst_seq_mem_ok pre s /\ run_inst_seq_mem_ok post mid
Proof
  Induct >> simp[run_inst_seq_def, run_inst_seq_mem_ok_def] >>
  rpt gen_tac >> Cases_on `step_inst_base h s` >>
  simp[run_inst_seq_def, run_inst_seq_mem_ok_def] >> metis_tac[]
QED

Theorem constructor_return_mem_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id RETURN [dst; sz] []) /\
  inst_mem_below_frontier (mk_inst id RETURN [dst; sz] []) s /\
  step_inst_base (mk_inst id RETURN [dst; sz] []) s = Halt final ==>
  gas_path_mem ctx func s 0 (Halt final)
Proof
  strip_tac >> irule (cj 3 gas_path_mem_rules) >> simp[exit_result_def] >>
  simp[gas_path_mem_edge_def] >>
  qexists_tac `0` >>
  simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
       mem_safe_step_non_invoke, inst_dload_in_section_def, exit_result_def]
QED

Theorem constructor_terminal_mem_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (pre ++ [mk_inst id RETURN [dst; sz] []])
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) pre /\
  run_inst_seq pre s = OK mid /\
  step_inst_base (mk_inst id RETURN [dst; sz] []) mid = Halt final /\
  run_inst_seq_mem_ok (pre ++ [mk_inst id RETURN [dst; sz] []]) s ==>
  ?final'. gas_path_mem ctx func s 0 (Halt final')
Proof
  strip_tac >> drule_all constructor_mem_seq_split >> strip_tac >>
  `isPREFIX pre (DROP s.vs_inst_idx bb.bb_instructions)` by
    metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
   EVERY (\i. ~is_terminator i.inst_opcode) pre /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) pre) = 0` by
    (fs[EVERY_MEM, LENGTH_NIL, FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >> gvs[] >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func s 0 (OK shifted)` >>
  `~shifted.vs_halted /\ shifted.vs_current_bb = s.vs_current_bb` by
    (simp[Abbr `shifted`] >>
     drule_all run_inst_seq_preserves_entry_control >> simp[]) >>
  `?rest. DROP shifted.vs_inst_idx bb.bb_instructions =
    mk_inst id RETURN [dst; sz] [] :: rest` by
    (qpat_x_assum `isPREFIX (pre ++ _) _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >> qexists_tac `l` >>
     simp_tac (srw_ss()) [Abbr `shifted`] >>
     once_rewrite_tac[GSYM DROP_DROP_T] >>
     asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND]) >>
  `get_instruction bb shifted.vs_inst_idx =
    SOME (mk_inst id RETURN [dst; sz] [])` by
    (`shifted.vs_inst_idx < LENGTH bb.bb_instructions` by
       (qpat_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
        simp[LENGTH_DROP] >> decide_tac) >>
     simp[get_instruction_def] >>
     qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `HD`) >> simp[HD_DROP]) >>
  `gas_path_mem ctx func shifted 0
    (Halt (final with vs_inst_idx := s.vs_inst_idx + LENGTH pre))` by
    (irule constructor_return_mem_path >> conj_tac >- simp[] >>
     qexistsl_tac [`bb`, `dst`, `id`, `sz`] >>
     simp[Abbr `shifted`, immutable_deploy_return_index, exec_result_map_def] >>
     fs[run_inst_seq_mem_ok_last]) >>
  qexists_tac `final with vs_inst_idx := s.vs_inst_idx + LENGTH pre` >>
  drule_all gas_path_mem_then >> simp[]
QED

Theorem constructor_epilogue_zero_path_mem:
  compile_constructor_epilogue rt cap imm st = ((),st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  ~block_is_terminated st /\
  stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
  rt + cap < dimword(:256) /\
  (cap <> 0 ==> cenv.ce_imm_alloca = SOME imm /\
    (!x. imm = Var x ==> not_fresh_at st x)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?final. gas_path_mem ctx func s 0 (Halt final)
Proof
  strip_tac >>
  drule_all compile_constructor_epilogue_mem_ok >> strip_tac >>
  drule_all compile_constructor_epilogue_padded_execution >> strip_tac >>
  drule_all compile_constructor_epilogue_code_placement >> strip_tac >>
  drule compile_constructor_epilogue_terminal_shape >> strip_tac >>
  `EVERY (\i. !s final. step_inst_base i s <> Halt final) pre /\
   EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) pre` by
    (fs[EVERY_MEM] >> conj_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[] >>
     simp[is_terminator_def] >>
     metis_tac[immutable_deploy_prefix_opcodes, MEM]) >>
  `?mid. run_inst_seq pre s = OK mid` by
    (Cases_on `run_inst_seq pre s` >> gvs[] >>
     `!ss. run_inst_seq pre s <> OK ss` by simp[] >>
     drule run_inst_seq_append_err >>
     disch_then (qspec_then `[mk_inst id RETURN [dst;szop] []]` assume_tac) >>
     gvs[] >> drule immutable_deploy_prefix_no_halt >> metis_tac[]) >>
  `step_inst_base (mk_inst id RETURN [dst;szop] []) mid = Halt final` by
    (`run_inst_seq [mk_inst id RETURN [dst;szop] []] mid = Halt final` by
       metis_tac[run_inst_seq_append] >>
     fs[run_inst_seq_def, AllCaseEqs()]) >>
  irule constructor_terminal_mem_path >> metis_tac[]
QED

Theorem constructor_exit_zero_path_mem:
  cenv.ce_is_ctor /\ same_frame cenv body_cenv /\
  st_exit.cs_current_insts = [] /\
  (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
    st_exit = ((), st_epilogue) /\
  compile_constructor_epilogue rt cap imm st_epilogue = ((), st_final) /\
  fn_has_code st_exit st_final func /\ fn_inst_ids_distinct func /\
  rt + cap < dimword(:256) /\
  (nr ==> ut /\ storage_layout_safe cx /\ cx.nonreentrant_slot = SOME nkey) /\
  (cap <> 0 ==> cenv.ce_imm_alloca = SOME imm /\
    (!x. imm = Var x ==> not_fresh_at st_epilogue x)) /\
  stmt_state_rel ctx func body_cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = st_exit.cs_current_bb /\ s.vs_inst_idx = 0 ==>
  ?final. gas_path_mem ctx func s 0 (Halt final)
Proof
  strip_tac >>
  `nr ==> ut` by simp[] >>
  drule_all constructor_exit_code_mem >> strip_tac >>
  drule optional_unlock_code >> simp[] >> strip_tac >>
  `body_cenv.ce_is_ctor /\
   (cap <> 0 ==> body_cenv.ce_imm_alloca = SOME imm /\
     (!x. imm = Var x ==> not_fresh_at st_epilogue x))` by
    gvs[same_frame_def, compile_env_component_equality] >>
  Cases_on `nr`
  >- (gvs[] >>
      qmatch_asmsub_abbrev_tac `fn_has_code st_exit ep func` >>
      qabbrev_tac `u = tstore (n2w nkey) 0w s` >>
      `stmt_state_rel ctx func body_cenv cx
         (es with tStorage := (cx.txn.target =+
           update_storage (n2w nkey) 0w (es.tStorage cx.txn.target)) es.tStorage)
         (u with vs_inst_idx := 1)` by
        (simp[stmt_state_rel_inst_idx, Abbr `u`] >>
         irule constructor_unlock_stmt_state_rel >> simp[]) >>
      `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
      `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX [mk_inst st_exit.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] []]
          (DROP s.vs_inst_idx bb.bb_instructions)` by
        (fs[fn_has_code_def, Abbr `ep`] >> metis_tac[]) >>
      `run_inst_seq [mk_inst st_exit.cs_next_id TSTORE
          [Lit (n2w nkey); Lit 0w] []] s = OK u /\
       run_inst_seq_mem_ok [mk_inst st_exit.cs_next_id TSTORE
          [Lit (n2w nkey); Lit 0w] []] s` by
        (simp[run_inst_seq_def, run_inst_seq_mem_ok_def, mk_inst_def,
              inst_mem_below_frontier_def, inst_dload_in_section_def,
              contextCodegenRelTheory.source_memory_read_ranges_def,
              codegenRelTheory.source_memory_write_ranges_def] >>
         PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
         simp[mk_inst_def, eval_operand_def, Abbr `u`, exec_write2_def]) >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        [mk_inst st_exit.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] []]` by
        simp[mk_inst_def, is_terminator_def] >>
      drule_all run_inst_seq_gas_path_mem >>
      disch_then (qspec_then `ctx` mp_tac) >>
      simp[mk_inst_def, is_terminator_def] >> strip_tac >>
      `~(u with vs_inst_idx := 1).vs_halted /\
       (u with vs_inst_idx := 1).vs_current_bb = ep.cs_current_bb /\
       (u with vs_inst_idx := 1).vs_inst_idx = LENGTH ep.cs_current_insts` by
        simp[Abbr `u`, tstore_def, Abbr `ep`] >>
      `?final. gas_path_mem ctx func (u with vs_inst_idx := 1) 0 (Halt final)` by
        (irule constructor_epilogue_zero_path_mem >> metis_tac[ADD_COMM]) >>
      drule_all gas_path_mem_then >> simp[] >> metis_tac[]) >>
  gvs[] >> irule constructor_epilogue_zero_path_mem >> simp[] >>
  metis_tac[ADD_COMM, LENGTH]
QED

Theorem constructor_return_none_frag_mem:
  cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE /\
  cenv.ce_ctor_exit_label = SOME exit_lbl /\ same_frame cenv body_cenv /\
  st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
  (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
    st_exit = ((), st_epilogue) /\
  compile_constructor_epilogue rt cap imm st_epilogue = ((), st_final) /\
  fn_has_code st_exit st_final func /\ rt + cap < dimword(:256) /\
  (nr ==> ut /\ storage_layout_safe cx /\ cx.nonreentrant_slot = SOME nkey) /\
  (cap <> 0 ==> cenv.ce_imm_alloca = SOME imm /\
    (!x. imm = Var x ==> not_fresh_at st_epilogue x)) ==>
  stmt_frag_mem NONE ctx func cx lctx (\v es r. T) body_cenv
    (stmt_env body_cenv lctx NoneT (Return NONE))
    (eval_stmt cx (Return NONE)) es
Proof
  strip_tac >>
  `body_cenv.ce_is_ctor /\ body_cenv.ce_return_pc = NONE /\
   body_cenv.ce_ctor_exit_label = SOME exit_lbl` by
    gvs[same_frame_def, compile_env_component_equality] >>
  pure_rewrite_tac[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `sb = sa with <|cs_next_id := sa.cs_next_id + 1;
     cs_current_insts := sa.cs_current_insts ++
       [mk_inst sa.cs_next_id JMP [Label exit_lbl] []]|>` by
    (qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, Once compile_stmt_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emitHelperTheory.emit_inst_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `gas_path_mem ctx func s0 0 (OK (jump_to exit_lbl s0))` by
    (irule emit_jump_zero_path_mem >> simp[] >>
     qexistsl_tac [`sa`, `sb`] >> simp[]) >>
  `stmt_state_rel ctx func body_cenv cx es (jump_to exit_lbl s0)` by
    simp[stmt_state_rel_jump_to] >>
  `~(jump_to exit_lbl s0).vs_halted /\
   (jump_to exit_lbl s0).vs_current_bb = st_exit.cs_current_bb /\
   (jump_to exit_lbl s0).vs_inst_idx = 0` by simp[jump_to_def] >>
  `?final. gas_path_mem ctx func (jump_to exit_lbl s0) 0 (Halt final)` by
    (drule_all constructor_exit_zero_path_mem >> simp[]) >>
  `gas_path_mem ctx func s0 0 (Halt final)` by
    (drule_all gas_path_mem_then >> simp[]) >>
  pure_rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  pure_rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR (ReturnException NoneV)`, `es`, `Halt final`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, Once evaluate_def,
       stmt_exit_def, exit_result_def, vyperStateTheory.raise_def]
QED

Theorem constructor_frame_ret_ok_mem:
  !ctx func cenv cx runtime_size immutables_len imm nr nkey ut exit_lbl
   st_exit st_epilogue st_final.
    cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE /\
    cenv.ce_ctor_exit_label = SOME exit_lbl /\
    st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
    (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
      st_exit = ((), st_epilogue) /\
    compile_constructor_epilogue runtime_size immutables_len imm
      st_epilogue = ((), st_final) /\
    fn_has_code st_exit st_final func /\
    runtime_size + immutables_len < dimword(:256) /\
    (nr ==> ut /\ storage_layout_safe cx /\
            cx.nonreentrant_slot = SOME nkey) /\
    (immutables_len <> 0 ==>
      cenv.ce_imm_alloca = SOME imm /\
      (!x. imm = Var x ==> not_fresh_at st_epilogue x)) ==>
    frame_ret_ok_mem NONE ctx func cx (\v es r. T) cenv NoneT
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[frame_ret_ok_mem_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `eo`
  >- (drule_all constructor_return_none_frag_mem >> simp[]) >>
  gvs[vyperTypeSystemTheory.type_stmt_def]
QED
