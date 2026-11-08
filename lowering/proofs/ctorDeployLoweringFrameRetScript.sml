(* Constructor frame return correctness from a zero-reading Return NONE
   fragment, including the optional unlock and deployment epilogue. *)
Theory ctorDeployLoweringFrameRet
Ancestors
  gasOutcome gasSummary fragGasMode loweringPosts emitHelper emitHelperProps
  ctorReturnFrame fragGasSeq fragGasPath gasCount instIdxIndep rich_list list arithmetic venomInstProofs
  bodySim stmtSimReturn immutableDeployExecution nonreentrantSource loweringHalt
  moduleLowering stmtLowering stmtSimDefs stmtSimProps exprLoweringProps fragExec compileEnv loweringStateRelDefs
  vyperInterpreter vyperState vyperContext vyperStorageLayoutSafety
  venomExecSemantics venomState venomInst

Theorem ctor_return_gas_edge[local]:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode = RETURN /\ step_inst_base i s = Halt final ==>
  gas_path ctx func s 0 (Halt final)
Proof
  strip_tac >> irule (cj 3 gas_path_rules) >> simp[exit_result_def] >>
  simp[gas_path_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def, exit_result_def]
QED

Theorem ctor_return_idx[local]:
  i.inst_opcode = RETURN ==>
  step_inst_base i (s with vs_inst_idx := n) =
  exec_result_map (\u. u with vs_inst_idx := n) (step_inst_base i s)
Proof
  strip_tac >> simp[Once step_inst_base_def] >>
  simp[Once step_inst_base_def] >>
  Cases_on `i.inst_operands` >> simp[exec_result_map_def] >>
  Cases_on `t` >> simp[exec_result_map_def] >>
  Cases_on `t'` >> simp[exec_result_map_def] >>
  Cases_on `eval_operand h s` >>
  Cases_on `eval_operand h' s` >>
  simp[eval_operand_def, halt_state_def, set_returndata_def,
       exec_result_map_def]
QED

Theorem ctor_terminal_seq_idx[local]:
  !prefix s ret n.
  EVERY (\i. ~is_terminator i.inst_opcode) prefix /\
  ret.inst_opcode = RETURN ==>
  run_inst_seq (prefix ++ [ret]) (s with vs_inst_idx := n) =
  exec_result_map (\u. u with vs_inst_idx := n)
    (run_inst_seq (prefix ++ [ret]) s)
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac
  >- (simp[ctor_return_idx] >>
      Cases_on `step_inst_base ret s` >> simp[exec_result_map_def]) >>
  simp[step_inst_inst_idx_indep] >>
  Cases_on `step_inst_base h s` >> gvs[exec_result_map_def]
QED

Theorem ctor_terminal_seq_gas_path[local]:
  !prefix s final ctx func bb ret.
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (prefix ++ [ret]) (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) prefix /\
  ret.inst_opcode = RETURN /\
  run_inst_seq (prefix ++ [ret]) s = Halt final ==>
  ?k. gas_path ctx func s 0 (Halt (final with vs_inst_idx := k))
Proof
  Induct >> simp[run_inst_seq_def]
  >- (rpt strip_tac >>
      `?rest. DROP s.vs_inst_idx bb.bb_instructions = ret :: rest` by
        (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
      `s.vs_inst_idx < LENGTH bb.bb_instructions` by
        (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
         simp[LENGTH_DROP]) >>
      `get_instruction bb s.vs_inst_idx = SOME ret` by
        (simp[get_instruction_def] >>
         qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `HD`) >> simp[HD_DROP]) >>
      Cases_on `step_inst_base ret s` >> gvs[] >>
      qexists_tac `final.vs_inst_idx` >> simp[] >>
      irule ctor_return_gas_edge >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h :: rest /\
          isPREFIX (prefix ++ [ret]) rest` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[LENGTH_DROP]) >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (simp[get_instruction_def] >>
     qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `HD`) >> simp[HD_DROP]) >>
  `DROP (SUC s.vs_inst_idx) bb.bb_instructions = rest` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP 1`) >>
     simp[DROP_DROP, ADD1]) >>
  reverse (Cases_on `step_inst_base h s`) >> gvs[]
  >- (qexists_tac `final.vs_inst_idx` >> simp[] >>
      irule (cj 3 gas_path_rules) >> simp[exit_result_def] >>
      simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[gas_count_step_def, step_inst_non_invoke, exit_result_def]) >>
  rename1 `step_inst_base h s = OK u` >>
  `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) prefix` by fs[EVERY_MEM] >>
  `gas_path_edge ctx func s 0
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_all tuple_straight_line_edge >> simp[]) >>
  first_x_assum (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  disch_then (qspec_then `final with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`, `ret`] mp_tac) >>
  simp[ctor_terminal_seq_idx, exec_result_map_def] >> strip_tac >>
  qexists_tac `k` >> drule (cj 2 gas_path_rules) >>
  disch_then drule >> simp[]
QED

Theorem ctor_epilogue_terminal_code[local]:
  compile_constructor_epilogue rt cap imm st = ((),st') ==>
  ?prefix ret. emitted_insts st st' = prefix ++ [ret] /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) prefix /\ ret.inst_opcode = RETURN
Proof
  strip_tac >> Cases_on `cap = 0`
  >- (gvs[] >> drule compile_constructor_epilogue_zero_insts >>
      strip_tac >>
      qmatch_asmsub_abbrev_tac `emitted_insts st st' = [a;b;c]` >>
      qexistsl_tac [`[a;b]`, `c`] >>
      simp[Abbr `a`, Abbr `b`, Abbr `c`, mk_inst_def, is_terminator_def]) >>
  `0 < cap` by decide_tac >>
  drule_all compile_constructor_epilogue_positive_insts >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts st st' = [a;b;c;d;e]` >>
  qexistsl_tac [`[a;b;c;d]`, `e`] >>
  simp[Abbr `a`, Abbr `b`, Abbr `c`, Abbr `d`, Abbr `e`,
       mk_inst_def, is_terminator_def]
QED

Theorem compile_constructor_epilogue_padded_gas_path:
  compile_constructor_epilogue rt cap imm st = ((),st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  ~block_is_terminated st /\
  stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
  rt + cap < dimword(:256) /\
  (cap <> 0 ==> cenv.ce_imm_alloca = SOME imm /\
    (!x. imm = Var x ==> not_fresh_at st x)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?final codepos.
    FLOOKUP s.vs_labels "runtime_begin" = SOME codepos /\
    gas_path ctx func s 0 (Halt final) /\ final.vs_halted /\
    final.vs_returndata =
      TAKE rt (DROP (w2n codepos) s.vs_code ++ REPLICATE rt 0w) ++
      TAKE cap (s.vs_memory ++ REPLICATE cap 0w) /\
    final.vs_accounts = s.vs_accounts /\ final.vs_transient = s.vs_transient /\
    final.vs_logs = s.vs_logs /\ final.vs_outcomes = s.vs_outcomes /\
    final.vs_requests = s.vs_requests /\
    final.vs_pending_deletions = s.vs_pending_deletions /\
    final.vs_call_ctx = s.vs_call_ctx /\ final.vs_tx_ctx = s.vs_tx_ctx /\
    final.vs_block_ctx = s.vs_block_ctx /\
    final.vs_data_section = s.vs_data_section /\
    final.vs_immutables = s.vs_immutables /\
    final.vs_code = s.vs_code /\ final.vs_labels = s.vs_labels
Proof
  strip_tac >>
  drule_all compile_constructor_epilogue_padded_execution >> strip_tac >>
  drule_all compile_constructor_epilogue_code_placement >> strip_tac >>
  drule ctor_epilogue_terminal_code >> strip_tac >>
  `?k. gas_path ctx func s 0 (Halt (final with vs_inst_idx := k))` by
    (irule ctor_terminal_seq_gas_path >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`final with vs_inst_idx := k`, `codepos`] >> simp[]
QED

Theorem constructor_return_q_gas_obs:
  constructor_return_q func cenv cx rt cap nr nkey v (es with gas_obs := tail) r <=>
  constructor_return_q func cenv cx rt cap nr nkey v es r
Proof
  Cases_on `nr` >> simp[constructor_return_q_def, state_rel_gas_obs] >>
  simp[state_rel_def, storage_rel_def, transient_rel_def, accounts_rel_def,
       immutables_rel_def, logs_rel_def]
QED

Theorem ctor_exit_code[local]:
  (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
    st_exit = ((), st_epilogue) /\
  (nr ==> ut) /\ st_exit.cs_current_insts = [] /\
  compile_constructor_epilogue rt cap imm st_epilogue = ((), st_final) /\
  fn_has_code st_exit st_final func ==>
  fn_has_code st_exit st_epilogue func /\
  fn_has_code st_epilogue st_final func /\
  ~block_is_terminated st_epilogue
Proof
  strip_tac >> drule optional_unlock_code >> simp[] >> strip_tac >>
  `~block_is_terminated st_epilogue` by
    (gvs[block_is_terminated_def] >> Cases_on `nr` >>
     gvs[block_is_terminated_def, mk_inst_def, is_terminator_def]) >>
  `cs_extends st_exit st_epilogue` by
    (irule cs_extends_same_block >> Cases_on `nr` >> gvs[]) >>
  `cs_extends st_epilogue st_final` by
    (irule cs_extends_same_block >>
     drule_all compile_constructor_epilogue_append >> strip_tac >>
     simp[IS_PREFIX_APPEND] >>
     qpat_x_assum `compile_constructor_epilogue _ _ _ _ = _` mp_tac >>
     Cases_on `cap > 0` >>
     simp[compile_constructor_epilogue_def, contextTheory.compile_alloc_buffer_def,
          emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
          emitHelperTheory.emit_inst_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[]) >>
  drule_all fn_has_code_split >> gvs[]
QED

Theorem ctor_unlock_gas_path[local]:
  (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
    st = ((),st') /\ (nr ==> ut) /\ st.cs_current_insts = [] /\
  fn_has_code st st' func /\ ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = 0 ==>
  gas_path ctx func s 0
    (OK ((if nr then tstore (n2w nkey) 0w s else s) with
         vs_inst_idx := LENGTH st'.cs_current_insts))
Proof
  strip_tac >> drule optional_unlock_code >> simp[] >> strip_tac >>
  Cases_on `nr` >> gvs[]
  >- (gvs[fn_has_code_def] >>
      `run_inst_seq [mk_inst st.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] []] s =
         OK (tstore (n2w nkey) 0w s)` by
        simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
             exec_write2_def, eval_operand_def, eval_operands_def] >>
      drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
      gvs[mk_inst_def, is_terminator_def]) >>
  `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality] >>
  simp[] >> irule (cj 1 gas_path_rules) >> simp[]
QED

Theorem constructor_exit_gas_path:
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
  ?final. gas_path ctx func s 0 (Halt final) /\
    constructor_return_q func cenv cx rt cap nr nkey NoneV
      (es with scopes := []) (Halt final)
Proof
  strip_tac >> `nr ==> ut` by simp[] >>
  drule_all ctor_exit_code >> strip_tac >>
  qmatch_goalsub_abbrev_tac `constructor_return_q _ _ _ _ _ _ _ _ es0 _` >>
  qabbrev_tac `es1 = if nr then
    es with tStorage := (cx.txn.target =+
      update_storage (n2w nkey) 0w (es.tStorage cx.txn.target)) es.tStorage
    else es` >>
  qabbrev_tac `s1 = (if nr then tstore (n2w nkey) 0w s else s) with
    vs_inst_idx := LENGTH st_epilogue.cs_current_insts` >>
  `stmt_state_rel ctx func body_cenv cx es1 s1` by
    (simp[Abbr `s1`, stmt_state_rel_inst_idx] >>
     Cases_on `nr` >> gvs[Abbr `es1`] >>
     irule constructor_unlock_stmt_state_rel >> simp[]) >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `gas_path ctx func s 0 (OK s1)` by
    (simp[Abbr `s1`] >> irule ctor_unlock_gas_path >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `body_cenv.ce_is_ctor /\
   (cap <> 0 ==> body_cenv.ce_imm_alloca = SOME imm /\
      (!x. imm = Var x ==> not_fresh_at st_epilogue x))` by
    gvs[same_frame_def, compile_env_component_equality] >>
  `~s1.vs_halted /\ s1.vs_current_bb = st_epilogue.cs_current_bb /\
   s1.vs_inst_idx = LENGTH st_epilogue.cs_current_insts` by
    (drule optional_unlock_code >> simp[] >> strip_tac >>
     simp[Abbr `s1`] >> Cases_on `nr` >> gvs[tstore_def]) >>
  drule_all compile_constructor_epilogue_padded_gas_path >> strip_tac >>
  qexists_tac `final` >> conj_tac
  >- (drule_all gas_path_then >> simp[]) >>
  `state_rel func cenv cx (es1 with scopes := []) s1` by
    (irule constructor_exit_state_rel >> qexists `body_cenv` >>
     gvs[stmt_state_rel_def]) >>
  `(if nr then es0 with tStorage := (cx.txn.target =+
       update_storage (n2w nkey) 0w (es0.tStorage cx.txn.target)) es0.tStorage
     else es0) = es1 with scopes := []` by
    (Cases_on `nr` >> simp[Abbr `es0`, Abbr `es1`]) >>
  simp[constructor_return_q_def] >> qexistsl_tac [`s1`, `codepos`] >> simp[]
QED

(* Return NONE jumps to the constructor exit. The entire path has zero
   GAS readings, including the optional unlock and deployment epilogue. *)
Theorem constructor_return_none_frag:
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
  stmt_frag ctx func cx lctx
    (constructor_return_q func cenv cx rt cap nr nkey) body_cenv
    (stmt_env body_cenv lctx NoneT (Return NONE))
    (eval_stmt cx (Return NONE)) es
Proof
  strip_tac >>
  `body_cenv.ce_return_pc = NONE /\
   body_cenv.ce_ctor_exit_label = SOME exit_lbl` by
    gvs[same_frame_def, compile_env_component_equality] >>
  rw[stmt_frag_def, stmt_framed_frag_def] >>
  qpat_x_assum `_ sa = (cenv', sb)` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, Once compile_stmt_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_inst _ _ _ sa = (_, sj)` >>
  drule emit_inst_extends >> strip_tac >>
  `stmt_state_rel ctx func body_cenv cx es (jump_to st_exit.cs_current_bb s0)` by
    simp[stmt_state_rel_jump_to] >>
  `?final. gas_path ctx func (jump_to st_exit.cs_current_bb s0) 0 (Halt final) /\
    constructor_return_q func cenv cx rt cap nr nkey NoneV
      (es with scopes := []) (Halt final)` by
    (irule constructor_exit_gas_path >> simp[jump_to_def] >>
     conj_tac
     >- (qexistsl_tac [`imm`, `st_epilogue`, `st_exit`, `st_final`, `T`] >> simp[]) >>
     qexists_tac `body_cenv` >> gvs[jump_to_def]) >>
  `gas_path ctx func s0 0 (OK (jump_to st_exit.cs_current_bb s0))` by
    (irule emit_jump_zero_path >> simp[] >>
     qexistsl_tac [`sa`, `sj`] >> simp[]) >>
  `gas_path ctx func s0 0 (Halt final)` by
    (drule_all gas_path_then >> simp[]) >>
  pure_rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  pure_rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR (ReturnException NoneV)`, `es`, `Halt final`] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def, Once evaluate_def, raise_def] >>
  simp[exit_result_def, stmt_exit_def] >> gen_tac >> disj2_tac >>
  `constructor_return_q func cenv cx rt cap nr nkey NoneV
     ((es with scopes := []) with gas_obs := tail) (Halt final)` by
    pure_asm_rewrite_tac[constructor_return_q_gas_obs] >>
  gvs[]
QED

Theorem constructor_frame_ret_ok:
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
    frame_ret_ok ctx func cx
      (constructor_return_q func cenv cx runtime_size immutables_len nr nkey)
      cenv NoneT
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac [frame_ret_ok_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `eo`
  >- (irule constructor_return_none_frag >> simp[] >>
      qexistsl [`imm`, `st_epilogue`, `st_exit`, `st_final`, `ut`] >>
      simp[]) >>
  gvs[vyperTypeSystemTheory.type_stmt_def]
QED


(* Check that this theory introduces no oracle-dependent results. *)
val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then
       print ("CTOR_FRAME_RET_KERNEL_CLOSED " ^ name ^ "\n")
     else raise Fail ("Unclosed constructor frame return theorem: " ^ name)
  end) (DB.thms "ctorDeployLoweringFrameRet");
