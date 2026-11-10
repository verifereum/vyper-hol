(* The default-return control shell, with payload intervals kept abstract. *)
Theory extcallReturnDefaultRouting
Ancestors
  extcallReturnDefaultPath placeMemoryPrimitiveForward stmtSimProps exprLowering exprLoweringProps emitHelper compileEnv
  venomState venomInst venomExecSemantics emitHelperProps fragGasPath fragGasMode fragExec list

Theorem return_default_path_intervals:
  compile_default_return_path ce rt dt base_op dst dop addr skip lo cap info a = (op,b) ==>
  ?rds iz dl cl xl a1 a2 a3 a4 a5 a6 ds de ck dj cs hs he cj old1 old2 old3 hi.
    emit_op RETURNDATASIZE [] a = (rds,a1) /\
    emit_op ISZERO [rds] a1 = (iz,a2) /\
    fresh_label "extcall_default" a2 = (dl,a3) /\
    fresh_label "extcall_decode" a3 = (cl,a4) /\
    fresh_label "extcall_exit" a4 = (xl,a5) /\
    emit_inst JNZ [iz; Label dl; Label cl] [] a5 = ((),a6) /\
    new_block dl a6 = (old1,ds) /\
    compile_store_memory ce dop dst rt dt ds = ((),de) /\
    (if skip then comp_return () else compile_extcodesize_check addr) de = ((),ck) /\
    emit_inst JMP [Label xl] [] ck = ((),dj) /\
    new_block cl dj = (old2,cs) /\
    compile_return_value_decode lo cap cs = (hi,hs) /\
    compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi info hs = ((),he) /\
    emit_inst JMP [Label xl] [] he = ((),cj) /\
    new_block xl cj = (old3,b) /\ op = dst
Proof
  simp[compile_default_return_path_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem return_default_join_path:
  emit_inst JMP [Label lbl] [] a = ((),b) /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  gas_marked_path F ctx func s 0 (OK (jump_to lbl s))
Proof
  strip_tac >> simp[gas_marked_path_def] >>
  irule emit_jump_zero_path >> simp[] >> qexistsl_tac [`a`, `b`] >>
  gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def]
QED

Theorem return_default_select_path:
  emit_inst JNZ [test; Label yes; Label no] [] a = ((),b) /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand test s = SOME (if empty then 1w else 0w) ==>
  gas_marked_path F ctx func s 0
    (OK (jump_to (if empty then yes else no) s))
Proof
  strip_tac >> simp[gas_marked_path_def] >>
  irule assert_jnz_zero_path >> simp[] >> qexistsl_tac [`test`, `a`, `b`] >>
  gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def]
QED

Theorem return_default_size_step[local]:
  step_inst_base (mk_inst iid RETURNDATASIZE [] [out]) s =
    OK (update_var out (n2w (LENGTH s.vs_returndata)) s)
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def]
QED

Theorem return_default_test_run:
  emit_op RETURNDATASIZE [] a = (rds,m) /\
  emit_op ISZERO [rds] m = (test,b) /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts a b) s = OK t /\
    eval_operand test t = SOME (if s.vs_returndata = [] then 1w else 0w) /\
    t = update_var (STRING #"%" (toString m.cs_next_var))
      (if s.vs_returndata = [] then 1w else 0w)
      (update_var (STRING #"%" (toString a.cs_next_var))
        (n2w (LENGTH s.vs_returndata)) s)
Proof
  strip_tac >>
  qpat_x_assum `emit_op RETURNDATASIZE _ _ = _` mp_tac >>
  qpat_x_assum `emit_op ISZERO _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_def, return_default_size_step, step_ISZERO,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, bool_to_word_def, wordsTheory.n2w_11,
       arithmeticTheory.LESS_MOD, LENGTH_NIL_SYM] >>
  simp[step_inst_base_opcode_eqs, exec_pure1_def, eval_operands_def,
       mk_inst_def, eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, update_var_def, bool_to_word_def,
       wordsTheory.n2w_11, arithmeticTheory.LESS_MOD, LENGTH_NIL_SYM] >>
  Cases_on `s.vs_returndata = []` >> simp[bool_to_word_def]
QED

Theorem return_default_test_counted:
  emit_op RETURNDATASIZE [] a = (rds,m) /\
  emit_op ISZERO [rds] m = (test,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand test t = SOME (if s.vs_returndata = [] then 1w else 0w) /\
    t = (update_var (STRING #"%" (toString m.cs_next_var))
      (if s.vs_returndata = [] then 1w else 0w)
      (update_var (STRING #"%" (toString a.cs_next_var))
        (n2w (LENGTH s.vs_returndata)) s))
      with vs_inst_idx := LENGTH b.cs_current_insts
Proof
  strip_tac >> drule_all return_default_test_run >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH b.cs_current_insts` >>
  reverse conj_tac
  >- (gvs[eval_operand_def, lookup_var_def]) >>
  irule straight_line_zero_gas_path >> simp[] >>
  qexistsl_tac [`emitted_insts a b`, `a`] >> simp[] >>
  qpat_x_assum `emit_op RETURNDATASIZE _ _ = _` mp_tac >>
  qpat_x_assum `emit_op ISZERO _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem return_default_shell_entry:
  emit_op RETURNDATASIZE [] a = (rds,a1) /\
  emit_op ISZERO [rds] a1 = (test,a2) /\
  fresh_label "extcall_default" a2 = (dl,a3) /\
  fresh_label "extcall_decode" a3 = (cl,a4) /\
  fresh_label "extcall_exit" a4 = (xl,a5) /\
  emit_inst JNZ [test; Label dl; Label cl] [] a5 = ((),a6) /\
  fn_has_code a a2 func /\ fn_has_code a5 a6 func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?t. gas_marked_path F ctx func s 0
        (OK (jump_to (if s.vs_returndata = [] then dl else cl) t)) /\
    t = (update_var (STRING #"%" (toString a1.cs_next_var))
      (if s.vs_returndata = [] then 1w else 0w)
      (update_var (STRING #"%" (toString a.cs_next_var))
        (n2w (LENGTH s.vs_returndata)) s))
      with vs_inst_idx := LENGTH a2.cs_current_insts
Proof
  strip_tac >> drule_all return_default_test_counted >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  `gas_marked_path F ctx func t 0
     (OK (jump_to (if s.vs_returndata = [] then dl else cl) t))` by
    (irule return_default_select_path >>
     conj_tac >- gvs[update_var_def] >>
     qexistsl_tac [`a5`, `a6`, `test`] >> simp[] >>
     gvs[fresh_label_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_var_def, fresh_id_def, emit_def,
         update_var_def]) >>
  `gas_marked_path F ctx func s (0 + 0)
     (OK (jump_to (if s.vs_returndata = [] then dl else cl) t))` by
    (irule gas_marked_path_then >> qexists_tac `t` >> simp[]) >> gvs[]
QED
