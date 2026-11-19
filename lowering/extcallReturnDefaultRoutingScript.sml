(* Compiler intervals and the read-only test for the default-return shell. *)
Theory extcallReturnDefaultRouting
Ancestors
  exprLowering exprLoweringProps emitHelper emitHelperProps context compileEnv
  exprSimWordArgs venomState venomInst venomExecSemantics fragExec list
  rawCallBufferPtr[qualified,ignore_grammar]

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

Theorem return_default_intervals_code:
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
  new_block xl cj = (old3,b) /\ fn_has_code a b func ==>
  fn_has_code a a2 func /\ fn_has_code a5 a6 func /\
  fn_has_code ds de func /\ fn_has_code de ck func /\
  fn_has_code ck dj func /\ fn_has_code cs hs func /\
  fn_has_code hs he func /\ fn_has_code he cj func
Proof
  strip_tac >>
  `cs_extends a a1` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `cs_extends a1 a2` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  imp_res_tac cs_extends_fresh_label >>
  imp_res_tac cs_extends_emit_inst >>
  imp_res_tac cs_extends_new_block >>
  `cs_extends ds de` by
    metis_tac[ci_mono_compile_store_memory, ci_mono_def, pairTheory.SND] >>
  `cs_extends de ck` by
    (Cases_on `skip` >- gvs[comp_return_def, cs_extends_refl] >>
     gvs[compile_extcodesize_check_def, comp_bind_def] >>
     pairarg_tac >> gvs[] >>
     metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def,
               pairTheory.SND, cs_extends_trans]) >>
  `cs_extends cs hs` by
    metis_tac[ci_mono_compile_return_value_decode, ci_mono_def, pairTheory.SND] >>
  `cs_extends hs he` by
    metis_tac[cj 1 ci_mono_compile_abi_decode, ci_mono_def, pairTheory.SND] >>
  imp_res_tac cs_extends_trans >>
  rpt conj_tac >> irule fn_has_code_mid >> simp[cs_extends_refl] >>
  qexistsl_tac [`b`, `a`] >> simp[cs_extends_refl] >>
  metis_tac[cs_extends_trans]
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
  simp[run_inst_seq_def, rawCallBufferPtrTheory.raw_call_returndatasize_step_base, step_ISZERO,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, bool_to_word_def, wordsTheory.n2w_11,
       arithmeticTheory.LESS_MOD, LENGTH_NIL_SYM] >>
  simp[step_inst_base_opcode_eqs, exec_pure1_def, eval_operands_def,
       mk_inst_def, eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, update_var_def, bool_to_word_def,
       wordsTheory.n2w_11, arithmeticTheory.LESS_MOD, LENGTH_NIL_SYM] >>
  Cases_on `s.vs_returndata = []` >> simp[bool_to_word_def]
QED
