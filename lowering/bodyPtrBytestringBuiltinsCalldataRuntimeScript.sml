(* Actual runtime witnesses, independent of pointer replay. *)
Theory bodyPtrBytestringBuiltinsCalldataRuntime
Ancestors
  bodyPtrBytestringBuiltinsBounds exprLoweringProps fragExec
  venomState venomExecSemantics words list rich_list
  exprSimAlloc loweringHalt context finite_map emitHelper emitHelperProps
  bodyPtrBytestringBuiltinsExternalSlice freshWrites compileEnv
  exprSimWordBuiltins venomInst

Theorem slice_bounds_runtime:
  compile_assert_slice_bounds start len limit sa = ((),sb) /\
  fresh_vars_wrt sa s /\ eval_operand start s = SOME wa /\
  eval_operand len s = SOME wn /\ eval_operand limit s = SOME wl ==>
  ?p. p = s with vs_vars := p.vs_vars /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op p = SOME w) /\
    run_inst_seq (emitted_insts sa sb) s =
      if w2n (wa + wn) < w2n wa \/ w2n wl < w2n (wa + wn) then
        Abort Revert_abort (revert_state (set_returndata [] p))
      else OK p
Proof
  strip_tac >> drule_all compile_assert_slice_bounds_prefix_run >> strip_tac >>
  `LENGTH (emitted_insts sa sb) = 6` by
    (drule compile_assert_slice_bounds_layout >> simp[]) >>
  `emitted_insts sa sb = TAKE 5 (emitted_insts sa sb) ++
    [EL 5 (emitted_insts sa sb)]` by
    (drule compile_assert_slice_bounds_layout >> simp[]) >>
  qexists_tac `p` >> simp[] >>
  qpat_assum `run_inst_seq (TAKE 5 _) _ = OK _`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `[EL 5 (emitted_insts sa sb)]` mp_tac) >>
  simp[run_inst_seq_def] >>
  Cases_on `w2n (wa + wn) < w2n wa \/ w2n wl < w2n (wa + wn)` >>
  gvs[] >> metis_tac[]
QED

Theorem slice_bounds_natural_runtime:
  compile_assert_slice_bounds start len limit sa = ((),sb) /\
  fresh_vars_wrt sa s /\ eval_operand start s = SOME (n2w a) /\
  eval_operand len s = SOME (n2w n) /\ eval_operand limit s = SOME (n2w cap) /\
  a < dimword (:256) /\ n < dimword (:256) /\ cap < dimword (:256) ==>
  ?p. p = s with vs_vars := p.vs_vars /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op p = SOME w) /\
    run_inst_seq (emitted_insts sa sb) s =
      if dimword (:256) <= a + n \/ cap < a + n then
        Abort Revert_abort (revert_state (set_returndata [] p))
      else OK p
Proof
  strip_tac >> drule_all slice_bounds_runtime >> strip_tac >>
  qexists_tac `p` >> simp[] >>
  `((a + n) MOD dimword (:256) < a \/
      cap < (a + n) MOD dimword (:256)) <=>
    dimword (:256) <= a + n \/ cap < a + n` by
    (irule slice_bounds_mod_overflow >> simp[]) >>
  gvs[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w]
QED

(* The semantic allocation endpoint is itself the ALLOCA result; this is the
   witness to feed pointer replay, not an independently chosen execution. *)
Theorem slice_buffer_allocation_runtime:
  compile_alloc_buffer N sa = (buf,sm) /\ fn_has_code sa sm fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ N < dimword (:256) ==>
  ?u w. step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
      [STRING #"%" (toString sa.cs_next_var)]) s = OK u /\
    stmt_state_rel ctx fn cenv cx es u /\
    buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,N) /\
    w2n w + N < dimword (:256) /\ u.vs_memory = s.vs_memory /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) N b len) /\
    (!name b len. local_region cenv es.scopes u name b len ==>
      regions_disjoint (w2n w) N b len)
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `emitted_insts sa sm = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
    [STRING #"%" (toString sa.cs_next_var)]]` by
    simp[emitted_insts_def, DROP_APPEND1] >>
  qexistsl_tac [`t`,`w`] >> simp[] >>
  qpat_x_assum `run_inst_seq _ _ = OK _` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem calldata_size_runtime:
  emit_op CALLDATASIZE [] sa = (limit,sb) /\ fresh_vars_wrt sa s ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    u = update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s /\
    eval_operand limit u = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    fresh_vars_wrt sb u /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op u = SOME w)
Proof
  strip_tac >>
  `limit = Var (STRING #"%" (toString sa.cs_next_var)) /\
   sb.cs_next_var = SUC sa.cs_next_var /\
   emitted_insts sa sb = [mk_inst sa.cs_next_id CALLDATASIZE []
     [STRING #"%" (toString sa.cs_next_var)]]` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def, emitted_insts_def, DROP_APPEND1] >>
     strip_tac >> gvs[DROP_APPEND1]) >>
  qexists_tac `update_var (STRING #"%" (toString sa.cs_next_var))
    (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s` >>
  `step_inst_base (mk_inst sa.cs_next_id CALLDATASIZE []
    [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s)` by
    (irule external_size_step >> simp[]) >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var] >>
  conj_tac
  >- (fs[fresh_vars_wrt_def, update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >>
  `eval_operand op (update_var (STRING #"%" (toString sa.cs_next_var))
    (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s) = eval_operand op s` suffices_by simp[] >>
  irule eval_operand_update_not_fresh >> qexists_tac `sa` >> simp[] >>
  rw[not_fresh_at_def] >>
  metis_tac[fresh_vars_wrt_eval_operand, arithmeticTheory.GREATER_EQ]
QED
