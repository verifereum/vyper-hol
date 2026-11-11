(* Actual runtime witnesses, independent of pointer replay. *)
Theory bodyPtrBytestringBuiltinsCalldataRuntime
Ancestors
  bodyPtrBytestringBuiltinsBounds exprLoweringProps fragExec
  venomState venomExecSemantics words list rich_list
  exprSimAlloc loweringHalt context finite_map emitHelper emitHelperProps
  bodyPtrBytestringBuiltinsExternalSlice freshWrites compileEnv loweringStateRelDefs
  exprSimWordBuiltins venomInst bodyPtrBytestringBuiltinsBuffer
  bodyPtrBytestringBuiltinsCalldataReserved

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


Theorem compile_slice_calldata_runtime:
  compile_slice_calldata start (Lit (n2w n)) N sa = (out,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  32 <= N /\ N < dimword (:256) /\ n < dimword (:256) /\
  a < dimword (:256) /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  eval_operand start s = SOME (n2w a) /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s1 s2 s3 s4 data limit buf sm r p u w G2 tn2 t v q.
    compile_slice_out_buf N sa = ((out,data),s1) /\
    emit_op CALLDATASIZE [] s1 = (limit,s2) /\
    compile_assert_slice_bounds start (Lit (n2w n)) limit s2 = ((),s3) /\
    emit_void CALLDATACOPY [data;start;Lit (n2w n)] s3 = ((),s4) /\
    emit_void MSTORE [out;Lit (n2w n)] s4 = ((),sb) /\
    compile_alloc_buffer N sa = (buf,sm) /\ fn_has_code sa sm fn /\
    out = Var r /\ buf.buf_operand = Var r /\ data = Var p /\
    emit_op ADD [Var r;Lit 32w] sm = (Var p,s1) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [r]) s = OK u /\
    lookup_var r u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,N) /\
    w2n w + N < dimword (:256) /\ u.vs_memory = s.vs_memory /\
    stmt_state_rel ctx fn cenv cx es u /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) N b len) /\
    (!name b len. local_region cenv es.scopes u name b len ==>
      regions_disjoint (w2n w) N b len) /\
    t = ((update_var p (w + 32w) u) with vs_inst_idx := s.vs_inst_idx + 2) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2 (OK t) /\
    ptr_covers G2 tn2 r t N /\ ptr_covers G2 tn2 p t (N - 32) /\
    stmt_state_rel ctx fn cenv cx es t /\ t.vs_memory = s.vs_memory /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t.vs_halted /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt s1 t) /\
    lookup_var r t = SOME w /\ lookup_var p t = SOME (w + 32w) /\
    t.vs_call_ctx = s.vs_call_ctx /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op t = eval_operand op s /\
      op_prov G2 op = op_prov G op /\ op_taint tn2 op = op_taint tn op) /\
    (!x. not_fresh_at s1 x ==> lookup_var x v = lookup_var x t) /\
    run_inst_seq (emitted_insts s1 s2) t = OK v /\
    v = update_var (STRING #"%" (toString s1.cs_next_var))
      (n2w (LENGTH s.vs_call_ctx.cc_calldata)) t /\

    eval_operand start v = SOME (n2w a) /\
    q = v with vs_vars := q.vs_vars /\
    (!x. not_fresh_at s2 x ==> lookup_var x q = lookup_var x v) /\
    eval_operand start q = SOME (n2w a) /\
    eval_operand out v = SOME w /\ eval_operand data v = SOME (w + 32w) /\
    eval_operand out q = SOME w /\ eval_operand data q = SOME (w + 32w) /\
    run_inst_seq (emitted_insts s2 s3) v =
      if dimword (:256) <= a + n \/ LENGTH s.vs_call_ctx.cc_calldata < a + n then
        Abort Revert_abort (revert_state (set_returndata [] q)) else OK q
Proof
  strip_tac >> drule compile_slice_calldata_stages >> strip_tac >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 fn` by metis_tac[fn_has_code_split] >>
  drule_all compile_slice_out_buf_counted >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  suspend "allocation"
QED

Resume compile_slice_calldata_runtime[allocation]:
  `cs_extends sa sm /\ cs_extends sm s1` by
    metis_tac[compile_alloc_buffer_extends, cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sm fn` by metis_tac[fn_has_code_split] >>
  qpat_x_assum `stmt_state_rel ctx fn cenv cx es s` assume_tac >>
  drule_all slice_buffer_allocation_runtime >> strip_tac >>
  `u' = u` by
    (drule compile_alloc_buffer_parts >> strip_tac >> gvs[]) >>
  qpat_x_assum `u' = u` SUBST_ALL_TAC >>
  qpat_x_assum `buf.buf_operand = Var (STRING _ _)` kall_tac >>
  `w = a'` by
    (qpat_x_assum `eval_operand buf.buf_operand u = SOME w` mp_tac >>
     simp[eval_operand_def]) >>
  qpat_x_assum `w = a'` SUBST_ALL_TAC >>
  suspend "query"
QED

Resume compile_slice_calldata_runtime[query]:
  `eval_operand start t = SOME (n2w a)` by
    (qpat_assum `!op. _` (qspec_then `start` mp_tac) >>
     simp[]) >>
  `s1.cs_next_var = sa.cs_next_var + 2 /\
   s2.cs_next_var = SUC s1.cs_next_var /\
   r = STRING #"%" (toString sa.cs_next_var) /\
   p = STRING #"%" (toString (SUC sa.cs_next_var)) /\
   limit = Var (STRING #"%" (toString s1.cs_next_var))` by
    (qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_assum `emit_op CALLDATASIZE [] _ = _` mp_tac >>
     qpat_assum `buf.buf_operand = Var r` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[compile_alloc_buffer_def,
       emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >> gvs[]) >>
  `!x. start = Var x ==> not_fresh_at s1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  drule_all calldata_size_reserved_runtime >>
  disch_then (qspec_then `t` strip_assume_tac) >>
  suspend "bounds"
QED

Resume compile_slice_calldata_runtime[bounds]:
  `eval_operand start u' = SOME (n2w a)` by simp[] >>
  `!op z. MEM op [start;Lit (n2w n);limit] /\ op = Var z ==>
    not_fresh_at s2 z` by
    (simp[] >> rpt strip_tac
     >- (irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `s1` >> simp[]) >>
     simp[not_fresh_at_def]) >>
  `eval_operand (Lit (n2w n)) u' = SOME (n2w n)` by simp[eval_operand_def] >>
  `LENGTH t.vs_call_ctx.cc_calldata < dimword (:256)` by simp[] >>
  drule_all slice_bounds_reserved_natural_runtime >> strip_tac >>
  `not_fresh_at s1 r /\ not_fresh_at s1 p /\
   not_fresh_at s2 r /\ not_fresh_at s2 p` by simp[not_fresh_at_def] >>
  `lookup_var r u' = SOME a' /\ lookup_var p u' = SOME (a' + 32w)` by
    (qpat_assum `!x. not_fresh_at s1 x ==> _` (qspec_then `r` mp_tac) >>
     qpat_assum `!x. not_fresh_at s1 x ==> _` (qspec_then `p` mp_tac) >> simp[]) >>
  `lookup_var r p' = SOME a' /\ lookup_var p p' = SOME (a' + 32w)` by
    (qpat_assum `!x. not_fresh_at s2 x ==> _` (qspec_then `r` mp_tac) >>
     qpat_assum `!x. not_fresh_at s2 x ==> _` (qspec_then `p` mp_tac) >> simp[]) >>
  qexistsl_tac [`s1`,`s2`,`s3`,`s4`,`data`,`limit`,`buf`,`sm`,`r`,`p`,
    `u`,`a'`,`G2`,`tn2`,`t`,`u'`,`p'`] >>
  gvs[eval_operand_def] >> conj_tac
  >- (qpat_x_assum `!aid b len. _` ACCEPT_TAC) >>
  qpat_x_assum `!name b len. _` ACCEPT_TAC
QED
Finalise compile_slice_calldata_runtime
