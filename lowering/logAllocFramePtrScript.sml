(* Transport across the actual allocation step, including reused sites. *)
Theory logAllocFramePtr
Ancestors logDataAllocPtr loweringHalt logValueFramePtr logGhostFramePtr
  bodyPtrDefs allocationPtr ptrDiscipline ptrSafeRun venomState venomInst
  venomExecSemantics finite_map words list arithmetic compileEnv exprSimDefs
  exprLoweringProps venomMemDefs abiBuiltinAllocation emitHelperProps stmtSimLogTrace
  ASCIInumbers string context stmtLowering fragGasSeqPtr ghostPcTransportPtr
  logTopicsRunPtr abiDecoderReentry

Theorem alloca_step_old_ghost:
  stmt_state_rel ctx func ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
  !PG G tn x. x <> out ==>
    FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t) x =
      FLOOKUP G x /\
    op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn)
      (Var x) = op_taint tn (Var x)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      simp[op_taint_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] strip_assume_tac) >>
  simp[op_taint_def, FLOOKUP_UPDATE]
QED

Theorem alloca_step_ptr_val_ok:
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx ty se sf es v op s /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> val_wf tv v) /\
  ptr_val_ok cx ty v op G tn s /\
  (!x. op = Var x ==> x <> out) /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
  ptr_val_ok cx ty v op
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn) t
Proof
  strip_tac >>
  `!x. x <> out ==>
    FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t) x = FLOOKUP G x /\
    op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn) (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >> irule alloca_step_old_ghost >> metis_tac[]) >>
  drule alloca_step_operand_preserved >>
  disch_then (qspec_then `op` mp_tac) >> simp[] >> strip_tac >>
  `t.vs_memory = s.vs_memory` by
    (qspecl_then [`id`, `n2w n`, `out`, `s`] strip_assume_tac step_alloca_frame >> gvs[]) >>
  irule ptr_val_ok_footprint_frame >>
  qexistsl_tac [`G`, `s`, `tn`] >> simp[] >>
  conj_tac >- (Cases_on `op` >> gvs[op_taint_def]) >>
  conj_tac
  >- (rpt strip_tac >> spose_not_then assume_tac >>
      drule_all alloca_step_expr_read_clean >> simp[]) >>
  Cases_on `op` >> gvs[op_taint_def]
QED

Theorem alloca_step_ptr_buf_ok:
  stmt_state_rel ctx func ce cx es s /\ ptr_buf_ok ce e op G s /\
  (!x. op = Var x ==> x <> out) /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
  ptr_buf_ok ce e op
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t) t
Proof
  strip_tac >>
  `!x. x <> out ==>
    FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t) x = FLOOKUP G x /\
    op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn) (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >> irule alloca_step_old_ghost >> metis_tac[]) >>
  drule alloca_step_operand_preserved >>
  disch_then (qspec_then `op` mp_tac) >> simp[] >> strip_tac >>
  irule ptr_buf_ok_frame >> qexistsl_tac [`G`, `s`] >> simp[] >> metis_tac[]
QED

Theorem alloca_step_taint_below_frontier:
  stmt_state_rel ctx func ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
  !tn i. i < s.vs_alloca_next ==>
    (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem
     <=> i IN tn.t_mem)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (irule fresh_alloca_taint_below_frontier >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> drule reused_alloca_memory_taint >>
  disch_then (qspecl_then [`out`, `tn`] mp_tac) >> simp[]
QED

Theorem alloca_step_ghost_kept:
  stmt_state_rel ctx func ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\ ~not_fresh_at sa out /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
  ghost_kept ce es sa G tn s
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn)
Proof
  strip_tac >> simp[ghost_kept_def] >> rpt conj_tac
  >- (rpt strip_tac >> metis_tac[alloca_step_old_ghost])
  >- suspend "older" >>
  suspend "local"
QED
Resume alloca_step_ghost_kept[older]:
  rpt strip_tac >>
  `off + sz <= s.vs_alloca_next` by
    (gvs[stmt_state_rel_def, state_rel_def, alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `i < s.vs_alloca_next` by decide_tac >>
  drule alloca_step_taint_below_frontier >>
  disch_then (qspecl_then [`t`, `out`, `n`, `id`, `tn`, `i`] mp_tac) >> simp[]
QED
Resume alloca_step_ghost_kept[local]:
  rpt strip_tac >>
  `b + sz <= s.vs_alloca_next` by
    (gvs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def, local_region_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `i < s.vs_alloca_next` by decide_tac >>
  drule alloca_step_taint_below_frontier >>
  disch_then (qspecl_then [`t`, `out`, `n`, `id`, `tn`, `i`] mp_tac) >> simp[]
QED
Finalise alloca_step_ghost_kept

Theorem alloca_step_robust_below_frontier:
  stmt_state_rel ctx func ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
  val_wf tv v /\ p + val_footprint tv v <= s.vs_alloca_next /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v p m) ==>
  !m. mem_agree_outside
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem
    t.vs_memory m ==> val_in_memory tv v p m
Proof
  strip_tac >> `t.vs_memory = s.vs_memory` by
    (qspecl_then [`id`, `n2w n`, `out`, `s`] strip_assume_tac step_alloca_frame >> gvs[]) >>
  rpt strip_tac >> irule robust_val_in_memory_footprint_frame >> simp[] >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`,
    `(step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem`] >>
  simp[] >> rpt strip_tac >>
  `i < s.vs_alloca_next` by decide_tac >>
  metis_tac[alloca_step_taint_below_frontier]
QED

Theorem alloca_step_ghost_inv:
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  (!name p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
  ghost_inv d ce cx es
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn) t
Proof
  strip_tac >> simp[ghost_inv_def] >> rpt conj_tac
  >- suspend "locals"
  >- suspend "return"
  >- (rpt strip_tac >> gvs[ghost_inv_def] >>
      metis_tac[alloca_step_old_ghost]) >>
  irule alloca_step_stor_taint_ok >>
  metis_tac[ghost_inv_def]
QED
Resume alloca_step_ghost_inv[locals]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule alloca_step_old_ptr_covers >> metis_tac[ghost_inv_def]) >>
  rpt gen_tac >> strip_tac >>
  `p <> out` by metis_tac[] >>
  `lookup_var p s = SOME w` by
    (drule alloca_step_operand_preserved >>
     disch_then (qspec_then `Var p` mp_tac) >>
     simp[eval_operand_def]) >>
  `val_wf entry.type entry.value /\
   w2n w + val_footprint entry.type entry.value <= s.vs_alloca_next` by
    suspend "bounds" >>
  irule alloca_step_robust_below_frontier >>
  metis_tac[ghost_inv_def]
QED
Resume alloca_step_ghost_inv[bounds]:
  `local_ptrs_rel func ce es.scopes s` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  rewrite_tac[local_ptrs_rel_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  `val_footprint entry.type entry.value <= type_memory_size entry.type` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  simp[] >> decide_tac
QED
Resume alloca_step_ghost_inv[return]:
  Cases_on `d` >> simp[return_buf_ptr_def] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  gvs[ghost_inv_def, return_buf_ptr_def] >>
  conj_tac
  >- (drule alloca_step_operand_preserved >>
      disch_then (qspec_then `Var x` mp_tac) >> simp[eval_operand_def]) >>
  irule alloca_step_old_ptr_covers >> metis_tac[]
QED
Finalise alloca_step_ghost_inv

Theorem log_buffer_alloca_step:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK t
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule_all log_buffer_trace_code >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()]
QED

Theorem log_buffer_ghost_frame:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  local_ptrs_reserved ce sa /\ cap < dimword (:256) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ghost_inv d ce cx es
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
      [STRING #"%" (toString sa.cs_next_var)]) t)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
      [STRING #"%" (toString sa.cs_next_var)]) s t tn) t /\
  ghost_kept ce es sa G tn s
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
      [STRING #"%" (toString sa.cs_next_var)]) t)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
      [STRING #"%" (toString sa.cs_next_var)]) s t tn)
Proof
  strip_tac >> drule_all log_buffer_alloca_step >> strip_tac >>
  `~not_fresh_at sa (STRING #"%" (toString sa.cs_next_var))` by
    simp[not_fresh_at_def] >>
  conj_tac
  >- (irule alloca_step_ghost_inv >> simp[] >>
      gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  irule alloca_step_ghost_kept >> metis_tac[]
QED

Theorem log_buffer_ghost_seq_ptr:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  local_ptrs_reserved ce sa /\ cap < dimword (:256) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ghost_inv d ce cx es Gf tnf (t with vs_inst_idx := k) /\
  ghost_kept ce es sa G tn s Gf tnf
Proof
  strip_tac >> drule_all log_buffer_ghost_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[inst_seq_ptr_def, run_inst_seq_def, AllCaseEqs()] >>
  Cases_on `d`
  >- (gvs[ghost_inv_def, ptr_covers_def, stor_taint_ok_def, lookup_var_def,
          return_buf_ptr_def] >> first_assum ACCEPT_TAC) >>
  PairCases_on `x` >>
  gvs[ghost_inv_def, ptr_covers_def, stor_taint_ok_def, lookup_var_def,
      return_buf_ptr_def] >> first_assum ACCEPT_TAC
QED

Theorem log_buffer_old_values_seq_ptr:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf /\
  stmt_state_rel ctx func ce cx es s /\ cap < dimword (:256) /\
  expr_val_at ce cx ty se sf es v op s /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> val_wf tv v) /\
  abi_decoder_operand_live sa.cs_next_var op /\
  ptr_val_ok cx ty v op G tn s /\ ptr_buf_ok ce e op G s ==>
  ptr_val_ok cx ty v op Gf tnf (t with vs_inst_idx := k) /\
  ptr_buf_ok ce e op Gf (t with vs_inst_idx := k)
Proof
  strip_tac >> drule_all log_buffer_alloca_step >> strip_tac >>
  `!x. op = Var x ==> x <> STRING #"%" (toString sa.cs_next_var)` by
    (Cases_on `op` >> gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >> metis_tac[LESS_EQ_REFL]) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[inst_seq_ptr_def, run_inst_seq_def, AllCaseEqs()] >>
  simp[ptr_val_ok_inst_idx, ptr_buf_ok_def] >> conj_tac
  >- (irule alloca_step_ptr_val_ok >> metis_tac[]) >>
  `ptr_buf_ok ce e op
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w buf.buf_size)]
      [STRING #"%" (toString sa.cs_next_var)]) t) t` by
    (irule alloca_step_ptr_buf_ok >> metis_tac[]) >>
  gvs[ptr_buf_ok_def]
QED

Theorem log_buffer_old_ghost_seq_ptr:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tm /\
  stmt_state_rel ctx func ce cx es s /\ cap < dimword(:256) ==>
  !p. not_fresh_at sa p ==>
    FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p)
Proof
  strip_tac >> drule_all log_buffer_alloca_step >> strip_tac >>
  drule alloca_step_old_ghost >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`PG`,`G`,`tn`] assume_tac) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[inst_seq_ptr_def, run_inst_seq_def, AllCaseEqs()] >>
  rpt strip_tac >>
  `p <> STRING #"%" (toString sa.cs_next_var)` by
    metis_tac[not_fresh_at_def, LESS_EQ_REFL] >> metis_tac[]
QED
