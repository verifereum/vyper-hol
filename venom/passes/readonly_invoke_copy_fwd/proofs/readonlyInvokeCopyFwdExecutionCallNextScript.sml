Theory readonlyInvokeCopyFwdExecutionCallNext
Ancestors
  readonlyInvokeCopyFwdExecutionCallOperands readonlyInvokeCopyFwdExecutionExternal
  readonlyInvokeCopyFwdExecutionCallAnnotations
  readonlyInvokeCopyFwdExecutionWriteGuards readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionHistory readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdStepsExternalOracle readonlyInvokeCopyFwdReadonlyContract
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdRel
  o1LowerDloadOccurrence internalReturnCopyFwdSim frameRel taintAgree ptrDiscipline
  o1PassContract venomCallOracleDefs extCallOracle regularCallEmitSim
  venomExecSemantics venomState venomInst codegenRel contextCodegenRel
  finite_map list pred_set words

Theorem ricf_execution_call_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_mapped_support a B E PG G sites /\
  ricf_analyzed_origins vs C stk PG G tn fn inst s a U B ledger sites maps /\
  ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B ledger /\
  o1_ctx_shape C /\ ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ taint_within D C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CALL;STATICCALL] /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `?gop adop vop aop azop rop rsop gas addr value ao az ro rs static prefix.
    eval_operand gop s = SOME gas /\ eval_operand adop s = SOME addr /\
    eval_operand aop s = SOME ao /\ eval_operand azop s = SOME az /\
    eval_operand rop s = SOME ro /\ eval_operand rsop s = SOME rs /\
    ((inst.inst_opcode = CALL /\ prefix = [gop;adop;vop] /\
      eval_operand vop s = SOME value /\ static = s.vs_call_ctx.cc_static) \/
     (inst.inst_opcode = STATICCALL /\ prefix = [gop;adop] /\ value = 0w /\ static = T)) /\
    inst.inst_operands = prefix ++ [aop;azop;rop;rsop] /\
    exec_ext_call inst s gas addr value ao az ro rs static = OK u` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     gvs[MEM] >> simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[AllCaseEqs()] >> metis_tac[]) >>
  `inst.inst_opcode = CALL ==> ~(s.vs_call_ctx.cc_static /\ value <> 0w)` by
    (strip_tac >> qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     gvs[MEM] >> simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     Cases_on `s.vs_call_ctx.cc_static /\ value <> 0w` >> gvs[]) >>
  `ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites` by
    fs[ricf_analyzed_origins_def] >>
  `IS_SOME (eval_operands prefix s)` by
    gvs[eval_operands_def] >>
  `(!op x. MEM op (prefix ++ [azop;rsop]) /\ eval_operand op s = SOME x ==>
      eval_operand op t = SOME x) /\
   ?ao' ro'. eval_operand aop t = SOME ao' /\ eval_operand rop t = SOME ro' /\
    read_memory (w2n ao) (w2n az) s = read_memory (w2n ao') (w2n az) t /\
    (w2n rs = 0 \/ ro = ro')` by
    (mp_tac ricf_execution_call_operands >> (impl_tac >- simp[]) >> simp[]) >>
  `eval_operand gop t = SOME gas /\ eval_operand adop t = SOME addr /\
   eval_operand azop t = SOME az /\ eval_operand rsop t = SOME rs /\
   (inst.inst_opcode = CALL ==> eval_operand vop t = SOME value)` by
    (gvs[MEM] >> metis_tac[]) >>
  qpat_x_assum `!op x. _` (K ALL_TAC) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  `t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `ricf_opaque_frame_agree _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >> strip_tac >>
     drule taint_agree_call_ctx >> simp[ricf_opaque_view_def]) >>
  `step_inst fuel C inst s = exec_ext_call inst s gas addr value ao az ro rs static /\
   step_inst fuel Ct inst t = exec_ext_call inst t gas addr value ao' az ro' rs static` by
    (fs[MEM] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  qabbrev_tac `rq1 = venom_call_request s addr value ao az static` >>
  qabbrev_tac `rq2 = venom_call_request t addr value ao' az static` >>
  Cases_on `consume_call_outcome rq1 (w2n ro) (w2n rs) s` >>
  rename1 `consume_call_outcome rq1 (w2n ro) (w2n rs) s = (w,r)` >>
  `?out. inst.inst_outputs = [out] /\ u = update_var out w r` by
    (gvs[exec_ext_call_def, Abbr `rq1`, Excl "consume_call_outcome_eq", AllCaseEqs()] >>
     metis_tac[]) >>
  `((computed_precompile rq1 /\ computed_precompile rq2 /\
      rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data) \/
    request_agree_except D rq1 rq2)` by
    (Cases_on `computed_precompile rq1`
     >- (disj1_tac >>
         gvs[Abbr `rq1`, Abbr `rq2`, computed_precompile_def, venom_call_request_def]) >>
     `LENGTH s.vs_requests < LENGTH u.vs_requests` by
       (qpat_x_assum `consume_call_outcome rq1 _ _ s = _` mp_tac >>
        simp[consume_call_outcome_eq] >> strip_tac >>
        gvs[update_var_def, record_request_def]) >>
     mp_tac ricf_execution_call_request_compatible >>
     (impl_tac >- simp[]) >> simp[Abbr `rq1`, Abbr `rq2`]) >>
  `source_memory_write_ranges inst s = [(w2n ro,w2n rs)]` by
    (fs[MEM] >> gvs[source_memory_write_ranges_def]) >>
  `step_prov PG G inst (update_var out w r) = set_prov G [out] NONE /\
   step_taint inst s (update_var out w r) tn =
     (ricf_call_taint tn rq1 s r (w2n ro) (w2n rs)
       with t_var := set_var_taint tn.t_var [out] {}) /\
   occurrence_sites_step a B inst (update_var out w r) = B` by
    (`r.vs_allocas = s.vs_allocas /\ r.vs_fmp = s.vs_fmp` by
       (qpat_x_assum `consume_call_outcome rq1 _ _ s = _` mp_tac >>
        simp[consume_call_outcome_eq] >> rpt strip_tac >> gvs[]) >>
     mp_tac (Q.INST [`rq` |-> `rq1`]
       (INST_TYPE [alpha |-> ``:num``] ricf_execution_call_annotations)) >>
     (impl_tac >- gvs[MEM, Abbr `rq1`, venom_call_request_def]) >> simp[]) >>
  `!gam. gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(w2n ro <= db+k /\ db+k < w2n ro + LENGTH (TAKE (w2n rs) r.vs_returndata)) /\
      ~(w2n ro <= sb+k /\ sb+k < w2n ro + LENGTH (TAKE (w2n rs) r.vs_returndata))` by
    (rpt strip_tac >>
     `LENGTH (TAKE (w2n rs) r.vs_returndata) <= w2n rs` by simp[LENGTH_TAKE_EQ] >>
     mp_tac (Q.INST [`off` |-> `w2n (ro:256 word)`,
       `len` |-> `w2n (rs:256 word)`, `certificates` |-> `ledger`]
       ricf_execution_write_ranges) >>
     (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
     decide_tac) >>
  `!z v. consume_call_outcome rq2 (w2n ro') (w2n rs) t = (z,v) ==>
    step_inst fuel Ct inst t = OK (update_var out z v)` by
    (rpt gen_tac >> strip_tac >>
     `rq2 = venom_call_request t addr value ao' az static` by simp[Abbr `rq2`] >>
     qpat_assum `step_inst fuel Ct inst t = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[exec_ext_call_def, LET_THM] >>
     qpat_assum `rq2 = venom_call_request _ _ _ _ _ _`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     qpat_assum `consume_call_outcome rq2 _ _ t = (z,v)`
       (fn th => pure_rewrite_tac[th]) >> simp[Excl "consume_call_outcome_eq"]) >>
  `rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
   rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient` by
    simp[Abbr `rq1`, Abbr `rq2`, venom_call_request_def] >>
  qabbrev_tac `source_off = w2n ro` >>
  qabbrev_tac `target_off = w2n ro'` >>
  qabbrev_tac `output_size = w2n rs` >>
  mp_tac (Q.INST [`ro` |-> `source_off`, `ro'` |-> `target_off`,
    `rs` |-> `output_size`] ricf_execution_consume_call_next) >>
  (impl_tac >- (gvs[Abbr `source_off`, Abbr `target_off`, Abbr `output_size`,
    MEM, is_terminator_def, Excl "consume_call_outcome_eq"] >> metis_tac[])) >>
  simp[]
QED
