Theory readonlyInvokeCopyFwdExecutionDelegateNext
Ancestors
  readonlyInvokeCopyFwdExecutionCallOperands readonlyInvokeCopyFwdExecutionExternal
  readonlyInvokeCopyFwdExecutionWriteGuards readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionHistory readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdStepsExternalOracle
  readonlyInvokeCopyFwdOperationalSupport
  readonlyInvokeCopyFwdExecutionCallAnnotations
  readonlyInvokeCopyFwdReadonlyContract readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdRel o1LowerDloadOccurrence internalReturnCopyFwdSim
  frameRel taintAgree ptrDiscipline o1PassContract
  o1LowerDloadConcreteExternal o1LowerDloadShared o1LowerDloadRelocationKernel
  venomCallOracleDefs extCallOracle regularCallEmitSim
  venomExecSemantics venomState venomInst codegenRel contextCodegenRel
  finite_map list pred_set words

Theorem ricf_delegate_frame_consume[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  request_agree_except D rq1 rq2 /\
  rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
  rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
  consume_call_outcome rq1 ro rs s = (w,r) /\
  consume_call_outcome rq2 ro' rs t = (z,u) /\ (rs = 0 \/ ro = ro') /\
  (!db sb sz k. (db,sb,sz) IN ricf_site_triples sites /\ k < sz ==>
    ~(ro <= db+k /\ db+k < ro + LENGTH (TAKE rs r.vs_returndata)) /\
    ~(ro <= sb+k /\ sb+k < ro + LENGTH (TAKE rs r.vs_returndata))) ==>
  w = z /\ ricf_opaque_frame_agree fn D X sites PG G
    (tn with t_mem := tn.t_mem DIFF
      {i | ro <= i /\ i < ro + LENGTH (TAKE rs r.vs_returndata)}) r u
Proof
  strip_tac >>
  `w = z /\ ricf_opaque_frame_agree fn D X sites PG G
    (ricf_call_taint tn rq1 s r ro rs) r u` by
    (Cases_on `rs = 0`
     >- (gvs[Excl "consume_call_outcome_eq"] >>
         irule (Q.INST [`rq2` |-> `rq2`, `t` |-> `t`,
           `ro2` |-> `ro'`] ricf_opaque_frame_consume_call_zero) >>
         simp[Excl "consume_call_outcome_eq"] >> metis_tac[]) >>
     gvs[Excl "consume_call_outcome_eq"] >>
     irule (Q.INST [`rq2` |-> `rq2`, `t` |-> `t`]
       ricf_opaque_frame_consume_call) >>
     simp[Excl "consume_call_outcome_eq"] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  `!tm. ricf_opaque_frame_agree fn D X sites PG G
      (tm with <|t_stor := {}; t_trans := {}|>) r u ==>
      ricf_opaque_frame_agree fn D X sites PG G tm r u` by
    (rpt (pop_assum (K ALL_TAC)) >> rpt gen_tac >>
     simp[ricf_opaque_frame_agree_def, ricf_frame_agree_def,
       taint_agree_def, ld_shared_agree_def, op_taint_def,
       ircf_cross_def, word_agree_except_def] >>
     rpt strip_tac >> metis_tac[]) >>
  Cases_on `~rq1.cr_static /\ r.vs_requests <> s.vs_requests /\
    r.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success` >>
  fs[ricf_call_taint_def, Excl "consume_call_outcome_eq"] >>
  first_x_assum (qspec_then `tn with t_mem := tn.t_mem DIFF
    {i | ro <= i /\ i < ro + LENGTH (TAKE rs r.vs_returndata)}` mp_tac) >>
  gvs[Excl "consume_call_outcome_eq"]
QED

Theorem ricf_execution_delegate_next:
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
  inst.inst_opcode = DELEGATECALL /\ step_inst fuel C inst s = OK u /\
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
  `?gop adop aop azop rop rsop gas addr ao az ro rs.
    inst.inst_operands = [gop;adop;aop;azop;rop;rsop] /\
    eval_operand gop s = SOME gas /\ eval_operand adop s = SOME addr /\
    eval_operand aop s = SOME ao /\ eval_operand azop s = SOME az /\
    eval_operand rop s = SOME ro /\ eval_operand rsop s = SOME rs /\
    exec_delegatecall inst s gas addr ao az ro rs = OK u` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     metis_tac[]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites` by
    fs[ricf_analyzed_origins_def] >>
  `(!op x. MEM op [gop;adop;azop;rsop] /\ eval_operand op s = SOME x ==>
      eval_operand op t = SOME x) /\
   ?ao' ro'. eval_operand aop t = SOME ao' /\ eval_operand rop t = SOME ro' /\
    read_memory (w2n ao) (w2n az) s = read_memory (w2n ao') (w2n az) t /\
    (w2n rs = 0 \/ ro = ro')` by
    (mp_tac (Q.INST [`prefix` |-> `[gop;adop]`]
       ricf_execution_call_family_operands) >>
     (impl_tac >- simp[eval_operands_def]) >> simp[DISJ_ASSOC] >> metis_tac[]) >>
  `eval_operand gop t = SOME gas /\ eval_operand adop t = SOME addr /\
   eval_operand azop t = SOME az /\ eval_operand rsop t = SOME rs` by
    metis_tac[MEM] >>
  qpat_x_assum `!op x. _` (K ALL_TAC) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (qpat_x_assum `ricf_opaque_frame_agree _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >> strip_tac >>
     drule taint_agree_call_ctx >> simp[ricf_opaque_view_def]) >>
  `step_inst fuel Ct inst t = exec_delegatecall inst t gas addr ao' az ro' rs` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  qabbrev_tac `rq1 = venom_call_request s addr 0w ao az F with
    <|cr_kind := DelegateMessageCall; cr_gas := SOME (w2n gas)|>` >>
  qabbrev_tac `rq2 = venom_call_request t addr 0w ao' az F with
    <|cr_kind := DelegateMessageCall; cr_gas := SOME (w2n gas)|>` >>
  Cases_on `consume_call_outcome rq1 (w2n ro) (w2n rs) s` >>
  rename1 `consume_call_outcome rq1 (w2n ro) (w2n rs) s = (w,r)` >>
  `?out. inst.inst_outputs = [out] /\ u = update_var out w r` by
    (gvs[exec_delegatecall_def, Abbr `rq1`, Excl "consume_call_outcome_eq", AllCaseEqs()] >>
     metis_tac[]) >>
  `s.vs_outcomes <> []` by
    (CCONTR_TAC >> gvs[exec_delegatecall_def, AllCaseEqs()]) >>
  `LENGTH s.vs_requests < LENGTH u.vs_requests` by
    (qpat_x_assum `consume_call_outcome rq1 _ _ s = _` mp_tac >>
     simp[consume_call_outcome_eq, Abbr `rq1`, computed_precompile_def,
       venom_call_request_def, record_request_def] >> strip_tac >>
     gvs[update_var_def]) >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  `tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
   tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)` by
    (fs[taint_within_def, Excl "consume_call_outcome_eq"] >> metis_tac[]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
    (qpat_x_assum `ricf_opaque_frame_agree _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >> strip_tac >>
     drule taint_agree_shared >> simp[ricf_opaque_view_def, ld_shared_agree_def]) >>
  `t.vs_outcomes <> []` by fs[ld_shared_agree_def] >>
  `accounts_agree_except D s.vs_accounts t.vs_accounts /\
   transient_agree_except D s.vs_transient t.vs_transient` by
    metis_tac[ld_shared_accounts_observe, ld_shared_transient_observe] >>
  `request_agree_except D rq1 rq2` by
    simp[Abbr `rq1`, Abbr `rq2`, venom_call_request_def,
      request_agree_except_def, call_request_component_equality] >>
  `!z v. consume_call_outcome rq2 (w2n ro') (w2n rs) t = (z,v) ==>
    step_inst fuel Ct inst t = OK (update_var out z v)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `step_inst fuel Ct inst t = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[exec_delegatecall_def, LET_THM] >>
     simp[Abbr `rq2`, Excl "consume_call_outcome_eq"] >> metis_tac[]) >>
  `source_memory_write_ranges inst s = [(w2n ro,w2n rs)]` by
    simp[source_memory_write_ranges_def] >>
  `step_prov PG G inst (update_var out w r) = set_prov G [out] NONE /\
   step_taint inst s (update_var out w r) tn =
     tn with <|t_mem := tn.t_mem DIFF
       {i | w2n ro <= i /\ i < w2n ro + LENGTH (TAKE (w2n rs) r.vs_returndata)};
       t_var := set_var_taint tn.t_var [out] {}|> /\
   occurrence_sites_step a B inst (update_var out w r) = B` by
    (`r.vs_allocas = s.vs_allocas /\ r.vs_fmp = s.vs_fmp` by
       (qpat_x_assum `consume_call_outcome rq1 _ _ s = _` mp_tac >>
        simp[consume_call_outcome_eq] >> rpt strip_tac >> gvs[]) >>
     mp_tac (INST_TYPE [alpha |-> ``:num``] ricf_execution_delegate_annotations) >>
     (impl_tac >- simp[]) >> simp[]) >>
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
  `rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
   rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient` by
    simp[Abbr `rq1`, Abbr `rq2`, venom_call_request_def] >>
  qabbrev_tac `mask = tn with t_mem := tn.t_mem DIFF
    {i | w2n ro <= i /\ i < w2n ro + LENGTH (TAKE (w2n rs) r.vs_returndata)}` >>
  `step_taint inst s (update_var out w r) tn =
    mask with t_var := set_var_taint mask.t_var [out] {}` by simp[Abbr `mask`] >>
  qpat_x_assum `step_taint inst s (update_var out w r) tn =
    tn with <|t_mem := _; t_var := _|>` (K ALL_TAC) >>
  Cases_on `consume_call_outcome rq2 (w2n ro') (w2n rs) t` >>
  rename1 `consume_call_outcome rq2 (w2n ro') (w2n rs) t =
    (target_result,target_state)` >>
  `ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) tn maps stk targets s t /\
   ircf_cross tn (ricf_phase_ranges 0 ledger) s t /\
   ricf_cert_crosses tn (ricf_phase_stack_ranges stk ledger) stk s t /\
   ricf_support_agree B E tn s t` by
    fs[ricf_execution_invariant_def, Excl "consume_call_outcome_eq"] >>
  `w = target_result /\ ricf_opaque_frame_agree fn D
    (ircf_dead (ricf_original_copy_ids C) s stk) sites
    (ricf_complete_params PG s.vs_params) G mask r target_state` by
    (qabbrev_tac `source_off = w2n ro` >>
     qabbrev_tac `target_off = w2n ro'` >>
     qabbrev_tac `output_size = w2n rs` >>
     mp_tac (Q.INST [`X` |-> `ircf_dead (ricf_original_copy_ids C) s stk`,
       `PG` |-> `ricf_complete_params PG s.vs_params`,
       `ro` |-> `source_off`, `ro'` |-> `target_off`, `rs` |-> `output_size`,
       `u` |-> `target_state`, `z` |-> `target_result`] ricf_delegate_frame_consume) >>
     (impl_tac >- (gvs[Abbr `source_off`, Abbr `target_off`, Abbr `output_size`,
       Excl "consume_call_outcome_eq"] >> metis_tac[arithmeticTheory.ADD_COMM])) >>
     simp[Abbr `mask`, Abbr `source_off`, Abbr `output_size`]) >>
  `r.vs_returndata = target_state.vs_returndata` by
    (qpat_x_assum `ricf_opaque_frame_agree _ _ _ _ _ _ _ r target_state` mp_tac >>
     simp[ricf_opaque_frame_agree_def, ricf_frame_agree_def,
       Excl "consume_call_outcome_eq"] >> strip_tac >>
     drule taint_agree_read_fields >> simp[ricf_opaque_view_def]) >>
  `r.vs_gas_readings = s.vs_gas_readings /\
   target_state.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[gasOracleReplayTheory.gas_consume_outcome_readings, pairTheory.SND] >>
  `ricf_opaque_live_stack_agree D (ricf_original_copy_ids C)
    mask maps stk targets r target_state` by
    (fs[ricf_opaque_live_stack_agree_def, Excl "consume_call_outcome_eq"] >>
     rpt strip_tac >>
     qpat_x_assum `!j. j < LENGTH stk ==> _` (qspec_then `j` mp_tac) >>
     simp[Excl "consume_call_outcome_eq"] >> strip_tac >>
     qabbrev_tac `source_off = w2n ro` >>
     qabbrev_tac `target_off = w2n ro'` >>
     qabbrev_tac `output_size = w2n rs` >>
     mp_tac (Q.INST [`fn` |-> `(EL j stk).cf_fn`,
       `X` |-> `ircf_dead (ricf_original_copy_ids C)
         (EL j stk).cf_state (DROP (SUC j) stk)`,
       `sites` |-> `EL j maps`,
       `PG` |-> `ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params`,
       `G` |-> `(EL j stk).cf_prov`, `tn` |-> `tn with t_var := (EL j stk).cf_tvar`,
       `s` |-> `merge_callee_state (EL j stk).cf_state s`,
       `t` |-> `merge_callee_state (EL j targets) t`,
       `r` |-> `merge_callee_state (EL j stk).cf_state r`,
       `u` |-> `merge_callee_state (EL j targets) target_state`,
       `ro` |-> `source_off`, `ro'` |-> `target_off`, `rs` |-> `output_size`,
       `rq1` |-> `rq1`, `rq2` |-> `rq2`, `z` |-> `target_result`]
       ricf_delegate_frame_consume) >>
     simp[ricf_consume_call_merge, merge_callee_state_def, Abbr `mask`,
       Abbr `source_off`, Abbr `target_off`, Abbr `output_size`,
       Excl "consume_call_outcome_eq"] >>
     (impl_tac >- (gvs[Excl "consume_call_outcome_eq"] >>
       metis_tac[arithmeticTheory.ADD_COMM])) >> simp[]) >>
  `r.vs_vars = s.vs_vars /\ r.vs_params = s.vs_params /\
   r.vs_allocas = s.vs_allocas` by metis_tac[ricf_consume_call_footprint] >>
  `step_inst fuel Ct inst t = OK (update_var out w target_state)` by
    metis_tac[] >>
  `!gam. (gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger)) ==>
    ircf_cross mask gam r target_state` by
    (rpt strip_tac >>
     `ircf_cross tn gam s t` by
       fs[ricf_cert_crosses_def, EVERY_MEM] >>
     (Cases_on `w2n rs = 0`
     >- (qpat_assum `consume_call_outcome rq1 _ _ s = _`
           (mp_then Any strip_assume_tac ricf_consume_call_footprint) >>
         qpat_assum `consume_call_outcome rq2 _ _ t = _`
           (mp_then Any strip_assume_tac ricf_consume_call_footprint) >>
         gvs[Abbr `mask`, ircf_cross_def, Excl "consume_call_outcome_eq"] >>
         metis_tac[]) >>
     gvs[Excl "consume_call_outcome_eq"] >>
     qmatch_goalsub_abbrev_tac `ircf_cross mask crossed_ranges r target_state` >>
     qabbrev_tac `source_off = w2n ro` >>
     qabbrev_tac `output_size = w2n rs` >>
     mp_tac (Q.INST [`gam` |-> `crossed_ranges`, `rq1` |-> `rq1`, `rq2` |-> `rq2`,
       `ro` |-> `source_off`, `rs` |-> `output_size`,
       `u` |-> `target_state`, `w` |-> `target_result`, `z` |-> `target_result`]
       ricf_cross_consume_call) >>
     (impl_tac >- (simp[Abbr `source_off`, Abbr `output_size`, Abbr `crossed_ranges`,
       Excl "consume_call_outcome_eq"] >>
       metis_tac[arithmeticTheory.ADD_COMM])) >>
     simp[ircf_cross_def, ricf_call_taint_def, Abbr `mask`,
       Abbr `source_off`, Abbr `output_size`, Abbr `crossed_ranges`])) >>
  `ricf_support_agree B E mask r target_state` by
    (`r.vs_memory = (write_memory_with_expansion (w2n ro)
        (TAKE (w2n rs) r.vs_returndata) s).vs_memory /\
      target_state.vs_memory = (write_memory_with_expansion (w2n ro')
        (TAKE (w2n rs) r.vs_returndata) t).vs_memory /\
      r.vs_alloca_next = s.vs_alloca_next` by
       (qpat_x_assum `consume_call_outcome rq1 _ _ s = _` mp_tac >>
        qpat_x_assum `consume_call_outcome rq2 _ _ t = _` mp_tac >>
        simp[consume_call_outcome_eq] >> rpt strip_tac >> gvs[]) >>
     Cases_on `w2n rs = 0`
     >- (gvs[ricf_support_agree_def, Abbr `mask`,
           read_byte_write_memory_with_expansion, Excl "consume_call_outcome_eq"] >>
         metis_tac[]) >>
     gvs[ricf_support_agree_def, Abbr `mask`,
       read_byte_write_memory_with_expansion, Excl "consume_call_outcome_eq"] >>
     rpt strip_tac >> IF_CASES_TAC >>
     simp[Excl "consume_call_outcome_eq"] >> metis_tac[]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) (set_prov G [out] NONE)
    (mask with t_var := set_var_taint mask.t_var [out] {})
    (update_var out w r) (update_var out w target_state)` by
    (mp_tac (Q.INST [`tn` |-> `mask`, `s` |-> `r`, `t` |-> `target_state`,
       `X` |-> `ircf_dead (ricf_original_copy_ids C) s stk`,
       `PG` |-> `ricf_complete_params PG s.vs_params`, `p` |-> `NONE`,
       `m` |-> `{}:num set`, `x` |-> `w:256 word`, `y` |-> `w:256 word`]
       ricf_opaque_frame_bind) >>
     (impl_tac >- simp[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
       ricf_value_agree_def, ld_value_agree_def, word_agree_except_def]) >> simp[]) >>
  qexists_tac `update_var out w target_state` >> simp[] >>
  mp_tac (Q.INST [`u` |-> `update_var out w r`,
    `v` |-> `update_var out w target_state`, `rt` |-> `tn`] ricf_execution_next) >>
  (impl_tac >- (fs[Excl "consume_call_outcome_eq"] >>
    simp[is_terminator_def, Excl "consume_call_outcome_eq"] >>
    rpt conj_tac
    >- gvs[ircf_dead_def, update_var_def, Excl "consume_call_outcome_eq"]
    >- (mp_tac (Q.INST [`ids` |-> `ricf_original_copy_ids C`, `tn` |-> `mask`,
          `s` |-> `r`, `t` |-> `target_state`,
          `tv` |-> `set_var_taint mask.t_var [out] {}`,
          `x` |-> `target_result:256 word`, `y` |-> `target_result:256 word`]
          ricf_opaque_live_stack_update_var) >> simp[Excl "consume_call_outcome_eq"])
    >- (fs[ircf_cross_def, update_var_def, Excl "consume_call_outcome_eq"] >> metis_tac[])
    >- (fs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def, update_var_def,
          Excl "consume_call_outcome_eq"] >> metis_tac[]) >>
    fs[ricf_support_agree_def, update_var_def, Excl "consume_call_outcome_eq"] >> metis_tac[])) >>
  gvs[Excl "consume_call_outcome_eq"]
QED
