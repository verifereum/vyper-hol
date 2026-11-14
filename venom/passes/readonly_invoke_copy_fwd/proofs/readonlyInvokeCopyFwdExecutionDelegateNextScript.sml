Theory readonlyInvokeCopyFwdExecutionDelegateNext
Ancestors
  readonlyInvokeCopyFwdExecutionCallOperands readonlyInvokeCopyFwdExecutionExternal
  readonlyInvokeCopyFwdExecutionWriteGuards readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionHistory readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdStepsExternalOracle
  readonlyInvokeCopyFwdExecutionCallAnnotations
  readonlyInvokeCopyFwdReadonlyContract readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdRel o1LowerDloadOccurrence internalReturnCopyFwdSim
  frameRel taintAgree ptrDiscipline o1PassContract
  o1LowerDloadConcreteExternal o1LowerDloadShared
  venomCallOracleDefs extCallOracle regularCallEmitSim
  venomExecSemantics venomState venomInst codegenRel contextCodegenRel
  finite_map list pred_set words

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
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
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
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `tn.t_stor = {} /\ tn.t_trans = {}` by fs[taint_ok_def] >>
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
  `s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
   s.vs_call_ctx = t.vs_call_ctx` by
    (fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >>
     drule taint_agree_call_ctx >> drule taint_agree_shared >>
     simp[ricf_opaque_view_def] >> strip_tac >>
     drule_all ld_shared_clean_accounts >>
     drule_all ld_shared_clean_transient >> simp[]) >>
  `step_inst fuel Ct inst t = exec_delegatecall inst t gas addr ao' az ro' rs` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  qabbrev_tac `rq = venom_call_request s addr 0w ao az F with
    cr_kind := DelegateMessageCall` >>
  `rq = venom_call_request t addr 0w ao' az F with
    cr_kind := DelegateMessageCall` by
    simp[Abbr `rq`, venom_call_request_def] >>
  Cases_on `consume_call_outcome rq (w2n ro) (w2n rs) s` >>
  rename1 `consume_call_outcome rq (w2n ro) (w2n rs) s = (w,r)` >>
  `?out. inst.inst_outputs = [out] /\ u = update_var out w r` by
    (gvs[exec_delegatecall_def, Abbr `rq`, Excl "consume_call_outcome_eq", AllCaseEqs()] >>
     metis_tac[]) >>
  `!z v. consume_call_outcome rq (w2n ro') (w2n rs) t = (z,v) ==>
    step_inst fuel Ct inst t = OK (update_var out z v)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `step_inst fuel Ct inst t = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[exec_delegatecall_def, LET_THM] >>
     qpat_assum `rq = venom_call_request t addr 0w ao' az F with
       cr_kind := DelegateMessageCall`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     simp[Excl "consume_call_outcome_eq"]) >>
  `source_memory_write_ranges inst s = [(w2n ro,w2n rs)]` by
    simp[source_memory_write_ranges_def] >>
  `step_prov PG G inst (update_var out w r) = set_prov G [out] NONE /\
   step_taint inst s (update_var out w r) tn =
     (ricf_call_taint tn rq s r (w2n ro) (w2n rs)
       with t_var := set_var_taint tn.t_var [out] {}) /\
   occurrence_sites_step a B inst (update_var out w r) = B` by
    (`r.vs_allocas = s.vs_allocas /\ r.vs_fmp = s.vs_fmp` by
       (qpat_x_assum `consume_call_outcome rq _ _ s = _` mp_tac >>
        simp[consume_call_outcome_eq] >> rpt strip_tac >> gvs[]) >>
     mp_tac (INST_TYPE [alpha |-> ``:num``] ricf_execution_call_annotations) >>
     (impl_tac >- simp[Abbr `rq`, venom_call_request_def]) >> simp[]) >>
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
  `rq.cr_accounts = s.vs_accounts /\ rq.cr_accounts = t.vs_accounts /\
   rq.cr_tStorage = s.vs_transient /\ rq.cr_tStorage = t.vs_transient /\
   request_agree_except D rq rq` by
    simp[Abbr `rq`, venom_call_request_def, request_agree_except_def,
      accounts_agree_except_def, transient_agree_except_def,
      storage_agree_except_def, word_agree_except_def] >>
  qabbrev_tac `source_off = w2n ro` >>
  qabbrev_tac `target_off = w2n ro'` >>
  qabbrev_tac `output_size = w2n rs` >>
  mp_tac (Q.INST [`rq1` |-> `rq`, `rq2` |-> `rq`,
    `ro` |-> `source_off`, `ro'` |-> `target_off`,
    `rs` |-> `output_size`] ricf_execution_consume_call_next) >>
  (impl_tac >- (gvs[Abbr `source_off`, Abbr `target_off`, Abbr `output_size`,
    is_terminator_def, Excl "consume_call_outcome_eq"] >> metis_tac[])) >>
  simp[]
QED
