Theory readonlyInvokeCopyFwdExecutionCreate
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdStepsExternalOracle readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdOperationalSupport
  internalReturnCopyFwdSim frameRel taintAgree ptrDiscipline
  venomCallOracleDefs venomExecSemantics venomState venomInst extCallOracle
  finite_map list pred_set words

Theorem ricf_opaque_consume_create[local]:
  consume_create_outcome rq s = (w,r) ==>
  consume_create_outcome rq (ricf_opaque_view fn PG G s) =
    (w,ricf_opaque_view fn PG G r)
Proof
  simp[consume_create_outcome_eq, ricf_opaque_view_def] >> strip_tac >> gvs[]
QED

Theorem ricf_opaque_frame_consume_create:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  s.vs_outcomes <> [] /\ request_agree_except D rq rq' /\
  (rq.cr_kind = CreateCall \/ ?salt. rq.cr_kind = Create2Call salt) /\ ~rq.cr_static /\
  consume_create_outcome rq s = (w,r) /\
  consume_create_outcome rq' t = (z,u) ==>
  w = z /\ ricf_opaque_frame_agree fn D X sites PG G
    (tn with <|t_stor := {}; t_trans := {}|>) r u
Proof
  strip_tac >>
  qabbrev_tac `ss = ricf_opaque_view fn PG G s` >>
  qabbrev_tac `tt = ricf_opaque_view fn PG G t` >>
  qabbrev_tac `rr = ricf_opaque_view fn PG G r` >>
  qabbrev_tac `uu = ricf_opaque_view fn PG G u` >>
  `consume_create_outcome rq ss = (w,rr) /\
   consume_create_outcome rq' tt = (z,uu)` by
    metis_tac[ricf_opaque_consume_create] >>
  `ss.vs_outcomes <> []` by simp[Abbr `ss`, ricf_opaque_view_def] >>
  `ricf_frame_agree D X sites (ricf_visible_params PG) (ricf_visible_prov G) tn ss tt` by
    fs[ricf_opaque_frame_agree_def, Excl "consume_create_outcome_eq"] >>
  `consume_create_outcome rq'
     (tt with <|vs_vars := ss.vs_vars; vs_params := ss.vs_params|>) =
    (z,uu with <|vs_vars := ss.vs_vars; vs_params := ss.vs_params|>)` by
    simp[ricf_consume_create_locals, Excl "consume_create_outcome_eq"] >>
  `w = z /\ taint_agree D X (tn with <|t_stor := {}; t_trans := {}|>) rr
     (uu with <|vs_vars := ss.vs_vars; vs_params := ss.vs_params|>)` by
    (irule taint_agree_consume_create_masked >>
     qexistsl [`rq`,`rq'`,`ss`,`tt with <|vs_vars := ss.vs_vars; vs_params := ss.vs_params|>`] >>
     fs[ricf_frame_agree_def, Excl "consume_create_outcome_eq"]) >>
  simp[ricf_opaque_frame_agree_def, Excl "consume_create_outcome_eq"] >>
  qpat_assum `Abbrev (rr = _)`
    (once_rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (uu = _)`
    (once_rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `consume_create_outcome rq ss = _` mp_tac >>
  qpat_x_assum `consume_create_outcome rq' tt = _` mp_tac >>
  simp[consume_create_outcome_eq] >>
  rpt strip_tac >> gvs[] >>
  fs[ricf_frame_agree_def, ircf_cross_def, op_taint_def] >> gvs[]
QED

Theorem ricf_opaque_live_stack_consume_create[local]:
  ricf_opaque_live_stack_agree D ids tn maps stk targets s t /\
  s.vs_outcomes <> [] /\ request_agree_except D rq rq' /\
  (rq.cr_kind = CreateCall \/ ?salt. rq.cr_kind = Create2Call salt) /\ ~rq.cr_static /\
  consume_create_outcome rq s = (w,r) /\
  consume_create_outcome rq' t = (z,u) ==>
  ricf_opaque_live_stack_agree D ids (tn with <|t_stor := {}; t_trans := {}|>)
    maps stk targets r u
Proof
  simp[ricf_opaque_live_stack_agree_def, Excl "consume_create_outcome_eq"] >> rpt strip_tac >>
  first_x_assum (qspec_then `j` mp_tac) >>
  simp[Excl "consume_create_outcome_eq"] >> strip_tac >>
  mp_tac (Q.INST [`fn` |-> `(EL j stk).cf_fn`,
    `X` |-> `ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk)`,
    `PG` |-> `ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params`,
    `G` |-> `(EL j stk).cf_prov`, `sites` |-> `EL j maps`,
    `tn` |-> `tn with t_var := (EL j stk).cf_tvar`,
    `s` |-> `merge_callee_state (EL j stk).cf_state s`,
    `t` |-> `merge_callee_state (EL j targets) t`,
    `r` |-> `merge_callee_state (EL j stk).cf_state r`,
    `u` |-> `merge_callee_state (EL j targets) u`]
    ricf_opaque_frame_consume_create) >>
  (impl_tac >- fs[ricf_consume_create_merge, merge_callee_state_def, Excl "consume_create_outcome_eq"]) >>
  simp[taint_fupdcanon, Excl "consume_create_outcome_eq"]
QED

Theorem ricf_execution_consume_create_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ MEM inst.inst_opcode [CREATE;CREATE2] /\
  s.vs_outcomes <> [] /\ request_agree_except D rq rq' /\
  (rq.cr_kind = CreateCall \/ ?salt. rq.cr_kind = Create2Call salt) /\ ~rq.cr_static /\
  inst.inst_outputs = [out] /\
  consume_create_outcome rq s = (w,r) /\
  step_inst fuel C inst s = OK (update_var out w r) /\
  (!z v. consume_create_outcome rq' t = (z,v) ==>
    step_inst fuel Ct inst t = OK (update_var out z v)) /\
  step_prov PG G inst (update_var out w r) = set_prov G [out] NONE /\
  step_taint inst s (update_var out w r) tn =
    tn with <|t_var := set_var_taint tn.t_var [out] {}; t_stor := {}; t_trans := {}|> /\
  occurrence_sites_step a B inst (update_var out w r) = B /\
  active_inst fn next ((update_var out w r) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG
      (step_prov PG G inst (update_var out w r))
      (step_taint inst s (update_var out w r) tn) fn next
      ((update_var out w r) with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst (update_var out w r))
      ledger E sites maps targets (step_taint inst s (update_var out w r) tn)
Proof
  strip_tac >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t /\
   ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) tn maps stk targets s t /\
   ircf_cross tn (ricf_phase_ranges 0 ledger) s t /\
   ricf_cert_crosses tn (ricf_phase_stack_ranges stk ledger) stk s t /\
   ricf_support_agree B E tn s t` by
    fs[ricf_execution_invariant_def, Excl "consume_create_outcome_eq"] >>
  Cases_on `consume_create_outcome rq' t` >>
  rename1 `consume_create_outcome rq' t = (target_result,target_state)` >>
  `w = target_result /\
   ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
     sites (ricf_complete_params PG s.vs_params) G
       (tn with <|t_stor := {}; t_trans := {}|>) r target_state` by
    (mp_tac (Q.INST [`X` |-> `ircf_dead (ricf_original_copy_ids C) s stk`,
       `PG` |-> `ricf_complete_params PG s.vs_params`,
       `z` |-> `target_result`, `u` |-> `target_state`]
       ricf_opaque_frame_consume_create) >>
     (impl_tac >- simp[Excl "consume_create_outcome_eq"]) >>
     simp[Excl "consume_create_outcome_eq"]) >>
  `ricf_opaque_live_stack_agree D (ricf_original_copy_ids C)
    (tn with <|t_stor := {}; t_trans := {}|>) maps stk targets r target_state` by
    (mp_tac (Q.INST [`ids` |-> `ricf_original_copy_ids C`,
       `z` |-> `target_result`, `u` |-> `target_state`]
       ricf_opaque_live_stack_consume_create) >>
     (impl_tac >- simp[Excl "consume_create_outcome_eq"]) >>
     simp[Excl "consume_create_outcome_eq"]) >>
  `r.vs_memory = s.vs_memory /\ target_state.vs_memory = t.vs_memory /\
   r.vs_allocas = s.vs_allocas /\ r.vs_params = s.vs_params /\
   r.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `consume_create_outcome rq s = _` mp_tac >>
     qpat_assum `consume_create_outcome rq' t = _` mp_tac >>
     simp[consume_create_outcome_eq] >> rpt strip_tac >> gvs[]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) (set_prov G [out] NONE)
    (tn with <|t_var := set_var_taint tn.t_var [out] {}; t_stor := {}; t_trans := {}|>)
    (update_var out w r) (update_var out w target_state)` by
    (mp_tac (Q.INST [`s` |-> `r`, `t` |-> `target_state`,
       `X` |-> `ircf_dead (ricf_original_copy_ids C) s stk`,
       `PG` |-> `ricf_complete_params PG s.vs_params`,
       `tn` |-> `tn with <|t_stor := {}; t_trans := {}|>`,
       `p` |-> `NONE`, `m` |-> `{}:num set`,
       `x` |-> `w:256 word`, `y` |-> `w:256 word`] ricf_opaque_frame_bind) >>
     (impl_tac >- simp[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
       ricf_value_agree_def, o1LowerDloadRelocationKernelTheory.ld_value_agree_def,
       word_agree_except_def, Excl "consume_create_outcome_eq"]) >>
     simp[Excl "consume_create_outcome_eq"]) >>
  `ricf_opaque_live_stack_agree D (ricf_original_copy_ids C)
    (tn with <|t_var := set_var_taint tn.t_var [out] {}; t_stor := {}; t_trans := {}|>) maps stk targets
    (update_var out w r) (update_var out w target_state)` by
    (mp_tac (Q.INST [`ids` |-> `ricf_original_copy_ids C`,
       `s` |-> `r`, `t` |-> `target_state`,
       `tn` |-> `tn with <|t_stor := {}; t_trans := {}|>`,
       `tv` |-> `set_var_taint tn.t_var [out] {}`,
       `x` |-> `w:256 word`, `y` |-> `w:256 word`]
       ricf_opaque_live_stack_update_var) >>
     (impl_tac >- simp[Excl "consume_create_outcome_eq"]) >>
     simp[Excl "consume_create_outcome_eq"]) >>
  qexists_tac `update_var out w target_state` >>
  mp_tac (Q.INST [`u` |-> `update_var out w r`,
    `v` |-> `update_var out w target_state`, `rt` |-> `tn`]
    ricf_execution_next) >>
  (impl_tac >- (fs[MEM, Excl "consume_create_outcome_eq"] >>
    simp[is_terminator_def, Once ircf_dead_def, update_var_def,
      Excl "consume_create_outcome_eq"] >>
    rpt conj_tac >>
    gvs[ircf_dead_def, ircf_cross_def, ricf_cert_crosses_def,
      taint_fupdcanon, ricf_support_agree_def, update_var_def, Excl "consume_create_outcome_eq"] >>
    metis_tac[])) >> simp[Excl "consume_create_outcome_eq"]
QED
