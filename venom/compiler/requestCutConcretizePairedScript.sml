Theory requestCutConcretizePaired
Ancestors
  requestCutConcretizeCursor requestCutConcretizeVisit requestCutConcretizeGhosts
  requestCutVisitReachability requestCutConcretizeOperands
  concretizePtrDallocaObservationTransport concretizePtrRequestHistory
  concretizePtrChronologicalHistory concretizeLayoutLocalReturn lowerDloadPtrCall
  lowerDloadRequestObservation o1PassContract unitTransformDefs
  ptrDiscipline lowerDloadDefs contextCodegenRel venomExecSemantics venomState venomWf list pred_set

Theorem request_cut_concretize_paired:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  clip0 = (v with vs_outcomes := TAKE (k - LENGTH v.vs_requests) v.vs_outcomes) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C CT /\
  dead_wf D /\ o1_ctx_shape C /\ o1_ctx_shape CT /\
  o1_initial_state_ok clip0 /\ clip0.vs_fmp = clip0.vs_initial_fmp /\
  code_layout_valid clip0 /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C clip0 /\ fixed_region_reserved lo C /\ ptr_discipline lo C clip0 /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom CT = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n clip0.vs_initial_fmp) /\
  frame_reachable v CT stkT PT gT un fnT i t /\ LENGTH t.vs_requests = k /\
  i.inst_opcode <> INVOKE /\ step_inst fuel CT i t = OK t' /\
  k < LENGTH t'.vs_requests ==>
  ?stk PG G tn fn s s'. frame_reachable v C stk PG G tn fn i s /\
    active_inst fn i s /\ ~in_revert_forward fn s /\
    LENGTH s.vs_requests = k /\ s.vs_outcomes = t.vs_outcomes /\
    step_inst fuel C i s = OK s' /\ k < LENGTH s'.vs_requests /\
    (tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
       (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
     tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
       (s.vs_transient s.vs_call_ctx.cc_address) ==>
     request_agree_except D (EL k s'.vs_requests) (EL k t'.vs_requests) /\
     un.t_stor SUBSET D.d_stor t.vs_call_ctx.cc_address
       (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
     un.t_trans SUBSET D.d_trans t.vs_call_ctx.cc_address
       (t.vs_transient t.vs_call_ctx.cc_address))
Proof
  strip_tac >>
  `LENGTH t.vs_requests < LENGTH t'.vs_requests` by simp[] >>
  drule_all ld_request_growth_external >> strip_tac >>
  `EVERY wf_function CT.ctx_functions` by
    fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `?stkC. frame_reachable clip0 CT stkC PT gT un fnT i
      (t with vs_outcomes := [])` by
    (drule_all request_cut_clip_visit >> fs[]) >>
  `ctx_has_dalloca C ==> !n. max_live_eom CT = SOME n ==> n <= w2n clip0.vs_initial_fmp` by
    (rpt strip_tac >> metis_tac[optionTheory.SOME_11]) >>
  mp_tac (Q.INST [`rpolicy` |-> `rpolicy`, `C` |-> `C`, `CT` |-> `CT`,
    `lo` |-> `lo`, `clip0` |-> `clip0`, `eom` |-> `eom`, `i` |-> `i`,
    `un` |-> `un`, `stk` |-> `stkC`, `PG` |-> `PT`, `G` |-> `gT`,
    `gn` |-> `fnT`, `t` |-> `t with vs_outcomes := []`] request_cut_concretize_cursor) >>
  (impl_tac >- (asm_rewrite_tac[] >> qexists_tac `names` >> simp[])) >>
  disch_then (qx_choosel_then [`R`,`lp`,`positions`,`h`,`a`,`ht`,`done`,
    `tokens`,`registry`,`births`,`PT'`,`TG`,`saved`,`entries`,`H`,`calls`,`ws`]
      strip_assume_tac) >>
  qabbrev_tac `at = ptr_observe stkC PT gT un fnT i (t with vs_outcomes := [])` >>
  `at.po_state = (t with vs_outcomes := []) /\ at.po_taint = un` by
    simp[Abbr `at`, ptr_observe_def] >>
  `a.po_state.vs_outcomes = []` by simp[] >>
  mp_tac (Q.INST [`v` |-> `v`, `vt` |-> `v`, `clip0` |-> `clip0`,
    `C` |-> `C`, `CT` |-> `CT`, `stk` |-> `a.po_stack`, `PG` |-> `a.po_params`,
    `G` |-> `a.po_prov`, `tn` |-> `a.po_taint`, `fn` |-> `a.po_fn`, `i` |-> `i`,
    `sc` |-> `a.po_state`, `j` |-> `i`, `stkT` |-> `stkT`, `PT` |-> `PT`,
    `gT` |-> `gT`, `un` |-> `un`, `fnT` |-> `fnT`, `t` |-> `t`, `k` |-> `k`]
     request_cut_restore_visit) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`stk`,`s`] strip_assume_tac) >>
  `active_inst a.po_fn i s /\ ~in_revert_forward a.po_fn s` by
    (qpat_assum `active_inst a.po_fn i a.po_state` mp_tac >>
     qpat_assum `~in_revert_forward a.po_fn a.po_state` mp_tac >>
     qpat_assum `(s with vs_outcomes := []) = a.po_state` (SUBST1_TAC o SYM) >>
     simp[active_inst_def, in_revert_forward_def, revert_forward_at_def]) >>
  mp_tac (Q.INST [`PT` |-> `PT'`] request_cut_concretize_visit) >>
  (impl_tac >- (rpt conj_tac >> metis_tac[])) >>
  disch_then (qx_choose_then `s'` strip_assume_tac) >>
  `step_inst fuel C i s = OK s'` by metis_tac[] >>
  qexistsl_tac [`stk`,`a.po_params`,`a.po_prov`,`a.po_taint`,`a.po_fn`,`s`,`s'`] >>
  asm_rewrite_tac[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- metis_tac[] >>
  mp_tac (Q.INST [`PT` |-> `PT'`, `Ct` |-> `CT`, `vs` |-> `clip0`]
    request_cut_concretize_ghost_masks) >>
  (impl_tac >- (rpt conj_tac >> metis_tac[])) >> simp[] >> strip_tac >>
  qpat_x_assum `(s with vs_outcomes := []) = a.po_state` (SUBST_ALL_TAC o SYM) >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (drule ptr_history_content_call_ctx >> simp[]) >>
  `dload_shared_store a.po_taint a.po_taint s t` by
    (drule request_cut_concretize_store >> simp[dload_shared_store_def]) >>
  mp_tac (Q.INST [`tn` |-> `a.po_taint`, `tt` |-> `un`, `s` |-> `s`,
    `t` |-> `t`, `D` |-> `D`] ptr_dalloca_request_taint_transport) >>
  simp[] >>
  qpat_assum `dload_shared_store _ _ s t`
    (mp_tac o Q.SPEC `t.vs_call_ctx.cc_address` o cj 4 o
      PURE_REWRITE_RULE [dload_shared_store_def]) >>
  simp[] >> metis_tac[]
QED
