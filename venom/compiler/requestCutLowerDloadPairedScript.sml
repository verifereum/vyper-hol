Theory requestCutLowerDloadPaired
Ancestors
  lowerDloadDefs unitTransformDefs
  requestCutLowerDloadCursor requestCutLowerDloadVisit requestCutVisitReachability
  lowerDloadOwnership lowerDloadReachableFloor lowerDloadNormalData
  lowerDloadCoverageInvariant lowerDloadSharedState lowerDloadRequestObservation
  requestCutReplayProofs e2eRequestCutDefs o1PassContract o1RequestContract
  jointRequestCut contextCodegenRel ptrDiscipline venomExecSemantics venomState list rich_list

Theorem request_cut_lower_dload_paired:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  clip0 = (v with vs_outcomes := TAKE (k - LENGTH v.vs_requests) v.vs_outcomes) /\
  ctx_pass_stage rp (CFP_Simple VP_LowerDload) view C CT /\
  dead_wf D /\ o1_ctx_shape C /\ o1_ctx_shape CT /\
  o1_initial_state_ok clip0 /\ clip0.vs_fmp = clip0.vs_initial_fmp /\
  code_layout_valid clip0 /\ o1_src_inv D C clip0 /\ callee_first names C.ctx_functions /\
  frame_reachable v CT stkT PT gT un fnT i t /\
  taint_within_rq_upto D k C v /\ LENGTH t.vs_requests = k /\
  i.inst_opcode <> INVOKE /\ step_inst fuel CT i t = OK t' /\
  k < LENGTH t'.vs_requests ==>
  ?stk PG G tn fn s s'. frame_reachable v C stk PG G tn fn i s /\
    active_inst fn i s /\ ~in_revert_forward fn s /\
    LENGTH s.vs_requests = k /\ s.vs_outcomes = t.vs_outcomes /\
    step_inst fuel C i s = OK s' /\ k < LENGTH s'.vs_requests /\
    request_agree_except D (EL k s'.vs_requests) (EL k t'.vs_requests) /\
    un.t_stor SUBSET D.d_stor t.vs_call_ctx.cc_address
      (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
    un.t_trans SUBSET D.d_trans t.vs_call_ctx.cc_address
      (t.vs_transient t.vs_call_ctx.cc_address)
Proof
  strip_tac >>
  `LENGTH t.vs_requests < LENGTH t'.vs_requests` by simp[] >>
  drule_all ld_request_growth_external >> strip_tac >>
  `EVERY wf_function CT.ctx_functions` by
    fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `?stkC. frame_reachable clip0 CT stkC PT gT un fnT i
      (t with vs_outcomes := [])` by
    (drule_all request_cut_clip_visit >> fs[]) >>
  mp_tac (Q.INST [`CS` |-> `C`, `CT` |-> `CT`, `rp` |-> `rp`, `view` |-> `view`,
    `D` |-> `D`, `names` |-> `names`, `clip0` |-> `clip0`, `stk` |-> `stkC`,
    `PG` |-> `PT`, `G` |-> `gT`, `un` |-> `un`, `gn` |-> `fnT`, `i` |-> `i`,
    `t` |-> `t with vs_outcomes := []`] request_cut_lower_dload_cursor) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (qx_choosel_then [`A`,`AG`,`AP`,`BH`,`BP`,`E`,`H`,`L`,`U`,`V`,
    `astk`,`d`,`f`,`fn`,`gstk`,`j`,`keys`,`live`,`sc`,`suspended`,`tn`] strip_assume_tac) >>
  drule ld_annotated_erasure >>
  disch_then (qx_choosel_then [`stk0`,`PG`,`G`] strip_assume_tac) >>
  mp_tac (Q.INST [`v` |-> `v`, `vt` |-> `v`, `clip0` |-> `clip0`,
    `C` |-> `C`, `CT` |-> `CT`, `stk` |-> `stk0`, `PG` |-> `PG`, `G` |-> `G`,
    `tn` |-> `tn`, `fn` |-> `fn`, `i` |-> `i`, `sc` |-> `sc`, `j` |-> `i`,
    `stkT` |-> `stkT`, `PT` |-> `PT`, `gT` |-> `gT`, `un` |-> `un`,
    `fnT` |-> `fnT`, `t` |-> `t`, `k` |-> `k`] request_cut_restore_visit) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`stk`,`s`] strip_assume_tac) >>
  qpat_x_assum `(s with vs_outcomes := []) = sc` (SUBST_ALL_TAC o SYM) >>
  `active_inst fn i s /\ ~in_revert_forward fn s` by
    fs[in_revert_forward_def, revert_forward_at_def] >>
  `ptr_discipline clip0.vs_alloca_next C clip0` by
    metis_tac[ld_o1_src_inv_frontier_discipline_static] >>
  `?P. !g. MEM g C.ctx_functions ==> fn_ptr_ok P g` by
    (qpat_assum `ptr_discipline _ C clip0` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ptr_discipline_def, EVERY_MEM] >>
     metis_tac[]) >>
  drule_all request_cut_lower_dload_visit >>
  disch_then (qspec_then `D` (qx_choose_then `s'` strip_assume_tac)) >>
  `tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
       (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
    tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
       (s.vs_transient s.vs_call_ctx.cc_address)` by
    (qpat_assum `taint_within_rq_upto D k C v`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [taint_within_rq_upto_def]) >>
     disch_then (qspecl_then [`stk`,`PG`,`G`,`tn`,`fn`,`i`,`s`,`fuel`,`s'`] mp_tac) >>
     simp[request_cut_def]) >>
  `request_agree_except D (EL k s'.vs_requests) (EL k t'.vs_requests)` by simp[] >>
  qexistsl_tac [`stk`,`PG`,`G`,`tn`,`fn`,`s`,`s'`] >> asm_rewrite_tac[] >>
  `?rq rq'. s'.vs_requests = s.vs_requests ++ [rq] /\
    t'.vs_requests = t.vs_requests ++ [rq'] /\
    rq.cr_accounts = s.vs_accounts /\ rq'.cr_accounts = t.vs_accounts /\
    rq.cr_tStorage = s.vs_transient /\ rq'.cr_tStorage = t.vs_transient` by
    metis_tac[recording_step_appends_one] >>
  drule ld_normal_data_masks >> strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (drule ld_normal_data_frame >>
     disch_then (mp_tac o MATCH_MP ld_frame_data_shared) >>
     simp[ld_shared_state_def]) >>
  `EL k s'.vs_requests = rq /\ EL k t'.vs_requests = rq'` by
    (conj_tac
     >- (qpat_assum `LENGTH s.vs_requests = k` (fn len =>
           qpat_assum `s'.vs_requests = _` (fn app =>
             simp_tac bool_ss [GSYM len, app, EL_LENGTH_APPEND_0]))) >>
     qpat_assum `LENGTH t.vs_requests = k` (fn len =>
       qpat_assum `t'.vs_requests = _` (fn app =>
         simp_tac bool_ss [GSYM len, app, EL_LENGTH_APPEND_0]))) >>
  `request_agree_except D rq rq'` by metis_tac[] >>
  qpat_x_assum `request_agree_except D rq rq'`
    (strip_assume_tac o REWRITE_RULE
      [request_agree_except_def, accounts_agree_except_def, transient_agree_except_def]) >>
  conj_tac
  >- (irule dead_stor_taint_transport >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`tn.t_stor`,`(s.vs_accounts t.vs_call_ctx.cc_address).storage`] >> fs[] >>
      qpat_assum `rq.cr_accounts = s.vs_accounts` (fn src =>
        qpat_assum `rq'.cr_accounts = t.vs_accounts` (fn dst =>
          qpat_assum `!a. _ /\ storage_agree_except _ _ _`
            (qspec_then `t.vs_call_ctx.cc_address`
              (ACCEPT_TAC o REWRITE_RULE [src,dst] o CONJUNCT2))))) >>
  irule dead_trans_taint_transport >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`tn.t_trans`,`s.vs_transient t.vs_call_ctx.cc_address`] >> fs[] >>
  qpat_assum `rq.cr_tStorage = s.vs_transient` (fn src =>
    qpat_assum `rq'.cr_tStorage = t.vs_transient` (fn dst =>
      qpat_assum `!a. storage_agree_except _ _ _`
        (qspec_then `t.vs_call_ctx.cc_address` (ACCEPT_TAC o REWRITE_RULE [src,dst]))))
QED
