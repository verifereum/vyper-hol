Theory requestCutFmpPaired
Ancestors
  requestCutFmpCursor requestCutFmpVisit requestCutVisitReachability
  fmpStageCoverage fmpStageRel lowerDloadRequestObservation
  lowerDloadOracleCallAssembly lowerDloadPtrRawReachable
  o1PassContract o1ContractSimplifyCfgSrcFrame ptrDiscipline
  e2eRequestCutDefs contextCodegenRel unitShapeDefs
  venomExecSemantics venomState venomWf list

(* Use the clipped FMP invariant through the cursor, then execute the
   paired recording instruction on the original outcomes. *)
Theorem request_cut_fmp_paired:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  v.vs_requests = vt.vs_requests /\ v.vs_outcomes = vt.vs_outcomes /\
  clip0 = (v with vs_outcomes := TAKE (k - LENGTH v.vs_requests) v.vs_outcomes) /\
  clipT = (vt with vs_outcomes := TAKE (k - LENGTH vt.vs_requests) vt.vs_outcomes) /\
  fmp_stage_ctx rp D C CT clip0 clipT fmp eom /\ o1_ctx_shape CT /\
  frame_reachable vt CT stkT PT gT un fnT i t /\ active_inst fnT i t /\
  LENGTH t.vs_requests = k /\
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
     request_agree_except D (EL k s'.vs_requests) (EL k t'.vs_requests))
Proof
  strip_tac >>
  `LENGTH t.vs_requests < LENGTH t'.vs_requests` by simp[] >>
  drule_all ld_request_growth_external >> strip_tac >>
  `EVERY wf_function CT.ctx_functions /\ ALL_DISTINCT (fn_labels fnT)` by
    (drule scfg_frame_reachable_functions >>
     fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `?stkC. frame_reachable clipT CT stkC PT gT un fnT i
      (t with vs_outcomes := [])` by
    (drule_all request_cut_clip_visit >> fs[]) >>
  `active_inst fnT i (t with vs_outcomes := [])` by simp[] >>
  qpat_assum `fmp_stage_ctx rp D C CT clip0 clipT fmp eom`
    (mp_tac o MATCH_MP fmp_stage_coverage) >>
  disch_then (qspecl_then [`stkC`,`PT`,`gT`,`un`,`fnT`,`i`,
    `t with vs_outcomes := []`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all request_cut_fmp_cursor >>
  disch_then (qx_choosel_then [`stk0`,`PG`,`G`,`tn`,`fn`,`sc`,`sm`,`lo`,
    `ts`,`restored`] strip_assume_tac) >>
  `sc.vs_outcomes = []` by simp[] >>
  mp_tac (Q.INST [`v` |-> `v`, `vt` |-> `vt`, `clip0` |-> `clip0`,
    `C` |-> `C`, `CT` |-> `CT`, `stk` |-> `stk0`, `PG` |-> `PG`, `G` |-> `G`,
    `tn` |-> `tn`, `fn` |-> `fn`, `i` |-> `i`, `sc` |-> `sc`, `j` |-> `i`,
    `stkT` |-> `stkT`, `PT` |-> `PT`, `gT` |-> `gT`, `un` |-> `un`,
    `fnT` |-> `fnT`, `t` |-> `t`, `k` |-> `k`] request_cut_restore_visit) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`stk`,`s`] strip_assume_tac) >>
  qpat_x_assum `(s with vs_outcomes := []) = sc` (SUBST_ALL_TAC o SYM) >>
  `active_inst fn i s /\ ~in_revert_forward fn s` by
    fs[in_revert_forward_def, revert_forward_at_def] >>
  `inst_wf i` by
    (drule scfg_frame_reachable_functions >>
     fs[fmp_stage_ctx_def, o1_ctx_shape_def, o1_fn_shape_def, fn_inst_wf_def,
        active_inst_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  drule_all request_cut_fmp_visit >>
  disch_then (qx_choose_then `s'` strip_assume_tac) >>
  qexistsl_tac [`stk`,`PG`,`G`,`tn`,`fn`,`s`,`s'`] >> asm_rewrite_tac[]
QED
