(* Zero/one-step normalization at a restore-relevant source point. *)
Theory fmpStageCoverRestore
Ancestors
  fmpStageCoverPointBase fmpStageFmpSteps fmpStageCoverInv fmpStageRel
  venomExecSemantics venomState venomInst finite_map words list

Theorem fmp_cov_point_restore:
  (!fn' C' name ti t fuel t2 n u.
    ALL_DISTINCT (fn_labels fn') /\
    lookup_function name C'.ctx_functions = SOME fn' /\ active_inst fn' ti t /\
    ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
    step_inst fuel C' ti t = OK t2 /\ 0 < n /\
    (!k. fmp_target_run k C' name t n u) ==>
    !k. fmp_target_run k C' name
      (t2 with vs_inst_idx := SUC t.vs_inst_idx) (n-1) u) /\
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs' C' stk' PG' G' tn' fn' ti t /\ active_inst fn' ti t /\
  ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
  step_inst fuel C' ti t = OK t2 /\
  active_inst fn' ti' (t2 with vs_inst_idx := SUC t.vs_inst_idx) /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\
  (MEM inst.inst_opcode [DALLOCA; INVOKE] \/ is_terminator inst.inst_opcode) /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_cov_stack C' stk ts stk' ==>
  fmp_cov D C C' vs vs' fmp eom stk' fn'
    (t2 with vs_inst_idx := SUC t.vs_inst_idx) \/
  (?sm1 lo1. fmp_stage_rel D C' sm1 (w2n vs'.vs_initial_fmp)
    (w2n fmp) eom T stk PG G tn fn s lo1 t ts)
Proof
  rpt strip_tac >> (
  drule fmp_stage_restore >> simp[] >>
  disch_then drule_all >> strip_tac >>
  Cases_on `n = 0`
  >- (disj2_tac >> `t1 = t` by metis_tac[fmp_target_run_zero] >>
      gvs[] >> metis_tac[]) >>
  `n = 1` by decide_tac >> gvs[] >>
  disj1_tac >>
  drule_all fmp_cov_target_labels >> strip_tac >>
  `t.vs_current_bb = t1.vs_current_bb` by
    metis_tac[fmp_cov_frame_pos] >>
  `t1.vs_inst_idx = t.vs_inst_idx + 1` by
    (qpat_x_assum `!k. fmp_target_run k _ _ _ _ _`
       (qspec_then `0` mp_tac) >>
     simp[fmp_target_run_def] >> strip_tac >> gvs[]) >>
  irule fmp_cov_endpoint_next >> (
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`G`, `PG`, `bb'`, `fn`, `inst`, `lo'`, `1`, `T`, `s`,
    `DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < lo'}`,
    `stk`, `tn`, `ts`, `t1`] >>
  simp[]))
QED
