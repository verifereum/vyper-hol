Theory requestCutReplayJoin
Ancestors
  requestCutPreDftReplay requestCutCoveredInvariants requestCutReplayProofs unitTransformDefs lowerDloadDefs
  e2eRequestCutDefs o1PipelineCorrect o1PassContract o1RequestContract
  o1SafeUpto o1PassLift unitMemInv dftGasOracleDefs contextCodegenRel
  venomPassSchedule venomPipelineRunner irSupply fcgPruning
  venomExecSemantics venomState venomInst venomWf extCallOracle list

(* The retained recording and the event covers use one oracle. The clipped
   source replay then gives the actual request and the whole prefix. *)
Theorem request_cut_recording_through_o1:
  unit_wf unit /\ o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,supply) /\ pre.cu_context.ctx_entry = SOME entry /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  (!j. j < LENGTH o1_fn_passes ==>
    ctx_pass_stage rp (EL j o1_fn_passes) (o1_walk_view rp j) (stage j) (stage (SUC j))) /\
  (!j. j <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage j)) /\
  (!j. j <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row j) (stage j).ctx_functions) /\
  dead_wf D /\ o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
  code_layout_valid vs0 /\ fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) vs0 /\
  v7 = (vs0 with vs_gas_readings := filling) /\
  vi = (v7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  clip = (vi with vs_outcomes := TAKE (k - LENGTH vi.vs_requests) vi.vs_outcomes) /\
  clip7 = (v7 with vs_outcomes := TAKE (k - LENGTH v7.vs_requests) v7.vs_outcomes) /\
  o1_inv D 0 (stage 0) clip /\ ctx_abort_rq D unit.cu_context (stage 7) clip clip7 /\
  raw_safe_rq_upto D 0 k unit.cu_context vi /\
  raw_reachable vi unit.cu_context fn i s /\ i.inst_opcode <> INVOKE /\
  LENGTH s.vs_requests = k /\ step_inst fuel unit.cu_context i s = OK u /\
  k < LENGTH u.vs_requests /\
  raw_reachable v7 (stage 7) f7 i7 s7 /\ i7.inst_opcode <> INVOKE /\
  LENGTH s7.vs_requests = k /\ step_inst fuel7 (stage 7) i7 s7 = OK u7 /\
  k < LENGTH u7.vs_requests /\
  raw_reachable vs0 (stage 9) f9 i9 s9 /\ i9.inst_opcode <> INVOKE /\
  LENGTH s9.vs_requests = k /\ step_inst fuel9 (stage 9) i9 s9 = OK u9 /\
  s9.vs_outcomes = s7.vs_outcomes /\ u9.vs_requests = u7.vs_requests /\
  EVERY wf_function unit.cu_context.ctx_functions /\
  EVERY wf_function (stage 9).ctx_functions /\
  ctx_pass_stage rp (CFP_Simple VP_DFT) (o1_walk_view rp 7) (stage 7) (stage 8) /\
  o1_pre 7 (stage 7) (stage 8) /\
  ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) (o1_walk_view rp 8) (stage 8) (stage 9) /\
  EVERY wf_ssa (stage 7).ctx_functions /\ ctx_labels_bound (stage 7) vs0.vs_labels /\
  (!fn inst t. raw_reachable vs0 (stage 8) fn inst t /\ LENGTH t.vs_requests <= k /\
    ~in_static_abort_prefix fn t ==>
    ?p d. ev_reachable orc vs0 (stage 8) p d fn inst (t with vs_gas_readings := vs0.vs_gas_readings)) /\
  (!p d fn inst t. ev_reachable orc vs0 (stage 7) p d fn inst t /\ LENGTH t.vs_requests <= k ==>
    ?ws. raw_reachable v7 (stage 7) fn inst (t with vs_gas_readings := ws)) /\
  max_live_eom (stage 9) = SOME eom /\
  mem_inv (\ctx fn inst t. request_cut k t ==> lowered_mem_fact eom ctx fn inst t)
    (stage 7) v7 /\
  (guarded ==> code_end_offset_ok
    (\ctx fn inst t. raw_reachable v7 ctx fn inst t /\ request_cut k t) (stage 7)) ==>
  (?gn j t n z. raw_reachable vs0 (stage 9) gn j t /\ j.inst_opcode <> INVOKE /\
    LENGTH t.vs_requests = k /\ step_inst n (stage 9) j t = OK z /\
    k < LENGTH z.vs_requests /\ request_agree_except D (EL k u.vs_requests) (EL k z.vs_requests) /\
    t.vs_outcomes = s.vs_outcomes) /\
  ctx_rq_upto D k unit.cu_context (stage 9) vi vs0 /\
  (?bound. max_live_eom (stage 9) = SOME bound /\
    mem_inv (\ctx fn inst t. request_cut k t /\ ~in_static_abort_prefix fn t ==>
      lowered_mem_ok bound (w2n t.vs_initial_fmp) ctx fn inst t) (stage 9) vs0) /\
  (guarded ==> code_end_offset_ok (\ctx fn inst t. raw_reachable vs0 ctx fn inst t /\
    request_cut k t /\ ~in_static_abort_prefix fn t) (stage 9))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!rq rqs. record_request rq rqs = rqs ++ [rq]` by simp[record_request_def] >>
  `o1_initial_state_ok v7 /\ v7.vs_fmp = v7.vs_initial_fmp /\
   code_layout_valid v7 /\ fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) v7` by
    (qpat_assum `code_layout_valid vs0` mp_tac >>
     qpat_assum `fmp_variant_room _ _ vs0` mp_tac >>
     qpat_assum `o1_initial_state_ok vs0` mp_tac >>
     qpat_assum `vs0.vs_fmp = vs0.vs_initial_fmp` mp_tac >>
     qpat_assum `v7 = _` SUBST1_TAC >>
     simp[NoAsms, o1_initial_state_ok_def, code_layout_valid_def, fmp_variant_room_def]) >>
  mp_tac (Q.INST [`v7` |-> `v7`, `clip` |-> `clip`, `clip7` |-> `clip7`,
    `gn` |-> `f7`, `j` |-> `i7`, `fuel'` |-> `fuel7`, `t` |-> `s7`, `z` |-> `u7`] request_cut_pre_dft_recording) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `k < LENGTH u9.vs_requests /\ LIST_REL (request_agree_except D) u.vs_requests u9.vs_requests`
    by simp[] >>
  mp_tac (Q.INST [`C` |-> `unit.cu_context`, `C'` |-> `stage 9`,
    `vs` |-> `vi`, `vs'` |-> `vs0`, `s` |-> `s`, `t` |-> `s9`,
    `u` |-> `u`, `v` |-> `u9`, `inst` |-> `i`, `inst'` |-> `i9`,
    `fn'` |-> `f9`, `fuel'` |-> `fuel9`] request_cut_paired_recordings) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  conj_tac
  >- (qexistsl_tac [`f9`,`i9`,`s9`,`fuel9`,`u9`] >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!j. j <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage j)`
    (fn shape => map_every (fn n =>
      assume_tac (SIMP_RULE (srw_ss()) [o1_fn_passes_def] (Q.SPEC n shape))) [`7`, `8`]) >>
  qpat_assum `mem_inv _ (stage 7) v7` (assume_tac o REWRITE_RULE [request_cut_def]) >>
  qpat_assum `guarded ==> code_end_offset_ok _ (stage 7)`
    (assume_tac o REWRITE_RULE [request_cut_def]) >>
  mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`, `C9` |-> `stage 9`,
    `source` |-> `v7`, `vs0` |-> `vs0`, `dft_view` |-> `o1_walk_view rp 7`,
    `cfg_view` |-> `o1_walk_view rp 8`] request_cut_covered_invariants) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  pure_rewrite_tac[request_cut_def] >>
  conj_tac >- (qexists_tac `eom` >> simp[]) >>
  first_assum ACCEPT_TAC
QED
