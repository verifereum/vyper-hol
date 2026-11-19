Theory requestCutClippedSafety
Ancestors
  loweringBudgetFrameOracleTransport
  requestCutOracleFrames requestCutOracleReplay e2eRequestCutDefs jointRequestCut
  concretizePtrCoverageStaticMemReachability frameRawProjection
  contextRawReachable contextCodegenRel unitMemInv unitTransformDefs
  o1SafeUpto o1PassContract unitShapeDefs ptrDiscipline memSafeRun lowerDloadDefs
  opcodeClass instIdxIndep venomExecSemantics
  venomState venomInst list rich_list arithmetic
Libs
  BasicProvers stepInstBaseLib

val _ = export_rewrites
  ["loweringBudgetFrameOracleTransport.read_ranges_outcomes_update"]

Theorem frame_reachable_clipped_oracle[local]:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  vs.vs_outcomes = short ++ tail /\
  LENGTH short + LENGTH vs.vs_requests <= k /\
  frame_reachable (vs with vs_outcomes := short) C stk PG G tn fn i s ==>
  request_cut k s /\
  frame_reachable vs C
    (MAP (\f. f with cf_state := (f.cf_state with
      vs_outcomes := f.cf_state.vs_outcomes ++ tail)) stk)
    PG G tn fn i (s with vs_outcomes := s.vs_outcomes ++ tail)
Proof
  strip_tac >> drule frame_reachable_oracle_length >> simp[request_cut_def] >>
  disch_tac >>
  drule frame_reachable_outcome_suffix >>
  disch_then (qspec_then `tail` mp_tac) >> simp[] >>
  `vs with vs_outcomes := short ++ tail = vs` by
    simp[venom_state_component_equality] >>
  simp[]
QED

Theorem raw_reachable_clipped_oracle[local]:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  vs.vs_outcomes = short ++ tail /\
  LENGTH short + LENGTH vs.vs_requests <= k /\
  EVERY wf_function C.ctx_functions /\
  raw_reachable (vs with vs_outcomes := short) C fn i s ==>
  request_cut k s /\
  raw_reachable vs C fn i (s with vs_outcomes := s.vs_outcomes ++ tail)
Proof
  strip_tac >> drule ptr_raw_reachable_frame >> strip_tac >>
  drule_all frame_reachable_clipped_oracle >>
  metis_tac[frame_reachable_raw]
QED

Theorem request_cut_safety_outcome_update[local]:
  request_cut k (s with vs_outcomes := os) = request_cut k s /\
  raw_mem_ok C fn i (s with vs_outcomes := os) = raw_mem_ok C fn i s /\
  dload_offset_ok C fn i (s with vs_outcomes := os) = dload_offset_ok C fn i s /\
  inst_dload_in_section i (s with vs_outcomes := os) = inst_dload_in_section i s /\
  access_ok lo G fn i (s with vs_outcomes := os) = access_ok lo G fn i s /\
  taint_ok fn tn i (s with vs_outcomes := os) = taint_ok fn tn i s /\
  allocas_from lo (s with vs_outcomes := os) = allocas_from lo s /\
  allocas_below_fmp (s with vs_outcomes := os) = allocas_below_fmp s /\
  ret_taint tn i (s with vs_outcomes := os) = ret_taint tn i s
Proof
  simp[request_cut_def, raw_mem_ok_def, inst_mem_ok_in_fn_def,
       inst_mem_below_frontiers_def, dalloca_no_wrap_def,
       dload_offset_ok_def, inst_dload_in_section_def, access_ok_def,
       taint_ok_def, in_revert_forward_def, about_to_revert_def, active_inst_def,
       allocas_from_def, allocas_below_fmp_def, ret_taint_def] >>
  rpt (PURE_TOP_CASE_TAC >> simp[])
QED

Theorem noninvoke_halt_oracle[local]:
  i.inst_opcode <> INVOKE /\ step_inst fuel C i s = Halt t ==>
  t.vs_outcomes = s.vs_outcomes
Proof
  strip_tac >> drule step_inst_halt_opcodes >> strip_tac >>
  fs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base i s = Halt t` mp_tac >>
  with_opcode_clause (fn clauses =>
    simp (clauses @ [halt_state_def, set_returndata_def, AllCaseEqs()])) >>
  rpt strip_tac >> gvs[halt_state_def, set_returndata_def]
QED

Theorem raw_safe_rq_upto_clipped_oracle:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  vs.vs_outcomes = short ++ tail /\
  LENGTH short + LENGTH vs.vs_requests <= k /\
  EVERY wf_function C.ctx_functions /\
  C.ctx_entry = SOME entry /\ lookup_function entry C.ctx_functions = SOME f /\
  fn_entry_label f = SOME lbl /\ raw_safe_rq_upto D lo k C vs ==>
  ptr_discipline lo C (vs with vs_outcomes := short) /\
  taint_within D C (vs with vs_outcomes := short) /\
  mem_inv raw_mem_ok C (vs with vs_outcomes := short) /\
  mem_inv dload_offset_ok C (vs with vs_outcomes := short) /\
  mem_inv (\ctx fn i s. inst_dload_in_section i s) C (vs with vs_outcomes := short)
Proof
  strip_tac >> fs[raw_safe_rq_upto_def] >> rpt conj_tac
  >- (fs[ptr_discipline_def, ptr_discipline_rq_upto_def] >>
      qexists_tac `P` >> simp[] >> rpt gen_tac >> strip_tac >>
      drule_all frame_reachable_clipped_oracle >> strip_tac >>
      qpat_x_assum `!stk PG G tn fn i s. frame_reachable vs C stk PG G tn fn i s /\ request_cut k s ==> _` drule >>
      simp[request_cut_safety_outcome_update])
  >- (fs[taint_within_def, taint_within_rq_upto_def] >> conj_tac
      >- (rpt strip_tac >>
          drule_all frame_reachable_clipped_oracle >> strip_tac >>
          rename1 `step_inst fuel C i s = OK t` >>
          mp_tac (Q.INST [`inst` |-> `i`, `r` |-> `OK t`]
            step_inst_noninvoke_success_outcome_suffix) >>
          simp[exec_result_map_def] >> strip_tac >>
          qpat_x_assum `!stk PG G tn fn i s fuel t.
            frame_reachable vs C stk PG G tn fn i s /\ request_cut k s /\
            active_inst fn i s /\ i.inst_opcode <> INVOKE /\
            step_inst fuel C i s = OK t /\ _ ==> _` drule >>
          simp[request_cut_safety_outcome_update] >>
          disch_then (qspecl_then [`fuel`, `t with vs_outcomes := t.vs_outcomes ++ tail`] mp_tac) >>
          simp[])
      >> simp[final_taint_def] >> rpt strip_tac >> gvs[] >>
      drule_all frame_reachable_clipped_oracle >> strip_tac >>
      rename1 `step_inst fuel C i s = Halt t` >>
      mp_tac (Q.INST [`inst` |-> `i`, `r` |-> `Halt t`]
        step_inst_noninvoke_success_outcome_suffix) >>
      simp[exec_result_map_def] >> strip_tac >>
      `t.vs_outcomes = s.vs_outcomes` by
        (irule noninvoke_halt_oracle >> metis_tac[]) >>
      qpat_x_assum `!stk PG G tn fn i s fuel t.
        frame_reachable vs C stk PG G tn fn i s /\ request_cut k s /\
        active_inst fn i s /\ i.inst_opcode <> INVOKE /\
        step_inst fuel C i s = Halt t ==> _` drule >>
      simp[request_cut_safety_outcome_update] >>
      disch_then (qspecl_then [`fuel`, `t with vs_outcomes := t.vs_outcomes ++ tail`] mp_tac) >>
      simp[step_taint_outcome_suffix])
  >> simp[mem_inv_raw_reachable] >> rpt strip_tac >>
  drule_all raw_reachable_clipped_oracle >> strip_tac >>
  qpat_x_assum `!fn i s. raw_reachable vs C fn i s /\ request_cut k s ==> _` drule >>
  simp[request_cut_safety_outcome_update]
QED

Theorem request_cut_clipped_pre_walk:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  vs.vs_outcomes = short ++ tail /\
  LENGTH short + LENGTH vs.vs_requests <= k /\
  EVERY wf_function C.ctx_functions /\
  C.ctx_entry = SOME entry /\ lookup_function entry C.ctx_functions = SOME f /\
  fn_entry_label f = SOME lbl /\ raw_safe_rq_upto D lo k C vs /\
  o1_safe_upto Ds reserve n C vs /\ fixed_region_reserved lo C /\
  EVERY (\fn. fn_defs_reach_uses fn /\
              EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn)) C.ctx_functions ==>
  o1_pre_walk_inv D C (vs with vs_outcomes := short) /\
  mem_inv (\ctx fn i s. inst_dload_in_section i s /\
    s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
    C (vs with vs_outcomes := short)
Proof
  strip_tac >> drule_all raw_safe_rq_upto_clipped_oracle >> strip_tac >>
  fs[o1_safe_upto_def, o1_ptr_safe_upto_def] >>
  `mem_inv dload_headroom_ok C (vs with vs_outcomes := short)` by
    (fs[mem_inv_raw_reachable] >> rpt strip_tac >>
     drule_all raw_reachable_clipped_oracle >> strip_tac >>
     qpat_x_assum `!fn i s. raw_reachable vs C fn i s ==> dload_headroom_ok C fn i s`
       drule >> simp[dload_headroom_ok_def]) >>
  conj_tac
  >- (simp[o1_pre_walk_inv_def, o1_src_inv_def] >> metis_tac[]) >>
  fs[mem_inv_raw_reachable] >>
  rpt strip_tac >> drule raw_reachable_code_data >> simp[] >> metis_tac[]
QED

Theorem request_cut_source_pre_walk:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  o1_source_unit_ok unit /\ unit_defs_reach_uses unit /\
  o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  lookup_function entry unit.cu_context.ctx_functions = SOME f /\
  fn_entry_label f = SOME lbl /\
  raw_safe_rq_upto D 0 k unit.cu_context vs /\
  o1_safe_upto Ds reserve n unit.cu_context vs /\
  raw_reachable vs unit.cu_context fn i s /\ LENGTH s.vs_requests = k /\
  clipped = (vs with vs_outcomes := TAKE (k - LENGTH vs.vs_requests) vs.vs_outcomes) ==>
  o1_pre_walk_inv D unit.cu_context clipped /\
  mem_inv (\ctx fn i s. inst_dload_in_section i s /\
      s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
    unit.cu_context clipped
Proof
  strip_tac >> drule_all raw_reachable_recorded_oracle_drop >> strip_tac >>
  `EVERY wf_function unit.cu_context.ctx_functions` by
    fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `EVERY (\fn. fn_defs_reach_uses fn /\
    EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn)) unit.cu_context.ctx_functions` by
    (fs[o1_source_unit_ok_def, unit_defs_reach_uses_def, raw_opcode_ok_def, EVERY_MEM] >>
     metis_tac[]) >>
  mp_tac (Q.INST [`C` |-> `unit.cu_context`, `lo` |-> `0`,
    `short` |-> `TAKE (k - LENGTH vs.vs_requests) vs.vs_outcomes`,
    `tail` |-> `DROP (k - LENGTH vs.vs_requests) vs.vs_outcomes`]
    request_cut_clipped_pre_walk) >>
  simp[TAKE_DROP, fixed_region_reserved_def] >>
  `LENGTH (TAKE (k - LENGTH vs.vs_requests) vs.vs_outcomes) +
     LENGTH vs.vs_requests <= k` by
    (simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> decide_tac) >>
  metis_tac[]
QED
