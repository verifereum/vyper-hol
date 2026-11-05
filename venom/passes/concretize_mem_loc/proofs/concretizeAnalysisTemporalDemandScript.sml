Theory concretizeAnalysisTemporalDemand
Ancestors
  concretizeAnalysisReadOrigin concretizeAnalysisSafeKill concretizePtrReadCoverage
  concretizeAnalysisScanCoverage concretizeAnalysisWriteSafety frameAllocationOwnership
  concretizeAnalysisLivenessTransfer frameHistoryDefinitions
  concretizeMemLocDefs memLocDefs basePtrDefs venomInst frameJointDemand
  frameOriginHistory frameOriginReachable o1PassContract finite_map pred_set arithmetic
  frameDemandTaint frameJointTaint frameJointRevert frameOriginCacheReach unitTransformDefs
  concretizeAnalysisLivenessPaths frameJointTrace frameJointTransition frameActivationCache frameCfgBoundary
  venomInstProps frameHistoryCfg cfgAnalysisProps frameHistoryInstructions contextCodegenRel ptrDiscipline venomExecSemantics venomExecProofs venomWf relation list

(* The indexed analysis includes the PHIs evaluated by block entry. *)
Theorem indexed_block_prefix[local]:
  MEM bb fn.fn_blocks /\ j < LENGTH bb.bb_instructions /\
  (!k. i < k /\ k <= j ==> guard (EL k bb.bb_instructions)) /\ i <= j ==>
  ml_indexed_path fn guard (bb.bb_label,i) (bb.bb_label,j)
Proof
  qid_spec_tac `i` >> Induct_on `j`
  >- (rpt strip_tac >> `i = 0` by decide_tac >>
      simp[ml_indexed_path_def]) >>
  rpt strip_tac >> Cases_on `i = SUC j`
  >- simp[ml_indexed_path_def] >>
  `i <= j /\ j < LENGTH bb.bb_instructions` by decide_tac >>
  `ml_indexed_path fn guard (bb.bb_label,i) (bb.bb_label,j)` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `ml_indexed_step fn guard (bb.bb_label,j) (bb.bb_label,SUC j)` by
    (simp[ml_indexed_step_def] >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum irule >> decide_tac) >>
  metis_tac[ml_indexed_path_def, RTC_SINGLE, RTC_TRANSITIVE, transitive_def]
QED

Theorem indexed_active_successor[local]:
  wf_function fn /\ active_inst fn inst s /\ active_inst fn inst' t /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = SUC s.vs_inst_idx /\
  guard inst' /\ p = (s.vs_current_bb,s.vs_inst_idx) /\
  q = (t.vs_current_bb,t.vs_inst_idx) ==>
  ml_indexed_step fn guard p q
Proof
  simp[active_inst_def] >> rpt strip_tac >>
  `bb = bb'` by metis_tac[same_label_same_block] >> gvs[] >>
  simp[ml_indexed_step_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem indexed_cfg_entry[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\ MEM dst fn.fn_blocks /\
  bb.bb_instructions <> [] /\ j < LENGTH dst.bb_instructions /\
  fn_cfg_edge fn bb.bb_label dst.bb_label /\
  (!k. 0 < k /\ k <= j ==> guard (EL k dst.bb_instructions)) ==>
  ml_indexed_path fn guard (bb.bb_label,PRE (LENGTH bb.bb_instructions))
    (dst.bb_label,j)
Proof
  strip_tac >>
  `MEM dst.bb_label (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
    (gvs[fn_cfg_edge_def] >>
     `bb = bb'` by metis_tac[same_label_same_block] >> gvs[] >>
     metis_tac[cfg_analyze_preserves_bb_succs]) >>
  `ml_indexed_step fn guard
     (bb.bb_label,PRE (LENGTH bb.bb_instructions)) (dst.bb_label,0)` by
    (rewrite_tac[ml_indexed_step_def] >> disj2_tac >>
     qexistsl_tac [`bb`,`dst`] >> simp[] >> Cases_on `dst.bb_instructions` >> gvs[]) >>
  `ml_indexed_path fn guard (dst.bb_label,0) (dst.bb_label,j)` by
    (irule indexed_block_prefix >> simp[] >> goal_assum (drule_at Any)) >>
  metis_tac[ml_indexed_path_def, RTC_SINGLE, RTC_TRANSITIVE, transitive_def]
QED

Theorem indexed_active_block[local]:
  wf_function fn /\ active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst s = OK post /\ ~post.vs_halted /\
  enters_block fn post t /\ active_inst fn inst' t /\
  (!bb k. MEM bb fn.fn_blocks /\ bb.bb_label = t.vs_current_bb /\
    0 < k /\ k <= t.vs_inst_idx ==> guard (EL k bb.bb_instructions)) ==>
  ml_indexed_path fn guard (s.vs_current_bb,s.vs_inst_idx)
    (t.vs_current_bb,t.vs_inst_idx)
Proof
  strip_tac >> drule_all active_terminator_cfg_transition >> strip_tac >>
  fs[active_inst_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[bb_well_formed_def] >>
  `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `ml_indexed_path fn guard (bb.bb_label,PRE (LENGTH bb.bb_instructions))
    (bb'.bb_label,t.vs_inst_idx)` suffices_by metis_tac[] >>
  irule indexed_cfg_entry >> simp[] >> metis_tac[]
QED

Definition activation_location_def:
  activation_location (JointConfig stk PG G tn current inst s oms om hs h) d fn p <=>
    (d = LENGTH stk /\ fn = current /\ active_inst fn inst s /\
      p = (s.vs_current_bb,s.vs_inst_idx)) \/
    (d < LENGTH stk /\
      fn = (EL (LENGTH stk - SUC d) stk).cf_fn /\
      active_inst fn (EL (LENGTH stk - SUC d) stk).cf_inst
        (EL (LENGTH stk - SUC d) stk).cf_state /\
      p = ((EL (LENGTH stk - SUC d) stk).cf_state.vs_current_bb,
           (EL (LENGTH stk - SUC d) stk).cf_state.vs_inst_idx))
End

Theorem phi_prefix_opcode[local]:
  !insts k. k < phi_prefix_length insts ==> (EL k insts).inst_opcode = PHI
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[] >>
  Cases_on `k` >> gvs[]
QED

Theorem indexed_block_phi_entry[local]:
  wf_function fn /\ active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst s = OK post /\ ~post.vs_halted /\
  enters_block fn post t /\ active_inst fn inst' t /\ guard inst' /\
  (!i. i.inst_opcode = PHI ==> guard i) ==>
  ml_indexed_path fn guard (s.vs_current_bb,s.vs_inst_idx)
    (t.vs_current_bb,t.vs_inst_idx)
Proof
  strip_tac >> irule indexed_active_block >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> drule enters_block_entry_index >> strip_tac >>
  qpat_x_assum `active_inst fn inst s` kall_tac >>
  fs[active_inst_def] >>
  `!b1 b2. MEM b1 fn.fn_blocks /\ MEM b2 fn.fn_blocks /\
    b1.bb_label = t.vs_current_bb /\ b2.bb_label = t.vs_current_bb ==> b1 = b2`
    by metis_tac[same_label_same_block] >>
  `bb = bb'` by metis_tac[] >>
  `inst' = EL t.vs_inst_idx bb.bb_instructions` by metis_tac[] >>
  Cases_on `k = t.vs_inst_idx`
  >- metis_tac[] >>
  `k < phi_prefix_length bb.bb_instructions` by gvs[] >>
  metis_tac[phi_prefix_opcode]) >> metis_tac[]
QED

Definition activation_guard_def:
  activation_guard (JointConfig stk PG G tn current inst s oms om hs h) d guard <=>
    (d = LENGTH stk ==> guard inst)
End

Theorem joint_activation_location_step[local]:
  !ctx q ev q'. joint_transition ctx q ev q' ==>
  !d fn p guard. wf_function fn /\ activation_location q d fn p /\
    d <= activation_depth q' /\ activation_guard q' d guard /\
    (!inst. inst.inst_opcode = PHI ==> guard inst) ==>
    ?p'. activation_location q' d fn p' /\ ml_indexed_path fn guard p p'
Proof
  ho_match_mp_tac joint_transition_ind >> rpt conj_tac
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume joint_activation_location_step[next]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  fs[activation_location_def, activation_depth_def, activation_guard_def]
  >- (gvs[] >>
      `s'.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_control_flow] >>
      rewrite_tac[ml_indexed_path_def] >> irule RTC_SINGLE >>
      irule indexed_active_successor >> simp[] >>
      qexistsl_tac [`inst`,`inst'`,`s`,`s' with vs_inst_idx := SUC s.vs_inst_idx`] >>
      simp[]) >>
  simp[ml_indexed_path_def]
QED

Resume joint_activation_location_step[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  fs[activation_location_def, activation_depth_def, activation_guard_def]
  >- (gvs[] >> irule indexed_block_phi_entry >> metis_tac[]) >>
  simp[ml_indexed_path_def]
QED

Resume joint_activation_location_step[call]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  fs[activation_location_def, activation_depth_def, activation_guard_def]
  >- simp[ml_indexed_path_def] >>
  `LENGTH stk - d = SUC (LENGTH stk - SUC d)` by decide_tac >>
  gvs[ml_indexed_path_def]
QED

Resume joint_activation_location_step[ret]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  fs[activation_location_def, activation_depth_def, activation_guard_def] >>
  Cases_on `d = LENGTH stk`
  >- (gvs[] >> drule return_binding_current_bb >> strip_tac >>
      rewrite_tac[ml_indexed_path_def] >> irule RTC_SINGLE >>
      irule indexed_active_successor >> simp[] >>
      qexistsl_tac [`f.cf_inst`,`inst'`,`f.cf_state`,
        `s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx`] >> simp[]) >>
  `d < LENGTH stk /\ LENGTH stk - d = SUC (LENGTH stk - SUC d)` by decide_tac >>
  gvs[ml_indexed_path_def]
QED

Finalise joint_activation_location_step

Theorem joint_activation_location_interval:
  !j n. joint_trace vs0 ctx q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  wf_function fn /\ activation_location (EL n (q0::qs)) d fn p /\
  (!k. n <= k /\ k <= j ==> d <= activation_depth (EL k (q0::qs))) /\
  (!k. n < k /\ k <= j ==> activation_guard (EL k (q0::qs)) d guard) /\
  (!inst. inst.inst_opcode = PHI ==> guard inst) ==>
  ?p'. activation_location (EL j (q0::qs)) d fn p' /\ ml_indexed_path fn guard p p'
Proof
  Induct
  >- (rpt strip_tac >> `n = 0` by decide_tac >> gvs[] >>
      goal_assum (drule_at Any) >> simp[ml_indexed_path_def]) >>
  rpt strip_tac >> Cases_on `n = SUC j`
  >- (gvs[] >> goal_assum (drule_at Any) >> simp[ml_indexed_path_def]) >>
  `n <= j /\ j < LENGTH es` by decide_tac >>
  `?p1. activation_location (EL j (q0::qs)) d fn p1 /\
    ml_indexed_path fn guard p p1` by
    (first_x_assum irule >> simp[] >> qexists_tac `n` >> simp[] >>
     rpt conj_tac >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `joint_transition ctx (EL j (q0::qs)) (EL j es) (EL (SUC j) (q0::qs))` by
    metis_tac[joint_trace_edge_at] >>
  drule joint_activation_location_step >>
  disch_then (qspecl_then [`d`,`fn`,`p1`,`guard`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac >> first_x_assum irule >> decide_tac) >>
  strip_tac >> goal_assum (drule_at Any) >>
  metis_tac[ml_indexed_path_def, RTC_TRANSITIVE, transitive_def]
QED

Theorem joint_activation_current_path:
  joint_trace vs0 ctx q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  wf_function fn /\ activation_location (EL n (q0::qs)) d fn p /\
  (!k. n <= k /\ k <= j ==> d <= activation_depth (EL k (q0::qs))) /\
  (!k. n < k /\ k <= j ==> activation_guard (EL k (q0::qs)) d guard) /\
  (!inst. inst.inst_opcode = PHI ==> guard inst) /\
  EL j (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\ LENGTH stk = d ==>
  ml_indexed_path fn guard p (s.vs_current_bb,s.vs_inst_idx)
Proof
  strip_tac >> drule_all joint_activation_location_interval >> strip_tac >>
  gvs[activation_location_def]
QED

Theorem joint_activation_used_past_generator:
  joint_trace vs0 ctx q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  EL n (q0::qs) = JointConfig stk0 PG0 G0 tn0 fn inst0 s0 oms0 om0 hs0 h0 /\
  active_inst fn inst0 s0 /\ ml_used_gen a bp mems inst0 /\ LENGTH stk0 = d /\
  (!k. n <= k /\ k <= j ==> d <= activation_depth (EL k (q0::qs))) /\
  activation_location (EL j (q0::qs)) d fn p ==>
  MEM a (ml_lookup us p)
Proof
  strip_tac >>
  `activation_location (EL n (q0::qs)) d fn (s0.vs_current_bb,s0.vs_inst_idx)` by
    gvs[activation_location_def] >>
  `!k. activation_guard (EL k (q0::qs)) d (\inst. T)` by
    (gen_tac >> Cases_on `EL k (q0::qs)` >> simp[activation_guard_def]) >>
  `ml_indexed_path fn (\inst. T) (s0.vs_current_bb,s0.vs_inst_idx) p` by
    (`?p'. activation_location (EL j (q0::qs)) d fn p' /\
        ml_indexed_path fn (\inst. T) (s0.vs_current_bb,s0.vs_inst_idx) p'` by
       (irule joint_activation_location_interval >> simp[] >>
        conj_tac >- (qexists_tac `n` >> simp[]) >>
        goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >> simp[]) >>
     Cases_on `EL j (q0::qs)` >> gvs[activation_location_def]) >>
  fs[active_inst_def] >>
  irule ml_production_used_past_generator >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem write_ops_operand:
  mem_write_ops inst = SOME ops ==>
  MEM ops.iao_ofst inst.inst_operands /\ inst.inst_opcode <> PHI /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode
Proof
  Cases_on `inst.inst_opcode` >> simp[mem_write_ops_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), is_terminator_def]
QED

Theorem kill_has_variable_write[local]:
  ptr_ml_can_kill a bp sizes inst ==>
  ?ops v. mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
    MEM (Var v) inst.inst_operands /\ inst.inst_opcode <> PHI /\
    inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode
Proof
  simp[ptr_ml_can_kill_def, inst_write_size_def, inst_write_op_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `mem_write_ops inst = SOME ops` >>
  Cases_on `ops.iao_ofst` >>
  gvs[find_base_allocas_opt_def, find_base_allocas_def] >>
  drule write_ops_operand >> strip_tac >> metis_tac[]
QED

Theorem surviving_write_step[local]:
  joint_transition ctx (JointConfig stk PG G tn fn inst s oms om hs h) ev q' /\
  LENGTH stk <= activation_depth q' /\ mem_write_ops inst = SOME ops ==>
  ?fuel post. ev = SOME (OriginOrdinary fuel post) /\ step_inst fuel ctx inst s = OK post /\
    joint_writes (JointConfig stk PG G tn fn inst s oms om hs h) ev =
      range_bytes (step_writes inst s post)
Proof
  strip_tac >> drule write_ops_operand >> strip_tac >>
  gvs[Once joint_transition_cases, activation_depth_def, joint_writes_def] >> metis_tac[]
QED

Theorem concretize_joint_cached_no_kill[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h) /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ all_reachable fn /\
  o1_walk_view rpolicy 2 C' fn observed /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  sizes = (\a. if context_alloca_size fn
    (imported_mems_used observed.cu_context fn) a = 0 then NONE
    else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a)) /\
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h) ev q' /\
  LENGTH stk <= activation_depth q' /\ ~in_revert_forward fn s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ b <= byte /\ byte < b + sz /\
  byte NOTIN joint_writes (JointConfig stk PG G tn fn inst s oms om hs h) ev ==>
  ~ptr_ml_can_kill (Allocation aid) bp sizes inst
Proof
  strip_tac >> strip_tac >> drule kill_has_variable_write >> strip_tac >>
  drule_all surviving_write_step >> strip_tac >>
  fs[joint_config_reachable_def] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    metis_tac[joint_origin_history_erasure, origin_frame_erasure] >>
  fs[ptr_discipline_def] >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `access_ok lo G fn inst s` by metis_tac[] >>
  drule_all concretize_protected_cached_byte_no_kill >> simp[]
QED

Theorem trace_config_at:
  joint_trace vs0 C q0 es qs q /\ k <= LENGTH es ==>
  joint_config_reachable vs0 C (EL k (q0::qs))
Proof
  strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  drule joint_trace_prefix_reachable >> strip_tac >>
  Cases_on `k` >> gvs[EVERY_EL] >>
  rename1 `SUC i <= LENGTH qs` >> `i < LENGTH qs` by decide_tac >> metis_tac[]
QED

Definition activation_nonrevert_def:
  activation_nonrevert (JointConfig stk PG G tn fn inst s oms om hs h) d <=>
    (d = LENGTH stk ==> ~in_revert_forward fn s)
End

Theorem concretize_cached_interval_guard[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ all_reachable fn /\
  o1_walk_view rpolicy 2 C' fn observed /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  sizes = (\a. if context_alloca_size fn
    (imported_mems_used observed.cu_context fn) a = 0 then NONE
    else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a)) /\
  joint_trace vs0 C q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  activation_cache (EL n (q0::qs)) d fn aid (b,sz) /\ b <= byte /\ byte < b + sz /\
  (!k. n <= k /\ k <= j ==> d <= activation_depth (EL k (q0::qs))) /\
  (!k. n <= k /\ k <= j ==> activation_nonrevert (EL k (q0::qs)) d) /\
  (!k. n <= k /\ k < j ==> byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
  activation_guard (EL j (q0::qs)) d (\inst. ~ptr_ml_can_kill (Allocation aid) bp sizes inst) ==>
  !k. n < k /\ k <= j ==>
    activation_guard (EL k (q0::qs)) d (\inst. ~ptr_ml_can_kill (Allocation aid) bp sizes inst)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `k = j`
  >- gvs[] >>
  `n <= k /\ n <= SUC k /\ k < j /\ k < LENGTH es /\ SUC k <= j` by decide_tac >>
  `activation_cache (EL k (q0::qs)) d fn aid (b,sz)` by
    (irule joint_activation_cache_interval >> metis_tac[LESS_EQ_TRANS]) >>
  `joint_config_reachable vs0 C (EL k (q0::qs))` by
    metis_tac[trace_config_at, LESS_EQ_TRANS] >>
  `joint_transition C (EL k (q0::qs)) (EL k es) (EL (SUC k) (q0::qs))` by
    metis_tac[joint_trace_edge_at] >>
  `activation_nonrevert (EL k (q0::qs)) d /\
   d <= activation_depth (EL (SUC k) (q0::qs)) /\
   byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)` by metis_tac[] >>
  Cases_on `EL k (q0::qs)` >>
  gvs[activation_guard_def] >> strip_tac >>
  gvs[activation_cache_def, activation_nonrevert_def] >>
  qpat_assum `!k. _ ==> LENGTH _ <= activation_depth _`
    (qspec_then `SUC k` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (assume_tac o REWRITE_RULE [EL, TL]) >>
  irule concretize_joint_cached_no_kill >>
  goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `joint_transition _ _ _ _`)) >> simp[] >> metis_tac[]
QED

Theorem joint_local_read_base[local]:
  joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h) /\
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ EVERY ssa_form C.ctx_functions /\
  all_reachable fn /\ ~ctx_has_dalloca C /\ FLOOKUP om v = SOME (OriginLocal aid,site) /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v ==>
  MEM (Allocation aid) (find_base_allocas_opt
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) (inst_read_op inst))
Proof
  strip_tac >> fs[joint_config_reachable_def] >>
  drule joint_origin_history_erasure >> strip_tac >>
  drule origin_frame_erasure >> strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[frame_allocation_ownership] >>
  `EVERY wf_function C.ctx_functions /\ wf_function fn /\ ssa_form fn` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  fs[ptr_discipline_def] >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `Allocation aid IN bp_bases
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) v` by
    (irule origin_frame_current_production_coverage >> metis_tac[]) >>
  gvs[inst_read_op_def, find_base_allocas_opt_def, bp_bases_find_base_allocas]
QED

Theorem reachable_active[local]:
  joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h) ==>
  active_inst fn inst s
Proof
  simp[joint_config_reachable_def] >>
  metis_tac[joint_origin_history_projection, frame_history_active]
QED

Theorem activation_location_functional:
  activation_location q d fn p /\ activation_location q d fn p' ==> p = p'
Proof
  Cases_on `q` >> rw[activation_location_def] >> gvs[]
QED

Theorem concretize_cached_generator_liveat:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ wf_function fn /\ all_reachable fn /\
  o1_walk_view rpolicy 2 C' fn observed /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  sizes = (\a. if context_alloca_size fn
    (imported_mems_used observed.cu_context fn) a = 0 then NONE
    else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a)) /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  joint_trace vs0 C q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  activation_cache (EL n (q0::qs)) d fn aid (b,sz) /\
  activation_location (EL n (q0::qs)) d fn p /\
  activation_location (EL j (q0::qs)) d fn (s.vs_current_bb,s.vs_inst_idx) /\
  active_inst fn inst s /\ ml_read_gen (Allocation aid) bp mems inst /\
  b <= byte /\ byte < b + sz /\
  (!k. n <= k /\ k <= j ==> d <= activation_depth (EL k (q0::qs))) /\
  (!k. n <= k /\ k <= j ==> activation_nonrevert (EL k (q0::qs)) d) /\
  (!k. n <= k /\ k < j ==> byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
  activation_guard (EL j (q0::qs)) d
    (\inst. ~ptr_ml_can_kill (Allocation aid) bp sizes inst) ==>
  MEM (Allocation aid) (ml_lookup la p)
Proof
  strip_tac >>
  `!k. n < k /\ k <= j ==> activation_guard (EL k (q0::qs)) d
     (\inst. ~ptr_ml_can_kill (Allocation aid) bp sizes inst)` by
    (rpt strip_tac >> irule concretize_cached_interval_guard >>
     goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `activation_guard _ _ _`)) >> simp[] >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >> simp[] >> metis_tac[]) >>
  `!i. i.inst_opcode = PHI ==> ~ptr_ml_can_kill (Allocation aid) bp sizes i` by
    metis_tac[kill_has_variable_write] >>
  `ml_indexed_path fn (\inst. ~ptr_ml_can_kill (Allocation aid) bp sizes inst)
      p (s.vs_current_bb,s.vs_inst_idx)` by
    (`?p'. activation_location (EL j (q0::qs)) d fn p' /\
        ml_indexed_path fn (\inst. ~ptr_ml_can_kill (Allocation aid) bp sizes inst) p p'` by
       (irule joint_activation_location_interval >> simp[] >>
        conj_tac >- (qexists_tac `n` >> gvs[]) >> metis_tac[]) >>
     metis_tac[activation_location_functional]) >>
  fs[active_inst_def] >> irule ml_production_liveat_future_generator >>
  goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`bb`,`s.vs_inst_idx`] >> gvs[]
QED

Theorem concretize_cached_read_liveat:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  sizes = (\a. if context_alloca_size fn
    (imported_mems_used observed.cu_context fn) a = 0 then NONE
    else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a)) /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  joint_trace vs0 C q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  activation_location (EL n (q0::qs)) d fn p /\
  activation_cache (EL n (q0::qs)) d fn aid (b,sz) /\
  EL j (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\ LENGTH stk = d /\
  FLOOKUP om v = SOME (OriginLocal aid,(b,sz)) /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  b <= byte /\ byte < b + sz /\ byte IN joint_reads (EL j (q0::qs)) /\ lo <= byte /\
  (!k. n <= k /\ k <= j ==> d <= activation_depth (EL k (q0::qs))) /\
  (!k. n <= k /\ k <= j ==> activation_nonrevert (EL k (q0::qs)) d) /\
  (!k. n <= k /\ k < j ==> byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) ==>
  MEM (Allocation aid) (ml_lookup la p)
Proof
  strip_tac >>
  `joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h)` by
    metis_tac[trace_config_at] >>
  `joint_origin_history vs0 C stk PG G tn fn inst s oms om hs h` by
    gvs[joint_config_reachable_def] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    metis_tac[joint_origin_history_erasure, origin_frame_erasure] >>
  `MEM fn C.ctx_functions` by metis_tac[frame_allocation_ownership] >>
  `wf_function fn /\ all_reachable fn` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `MEM (Allocation aid) (find_base_allocas_opt bp (inst_read_op inst))` by
    (gvs[] >> irule joint_local_read_base >> metis_tac[]) >>
  `~ptr_ml_can_kill (Allocation aid) bp sizes inst` by
    simp[ptr_ml_can_kill_def] >>
  `activation_guard (EL j (q0::qs)) d
     (\inst. ~ptr_ml_can_kill (Allocation aid) bp sizes inst)` by
    gvs[activation_guard_def] >>

  `active_inst fn inst s` by
    metis_tac[joint_origin_history_projection, frame_history_active] >>
  `activation_location (EL j (q0::qs)) d fn (s.vs_current_bb,s.vs_inst_idx)` by
    gvs[activation_location_def] >>
  irule concretize_cached_generator_liveat >>
  goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `active_inst fn inst s`)) >>
  qexists_tac `byte` >> gvs[ml_read_gen_def] >>
  qexistsl_tac [`j`,`lo`,`names`,`observed`] >> gvs[]
QED

Theorem concretize_untainted_local_read_liveat_at_location:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  sizes = (\a. if context_alloca_size fn
    (imported_mems_used observed.cu_context fn) a = 0 then NONE
    else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a)) /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  joint_trace vs0 C q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  activation_location (EL n (q0::qs)) d fn p /\
  EL j (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\ LENGTH stk = d /\
  FLOOKUP om v = SOME (OriginLocal aid,(b,sz)) /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  b <= byte /\ byte < b + sz /\ byte IN joint_reads (EL j (q0::qs)) /\ lo <= byte /\
  byte NOTIN joint_mem_taint (EL j (q0::qs)) /\ ~in_revert_forward fn s /\
  (!k. n <= k /\ k < j ==> byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) ==>
  MEM (Allocation aid) (ml_lookup la p)
Proof
  strip_tac >>
  `joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h)` by
    metis_tac[trace_config_at] >>
  `FLOOKUP s.vs_allocas aid = SOME (b,sz)` by
    (gvs[joint_config_reachable_def] >>
     drule joint_origin_history_erasure >> strip_tac >>
     metis_tac[origin_frame_current_cache]) >>
  `activation_cache (EL j (q0::qs)) d fn aid (b,sz)` by
    gvs[activation_cache_def] >>
  `vs0.vs_allocas = FEMPTY` by gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `!k. n <= k /\ k <= j ==>
    d <= activation_depth (EL k (q0::qs)) /\
    activation_cache (EL k (q0::qs)) d fn aid (b,sz)` by
    (rpt gen_tac >> strip_tac >> irule joint_untainted_demand_cache >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
     qexists_tac `byte` >> simp[] >> qexists_tac `n` >> simp[]) >>
  `activation_cache (EL n (q0::qs)) d fn aid (b,sz)` by
    (first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  `!k. n <= k /\ k <= j ==> activation_nonrevert (EL k (q0::qs)) d` by
    (rpt strip_tac >>
     `joint_nonrevert (EL k (q0::qs))` by
       (irule joint_trace_nonrevert_read_at >>
        goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
        qexistsl_tac [`byte`,`j`] >> simp[joint_nonrevert_def]) >>
     Cases_on `EL k (q0::qs)` >>
     gvs[joint_nonrevert_def, activation_nonrevert_def]) >>
  irule concretize_cached_read_liveat >>
  goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `o1_walk_view _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `activation_location _ _ _ _`)) >>
  goal_assum (drule_at (Pat `EL j (_::_) = _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP om _ = _`)) >>
  goal_assum (drule_at (Pat `mem_read_ops _ = _`)) >>
  qexists_tac `byte` >> simp[] >> metis_tac[]
QED

Theorem concretize_untainted_local_read_liveat:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  sizes = (\a. if context_alloca_size fn
    (imported_mems_used observed.cu_context fn) a = 0 then NONE
    else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a)) /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  joint_trace vs0 C q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  EL n (q0::qs) = JointConfig stk0 PG0 G0 tn0 fn inst0 s0 oms0 om0 hs0 h0 /\
  LENGTH stk0 = d /\
  EL j (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\ LENGTH stk = d /\
  FLOOKUP om v = SOME (OriginLocal aid,(b,sz)) /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  b <= byte /\ byte < b + sz /\ byte IN joint_reads (EL j (q0::qs)) /\ lo <= byte /\
  byte NOTIN joint_mem_taint (EL j (q0::qs)) /\ ~in_revert_forward fn s /\
  (!k. n <= k /\ k < j ==> byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) ==>
  MEM (Allocation aid) (ml_lookup la (s0.vs_current_bb,s0.vs_inst_idx))
Proof
  strip_tac >>
  `active_inst fn inst0 s0` by
    (irule reachable_active >>
     `joint_config_reachable vs0 C (EL n (q0::qs))` by
       (irule trace_config_at >> metis_tac[LESS_EQ_TRANS]) >> metis_tac[]) >>
  irule concretize_untainted_local_read_liveat_at_location >>
  goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP om _ = _`)) >>
  goal_assum (drule_at (Pat `mem_read_ops _ = _`)) >>
  goal_assum (drule_at (Pat `EL j (_::_) = _`)) >>
  goal_assum (drule_at (Pat `o1_walk_view _ _ _ _ _`)) >>
  qexists_tac `byte` >> simp[] >>
  qexistsl_tac [`lo`,`n`,`names`] >> simp[activation_location_def]
QED
