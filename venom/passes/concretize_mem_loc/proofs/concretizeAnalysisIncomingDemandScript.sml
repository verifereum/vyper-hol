Theory concretizeAnalysisIncomingDemand
Ancestors
  concretizeAnalysisTemporalDemand frameDemandTaint frameJointRevert frameJointTaint
  frameJointTrace frameJointDemand frameJointTransition frameActivationCache unitTransformDefs
  frameIncomingArgument frameOpenCall concretizeAnalysisScanCoverage concretizeAnalysisWriteSafety
  concretizeAnalysisLivenessPaths concretizeAnalysisLivenessTransfer
  frameOriginHistory frameOriginReachable frameAllocationOwnership
  o1PassContract ptrDiscipline concretizeMemLocDefs basePtrDefs cfgAnalysis
  venomExecSemantics contextCodegenRel venomInst venomWf finite_map list pred_set

(* The ML interface is instruction-local; semantic ancestry is not unfolded here. *)
Theorem active_invoke_argument_generators:
  wf_function fn /\ all_reachable fn /\ active_inst fn inst s /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  MEM (Var u) ops /\ Allocation aid IN bp_bases bpr u /\
  (!name. OL alloc_to (mems name)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) ==>
  MEM (Allocation aid) (ml_lookup la (s.vs_current_bb,s.vs_inst_idx)) /\
  MEM (Allocation aid) (ml_lookup us (s.vs_current_bb,s.vs_inst_idx))
Proof
  strip_tac >>
  `inst.inst_operands = Label nm :: ops` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  `ml_operand_gen (Allocation aid) bpr inst` by
    (simp[ml_operand_gen_def] >> qexists_tac `Var u` >>
     gvs[bp_bases_find_base_allocas]) >>
  gvs[active_inst_def] >> metis_tac[ml_production_invoke_generators]
QED

Theorem joint_incoming_production_argument:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  o1_ctx_shape ctx /\ ptr_discipline lo ctx vs0 /\
  EVERY ssa_form ctx.ctx_functions /\ EVERY all_reachable ctx.ctx_functions /\
  ~ctx_has_dalloca ctx /\ FLOOKUP om v = SOME (OriginParameter p,site) ==>
  ?k aid u nm ops.
    k < LENGTH stk /\ k < LENGTH oms /\
    (EL k stk).cf_inst.inst_opcode = INVOKE /\
    decode_invoke (EL k stk).cf_inst = SOME (nm,ops) /\
    active_inst (EL k stk).cf_fn (EL k stk).cf_inst (EL k stk).cf_state /\
    MEM (Var u) ops /\ FLOOKUP (EL k oms) u = SOME (OriginLocal aid,site) /\
    FLOOKUP (EL k stk).cf_state.vs_allocas aid = SOME site /\
    Allocation aid IN bp_bases
      (bp_analyze_fuel (concretize_memloc_fuel (EL k stk).cf_fn)
        (cfg_analyze (EL k stk).cf_fn) (EL k stk).cf_fn) u /\
    (!mems sizes pallocas la us.
      (!name. OL alloc_to (mems name)) /\ OL alloc_to pallocas /\
      ml_iterate_fuel (concretize_memloc_fuel (EL k stk).cf_fn)
        (bp_analyze_fuel (concretize_memloc_fuel (EL k stk).cf_fn)
          (cfg_analyze (EL k stk).cf_fn) (EL k stk).cf_fn)
        mems sizes pallocas (cfg_analyze (EL k stk).cf_fn) (EL k stk).cf_fn
        FEMPTY FEMPTY = (la,us) ==>
      MEM (Allocation aid) (ml_lookup la
        ((EL k stk).cf_state.vs_current_bb,(EL k stk).cf_state.vs_inst_idx)) /\
      MEM (Allocation aid) (ml_lookup us
        ((EL k stk).cf_state.vs_current_bb,(EL k stk).cf_state.vs_inst_idx)))
Proof
  strip_tac >> drule_all joint_incoming_argument >> strip_tac >>
  drule joint_origin_history_erasure >> strip_tac >>
  `MEM (EL k stk).cf_fn ctx.ctx_functions` by
    (drule origin_frame_erasure >> strip_tac >>
     drule_all frame_allocation_ownership >> simp[EVERY_EL] >> metis_tac[]) >>
  `EVERY wf_function ctx.ctx_functions` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `wf_function (EL k stk).cf_fn /\ all_reachable (EL k stk).cf_fn /\
   ssa_form (EL k stk).cf_fn` by metis_tac[EVERY_MEM] >>
  `Allocation aid IN bp_bases
      (bp_analyze_fuel (concretize_memloc_fuel (EL k stk).cf_fn)
        (cfg_analyze (EL k stk).cf_fn) (EL k stk).cf_fn) u` by
    (fs[ptr_discipline_def] >>
     `EVERY (fn_ptr_ok P) ctx.ctx_functions` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     metis_tac[origin_frame_saved_production_coverage]) >>
  qexistsl_tac [`k`,`aid`,`u`,`nm`,`ops`] >> simp[] >>
  metis_tac[active_invoke_argument_generators]
QED

Theorem concretize_untainted_incoming_read_liveat:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  EL j (q0::qs) = JointConfig stk PG G tn current inst s oms om hs h /\
  FLOOKUP om v = SOME (OriginParameter param,(b,sz)) /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  b <= byte /\ byte < b + sz /\ lo <= byte /\ byte IN joint_reads (EL j (q0::qs)) /\
  byte NOTIN joint_mem_taint (EL j (q0::qs)) /\ ~in_revert_forward current s /\
  (!t. n <= t /\ t < j ==> byte NOTIN joint_writes (EL t (q0::qs)) (EL t es)) ==>
  ?k aid owner d.
    k < LENGTH stk /\ owner = (EL k stk).cf_fn /\ d = LENGTH stk - SUC k /\
    FLOOKUP (EL k stk).cf_state.vs_allocas aid = SOME (b,sz) /\
    activation_cache (EL n (q0::qs)) d owner aid (b,sz) /\
    (!p observed bp sizes mems pallocas la us.
      activation_location (EL n (q0::qs)) d owner p /\
      o1_walk_view rpolicy 2 C' owner observed /\
      bp = bp_analyze_fuel (concretize_memloc_fuel owner) (cfg_analyze owner) owner /\
      sizes = (\a. if context_alloca_size owner
        (imported_mems_used observed.cu_context owner) a = 0 then NONE
        else SOME (context_alloca_size owner (imported_mems_used observed.cu_context owner) a)) /\
      (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
      ml_iterate_fuel (concretize_memloc_fuel owner) bp mems sizes pallocas
        (cfg_analyze owner) owner FEMPTY FEMPTY = (la,us) ==>
      MEM (Allocation aid) (ml_lookup la p))
Proof
  strip_tac >>
  `joint_config_reachable vs0 C (JointConfig stk PG G tn current inst s oms om hs h)` by
    metis_tac[trace_config_at] >>
  `joint_origin_history vs0 C stk PG G tn current inst s oms om hs h` by
    gvs[joint_config_reachable_def] >>
  drule_all joint_incoming_production_argument >> strip_tac >>
  qabbrev_tac `d = LENGTH stk - SUC k` >>
  qabbrev_tac `owner = (EL k stk).cf_fn` >>
  `d < LENGTH stk /\ LENGTH stk - SUC d = k` by
    (simp[Abbr `d`] >> decide_tac) >>
  `activation_cache (EL j (q0::qs)) d owner aid (b,sz)` by
    gvs[activation_cache_def, Abbr `owner`] >>
  `vs0.vs_allocas = FEMPTY` by gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `!t. n <= t /\ t <= j ==>
    d <= activation_depth (EL t (q0::qs)) /\
    activation_cache (EL t (q0::qs)) d owner aid (b,sz)` by
    (rpt gen_tac >> strip_tac >> irule joint_untainted_demand_cache >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
     qexists_tac `byte` >> simp[] >> qexists_tac `n` >> simp[]) >>
  `!t. n <= t /\ t <= j ==> activation_nonrevert (EL t (q0::qs)) d` by
    (rpt strip_tac >>
     `joint_nonrevert (EL t (q0::qs))` by
       (irule joint_trace_nonrevert_read_at >>
        goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
        qexistsl_tac [`byte`,`j`] >> simp[joint_nonrevert_def]) >>
     Cases_on `EL t (q0::qs)` >>
     gvs[joint_nonrevert_def, activation_nonrevert_def]) >>
  `MEM owner C.ctx_functions` by
    (drule joint_origin_history_erasure >> strip_tac >>
     drule origin_frame_erasure >> strip_tac >>
     drule_all frame_allocation_ownership >> simp[EVERY_EL, Abbr `owner`] >> metis_tac[]) >>
  `wf_function owner /\ all_reachable owner` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  qexistsl_tac [`k`,`aid`,`owner`,`d`] >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[Abbr `owner`]) >>
  (conj_tac >- simp[Abbr `d`]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- (first_x_assum (qspec_then `n` mp_tac) >> simp[])) >>
  rpt gen_tac >> strip_tac >>
  `activation_location (EL j (q0::qs)) d owner
      ((EL k stk).cf_state.vs_current_bb,(EL k stk).cf_state.vs_inst_idx)` by
    gvs[activation_location_def, Abbr `owner`] >>
  `ml_read_gen (Allocation aid) bp mems (EL k stk).cf_inst` by
    (`ml_operand_gen (Allocation aid) bp (EL k stk).cf_inst` by
       (simp[ml_operand_gen_def] >> qexists_tac `Var u` >>
        gvs[decode_invoke_def, AllCaseEqs(), bp_bases_find_base_allocas, Abbr `owner`]) >>
     gvs[decode_invoke_def, AllCaseEqs()] >> simp[ml_read_gen_def]) >>
  `activation_guard (EL j (q0::qs)) d
      (\i. ~ptr_ml_can_kill (Allocation aid) bp sizes i)` by
    gvs[activation_guard_def] >>
  `activation_cache (EL n (q0::qs)) d owner aid (b,sz)` by
    (qpat_x_assum `!t. _ ==> _ /\ activation_cache _ _ _ _ _`
       (qspec_then `n` mp_tac) >> simp[]) >>
  irule concretize_cached_generator_liveat >>
  goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ml_read_gen _ _ _ _`)) >>
  goal_assum (drule_at (Pat `active_inst _ _ _`)) >>
  goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `o1_walk_view _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `callee_first _ _`)) >>
  goal_assum (drule_at (Pat `ptr_discipline _ _ _`)) >>
  qexistsl_tac [`byte`,`j`] >> gvs[]
QED

(* Incoming provenance selects the suspended owner, not the physical writer. *)
Theorem joint_incoming_used_generator:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  o1_ctx_shape ctx /\ ptr_discipline lo ctx vs0 /\
  EVERY ssa_form ctx.ctx_functions /\ EVERY all_reachable ctx.ctx_functions /\
  ~ctx_has_dalloca ctx /\ FLOOKUP om v = SOME (OriginParameter p,site) ==>
  ?k aid owner d.
    k < LENGTH stk /\ owner = (EL k stk).cf_fn /\ d = LENGTH stk - SUC k /\
    FLOOKUP (EL k stk).cf_state.vs_allocas aid = SOME site /\
    active_inst owner (EL k stk).cf_inst (EL k stk).cf_state /\
    (EL k stk).cf_inst.inst_opcode = INVOKE /\
    ml_used_gen (Allocation aid)
      (bp_analyze_fuel (concretize_memloc_fuel owner) (cfg_analyze owner) owner)
      mems (EL k stk).cf_inst
Proof
  strip_tac >> drule_all joint_incoming_production_argument >> strip_tac >>
  qexistsl_tac [`k`,`aid`,`(EL k stk).cf_fn`,`LENGTH stk - SUC k`] >> simp[] >>
  `MEM (Var u) (EL k stk).cf_inst.inst_operands` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  simp[ml_used_gen_def, ml_operand_gen_def] >>
  disj1_tac >> qexists_tac `Var u` >> gvs[bp_bases_find_base_allocas]
QED

(* Only equal function/instruction/state is transported from the open call. *)
Theorem joint_saved_used_generator_occurrence:
  joint_trace vs0 ctx q0 es qs q /\ n <= m /\ m <= LENGTH es /\
  EL m (q0::qs) = JointConfig stk PG G tn current inst s oms om hs h /\
  k < LENGTH stk /\ d = LENGTH stk - SUC k /\ owner = (EL k stk).cf_fn /\
  active_inst owner (EL k stk).cf_inst (EL k stk).cf_state /\
  ml_used_gen (Allocation aid) bp mems (EL k stk).cf_inst /\
  activation_depth (EL n (q0::qs)) = d /\
  (!t. n <= t /\ t <= m ==> d <= activation_depth (EL t (q0::qs))) ==>
  ?c stk0 PG0 G0 tn0 invoke sc oms0 om0 hs0 h0.
    n <= c /\ c < m /\ LENGTH stk0 = d /\
    EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 owner invoke sc oms0 om0 hs0 h0 /\
    active_inst owner invoke sc /\ invoke.inst_opcode = INVOKE /\
    ml_used_gen (Allocation aid) bp mems invoke
Proof
  strip_tac >>
  `d < activation_depth (EL m (q0::qs)) /\ LENGTH stk - SUC d = k` by
    (simp[activation_depth_def] >> decide_tac) >>
  drule_all joint_open_call_saved >> strip_tac >> gvs[] >>
  `LENGTH stk - SUC (LENGTH stk - SUC k) = k` by decide_tac >>
  fs[] >> qexists_tac `c` >>
  goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED
