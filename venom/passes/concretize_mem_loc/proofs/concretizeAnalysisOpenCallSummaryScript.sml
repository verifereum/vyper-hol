Theory concretizeAnalysisOpenCallSummary
Ancestors venomWfProps concretizeAnalysisCallProjection concretizeAnalysisSummaryStage
  concretizeAnalysisSummaryCoverage concretizeAnalysisOwnership concretizeMemLocDefs
  frameJointTrace frameJointTransition frameActivationCache o1PassContract
  venomPassDispatcher venomPassSchedule venomWf venomInst contextCodegenRel
  removeUnusedSsaProofs venomExecSemantics venomExecProps relation list

Theorem joint_open_call_observed_summary:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ c < j /\ j <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 /\
  joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
  EL j (q0::qs) = JointConfig stk PG G tn owner inst s oms om hs h /\
  (!k. c < k /\ k <= j ==> LENGTH stk0 < activation_depth (EL k (q0::qs))) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  static_alloca_items owner = SOME items /\ MEM (a,sz) items /\
  o1_walk_view rpolicy 2 C' caller observed ==>
  ?root name ops g p.
    invoke.inst_opcode = INVOKE /\ invoke.inst_operands = Label name :: ops /\
    lookup_function name C.ctx_functions = SOME root /\
    source_call C caller root /\ RTC (source_call C) root owner /\
    lookup_function root.fn_name observed.cu_context.ctx_functions = SOME g /\
    MEM (a,p,sz) g.fn_mems_used
Proof
  strip_tac >> drule_all joint_open_call_path_at >> strip_tac >>
  `MEM owner C.ctx_functions` by
    (qpat_x_assum `RTC _ root owner` mp_tac >>
     once_rewrite_tac[RTC_CASES2] >> gvs[source_call_def] >> metis_tac[]) >>
  drule_all concretize_observed_descendant_item_coverage >> strip_tac >>
  metis_tac[]
QED

Theorem joint_open_call_imported_key:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ c < j /\ j <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 /\
  joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
  EL j (q0::qs) = JointConfig stk PG G tn owner inst s oms om hs h /\
  (!k. c < k /\ k <= j ==> LENGTH stk0 < activation_depth (EL k (q0::qs))) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  static_alloca_items owner = SOME items /\ MEM (a,sz) items /\
  o1_walk_view rpolicy 2 C' caller observed ==>
  ?p sz'. MEM (a,p,sz') (imported_mems_used observed.cu_context caller)
Proof
  strip_tac >> drule_all joint_open_call_observed_summary >> strip_tac >>
  `root.fn_name = name` by
    (qpat_x_assum `lookup_function name _ = _` mp_tac >>
     simp[lookup_function_def] >> strip_tac >> drule FIND_P >> simp[]) >>
  `active_inst caller invoke s0` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_call_iff] >> metis_tac[]) >>
  `MEM invoke (fn_insts caller)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  `MEM (a,p,sz) (callee_mems_used observed.cu_context name)` by
    gvs[callee_mems_used_def] >>
  drule_all invoke_import_key_coverage >> simp[]
QED
