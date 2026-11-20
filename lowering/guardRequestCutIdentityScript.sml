(* The identity-finalizer case of the request-cut companion: a lowered
   request step below the cut is the frame's next recorded call, and the
   head of the step's outcomes answers it in the call trace.

   TOP-LEVEL: codegen_request_cut_outcome_identity.
 *)
Theory guardRequestCutIdentity
Ancestors
  fnFrameRequestPrefix jointRequestCut e2eRequestCutDefs
  codegenRequestPrefix[qualified] e2eComposition[qualified] immutableCodeLayout[qualified] e2eProducers e2eEntry e2eDefs
  contextCodegenRel codegenEntryRel contextPlanLayoutProps unitMemInv
  staticAbortDefs ctxLookupAgree stepWriteFootprintBase dftGasFromListLookup
  frameRawProjection frameJointTrace frameJointTransition
  frameOriginReachable frameOriginHistory
  concretizePtrCoverageStaticMemReachability
  callTrace unitTransformDefs o1PipelineCorrect venomExecSemantics
  stackPlanGen vyperLoweringCorrect loweringShapeSource contextRawReachable
  venomWf list rich_list words arithmetic

(* A configuration of a trace that ends at a call step: it is
   raw-reachable, off the revert-forwarding and static-abort prefixes, and
   below the call's request cut. *)
Theorem request_cut_trace_config:
  EVERY wf_function ctx.ctx_functions /\
  joint_trace vs0 ctx q0 evs qs
    (JointConfig stk PG G tn fn inst t oms om hs h) /\
  active_inst fn inst t /\
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  j <= LENGTH evs /\
  EL j (q0::qs) = JointConfig stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1 ==>
  raw_reachable vs0 ctx fn1 inst1 s1 /\ ~in_revert_forward fn1 s1 /\
  ~in_static_abort_prefix fn1 s1 /\
  request_cut (LENGTH t.vs_requests) s1
Proof
  strip_tac >>
  `joint_config_reachable vs0 ctx
     (JointConfig stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1)` by
    metis_tac[joint_trace_reachable_at] >>
  drule_all joint_config_raw >> strip_tac >>
  `wf_function fn1` by metis_tac[raw_reachable_wf] >>
  `ALL_DISTINCT (fn_labels fn1)` by fs[wf_function_def] >>
  `~MEM inst.inst_opcode [RETURNDATACOPY; ASSIGN; REVERT]` by
    (qpat_x_assum `MEM inst.inst_opcode _` mp_tac >> rw[] >> simp[]) >>
  `~in_revert_forward fn1 s1` by
    (irule joint_trace_nonforward_endpoint >> metis_tac[]) >>
  `~in_static_abort_prefix fn1 s1` by
    (irule joint_trace_call_not_static_prefix >> conj_tac >- simp[] >>
     qexistsl_tac [`ctx`, `G`, `G1`, `PG`, `PG1`, `evs`, `h`, `h1`, `hs`,
       `hs1`, `inst1`, `j`, `fn`, `inst`, `t`, `om`, `om1`, `oms`, `oms1`,
       `q0`, `qs`, `stk`, `stk1`, `tn`, `tn1`, `vs0`] >> simp[]) >>
  `EL (LENGTH evs) (q0::qs) = JointConfig stk PG G tn fn inst t oms om hs h` by
    metis_tac[joint_trace_endpoint] >>
  `s1.vs_requests <<= t.vs_requests` by
    (irule joint_trace_requests_prefix >>
     qexistsl_tac [`ctx`, `G1`, `G`, `PG1`, `PG`, `evs`, `fn1`, `fn`, `h1`,
       `h`, `hs1`, `hs`, `inst1`, `inst`, `LENGTH evs`, `j`, `om1`, `om`,
       `oms1`, `oms`, `JointConfig stk PG G tn fn inst t oms om hs h`,
       `q0`, `qs`, `stk1`, `stk`, `tn1`, `tn`, `vs0`] >> simp[]) >>
  simp[request_cut_def] >> metis_tac[IS_PREFIX_LENGTH]
QED

(* The memory obligations of the frame driver at every configuration of a
   trace that ends at a call step below the cut. *)
Theorem request_cut_trace_memory:
  generate_context_plan ctx = SOME cplan /\
  EVERY wf_function ctx.ctx_functions /\
  vs0.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
  max_live_eom ctx = SOME eom /\
  mem_inv (\ctx fn inst u.
    (request_cut (LENGTH t.vs_requests) u /\ ~in_static_abort_prefix fn u) ==>
    lowered_mem_ok eom (w2n u.vs_initial_fmp) ctx fn inst u) ctx vs0 /\
  joint_trace vs0 ctx q0 evs qs
    (JointConfig stk PG G tn fn inst t oms om hs h) /\
  active_inst fn inst t /\
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  j <= LENGTH evs /\
  EL j (q0::qs) = JointConfig stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1 ==>
  source_memory_reads_disjoint cplan inst1 s1 /\
  context_source_memory_writes_disjoint cplan inst1 s1
Proof
  strip_tac >>
  drule_all request_cut_trace_config >> strip_tac >>
  drule generate_context_plan_spill_gap >> strip_tac >> gvs[] >>
  `s1.vs_initial_fmp = n2w cplan.cp_initial_fmp` by
    metis_tac[raw_reachable_initial_fmp] >>
  `w2n s1.vs_initial_fmp = cplan.cp_initial_fmp` by gvs[w2n_n2w, LESS_MOD] >>
  `lowered_mem_ok cplan.cp_max_static_eom cplan.cp_initial_fmp ctx fn1 inst1 s1` by
    (qpat_x_assum `mem_inv _ _ _` mp_tac >> simp[mem_inv_raw_reachable] >>
     strip_tac >> first_x_assum drule >> impl_tac >- fs[] >> fs[]) >>
  metis_tac[lowered_reads_disjoint, lowered_writes_disjoint]
QED

Theorem codegen_request_cut_outcome_identity:
  !fn inst fuel final k.
  supported_program tops /\ source_typing_ok tops am tx /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  codegen_assembly rpolicy out.po_unit = SOME prog /\
  generate_context_plan out.po_unit.cu_context = SOME cplan /\
  call_state_rel tops (assemble prog) am tx es /\
  run_call es = SOME (r,final) /\ ~frame_resource_starved es r final /\
  (?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
    mem_inv (\ctx fn inst u.
      (request_cut k u /\ ~in_static_abort_prefix fn u) ==>
      lowered_mem_ok eom (w2n u.vs_initial_fmp) ctx fn inst u)
      out.po_unit.cu_context (entry_venom_state prog cplan es)) /\
  raw_reachable (entry_venom_state prog cplan es) out.po_unit.cu_context
    fn inst t /\
  inst.inst_opcode <> INVOKE /\ LENGTH t.vs_requests = k /\
  step_inst fuel out.po_unit.cu_context inst t = OK t' /\
  k < LENGTH t'.vs_requests ==>
  k < LENGTH (call_requests es) /\
  EL k (call_requests es) = EL k t'.vs_requests /\
  t.vs_outcomes <> [] /\
  MEM (EL k (call_requests es), HD t.vs_outcomes) (call_trace es)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `LENGTH t.vs_requests = k` (SUBST_ALL_TAC o SYM) >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    fs[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `codegen_context_obligations (\_ _ _ _. F) out.po_unit.cu_context cplan` by
    (irule o1_pipeline_codegen_obligations >>
     simp[codegen_memory_obligations_def] >> metis_tac[]) >>
  `initial_ctx_rel_tail [] cplan prog out.po_unit.cu_context
     (entry_venom_state prog cplan es) es` by
    (simp[initial_ctx_rel_tail_nil] >>
     irule entry_venom_state_initial_ctx_rel >> metis_tac[]) >>
  `EVERY wf_function out.po_unit.cu_context.ctx_functions` by
    fs[codegen_context_obligations_def, codegen_ready_def,
       codegen_ready_fn_def, EVERY_MEM] >>
  `(entry_venom_state prog cplan es).vs_initial_fmp =
     n2w cplan.cp_initial_fmp` by simp[entry_venom_state_def] >>
  `active_inst fn inst t` by metis_tac[raw_reachable_active] >>
  drule_all step_inst_request_outcomes >> strip_tac >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  drule frame_reachable_has_origins >> strip_tac >>
  drule origin_frame_has_joint_history >> strip_tac >>
  `joint_config_reachable (entry_venom_state prog cplan es)
     out.po_unit.cu_context (JointConfig stk PG G tn fn inst t oms om hs h)` by
    simp[joint_config_reachable_def] >>
  pop_assum (qx_choosel_then [`q0`, `evs`, `qs`] assume_tac o
    REWRITE_RULE [joint_reachable_iff_trace]) >>
  qspecl_then [`rpolicy`, `out.po_unit`, `cplan`, `prog`, `[]`,
    `entry_venom_state prog cplan es`, `q0`, `evs`, `qs`, `es`, `t`, `t'`,
    `r`, `final`] mp_tac codegen_request_step_alignment >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt strip_tac >>
      FIRST [irule (cj 1 request_cut_trace_memory),
             irule (cj 2 request_cut_trace_memory)] >>
      metis_tac[]) >>
  simp[]
QED
