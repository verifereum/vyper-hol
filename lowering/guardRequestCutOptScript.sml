(* The request-cut companion through the assembly optimizer: a lowered
   request step below the cut is the frame's next recorded call, and the
   head of the step's outcomes answers it in the call trace.

   TOP-LEVEL: codegen_request_cut_outcome_opt_own.
 *)
Theory guardRequestCutOpt
Ancestors
  guardRequestCutIdentity fnFrameRequestPrefixOpt fnFrameSymbolicPrefix
  jointRequestCut frameJointTransition asmOptimizer
  codegenSymRel codegenEntrySim e2eOptEntry e2eProducers e2eEntry e2eDefs
  e2eRequestCutDefs runtimeSymSrcUnit o1LabelFlowCompose o1PassLift
  asmOptNonemptyFinalizer contextCodegenRel unitMemInv staticAbortDefs
  ctxLookupAgree stepWriteFootprintBase frameJointTrace
  frameOriginReachable frameOriginHistory
  concretizePtrCoverageStaticMemReachability callTrace unitTransformDefs
  o1PipelineCorrect venomExecSemantics stackPlanGen vyperLoweringCorrect
  loweringShapeSource contextRawReachable venomWf list rich_list words
  arithmetic finite_map ownSymSrcUnit gasFocusOptLabelFlow codegenLabelDisciplined

(* The symbolic driver's guard at every configuration of a trace that ends
   at a call step below the cut. *)
Theorem request_cut_trace_guard_reloc[local]:
  !ctx cplan vs0 lo eom t q0 evs qs stk PG G tn fn inst oms om hs h
   j stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1.
  generate_context_plan ctx = SOME cplan /\
  EVERY wf_function ctx.ctx_functions /\
  vs0.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
  (!l. FLOOKUP vs0.vs_labels l =
       OPTION_MAP n2w (FLOOKUP lo l)) /\
  max_live_eom ctx = SOME eom /\
  mem_inv (\ctx fn inst u.
    (request_cut (LENGTH t.vs_requests) u /\ ~in_static_abort_prefix fn u) ==>
    lowered_mem_ok eom (w2n u.vs_initial_fmp) ctx fn inst u) ctx vs0 /\
  code_end_offset_ok (\ctx fn inst u.
    raw_reachable vs0 ctx fn inst u /\
    request_cut (LENGTH t.vs_requests) u /\ ~in_static_abort_prefix fn u) ctx /\
  joint_trace vs0 ctx q0 evs qs
    (JointConfig stk PG G tn fn inst t oms om hs h) /\
  active_inst fn inst t /\
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  j <= LENGTH evs /\
  EL j (q0::qs) = JointConfig stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1 ==>
  ~in_revert_forward fn1 s1 /\ focus_s7_symbolic_guard_own lo cplan fn1 inst1 s1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all request_cut_trace_config >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rewrite_tac[focus_s7_symbolic_guard_own_def] >> conj_tac
  >- (strip_tac >> conj_tac >>
      FIRST [irule (cj 1 request_cut_trace_memory),
             irule (cj 2 request_cut_trace_memory)] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `FLOOKUP s1.vs_labels "code_end" = SOME (n2w off)` by
    (drule raw_reachable_labels >> disch_then SUBST1_TAC >>
     qpat_x_assum `!l. FLOOKUP vs0.vs_labels l = _`
       (fn th => rewrite_tac[th]) >>
     qpat_x_assum `FLOOKUP lo _ = _`
       (fn th => rewrite_tac[th]) >>
     simp[]) >>
  qpat_x_assum `code_end_offset_ok _ _`
    (mp_tac o SIMP_RULE bool_ss [code_end_offset_ok_def]) >>
  disch_then (qspecl_then [`fn1`, `inst1`, `s1`, `dst`, `x`, `sz`, `src`,
                           `n2w off`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
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
  `~ctx_has_dalloca unit.cu_context` by
    (irule every_no_dalloca >>
     drule_all lower_vyper_runtime_unit_no_dalloca_checked >> simp[]) >>
  `codegen_context_obligations (\_ _ _ _. F) out.po_unit.cu_context cplan` by
    (irule o1_pipeline_codegen_obligations >>
     simp[codegen_memory_obligations_def] >> metis_tac[]) >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[entryStateRelTheory.source_typing_ok_vtype_keys_distinct] >>
  drule_all lower_vyper_runtime_unit_sym_src_ok_own >> strip_tac >>
  drule_all focus_opt_label_flow_own >> strip_tac >>
  drule_all o1_pipeline_sym_unit_static_ok >> strip_tac >>
  `assemble prog' <> []` by
    (irule codegen_assembly_finalizer_nonempty >> metis_tac[]) >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`]
    mp_tac opt_entry_asm_rels_own >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qabbrev_tac `vs0 = opt_entry_state_own prog prog' cplan es` >>
  `vs0.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
    (!l. FLOOKUP vs0.vs_labels l = OPTION_MAP n2w (FLOOKUP (lo_reloc prog prog') l))` by
    fs[codegen_asm_entry_rel_reloc_def] >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  `EVERY wf_function out.po_unit.cu_context.ctx_functions` by
    fs[codegen_context_obligations_def, codegen_ready_def,
       codegen_ready_fn_def, EVERY_MEM] >>
  `active_inst fn inst t` by metis_tac[raw_reachable_active] >>
  drule_all step_inst_request_outcomes >> strip_tac >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  drule frame_reachable_has_origins >> strip_tac >>
  drule origin_frame_has_joint_history >> strip_tac >>
  `joint_config_reachable vs0 out.po_unit.cu_context
     (JointConfig stk PG G tn fn inst t oms om hs h)` by
    simp[joint_config_reachable_def] >>
  pop_assum (qx_choosel_then [`q0`, `evs`, `qs`] assume_tac o
    REWRITE_RULE [joint_reachable_iff_trace]) >>
  qspecl_then [`asm_opt_finalizer`, `rpolicy`, `out.po_unit`, `cplan`, `prog`, `prog'`,
    `vs0`, `q0`, `evs`, `qs`, `es`, `t`, `t'`, `r`, `final`] mp_tac
    codegen_request_step_alignment_opt_own >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- simp[accepted_finalizers_def] >>
      rpt gen_tac >> strip_tac >>
      qspecl_then [`out.po_unit.cu_context`, `cplan`, `vs0`, `lo_reloc prog prog'`, `eom`,
        `t`, `q0`, `evs`, `qs`, `stk`, `PG`, `G`, `tn`, `fn`, `inst`, `oms`,
        `om`, `hs`, `h`, `j`, `stk1`, `PG1`, `G1`, `tn1`, `fn1`, `inst1`,
        `s1`, `oms1`, `om1`, `hs1`, `h1`] mp_tac request_cut_trace_guard_reloc >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      simp[]) >>
  simp[]
QED
*)
Theorem codegen_request_cut_outcome_opt_own:
  !fn inst fuel final k.
  asm_opt_finalizer rpolicy prog = SOME prog' /\
  supported_program tops /\
  source_typing_ok tops am tx /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  codegen_assembly rpolicy out.po_unit = SOME prog /\
  generate_context_plan out.po_unit.cu_context = SOME cplan /\
  call_state_rel tops (assemble prog') am tx es /\
  run_call es = SOME (r,final) /\ ~frame_resource_starved es r final /\
  (?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
    mem_inv (\ctx fn inst u.
      (request_cut k u /\ ~in_static_abort_prefix fn u) ==>
      lowered_mem_ok eom (w2n u.vs_initial_fmp) ctx fn inst u)
      out.po_unit.cu_context (opt_entry_state_own prog prog' cplan es)) /\
  code_end_offset_ok (\ctx fn inst u.
    raw_reachable (opt_entry_state_own prog prog' cplan es) ctx fn inst u /\
    request_cut k u /\ ~in_static_abort_prefix fn u) out.po_unit.cu_context /\
  raw_reachable (opt_entry_state_own prog prog' cplan es) out.po_unit.cu_context
    fn inst t /\
  inst.inst_opcode <> INVOKE /\ LENGTH t.vs_requests = k /\
  step_inst fuel out.po_unit.cu_context inst t = OK t' /\
  k < LENGTH t'.vs_requests ==>
  k < LENGTH (call_requests es) /\
  EL k (call_requests es) = EL k t'.vs_requests /\
  t.vs_outcomes <> [] /\
  MEM (EL k (call_requests es), HD t.vs_outcomes) (call_trace es)
Proof
  cheat
QED
