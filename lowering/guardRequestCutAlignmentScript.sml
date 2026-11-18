Theory guardRequestCutAlignment
Ancestors
  e2eRequestCutDefs e2eDefs e2eEntry asmOptimizer codegenSymRel
  codegen stackPlanGen unitTransformDefs o1PipelineCorrect
  unitMemInv staticAbortDefs contextRawReachable ptrDiscipline
  venomExecSemantics callTrace frameOutcome vfmExecution
  guardRequestCutIdentity

(* Match a witnessed request step to the corresponding non-precompile call
   in the EVM frame. The lowered witness lets the simulation stop at the
   request, with no termination or memory obligation beyond that cut. *)
Theorem codegen_request_cut_outcome:
  !fin tops am tx rpolicy unit out prog cplan prog' es r es'
   vs0 D k vs fn inst s fuel s' fn' inst' t fuel' t'.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    supported_program tops /\ source_typing_ok tops am tx /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cplan /\
    fin rpolicy prog = SOME prog' /\
    call_state_rel tops (assemble prog') am tx es /\
    run_call es = SOME (r,es') /\ ~frame_resource_starved es r es' /\
    vs0 = opt_entry_state prog prog' cplan es /\
    raw_safe_rq_upto D 0 k unit.cu_context vs /\
    ctx_rq_upto D k unit.cu_context out.po_unit.cu_context vs vs0 /\
    (?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
      mem_inv (\ctx fn inst u.
        (request_cut k u /\ ~in_static_abort_prefix fn u) ==>
        lowered_mem_ok eom (w2n u.vs_initial_fmp) ctx fn inst u)
        out.po_unit.cu_context vs0) /\
    (fin = asm_opt_finalizer ==>
      code_end_offset_ok (\ctx fn inst u.
        raw_reachable vs0 ctx fn inst u /\
        request_cut k u /\ ~in_static_abort_prefix fn u) out.po_unit.cu_context) /\
    raw_reachable vs unit.cu_context fn inst s /\
    inst.inst_opcode <> INVOKE /\ LENGTH s.vs_requests = k /\
    step_inst fuel unit.cu_context inst s = OK s' /\
    k < LENGTH s'.vs_requests /\
    raw_reachable vs0 out.po_unit.cu_context fn' inst' t /\
    inst'.inst_opcode <> INVOKE /\ LENGTH t.vs_requests = k /\
    step_inst fuel' out.po_unit.cu_context inst' t = OK t' /\
    k < LENGTH t'.vs_requests /\
    request_agree_except D (EL k s'.vs_requests) (EL k t'.vs_requests) /\
    t.vs_outcomes = s.vs_outcomes ==>
    k < LENGTH (call_requests es) /\
    request_agree_except D (EL k s'.vs_requests) (EL k (call_requests es)) /\
    s.vs_outcomes <> [] /\
    MEM (EL k (call_requests es), HD s.vs_outcomes) (call_trace es)
Proof
  rpt gen_tac >> strip_tac >>
  `fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  gvs[]
  >- (`opt_entry_state prog prog cplan es = entry_venom_state prog cplan es` by
        metis_tac[opt_entry_state_identity] >>
      pop_assum (fn th => fs[th]) >>
      qspecl_then [`fn'`, `inst'`, `fuel'`, `es'`, `LENGTH s.vs_requests`] mp_tac
        codegen_request_cut_outcome_identity >>
      impl_tac >- (simp[] >> metis_tac[]) >>
      strip_tac >> gvs[]) >>
  (* ADMISSION: S7 request-cut simulation through the assembly optimizer.
     The backend lane owns its discharge. *)
  cheat
QED
