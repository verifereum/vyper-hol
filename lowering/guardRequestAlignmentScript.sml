(* Request indexing between the raw run, O1 run and compiled call trace. *)
Theory guardRequestAlignment
Ancestors
  o1RequestContract o1PassContract codegenRequestPrefix callTrace
  contextCodegenRel unitTransformDefs venomExecSemantics ptrDiscipline
  extCallOracle list rich_list pair
  e2eDefs e2eProducers e2eEntry e2eComposition sourceUnitExecution
  vyperLoweringCorrect supportedProgram o1PipelineCorrect loweringShapeProps
  vyperCompiler vyperContext immutableCodeLayout

(* A terminating raw run has a matching lowered request prefix on either
   exit path; ctx_sim supplies the halt case and ctx_abort_rq the abort. *)
Theorem ctx_sim_abort_request_prefix:
  ctx_sim D C C' si so /\ ctx_abort_rq D C C' si so /\
  (run_context fuel C si = Halt ss \/
   ?a. run_context fuel C si = Abort a ss) ==>
  ?fuel' ts.
    (run_context fuel' C' so = Halt ts \/
     ?a. run_context fuel' C' so = Abort a ts) /\
    request_prefix_rel D ss.vs_requests ts.vs_requests
Proof
  strip_tac
  >- (fs[ctx_sim_def] >>
      first_x_assum (qspec_then `fuel` mp_tac) >>
      simp[terminates_def] >> strip_tac >>
      Cases_on `run_context fuel' C' so` >>
      gvs[dead_result_rel_def] >>
      rename1 `run_context matched_fuel C' so = Halt matched_state` >>
      qexistsl_tac [`matched_fuel`, `matched_state`] >>
      simp[LIST_REL_imp_request_prefix_rel]) >>
  fs[ctx_abort_rq_def] >> metis_tac[]
QED

Theorem compiled_request_outcome_alignment:
  ctx_sim D raw.cu_context lowered.cu_context si so /\
  ctx_abort_rq D raw.cu_context lowered.cu_context si so /\
  (run_context fuel raw.cu_context si = Halt ss \/
   ?a. run_context fuel raw.cu_context si = Abort a ss) /\
  generate_context_plan lowered.cu_context = SOME cplan /\
  codegen_assembly rpolicy lowered = SOME prog /\
  unit_shape_ok lowered /\
  codegen_context_obligations Inv lowered.cu_context cplan /\
  codegen_reachability_package Inv lowered.cu_context so /\
  initial_ctx_rel cplan prog lowered.cu_context so es /\
  EVERY (\p. ~computed_precompile (FST p)) (call_trace es) /\
  si.vs_outcomes = MAP SND (call_trace es) /\
  k < LENGTH si.vs_outcomes ==>
  MEM (EL k (call_requests es), EL k si.vs_outcomes) (call_trace es) /\
  request_agree_except D (EL k ss.vs_requests) (EL k (call_requests es))
Proof
  strip_tac >>
  drule_all ctx_sim_abort_request_prefix >> strip_tac >>
  drule_all codegen_request_prefix >> strip_tac >>
  `call_requests es = MAP FST (call_trace es)` by
    (simp[call_requests_def, FILTER_EQ_ID, EVERY_MAP] >>
     gvs[EVERY_MEM, FORALL_PROD]) >>
  `k < LENGTH (call_trace es)` by fs[] >>
  conj_tac
  >- (drule (Q.SPECL [`k`, `call_trace es`] EL_MEM) >>
      simp[EL_MAP] >> Cases_on `EL k (call_trace es)` >> simp[]) >>
  fs[request_prefix_rel_EL, IS_PREFIX_APPEND, EL_APPEND1]
QED

Theorem source_compiled_request_alignment:
  source_typing_ok tops am tx /\ supported_program tops /\
  call_state_rel tops (assemble prog) am tx es /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  o1_pipeline rpolicy unit = SOME out /\
  codegen_assembly rpolicy out.po_unit = SOME prog /\
  generate_context_plan out.po_unit.cu_context = SOME cplan /\
  gas_variant vs (entry_venom_state prog cplan es) /\
  ctx_sim (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
    unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cplan es) /\
  ctx_abort_rq (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
    unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cplan es) /\
  o1_lowered_inv out.po_unit.cu_context (entry_venom_state prog cplan es) /\
  (run_context fuel unit.cu_context vs = Halt ss \/
   ?a. run_context fuel unit.cu_context vs = Abort a ss) /\
  EVERY (\p. ~computed_precompile (FST p)) (call_trace es) /\
  k < LENGTH vs.vs_outcomes /\
  request_agree H (initial_evaluation_context am.sources am.layouts tx NONE)
    rq (EL k ss.vs_requests) ==>
  MEM (EL k (call_requests es), EL k vs.vs_outcomes) (call_trace es) /\
  request_agree H (initial_evaluation_context am.sources am.layouts tx NONE)
    rq (EL k (call_requests es))
Proof
  strip_tac >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    fs[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `(entry_venom_state prog cplan es).vs_initial_fmp = n2w cplan.cp_initial_fmp` by
    simp[entry_venom_state_def] >>
  drule_all o1_pipeline_memory_obligations >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  `initial_ctx_rel cplan prog out.po_unit.cu_context
     (entry_venom_state prog cplan es) es` by
    (irule entry_venom_state_initial_ctx_rel >> metis_tac[]) >>
  `vs.vs_outcomes = MAP SND (call_trace es)` by
    (drule gas_variant_outcomes >> simp[entry_venom_state_def]) >>
  drule_all compiled_request_outcome_alignment >> strip_tac >> simp[] >>
  irule (request_agree_dead_trans |>
    Q.INST [`am'` |-> `am`, `res` |-> `ARB`, `rqs` |-> `[]`,
            `tx` |-> `tx`, `r1` |-> `EL k ss.vs_requests`]) >>
  simp[external_call_dead_def, cx_dead_def, initial_evaluation_context_def]
QED
