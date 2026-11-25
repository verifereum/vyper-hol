(* Recover the failed CREATE from the selected terminating raw run. *)
Theory entryCreateExit
Ancestors
  createSizeExit entryCreateReject requestCutEntryFacts stepWriteFootprintBase
  o1LowerDloadRunnerBoundary lowerDloadPtrRawReachable fragExec
  contextRawReachable contextCodegenRel venomRunBounded venomWf venomState
  venomInst arithmetic words list ctorDeployRunBounded actualDecoderPackaging
  venomCompilerWf o1PipelineCorrect passSimulationDefs

Theorem raw_reachable_call_context[local]:
  !vs ctx fn inst s. raw_reachable vs ctx fn inst s ==>
    s.vs_call_ctx = vs.vs_call_ctx
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt strip_tac >>
  imp_res_tac ld_enters_block_call_ctx >>
  imp_res_tac ld_step_ok_call_ctx >>
  imp_res_tac ld_setup_callee_call_ctx >> fs[]
QED

Theorem raw_reachable_oversized_create_abort:
  EVERY wf_function ctx.ctx_functions /\ ~vs.vs_call_ctx.cc_static /\
  run_context fuel ctx vs = r /\ exit_result r /\
  raw_reachable vs ctx fn inst s /\ ~inst_create_size_ok inst s ==>
  oversized_create_abort ctx r
Proof
  strip_tac >>
  `!err. run_context fuel ctx vs <> Error err` by
    metis_tac[exit_result_not_error] >>
  drule_all raw_reached_oversized_create_terminal >> strip_tac >>
  `MEM fn ctx.ctx_functions` by metis_tac[raw_visit_function_member] >>
  `ALL_DISTINCT (fn_labels fn)` by
    fs[EVERY_MEM, wf_function_def, fn_labels_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    metis_tac[raw_reachable_active, active_inst_block_lookup] >>
  `~s.vs_call_ctx.cc_static` by metis_tac[raw_reachable_call_context] >>
  `r = Abort ExHalt_abort (halt_state (set_returndata [] s))` by metis_tac[] >>
  qpat_x_assum `~inst_create_size_ok inst s` mp_tac >>
  simp[inst_create_size_ok_def] >> rpt strip_tac >>
  simp[oversized_create_abort_def] >>
  qexistsl_tac [`fn`, `bb`, `inst`, `v`, `off`, `sz`, `salt`, `sz_w`] >>
  Cases_on `sz` >> fs[halt_state_def, set_returndata_def, eval_operand_def, lookup_var_def]
QED

(* A safe terminating run rules out every reachable oversized CREATE.
   For a static call, an ExHalt_abort would contradict the selected run
   even though the size-specific clause does not constrain static aborts. *)
Theorem selected_raw_create_size_ok:
  EVERY wf_function ctx.ctx_functions /\
  ALL_DISTINCT (FLAT (MAP fn_labels ctx.ctx_functions)) /\
  run_context fuel ctx vs = r /\ exit_result r /\
  create_size_exit_ok ctx res r /\
  res <> INR (Error (RuntimeError "create initcode too large")) /\
  (vs.vs_call_ctx.cc_static ==>
   ~(!n. terminates (run_context n ctx vs) ==>
        ?u. run_context n ctx vs = Abort ExHalt_abort u)) ==>
  !fn inst s. raw_reachable vs ctx fn inst s ==> inst_create_size_ok inst s
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> CCONTR_TAC >>
  Cases_on `vs.vs_call_ctx.cc_static`
  >- (`!err. run_context fuel ctx vs <> Error err` by
        metis_tac[exit_result_not_error] >>
      drule_all raw_reached_oversized_create_terminal >> strip_tac >>
      `terminates (run_context fuel ctx vs)` by simp[terminates_def] >>
      `!n. terminates (run_context n ctx vs) ==>
           ?u. run_context n ctx vs = Abort ExHalt_abort u` by
        (rpt strip_tac >> qexists_tac `halt_state (set_returndata [] s)` >>
         Cases_on `n <= fuel` >>
         metis_tac[run_context_terminates_mono, arithmeticTheory.NOT_LESS_EQUAL,
                   arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
      metis_tac[]) >>
  drule_all raw_reachable_oversized_create_abort >>
  fs[create_size_exit_ok_def] >> metis_tac[]
QED

Theorem create_size_raw_unit_wf:
  o1PipelineCorrect$o1_pipeline rp unit = SOME out ==>
  EVERY wf_function unit.cu_context.ctx_functions /\
  ALL_DISTINCT (FLAT (MAP fn_labels unit.cu_context.ctx_functions))
Proof
  simp[o1PipelineCorrectTheory.o1_pipeline_def] >>
  disch_then (mp_tac o MATCH_MP checked_pipeline_input_wf) >>
  simp[unit_wf_def, unit_labels_wf_def, unit_label_namespace_def,
       venom_wf_def, EVERY_MEM] >> metis_tac[]
QED
