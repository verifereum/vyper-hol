(* Recover the failed CREATE from the selected terminating raw run. *)
Theory entryCreateExit
Ancestors
  createSizeExit entryCreateReject requestCutEntryFacts stepWriteFootprintBase
  o1LowerDloadRunnerBoundary lowerDloadPtrRawReachable fragExec
  contextRawReachable contextCodegenRel venomRunBounded venomWf venomState
  venomInst arithmetic words list

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
