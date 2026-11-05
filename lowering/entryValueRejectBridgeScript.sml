Theory entryValueRejectBridge
Ancestors
  entrySourcePackages entryRejectCode entryDispatchRejectMem
  entryValueRejectFacts entryDispatchProps vyperLoweringCorrect compileEnv finite_map

Theorem source_entry_value_reject_mem_safe:
  lower_vyper_runtime_unit tops rp = SOME u /\
  supported_program tops /\ source_typing_ok tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <| outcomes := SOME vs.vs_outcomes; requests := [] |>) = (INR e,st) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl ==>
  !fuel. mem_safe_blocks fuel u.cu_context efn
    (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0 |>)
Proof
  strip_tac >>
  drule_all entry_value_reject_callvalue >> strip_tac >>
  drule_all lower_runtime_selected_source_packages >> strip_tac >>
  drule_all run_lowering_entry_label >> strip_tac >> gvs[] >>
  drule_all run_lowering_selected_entry_code >> strip_tac >>
  drule_all valid_call_linear_dispatch_target >>
  disch_then (qspec_then `fl` assume_tac) >>
  drule_all initial_venom_state_calldata_length >> strip_tac >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
    gvs[initial_venom_state_rel_def] >>
  irule linear_dispatch_value_reject_mem_safe >> simp[] >>
  qexistsl_tac [`fl`, `mc`, `sc`, `sd`,
    `MAP (\(sel,lbl,z). (sel,lbl))
      (build_selectors (type_env tops) (FST (classify_functions tops)))`,
    `sf`, `sk`] >>
  simp[fresh_vars_wrt_def] >>
  qspecl_then [`type_env tops`, `FST (classify_functions tops)`]
    mp_tac linear_selectors_lt >> simp[]
QED
