(* Concrete terminal outcomes from the two selected nonpayable checks. *)
Theory entryCreateValueReject
Ancestors
  groupedEntryExit dispatchedEntryValueRevert slotCopyExecution
  fragGasOriginPtr fragGasOrigin fragGasMode fragGasPathMem fragExec
  venomExecSemantics venomInst venomState e2eDefs
  vyperInterpreter entryValueRevertPtr vyperCalldata

Theorem entry_origin_revert_run[local]:
  C.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  gas_origin_path T explicit C fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)
    [] (Abort Revert_abort u) ==>
  ?fuel. run_context fuel C vs = Abort Revert_abort u
Proof
  strip_tac >>
  drule gas_origin_path_erase >> simp[gas_marked_path_def] >>
  disch_then (strip_assume_tac o MATCH_MP gas_path_mem_exec) >> gvs[] >>
  qexists_tac `SUC fuel` >> simp[run_context_def, run_function_def] >>
  irule slot_copy_run_from_entry >> simp[]
QED

Theorem grouped_value_check_reverts:
  C.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  compile_entry_checks m F opened = ((),checked) /\
  fn_has_code opened checked fn /\ opened.cs_current_insts = [] /\
  ~block_is_terminated opened /\ fresh_vars_wrt opened t /\
  ~t.vs_halted /\ t.vs_current_bb = opened.cs_current_bb /\
  t.vs_inst_idx = 0 /\ allocas_from 0 t /\
  (ctx_has_dalloca C ==> allocas_below_fmp t) /\
  t.vs_call_ctx.cc_callvalue <> 0w /\
  (!D explicit. gas_origin_ptr_path (D,0,explicit,C,fn,[])
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
     FEMPTY,entry_taint) [] (OK t,G,tn)) ==>
  ?fuel u. run_context fuel C vs = Abort Revert_abort u
Proof
  strip_tac >> drule_all grouped_entry_value_reject_path >>
  disch_then (qx_choosel_then [`u`,`J`,`tz`] (qspecl_then [`ARB`,`{}`] assume_tac)) >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  drule_all entry_origin_revert_run >> metis_tac[]
QED

Theorem dispatched_value_check_reverts:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  source_typing_ok tops am tx /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
    SOME (tx.function_name, tx.args) /\
  initial_venom_state_rel tops am tx vs /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut, nr, args, [], ret, fbody) /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
       <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
    (INR e, st) ==>
  ?fuel u. run_context fuel unit.cu_context vs = Abort Revert_abort u
Proof
  strip_tac >> drule_all initial_entry_rejected_value >> strip_tac >>
  drule_all dispatched_value_reject_path >> strip_tac >>
  qpat_assum `!explicit. gas_origin_path _ _ _ _ _ _ _`
    (qspec_then `{}` assume_tac) >>
  drule_all entry_origin_revert_run >> metis_tac[]
QED
