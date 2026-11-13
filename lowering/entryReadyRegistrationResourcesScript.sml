(* Resource adapter for the selected check cursor before registration. *)
Theory entryReadyRegistrationResources
Ancestors
  entryPrefixAllocationResources entryRegistrationCursorHistory
  calldataRegistrationExec emitHelperProps compileEnv

Theorem runtime_ready_registration_resources:
  lower_vyper_runtime_unit tops pol = SOME unit /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  vars_pc_only (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                          vs_inst_idx := 0 |>) t /\
  compile_entry_checks mc pay sc = ((),sk) /\
  sc.cs_current_insts = [] /\ fn_has_code sc sk func /\
  t.vs_current_bb = sk.cs_current_bb /\
  t.vs_inst_idx = LENGTH sk.cs_current_insts /\
  compile_register_positional_args ce specs 4 sk = (cer,registered) /\
  fresh_vars_wrt sk t ==>
  alloca_inv t /\ alloca_frontier_inv unit.cu_context func site t /\
  t.vs_allocas = FEMPTY /\ t.vs_alloca_next = 0 /\
  (!id. FLOOKUP t.vs_allocas id = NONE) /\ alloca_history func t /\
  fresh_vars_wrt registered t
Proof
  strip_tac >> drule_all runtime_prefix_allocation_resources >>
  disch_then (qspec_then `site` strip_assume_tac) >>
  drule_all entry_checks_cursor_alloca_history >> strip_tac >> simp[] >>
  drule registration_compile_counters >> strip_tac >>
  irule fresh_vars_wrt_mono >> qexists_tac `sk` >> simp[]
QED
