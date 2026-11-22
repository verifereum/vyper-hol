(* The installed fixture's constructor and selected external entry contexts. *)
Theory linkedBodyWitnessContext
Ancestors
  e2eModsWitness e2eDeployModsDefs e2eModsDefs e2eDefs e2eWitnessCompute
  vyperTypeContract vyperTypeContractContext vyperContext vyperInterpreter
  vyperAST alist list
Libs computeLib finite_mapLib intReduce

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset
val () = computeLib.add_funs [alistTheory.fmap_to_alist_FEMPTY,
                             integer_wordTheory.i2w_pos]

val constructor_context =
  ``deploy_evaluation_context_mods linked_witness_mods
      linked_witness_initial_machine linked_witness_deploy_tx``
val external_context =
  ``initial_evaluation_context linked_witness_am_call.sources
      linked_witness_am_call.layouts linked_witness_call_tx (SOME 2)``

val fixture_load = EVAL
  ``load_contract (SOME []) [] linked_witness_initial_machine
       linked_witness_deploy_tx linked_witness_mods linked_witness_exports``

val runtime_layouts = SIMP_CONV (srw_ss())
  [linked_witness_am_call_def, next_source_machine_def,
   linked_witness_am_deploy_post_def, fixture_load]
  ``linked_witness_am_call.layouts``

val entry_context_simps =
  [deploy_evaluation_context_mods_def, initial_evaluation_context_def,
   linked_witness_initial_machine_def, linked_witness_deploy_tx_def,
   linked_witness_call_tx_def, e2eWitnessComputeTheory.p23_deploy_tx_def,
   e2eWitnessComputeTheory.p23_call_tx_def,
   empty_call_txn_def, runtime_layouts, initial_machine_state_def]

Theorem linked_witness_constructor_context:
  (^constructor_context).in_deploy /\
  ALOOKUP (^constructor_context).sources ((^constructor_context).txn).target =
    SOME linked_witness_mods /\
  (^constructor_context).stk = [(NONE,"__init__")] /\
  (^constructor_context).nonreentrant_slot = SOME global_nonreentrant_slot /\
  context_function_live ^constructor_context (NONE,"__init__") /\
  layouts_agree_mods linked_witness_mods linked_witness_exports
    linked_witness_initial_machine linked_witness_deploy_tx /\
  (?art. check_contract T (^constructor_context).layouts
    ((^constructor_context).txn).target linked_witness_mods = SOME art)
Proof
  mp_tac linked_witness_deploy_premises >>
  simp[deploy_typing_ok_mods_def, deploy_state_rel_mods_def] >>
  rpt strip_tac >>
  simp[initial_evaluation_context_def, deploy_evaluation_context_mods_def] >>
  simp entry_context_simps >>
  simp[context_function_live_def, function_live_def] >>
  disj1_tac >>
  simp[linked_witness_mods_def, ALOOKUP_def, module_allocated_def,
       toplevel_allocated_def, lookup_var_slot_in_layouts_def]
QED

Theorem linked_witness_external_context:
  ~(^external_context).in_deploy /\
  ALOOKUP (^external_context).sources ((^external_context).txn).target =
    SOME linked_witness_mods /\
  (^external_context).stk = [(SOME 2,"locked_get_x")] /\
  (^external_context).nonreentrant_slot = SOME global_nonreentrant_slot /\
  context_function_live ^external_context (SOME 2,"locked_get_x") /\
  layouts_agree_mods linked_witness_mods linked_witness_exports
    linked_witness_am_call linked_witness_call_tx /\
  (?art. check_contract F (^external_context).layouts
    ((^external_context).txn).target linked_witness_mods = SOME art) /\
  find_function_module linked_witness_am_call linked_witness_call_tx.target
    "locked_get_x" = SOME 2
Proof
  mp_tac linked_witness_call_premises >>
  simp[source_typing_ok_mods_def, call_state_rel_mods_def, source_deployment_rel_mods_def] >>
  rpt strip_tac >>
  simp[initial_evaluation_context_def, find_function_module_def] >>
  simp entry_context_simps >>
  simp[context_function_live_def, function_live_def, linked_witness_exports_def] >>
  disj1_tac >>
  simp[linked_witness_mods_def, ALOOKUP_def, module_allocated_def,
       toplevel_allocated_def, lookup_var_slot_in_layouts_def]
QED
