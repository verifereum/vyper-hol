Theory bodyPtrPopGlobalSource
Ancestors
  bodyPtrPopGlobalUnit bodyPtrPopGlobalLegality bodyPtrPopGlobalOperand
  vyperContext vyperState vyperTypeInvariants vyperTypeCallStackSoundness
  bodyPtrPreds vyperTypeCallGraphSoundness vyperTypeCallGraph
  vyperTypeContractFunction vyperValue vyperInterpreter vyperTypeContract
  vyperTypeSystem vyperTypeContractContext vyperStorageBackend

(* Closed diagnostic context fixes the actual module and declared slot layout.
   The enclosing expression is tested in its own nonrecursive call frame. *)
Definition pop_global_cx_def:
  pop_global_cx = empty_evaluation_context with
    <| stk := [(NONE,"probe")];
       sources := [(0w,pop_global_mods)];
       layouts := [(0w,([((NONE,"A"),0);((NONE,"B"),4)],[]))] |>
End

Theorem pop_global_source_module:
  get_module_code pop_global_cx NONE = SOME pop_global_tops
Proof
  EVAL_TAC
QED

Theorem pop_global_source_callable:
  lookup_callable_function pop_global_cx.in_deploy "replace" pop_global_tops =
    SOME (Nonpayable,F,[],[],BaseT (UintT 256),pop_global_body)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``pop_global_body``])
QED

Theorem pop_global_source_context_typed:
  context_well_typed pop_global_cx
Proof
  EVAL_TAC
QED

Theorem pop_global_source_operand:
  body_base_target_ptr_ok pop_global_cx pop_global_target
Proof
  irule pop_global_target_body_ptr >>
  simp[pop_global_source_module, pop_global_source_callable] >>
  qexists_tac `pop_global_tops` >>
  simp[pop_global_source_module, pop_global_source_callable]
QED

Theorem pop_global_source_module_cases:
  get_module_code pop_global_cx src = SOME ts <=>
    src = NONE /\ ts = pop_global_tops
Proof
  Cases_on `src` >>
  simp[pop_global_cx_def, empty_evaluation_context_def, empty_call_txn_def,
       get_module_code_def, pop_global_mods_def]
QED

Theorem pop_global_source_lookup_cases:
  lookup_callable_function F fn pop_global_tops = SOME (mut,nr,args,dflts,ret,bdy) <=>
    fn = "replace" /\ mut = Nonpayable /\ nr = F /\ args = [] /\ dflts = [] /\
    ret = BaseT (UintT 256) /\ bdy = pop_global_body
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``pop_global_body``]) >>
  Cases_on `fn = "replace"` >> simp[] >> metis_tac[]
QED

Theorem pop_global_source_functions_call_free:
  functions_follow_call_graph edges pop_global_cx
Proof
  simp[functions_follow_call_graph_def, pop_global_source_module_cases] >>
  rpt strip_tac >>
  gvs[pop_global_cx_def, empty_evaluation_context_def,
      pop_global_source_lookup_cases] >>
  EVAL_TAC
QED

Theorem pop_global_source_call_graph:
  irreflexive (TC (call_edge_rel [((NONE,"probe"),(NONE,"replace"))]))
Proof
  simp[relationTheory.irreflexive_def] >> gen_tac >> strip_tac >>
  drule relationTheory.TC_CASES1_E >>
  simp[call_edge_rel_def] >> strip_tac >>
  last_x_assum kall_tac >> gvs[] >> strip_tac >>
  drule relationTheory.TC_CASES1_E >> simp[call_edge_rel_def]
QED

Theorem pop_global_source_call_safe:
  call_evaluation_safe pop_global_cx [(NONE,"replace")]
Proof
  simp[call_evaluation_safe_def, pop_global_cx_def] >>
  qexists_tac `[((NONE,"probe"),(NONE,"replace"))]` >>
  simp[call_stack_follows_def, pop_global_source_call_graph,
       GSYM pop_global_cx_def, pop_global_source_functions_call_free,
       calls_follow_call_graph_def, call_edge_rel_def]
QED

Theorem pop_global_source_contract_checked:
  check_contract F pop_global_cx.layouts 0w pop_global_mods = SOME pop_global_art
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_global_source_initial_functions:
  functions_well_typed pop_global_cx <=>
  functions_well_typed (initial_evaluation_context pop_global_cx.sources
    pop_global_cx.layouts pop_global_cx.txn NONE)
Proof
  simp[functions_well_typed_def, pop_global_cx_def,
       empty_evaluation_context_def, initial_evaluation_context_def,
       lookup_nonreentrant_slot_def, empty_call_txn_def,
       get_module_code_def, get_tenv_def, context_function_live_def,
       fn_sigs_consistent_def, fn_sigs_declared_complete_def,
       toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def,
       well_formed_type_def]
QED

Theorem pop_global_source_functions_typed:
  functions_well_typed pop_global_cx
Proof
  rewrite_tac[pop_global_source_initial_functions] >>
  irule check_contract_functions_well_typed_initial >>
  qexistsl_tac [`0w`, `pop_global_art`, `pop_global_mods`] >>
  simp[pop_global_source_contract_checked, pop_global_cx_def,
       empty_evaluation_context_def, empty_call_txn_def]
QED

Theorem pop_global_source_initial_context:
  pop_global_cx = (initial_evaluation_context pop_global_cx.sources
    pop_global_cx.layouts pop_global_cx.txn NONE) with stk := [(NONE,"probe")]
Proof
  EVAL_TAC
QED

Theorem pop_global_source_artifact_env:
  pop_global_env = artifact_env pop_global_art pop_global_mods NONE
Proof
  EVAL_TAC
QED

Theorem pop_global_source_env_context:
  env_context_consistent pop_global_env pop_global_cx
Proof
  once_rewrite_tac[pop_global_source_initial_context] >>
  rewrite_tac[pop_global_source_artifact_env] >>
  irule check_contract_env_context_consistent_initial_with_current_src >>
  qexists_tac `0w` >>
  simp[pop_global_source_contract_checked, pop_global_cx_def,
       empty_evaluation_context_def, empty_call_txn_def]
QED

(* Concrete diagnostic storage: A has one element at each of its three array
   levels and payload 7; B is empty. The names bound evaluation of records. *)
Definition pop_global_storage_def:
  pop_global_storage : bytes32 -> bytes32 =
    (0w =+ 1w) ((1w =+ 1w) ((2w =+ 1w) ((3w =+ 7w) (K 0w))))
End

Definition pop_global_es_def:
  pop_global_es = set_storage pop_global_cx
    (empty_state with <|scopes := [FEMPTY]; outcomes := SOME []|>) F pop_global_storage
End

Theorem pop_global_source_scopes:
  env_scopes_consistent pop_global_env pop_global_cx pop_global_es
Proof
  EVAL_TAC >> simp[]
QED

Theorem pop_global_source_immutables:
  env_immutables_consistent pop_global_env pop_global_cx pop_global_es
Proof
  EVAL_TAC >> rpt strip_tac >>
  Cases_on `id = "B"` >> Cases_on `id = "A"` >> gvs[] >>
  gvs[find_var_decl_by_name_def]
QED

Theorem pop_global_source_env_consistent:
  env_consistent pop_global_env pop_global_cx pop_global_es
Proof
  simp[env_consistent_def, pop_global_source_env_context,
       pop_global_source_scopes, pop_global_source_immutables]
QED

Theorem pop_global_source_state_typed:
  state_well_typed pop_global_es
Proof
  EVAL_TAC >> simp[]
QED

Theorem pop_global_source_accounts_typed:
  accounts_well_typed pop_global_es.accounts
Proof
  EVAL_TAC >> gen_tac >> Cases_on `addr = 0w` >> simp[]
QED
