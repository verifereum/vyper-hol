(* Normalized transaction witness: old entries are excluded by tx_env_ok. *)
Theory augAssignNestedNormalizedProbe
Ancestors
  augAssignNestedRelatedEntryProbe augAssignNestedSemanticAudit vyperState vyperInterpreter
  vyperTypeInvariants vyperContext vyperStorageLayoutSafety vyperLookupStorage
  targetPlaceSimCases exprSimHypsDefs gasContext exprLoweringProps loweringPosts stmtSimDefs
Libs finite_mapLib computeLib

val () = computeLib.upd_compset add_finite_map_compset

Definition nested_valid_cx_def:
  nested_valid_cx = nested_initial_cx with
    txn := nested_initial_cx.txn with <|block_number := 1; block_hashes := [0w]|>
End

Theorem nested_valid_transaction:
  tx_env_ok nested_valid_cx.txn
Proof
  EVAL_TAC
QED

Theorem nested_valid_source_replay:
  !obs. FST (eval_stmt nested_valid_cx
    (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1)))
    (nested_premise_es with gas_obs := obs)) = INL ()
Proof
  gen_tac >>
  `7 - 1 = (6:int)` by intLib.COOPER_TAC >>
  EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >>
  simp[return_def, get_place_def, combinTheory.APPLY_UPDATE_THM] >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem nested_valid_body_inv:
  body_inv nested_reach_tops nested_premise_unit.cu_context
    nested_premise_cenv nested_valid_cx
Proof
  mp_tac augAssignNestedPremiseProbeTheory.nested_initial_body_inv >>
  simp[bodySimTheory.body_inv_def, nested_valid_cx_def,
       bodySimTheory.cenv_module_pins_def,
       vyperContextTheory.get_module_code_def, vyperContextTheory.get_tenv_def]
QED


Theorem nested_valid_observations[simp]:
  (!src. get_module_code nested_valid_cx src = get_module_code nested_initial_cx src) /\
  get_tenv nested_valid_cx = get_tenv nested_initial_cx /\
  current_module nested_valid_cx = current_module nested_initial_cx /\
  (!b src id. lookup_var_slot_from_layout nested_valid_cx b src id =
             lookup_var_slot_from_layout nested_initial_cx b src id) /\
  (!k. context_function_live nested_valid_cx k = context_function_live nested_initial_cx k) /\
  nested_valid_cx.in_deploy = nested_initial_cx.in_deploy
Proof
  simp[nested_valid_cx_def, get_module_code_def, get_tenv_def,
       current_module_def, lookup_var_slot_from_layout_def,
       vyperTypeContractTheory.context_function_live_def]
QED

Theorem nested_valid_env_consistent:
  !env es. env_consistent env nested_valid_cx es <=>
           env_consistent env nested_initial_cx es
Proof
  simp[env_consistent_def, env_context_consistent_def,
       env_scopes_consistent_def, env_immutables_consistent_def,
       fn_sigs_consistent_def, fn_sigs_live_def, fn_sigs_declared_complete_def,
       toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def,
       nested_valid_cx_def, get_module_code_def, get_tenv_def,
       current_module_def, lookup_var_slot_from_layout_def,
       vyperTypeContractTheory.context_function_live_def]
QED

Theorem nested_valid_functions:
  functions_well_typed nested_valid_cx <=> functions_well_typed nested_initial_cx
Proof
  simp[functions_well_typed_def, fn_sigs_consistent_def, fn_sigs_live_def,
       fn_sigs_declared_complete_def, toplevel_vtypes_complete_def,
       bare_globals_complete_def, bare_global_assignable_complete_def,
       flag_members_complete_def, nested_valid_cx_def,
       get_module_code_def, get_tenv_def, lookup_var_slot_from_layout_def,
       vyperTypeContractTheory.context_function_live_def]
QED

Theorem nested_valid_backend[simp]:
  !b es. get_storage_backend nested_valid_cx b es =
         get_storage_backend nested_initial_cx b es
Proof
  Cases >> simp[nested_valid_cx_def, get_storage_backend_def]
QED

Theorem nested_valid_storage_wf:
  !es. contract_storage_well_formed nested_valid_cx es <=>
       contract_storage_well_formed nested_initial_cx es
Proof
  simp[contract_storage_well_formed_def, well_formed_storage_def,
       storage_var_in_range_def, storage_var_info_def, declared_storage_region_def,
       nested_valid_cx_def, get_module_code_def, get_tenv_def,
       lookup_var_slot_from_layout_def, get_storage_backend_def]
QED

Theorem nested_valid_layout:
  storage_layout_safe nested_valid_cx <=> storage_layout_safe nested_initial_cx
Proof
  simp[storage_layout_safe_def, well_formed_layout_def,
       nonreentrant_slot_separated_def, storage_var_info_def,
       declared_storage_region_def, nested_valid_cx_def,
       get_module_code_def, get_tenv_def, lookup_var_slot_from_layout_def]
QED

Theorem nested_valid_expr_inv_transfer:
  !ce env es. expr_sim_inv ce nested_valid_cx env es <=>
              expr_sim_inv ce nested_initial_cx env es
Proof
  `nested_initial_cx.txn.block_number = 0` by EVAL_TAC >>
  simp[exprSimHypsDefsTheory.expr_sim_inv_def, nested_valid_env_consistent,
       nested_valid_functions, nested_valid_storage_wf, nested_valid_layout,
       vyperTypeStoragePreservationTheory.oracle_storage_ok_def,
       context_well_typed_def, exprSimHypsDefsTheory.bare_globals_layout_def,
       nested_valid_cx_def, get_module_code_def, get_tenv_def]
QED

Theorem nested_valid_expr_inv:
  expr_sim_inv nested_premise_cenv nested_valid_cx nested_premise_env nested_premise_es
Proof
  simp[nested_valid_expr_inv_transfer,
       augAssignNestedPremiseProbeTheory.nested_initial_expr_inv]
QED

Theorem nested_valid_index_body_ok:
  body_expr_ok nested_valid_cx
    (Call (BaseT (UintT 256)) (IntCall (NONE,"f")) [] NONE)
Proof
  irule bodySimCallIntcallTheory.intcall_body_expr_ok >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  `get_module_code nested_valid_cx NONE = SOME nested_reach_tops` by EVAL_TAC >>
  `~nested_valid_cx.in_deploy` by EVAL_TAC >>
  gvs[lift_option_type_def, augAssignNestedReachProbeTheory.nested_reach_tops_def,
      lookup_callable_function_def, lookup_function_def, return_def, AllCaseEqs()] >>
  simp[augAssignNestedCalleeFactsTheory.nested_replacement_body_ok,
       bodySimTheory.body_exprs_ok_def, bodySimTheory.body_results_ok_def]
QED

Theorem nested_valid_target_case:
  !tops ctx func cenv.
    body_inv tops ctx cenv nested_valid_cx ==>
    target_case F ctx func cenv nested_valid_cx nested_reach_target
Proof
  rpt strip_tac >> irule targetPlaceSimCasesTheory.target_case_all >>
  `body_expr_ok nested_valid_cx
    (Literal (BaseT (UintT 256)) (IntL 0))` by
    (irule bodySimExprCasesTheory.body_expr_ok_intro >>
     simp[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
  drule_all bodySimExprCasesTheory.body_expr_ok_case >> strip_tac >>
  mp_tac nested_valid_index_body_ok >>
  disch_then (mp_then Any mp_tac bodySimExprCasesTheory.body_expr_ok_case) >>
  simp[] >> strip_tac >>
  simp[augAssignNestedReachProbeTheory.nested_reach_target_def,
       targetPlaceSimTheory.target_idx_case_def] >> metis_tac[]
QED

Theorem nested_valid_call_safe:
  call_evaluation_safe nested_valid_cx [(NONE,"f")]
Proof
  rewrite_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
  qexistsl [`[((NONE,""),(NONE,"f"))]`, `(NONE,"")`, `[]`] >>
  EVAL_TAC >> simp[] >> conj_tac
  >- (qmatch_goalsub_abbrev_tac `TC R` >>
      `transitive R` by
        (simp[Abbr `R`, relationTheory.transitive_def,
          vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]) >>
      drule relationTheory.transitive_TC_identity >>
      disch_then SUBST1_TAC >>
      simp[Abbr `R`, relationTheory.irreflexive_def,
        vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]) >>
  simp[lookup_function_def] >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem nested_valid_indices:
  target_indices_pre nested_premise_cenv nested_valid_cx
    nested_premise_env nested_reach_target
Proof
  rewrite_tac[augAssignNestedReachProbeTheory.nested_reach_target_def,
    targetPlaceSimTheory.target_indices_pre_def, exprSimHypsDefsTheory.expr_body_pre_def] >>
  `get_tenv nested_valid_cx = type_env (cx_tops nested_valid_cx)` by EVAL_TAC >>
  simp[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``call_evaluation_safe``, ``expr_sim_inv``, ``nested_premise_cenv``, ``nested_premise_env``, ``nested_valid_cx``, ``supported_program``, ``nested_reach_tops``]) >>
  `call_evaluation_safe nested_valid_cx []` by
    (irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_mono >>
     qexists `[(NONE,"f")]` >> simp[nested_valid_call_safe]) >>
  simp[nested_valid_call_safe] >>
  simp[augAssignNestedPremiseProbeTheory.nested_premise_supported_program] >>
  gen_tac >> disch_then kall_tac >> EVAL_TAC >> simp[]
QED
