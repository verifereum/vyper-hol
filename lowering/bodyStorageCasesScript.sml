(*
 * Case lemmas for bodyStoragePreservation's mutual induction
 *
 * One lemma per evaluate_ind clause shape (statements, tuple targets,
 * loops, builtins, internal-call frame entry and exit), each saying that
 * contract_storage_well_formed, IS_SOME st.outcomes and oracle_storage_ok
 * carry across that step given the induction hypotheses for its parts.
 * bodyStoragePreservation assembles them.
 *)

Theory bodyStorageCases
Ancestors
  vyperCall
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeExprSoundness vyperTypeCallStackSoundness vyperTypeInvariants
  vyperStorageLayoutSafety vyperTypeStoragePreservation
  vyperTypeEvalStoragePreservation vyperEvalOutcomeSuffix
  supportedExprTraverse supportedProgram vyperPlaceFrames
  vyperStatePreservation vyperTypeAssignContext vyperStoragePlaceProvenance
  vyperPlaceStoragePreservation vyperValue vyperMachineFrame
  vyperTypeContractStaticMaps supportedDecls supportedStmts supportedExprs
  supportedTargets supportedStmtTraverse list

(* The callee of a runtime internal call is a declared Internal function, so
   the lookup finds it, never the constructor or the synthetic fallback. *)
Theorem supported_callable_body_contract:
  supported_program tops /\
  IS_SOME (supported_function_decl tops (NONE,name) Internal) /\
  lookup_callable_function deploy name tops =
    SOME (mut,nr,args,defaults,ret,stmts) ==>
  defaults = [] /\ ?bindings. supported_stmts tops bindings stmts
Proof
  strip_tac >> gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `supported_function_decl _ _ _ = SOME decl` >> PairCases_on `decl` >>
  drule supported_internal_lookup >> strip_tac >>
  gvs[lookup_callable_function_def] >>
  drule lookup_function_Internal_SOME_MEM >> strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_declaration_header_def, supported_declaration_body_def,
       supported_function_body_def, NULL_EQ] >> metis_tac[]
QED

Theorem supported_pure_main_calls:
  (!tops e. supported_pure_expr tops e ==>
    EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e)) /\
  (!tops es. supported_pure_exprs tops es ==>
    EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs es)) /\
  (!tops fields. supported_pure_fields tops fields ==>
    EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_named_exprs fields)) /\
  (!tops e. supported_place_expr tops e ==>
    EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e))
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  simp[supported_pure_expr_def, int_calls_expr_def, EVERY_APPEND] >>
  rpt conj_tac >> rpt gen_tac >>
  TRY (Cases_on `base`) >>
  simp[supported_pure_expr_def, int_calls_expr_def, EVERY_APPEND]
QED

Theorem supported_function_decl_main:
  IS_SOME (supported_function_decl tops id vis) ==> FST id = NONE
Proof
  Cases_on `id` >> CCONTR_TAC >>
  gvs[supported_lookup_other_module]
QED

Theorem supported_effect_main_calls:
  (!tops e. supported_effect_expr tops e ==>
    EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e)) /\
  (!tops e. supported_effect_place_expr tops e ==>
    EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e))
Proof
  ho_match_mp_tac supported_effect_expr_ind >>
  simp[supported_effect_expr_def, int_calls_expr_def, EVERY_APPEND] >>
  rpt conj_tac >> rpt gen_tac >> simp[] >>
  metis_tac[supported_pure_main_calls, supported_function_decl_main]
QED

Theorem supported_expr_main_calls:
  supported_expr tops e ==> EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e)
Proof
  simp[supported_expr_def] >>
  metis_tac[supported_pure_main_calls, supported_effect_main_calls]
QED

Theorem supported_target_info_storage_syntax:
  !tops bindings target.
    IS_SOME (supported_target_info tops bindings target) ==>
    ~supported_target_exists expr_evm_run_root target /\
    ~supported_target_exists call_operands_effect_root target /\
    EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_target target)
Proof
  rpt gen_tac >>
  map_every qid_spec_tac [`bindings`, `tops`, `target`] >>
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >>
  simp[supported_target_info_def, supported_expr_exists_def, call_operands_effect_root_def,
       int_calls_expr_def, EVERY_APPEND] >>
  rpt gen_tac >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  gvs[AllCaseEqs(), expr_size_def] >>
  qmatch_goalsub_rename_tac `int_calls_target tgt` >>
  first_x_assum (qspec_then `tgt` mp_tac) >> simp[] >>
  simp[GSYM optionTheory.IS_SOME_EXISTS] >>
  metis_tac[supported_expr_no_evm_run, expr_has_evm_run_def,
            supported_expr_main_calls, supported_expr_no_call_operand_effects, optionTheory.IS_SOME_EXISTS]
QED

Theorem supported_target_storage_syntax:
  supported_target tops bindings target ==>
  ~supported_target_exists expr_evm_run_root target /\
  ~supported_target_exists call_operands_effect_root target /\
  EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_target target)
Proof
  Cases_on `target` >>
  simp[supported_target_def, supported_expr_exists_def, call_operands_effect_root_def, int_calls_expr_def] >>
  qmatch_goalsub_rename_tac `supported_target_exists _ tgt` >> Cases_on `tgt` >>
  simp[supported_expr_exists_def, call_operands_effect_root_def, int_calls_expr_def] >>
  metis_tac[supported_expr_no_evm_run, expr_has_evm_run_def,
            supported_expr_main_calls, supported_expr_no_call_operand_effects]
QED

Theorem supported_assignment_storage_syntax:
  supported_assignment tops bindings tgt e ==>
  ~supported_assignment_exists expr_evm_run_root tgt /\
  ~supported_assignment_exists call_operands_effect_root tgt /\
  EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_atarget tgt)
Proof
  Cases_on `tgt`
  >- (qmatch_goalsub_rename_tac `BaseTarget btgt` >>
      simp[supported_assignment_def, supported_assignment_exists_def,
           int_calls_atarget_def] >> strip_tac >>
      gvs[AllCaseEqs()]
      >- (irule supported_target_storage_syntax >>
          qexists_tac `bindings` >> simp[]) >>
      irule supported_target_info_storage_syntax >>
      qexists_tac `bindings` >>
      Cases_on `supported_target_info tops bindings btgt` >> gvs[]) >>
  simp[supported_assignment_def] >> strip_tac >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  qmatch_goalsub_rename_tac `TupleTarget tgts` >>
  Induct_on `tgts` >>
  simp[supported_assignment_exists_def, int_calls_atarget_def] >>
  qx_gen_tac `tgt` >> Cases_on `tgt` >>
  simp[supported_assignment_exists_def, int_calls_atarget_def, EVERY_APPEND] >>
  gvs[supported_assignment_exists_def, int_calls_atarget_def] >>
  strip_tac >> drule supported_target_storage_syntax >>
  metis_tac[]
QED

Theorem supported_iterator_storage_syntax:
  supported_iterator tops ty iter n ==>
  ~supported_iterator_exists expr_evm_run_root iter /\
  ~supported_iterator_exists call_operands_effect_root iter /\
  EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_iterator iter)
Proof
  Cases_on `iter`
  >- (simp[supported_iterator_def, supported_iterator_exists_def,
           int_calls_iterator_def] >>
      qmatch_goalsub_rename_tac `int_calls_expr arr` >>
      Cases_on `arr` >> simp[] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp[supported_expr_exists_def, call_operands_effect_root_def, expr_evm_run_root_def, int_calls_expr_def]) >>
  simp[supported_iterator_def, supported_iterator_exists_def,
       int_calls_iterator_def, EVERY_APPEND] >>
  qmatch_goalsub_rename_tac `~supported_expr_exists _ lo /\ ~supported_expr_exists _ hi` >>
  strip_tac >>
  `supported_pure_expr tops lo /\ supported_pure_expr tops hi` suffices_by
    metis_tac[supported_pure_main_calls, supported_expr_no_evm_run,
              supported_expr_no_call_operand_effects,
              supported_expr_def, expr_has_evm_run_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[supported_pure_expr_def]
QED

Theorem supported_string_reason_storage_syntax:
  supported_string_reason tops e ==>
  ~supported_expr_exists expr_evm_run_root e /\
  ~supported_expr_exists call_operands_effect_root e /\
  EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e)
Proof
  strip_tac >>
  `supported_pure_expr tops e` suffices_by
    metis_tac[supported_pure_main_calls, supported_expr_no_evm_run,
              supported_expr_no_call_operand_effects,
              supported_expr_def, expr_has_evm_run_def] >>
  Cases_on `e` >> gvs[supported_string_reason_def] >>
  rename1 `Literal _ lit` >> Cases_on `lit` >>
  gvs[supported_string_reason_def, supported_pure_expr_def]
QED

Theorem supported_reasons_storage_syntax:
  (!tops reason. supported_assert_reason tops reason ==>
    ~supported_assert_exists expr_evm_run_root reason /\
    ~supported_assert_exists call_operands_effect_root reason /\
    EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_assert_reason reason)) /\
  (!tops reason. supported_raise_reason tops reason ==>
    ~supported_raise_exists expr_evm_run_root reason /\
    ~supported_raise_exists call_operands_effect_root reason /\
    EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_raise_reason reason))
Proof
  conj_tac >> rpt gen_tac >> Cases_on `reason` >>
  simp[supported_assert_reason_def, supported_raise_reason_def,
       supported_assert_exists_def, supported_raise_exists_def,
       int_calls_assert_reason_def, int_calls_raise_reason_def] >>
  metis_tac[supported_string_reason_storage_syntax]
QED

Theorem supported_pure_exprs_storage_syntax:
  supported_pure_exprs tops es ==>
  ~supported_exprs_exists expr_evm_run_root es /\
  ~supported_exprs_exists call_operands_effect_root es /\
  EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs es)
Proof
  Induct_on `es` >>
  simp[supported_pure_expr_def, supported_expr_exists_def, call_operands_effect_root_def,
       int_calls_expr_def, EVERY_APPEND] >>
  metis_tac[supported_expr_no_evm_run, supported_expr_def,
            expr_has_evm_run_def, supported_pure_main_calls,
            supported_expr_no_call_operand_effects]
QED

Theorem supported_append_target_storage_syntax:
  supported_append_target tops tgt ==>
  ~supported_target_exists expr_evm_run_root tgt /\
  ~supported_target_exists call_operands_effect_root tgt /\
  EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_target tgt)
Proof
  Cases_on `tgt` >>
  simp[supported_append_target_def, supported_expr_exists_def, call_operands_effect_root_def, int_calls_expr_def]
QED

Theorem supported_aug_target_storage_syntax:
  supported_aug_target tops bindings tgt ==>
  ~supported_target_exists expr_evm_run_root tgt /\
  ~supported_target_exists call_operands_effect_root tgt /\
  EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_target tgt)
Proof
  strip_tac >> irule supported_target_info_storage_syntax >>
  qexists_tac `bindings` >>
  qpat_x_assum `supported_aug_target _ _ _` mp_tac >>
  Cases_on `supported_target_info tops bindings tgt` >>
  simp[supported_aug_target_def]
QED

Theorem supported_stmts_storage_syntax:
  (!tops bindings s. supported_stmt tops bindings s ==>
    ~supported_stmt_expr_exists expr_evm_run_root s /\
    ~supported_stmt_expr_exists call_operands_effect_root s /\
    EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt s)) /\
  (!tops bindings ss. supported_stmts tops bindings ss ==>
    ~supported_stmts_expr_exists expr_evm_run_root ss /\
    ~supported_stmts_expr_exists call_operands_effect_root ss /\
    EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts ss))
Proof
  ho_match_mp_tac supported_stmt_ind >>
  simp[supported_stmt_def, supported_stmt_expr_exists_def,
       supported_expr_exists_def, call_operands_effect_root_def, int_calls_expr_def,
       int_calls_stmt_def, EVERY_APPEND] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  imp_res_tac supported_assignment_def >>
  imp_res_tac supported_log_def >>
  imp_res_tac (REWRITE_RULE [DISJ_IMP_THM] (iffRL supported_expr_def)) >>
  imp_res_tac supportedExprTraverseTheory.supported_expr_no_evm_run >>
  imp_res_tac supported_expr_main_calls >>
  imp_res_tac supported_expr_no_call_operand_effects >>
  imp_res_tac supported_assignment_storage_syntax >>
  imp_res_tac supported_target_storage_syntax >>
  imp_res_tac supported_aug_target_storage_syntax >>
  imp_res_tac supported_append_target_storage_syntax >>
  imp_res_tac supported_iterator_storage_syntax >>
  imp_res_tac supported_reasons_storage_syntax >>
  imp_res_tac supported_pure_exprs_storage_syntax >>
  gvs[expr_has_evm_run_def]
QED

Theorem supported_callable_storage_syntax:
  supported_program tops /\
  IS_SOME (supported_function_decl tops (NONE,name) Internal) /\
  lookup_callable_function deploy name tops =
    SOME (mut,nr,args,defaults,ret,stmts) ==>
  defaults = [] /\
  ~supported_stmts_expr_exists expr_evm_run_root stmts /\
  EVERY (\c. FST c = NONE /\
             IS_SOME (supported_function_decl tops c Internal))
    (int_calls_stmts stmts)
Proof
  strip_tac >> drule_all supported_callable_body_contract >> strip_tac >>
  drule (CONJUNCT2 supported_stmts_storage_syntax) >> simp[]
QED

(* Entry transport separates semantic runtime preservation from storage
   preservation and the monotone oracle stream. *)
Theorem body_oracle_storage_entry_transfer:
  runtime_storage_consistent env cx st /\
  runtime_consistent env cx st' /\
  contract_storage_well_formed cx st' /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  outcome_suffix st.outcomes st'.outcomes ==>
  runtime_storage_consistent env cx st' /\
  IS_SOME st'.outcomes /\ oracle_storage_ok cx st'
Proof
  rpt strip_tac
  >- metis_tac[runtime_storage_consistent_intro,
               runtime_storage_consistent_layout]
  >- metis_tac[exprOracleStorageInterfacesTheory.oracle_storage_entry_suffix]
  >> metis_tac[exprOracleStorageInterfacesTheory.oracle_storage_entry_suffix]
QED

Theorem body_oracle_storage_frame_entry:
  contract_storage_well_formed cx st /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st ==>
  contract_storage_well_formed (cx with stk updated_by f)
    (st with scopes := scopes) /\
  IS_SOME (st with scopes := scopes).outcomes /\
  oracle_storage_ok (cx with stk updated_by f) (st with scopes := scopes)
Proof
  `!b. get_storage (cx with stk updated_by f)
         (st with scopes := scopes) b = get_storage cx st b` by
    (gen_tac >> Cases_on `b` >>
     simp[vyperStorageBackendTheory.get_storage_def]) >>
  rpt strip_tac
  >- (gvs[contract_storage_well_formed_def,
          vyperLookupStorageTheory.well_formed_storage_def,
          vyperLookupStorageTheory.storage_var_in_range_def,
          vyperStorageBackendTheory.get_storage_backend_eq,
          vyperStorageBackendTheory.get_storage_def] >> metis_tac[])
  >- simp[]
  >> gvs[oracle_storage_ok_payload]
QED

(* List sequencing is independent of the syntactic source of the recursive
   preservation premises.  Consumers discharge these premises using their IH. *)
Theorem body_eval_expr_results_cons_storage:
  (!s r s'. runtime_storage_consistent env cx s /\
    IS_SOME s.outcomes /\ oracle_storage_ok cx s /\
    eval_expr cx e s = (r,s') ==> contract_storage_well_formed cx s') /\
  (!tv s r s'. eval_expr cx e st = (INL tv,s) /\
    runtime_storage_consistent env cx s /\
    IS_SOME s.outcomes /\ oracle_storage_ok cx s /\
    eval_expr_results cx es s = (r,s') ==> contract_storage_well_formed cx s') /\
  well_typed_expr env e /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_expr_results cx (e::es) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_expr_results _ (_::_) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (head_res,head_st)` >>
  `contract_storage_well_formed cx head_st` by metis_tac[] >>
  `runtime_consistent env cx head_st` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `outcome_suffix st.outcomes head_st.outcomes` by
    (drule (cj 5 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  Cases_on `head_res` >> gvs[] >> rpt strip_tac >> gvs[] >>
  Cases_on `eval_expr_results cx es head_st` >>
  rename1 `eval_expr_results cx es head_st = (tail_res,tail_st)` >>
  `contract_storage_well_formed cx tail_st` by metis_tac[] >>
  Cases_on `tail_res` >> gvs[bind_def] >> rpt strip_tac >> gvs[]
QED
Theorem body_eval_exprs_cons_storage:
  (!s r s'. runtime_storage_consistent env cx s /\
    IS_SOME s.outcomes /\ oracle_storage_ok cx s /\
    eval_expr cx e s = (r,s') ==> contract_storage_well_formed cx s') /\
  (!tv v s r s'. eval_expr cx e st = (INL tv,s) /\
    read_result cx tv s = (INL v,s) /\ runtime_storage_consistent env cx s /\
    IS_SOME s.outcomes /\ oracle_storage_ok cx s /\
    eval_exprs cx es s = (r,s') ==> contract_storage_well_formed cx s') /\
  well_typed_expr env e /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_exprs cx (e::es) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_exprs _ (_::_) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (head_res,head_st)` >>
  `contract_storage_well_formed cx head_st` by metis_tac[] >>
  `runtime_consistent env cx head_st` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `outcome_suffix st.outcomes head_st.outcomes` by
    (drule (cj 5 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  Cases_on `head_res` >> gvs[]
  >- (rename1 `eval_expr cx e st = (INL tv,head_st)` >>
      Cases_on `read_result cx tv head_st` >>
      rename1 `read_result cx tv head_st = (read_res,read_st)` >>
      `read_st = head_st` by metis_tac[read_result_state] >> gvs[] >>
      Cases_on `read_res` >> gvs[]
      >- (Cases_on `eval_exprs cx es head_st` >>
          rename1 `eval_exprs cx es head_st = (tail_res,tail_st)` >>
          `contract_storage_well_formed cx tail_st` by metis_tac[] >>
          Cases_on `tail_res` >> gvs[bind_def] >> rpt strip_tac >> gvs[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED


Theorem body_eval_target_place_storage:
  (!r s. eval_base_place cx tgt st = (r,s) ==>
         contract_storage_well_formed cx s) /\
  eval_target_place cx tgt st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac get_place_state >> gvs[] >> metis_tac[]
QED

Theorem body_eval_attribute_target_storage:
  (!r s. eval_base_place cx tgt st = (r,s) ==>
         contract_storage_well_formed cx s) /\
  eval_base_place cx (AttributeTarget tgt fld) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac extend_place_state >> gvs[] >> metis_tac[]
QED

Theorem body_eval_subscript_target_storage:
  (!r s'. eval_base_place cx tgt st = (r,s') ==>
          contract_storage_well_formed cx s') /\
  (!pv s r s'. eval_base_place cx tgt st = (INL pv,s) /\
    runtime_storage_consistent env cx s /\
    IS_SOME s.outcomes /\ oracle_storage_ok cx s /\
    eval_expr cx e s = (r,s') ==> contract_storage_well_formed cx s') /\
  type_place_target env tgt = SOME vt /\
  runtime_storage_consistent env cx st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_target tgt) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_base_place cx (SubscriptTarget tgt e) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx tgt st` >>
  rename1 `eval_base_place cx tgt st = (base_res,base_st)` >>
  `contract_storage_well_formed cx base_st` by metis_tac[] >>
  `runtime_consistent env cx base_st` by
    metis_tac[eval_base_place_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `outcome_suffix st.outcomes base_st.outcomes` by
    (drule (cj 7 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  Cases_on `base_res` >> gvs[return_def]
  >- (gvs[bind_def, return_def] >>
      Cases_on `eval_expr cx e base_st` >>
      rename1 `eval_expr cx e base_st = (expr_res,expr_st)` >>
      `contract_storage_well_formed cx expr_st` by metis_tac[] >>
      Cases_on `expr_res` >> gvs[bind_def, return_def]
      >- (rename1 `eval_expr cx e base_st = (INL tv,expr_st)` >>
          Cases_on `read_result cx tv expr_st` >>
          rename1 `read_result cx tv expr_st = (read_res,read_st)` >>
          imp_res_tac read_result_state >> gvs[] >>
          Cases_on `read_res` >> gvs[return_def, raise_def] >>
          rpt strip_tac >> imp_res_tac extend_place_state >> gvs[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_attribute_storage:
  (!r s. eval_expr cx e st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_expr cx (Attribute ty e fld) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (base_res,base_st)` >>
  `contract_storage_well_formed cx base_st` by metis_tac[] >>
  Cases_on `base_res` >> gvs[bind_def, return_def, raise_def] >>
  rpt strip_tac >> imp_res_tac select_result_state >> gvs[]
QED

Theorem body_eval_struct_storage:
  (!r s. eval_exprs cx (MAP SND kes) st = (r,s) ==>
         contract_storage_well_formed cx s) /\
  eval_expr cx (StructLit ty (src_id_opt,id) kes) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx (MAP SND kes) st` >>
  rename1 `eval_exprs cx (MAP SND kes) st = (exprs_res,exprs_st)` >>
  `contract_storage_well_formed cx exprs_st` by metis_tac[] >>
  Cases_on `exprs_res` >> gvs[LET_THM, bind_def, return_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_type_builtin_storage:
  contract_storage_well_formed cx st /\
  (!r s. type_builtin_args_length_ok tb (LENGTH es) /\
    eval_exprs cx es st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_expr cx (TypeBuiltin ty tb typ es) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def,
                      type_check_def, assert_def] >>
  Cases_on `type_builtin_args_length_ok tb (LENGTH es)` >>
  gvs[return_def, raise_def]
  >- (Cases_on `eval_exprs cx es st` >>
      rename1 `eval_exprs cx es st = (args_res,args_st)` >>
      `contract_storage_well_formed cx args_st` by metis_tac[] >>
      Cases_on `args_res` >> gvs[bind_def, return_def, raise_def]
      >- (rename1 `eval_exprs cx es st = (INL vs,args_st)` >>
          Cases_on `lift_sum (evaluate_type_builtin cx tb typ (MAP expr_type es) vs) args_st` >>
          rename1 `lift_sum _ args_st = (lift_res,lift_st)` >>
          imp_res_tac lift_sum_state >> gvs[] >>
          Cases_on `lift_res` >> gvs[return_def, raise_def] >> rpt strip_tac >> gvs[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_subscript_storage:
  (!r s'. eval_expr cx e1 st = (r,s') ==>
          contract_storage_well_formed cx s') /\
  (!tv s r s'. eval_expr cx e1 st = (INL tv,s) /\
    runtime_storage_consistent env cx s /\
    IS_SOME s.outcomes /\ oracle_storage_ok cx s /\
    eval_expr cx idx s = (r,s') ==> contract_storage_well_formed cx s') /\
  (well_typed_expr env e1 \/ ?vt. type_place_expr env e1 = SOME vt) /\
  runtime_storage_consistent env cx st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e1) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_expr cx (Subscript ty e1 idx) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `eval_expr _ (Subscript _ _ _) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e1 st` >>
  rename1 `eval_expr cx e1 st = (base_res,base_st)` >>
  `contract_storage_well_formed cx base_st` by metis_tac[] >>
  `runtime_consistent env cx base_st` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              eval_expr_place_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  qpat_x_assum `well_typed_expr env e1 \/ _` kall_tac >>
  `outcome_suffix st.outcomes base_st.outcomes` by
    (drule (cj 5 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  Cases_on `base_res` >> gvs[return_def, raise_def]
  >- (Cases_on `eval_expr cx idx base_st` >>
      rename1 `eval_expr cx idx base_st = (idx_res,idx_st)` >>
      `contract_storage_well_formed cx idx_st` by metis_tac[] >>
      Cases_on `idx_res` >> gvs[return_def, raise_def]
      >- (rename1 `eval_expr cx idx base_st = (INL idx_tv,idx_st)` >>
          Cases_on `read_result cx idx_tv idx_st` >>
          rename1 `read_result cx idx_tv idx_st = (read_res,read_st)` >>
          `read_st = idx_st` by metis_tac[read_result_state] >> gvs[] >>
          Cases_on `read_res` >> gvs[return_def, raise_def] >>
          rpt strip_tac >> imp_res_tac select_result_state >> gvs[]) >>
      strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem body_eval_send_storage:
  contract_storage_well_formed cx st /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  (!r s. (LENGTH es = if has_gas then 3 else 2) /\
    eval_exprs cx es st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_expr cx (Call ty (Send has_gas) es extra) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ (Call _ (Send _) _ _) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def,
                      type_check_def, assert_def] >>
  Cases_on `LENGTH es = if has_gas then 3 else 2` >>
  gvs[return_def, raise_def]
  >- (Cases_on `eval_exprs cx es st` >>
      rename1 `eval_exprs cx es st = (args_res,args_st)` >>
      `contract_storage_well_formed cx args_st` by metis_tac[] >>
      `IS_SOME args_st.outcomes /\ oracle_storage_ok cx args_st` by
        (irule exprOracleStorageInterfacesTheory.oracle_storage_entry_suffix >>
         qexists_tac `st` >> simp[] >>
         drule (cj 6 eval_outcome_suffix_mutual) >> simp[]) >>
      Cases_on `args_res` >> gvs[]
      >- metis_tac[vyperOracleCallStorageTheory.eval_send_oracle_storage_preserved] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_builtin_storage:
  contract_storage_well_formed cx st /\
  (!r s. builtin_args_length_ok bt (LENGTH es) /\ bt = Len /\
    eval_expr cx (HD es) st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!r s. builtin_args_length_ok bt (LENGTH es) /\ bt <> Len /\
    eval_exprs cx es st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_expr cx (Builtin ty bt es) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def,
                      type_check_def, assert_def] >>
  reverse (Cases_on `builtin_args_length_ok bt (LENGTH es)`)
  >- (gvs[return_def, raise_def] >> rpt strip_tac >> gvs[]) >>
  gvs[return_def, raise_def] >> Cases_on `bt = Len`
  >- (gvs[] >> Cases_on `eval_expr cx (HD es) st` >>
      rename1 `eval_expr cx (HD es) st = (arg_res,arg_st)` >>
      `contract_storage_well_formed cx arg_st` by metis_tac[] >>
      Cases_on `arg_res` >> gvs[bind_def, return_def, raise_def]
      >- (rename1 `eval_expr cx (HD es) st = (INL tv,arg_st)` >>
          Cases_on `result_array_length cx tv arg_st` >>
          rename1 `result_array_length cx tv arg_st = (len_res,len_st)` >>
          imp_res_tac result_array_length_state >> gvs[] >>
          Cases_on `len_res` >> gvs[return_def, raise_def] >>
          rpt strip_tac >> gvs[]) >> rpt strip_tac >> gvs[]) >>
  Cases_on `bt = Env MsgGas`
  >- (gvs[] >> Cases_on `next_gas_reading st` >>
      imp_res_tac vyperStatePreservationTheory.next_gas_reading_state >>
      Cases_on `q` >> gvs[return_def, raise_def] >>
      rpt strip_tac >> gvs[] >>
      irule contract_storage_well_formed_backends_frame >>
      qexists_tac `st` >> simp[]) >>
  Cases_on `bt = Bop In \/ bt = Bop NotIn`
  >- (simp[] >>
      qpat_x_assum `bt = Bop In \/ bt = Bop NotIn` kall_tac >>
      Cases_on `eval_exprs cx es st` >>
      rename1 `eval_exprs cx es st = (args_res,args_st)` >>
      `contract_storage_well_formed cx args_st` by metis_tac[] >>
      Cases_on `args_res` >>
      gvs[bind_def, ignore_bind_def, assert_def, return_def, raise_def]
      >- (rename1 `eval_exprs cx es st = (INL vs,args_st)` >>
          Cases_on `LENGTH vs = 2` >>
          gvs[bind_def, return_def, raise_def] >>
          Cases_on `evaluate_type (get_tenv cx) (expr_type (EL 1 es))` >>
          gvs[lift_option_type_def, bind_def, return_def, raise_def] >>
          rpt strip_tac >> gvs[] >>
          qmatch_asmsub_abbrev_tac `lift_sum membership_result` >>
          Cases_on `membership_result` >>
          gvs[lift_sum_def, return_def, raise_def] >>
          rpt strip_tac >> gvs[]) >>
      rpt strip_tac >> gvs[]) >>
  gvs[] >> Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  `contract_storage_well_formed cx args_st` by metis_tac[] >>
  Cases_on `args_res` >>
  gvs[bind_def, return_def, raise_def, get_accounts_def, lift_sum_def]
  >- (rename1 `eval_exprs cx es st = (INL vs,args_st)` >>
      Cases_on `evaluate_builtin cx args_st.accounts ty bt (MAP expr_type es) vs` >>
      gvs[return_def, raise_def] >>
      Cases_on `precompile_call_success bt args_st` >>
      imp_res_tac precompile_call_success_state >> gvs[] >>
      rename1 `precompile_call_success bt args_st = (pres,_)` >>
      Cases_on `pres` >> gvs[return_def, raise_def] >> rpt strip_tac >>
      gvs[] >> irule contract_storage_well_formed_storage_frame >>
      qexists_tac `args_st` >> simp[] >>
      Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_raw_revert_storage:
  (!r s. eval_exprs cx es st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_expr cx (Call ty RawRevert es extra) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ (Call _ RawRevert _ _) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def,
                      type_check_def, assert_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  `contract_storage_well_formed cx args_st` by metis_tac[] >>
  Cases_on `args_res` >>
  gvs[bind_def, ignore_bind_def, type_check_def, assert_def, return_def, raise_def]
  >- (rename1 `eval_exprs cx es st = (INL vs,args_st)` >>
      Cases_on `LENGTH vs = 1` >> gvs[] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_raw_log_storage:
  (!r s. eval_exprs cx es st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_expr cx (Call ty RawLog es extra) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ (Call _ RawLog _ _) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def,
                      type_check_def, assert_def, return_def, raise_def, push_log_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  `contract_storage_well_formed cx args_st` by metis_tac[] >>
  Cases_on `args_res` >>
  gvs[bind_def, ignore_bind_def, type_check_def, assert_def,
      return_def, raise_def, push_log_def]
  >- (strip_tac >> gvs[AllCaseEqs()] >>
      imp_res_tac lift_option_type_state >> gvs[] >>
      metis_tac[contract_storage_well_formed_logs]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_selfdestruct_storage:
  (!r s. eval_exprs cx es st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_expr cx (Call ty SelfDestructTarget es extra) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ (Call _ SelfDestructTarget _ _) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, return_def, raise_def,
    lift_option_type_def, get_accounts_def] >> simp[] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  `contract_storage_well_formed cx args_st` by metis_tac[] >>
  Cases_on `args_res` >> gvs[]
  >- (rename1 `eval_exprs cx es st = (INL vs,args_st)` >>
      Cases_on `LENGTH vs = 1` >>
      gvs[type_check_def, assert_def, return_def, raise_def]
      >- (Cases_on `dest_AddressV (HD vs)` >> gvs[return_def, raise_def]
          >- (rpt strip_tac >> gvs[]) >>
          rename1 `dest_AddressV (HD vs) = SOME addr` >>
          Cases_on `transfer_value cx.txn.target addr
            (lookup_account cx.txn.target args_st.accounts).balance args_st` >>
          rename1 `transfer_value _ _ _ args_st = (transfer_res,transfer_st)` >>
          drule_all transfer_value_preserves_contract_storage_well_formed >>
          Cases_on `transfer_res` >>
          gvs[bind_apply, ignore_bind_apply, return_def, raise_def] >>
          rpt strip_tac >> Cases_on `cx.txn.is_static` >> gvs[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_switch_bool_storage:
  contract_storage_well_formed cx st /\
  (!r s. read_result cx tv st = (INL (BoolV T),st) /\
         f st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!r s. read_result cx tv st = (INL (BoolV F),st) /\
         g st = (r,s) ==> contract_storage_well_formed cx s) /\
  switch_BoolV cx tv f g st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `switch_BoolV _ _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [switch_BoolV_def, bind_def] >>
  Cases_on `read_result cx tv st` >>
  rename1 `read_result cx tv st = (read_res,read_st)` >>
  `read_st = st` by metis_tac[read_result_state] >> gvs[] >>
  Cases_on `read_res` >> gvs[]
  >- (rename1 `read_result cx tv st = (INL v,st)` >>
      Cases_on `v = BoolV T` >> gvs[] >>
      Cases_on `v = BoolV F` >> gvs[raise_def] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_if_storage:
  (!r s. eval_expr cx cond st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!tv s r s'. eval_expr cx cond st = (INL tv,s) /\
    read_result cx tv s = (INL (BoolV T),s) /\
    runtime_storage_consistent env cx s /\ IS_SOME s.outcomes /\
    oracle_storage_ok cx s /\ eval_expr cx left s = (r,s') ==>
    contract_storage_well_formed cx s') /\
  (!tv s r s'. eval_expr cx cond st = (INL tv,s) /\
    read_result cx tv s = (INL (BoolV F),s) /\
    runtime_storage_consistent env cx s /\ IS_SOME s.outcomes /\
    oracle_storage_ok cx s /\ eval_expr cx right s = (r,s') ==>
    contract_storage_well_formed cx s') /\
  well_typed_expr env cond /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr cond) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_expr cx (IfExp ty cond left right) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx cond st` >>
  rename1 `eval_expr cx cond st = (cond_res,cond_st)` >>
  `contract_storage_well_formed cx cond_st` by metis_tac[] >>
  `runtime_consistent env cx cond_st` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `outcome_suffix st.outcomes cond_st.outcomes` by
    (drule (cj 5 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  Cases_on `cond_res` >> gvs[]
  >- (rename1 `eval_expr cx cond st = (INL tv,cond_st)` >>
      Cases_on `switch_BoolV cx tv (eval_expr cx left) (eval_expr cx right) cond_st` >>
      rename1 `switch_BoolV _ _ _ _ _ = (switch_res,switch_st)` >>
      `contract_storage_well_formed cx switch_st` by
        (qpat_assum `switch_BoolV _ _ _ _ _ = _`
           (mp_then Any mp_tac body_switch_bool_storage) >>
         simp[]) >>
      Cases_on `switch_res` >> gvs[] >> rpt strip_tac >>
      imp_res_tac conditional_result_state >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_pop_storage:
  (!r s. eval_target_place cx bt st = (r,s) ==>
         contract_storage_well_formed cx s) /\
  well_typed_expr env (Pop ty bt) /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_expr cx (Pop ty bt) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  drule well_typed_expr_Pop_dynamic_target >> strip_tac >>
  `well_typed_target env bt (ArrayT ty (Dynamic n))` by
    simp[well_typed_target_def] >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  qpat_x_assum `eval_expr cx (Pop _ _) st = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,target_st)` >>
  `contract_storage_well_formed cx target_st` by metis_tac[] >>
  Cases_on `target_res` >> gvs[bind_def] >> strip_tac >> gvs[] >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  drule eval_target_place_region >> strip_tac >>
  gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
  `storage_layout_safe cx` by
    metis_tac[runtime_storage_consistent_layout] >>
  drule_all pop_place_preserves_contract_storage >> simp[]
QED

Theorem body_ext_call_kwargs_storage:
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  (!r s. eval_exprs cx es st = (r,s) ==> contract_storage_well_formed cx s) /\
  bind (eval_exprs cx es) (\kwargs.
    bind (read_results cx results) (\vs.
      eval_ext_call cx static skip_check sig opts (target ++ vs ++ kwargs))) st =
    (res,st') ==> contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `bind _ _ st = _` mp_tac >>
  simp_tac (srw_ss()) [bind_apply] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (kw_res,kw_st)` >>
  `contract_storage_well_formed cx kw_st` by metis_tac[] >>
  `IS_SOME kw_st.outcomes /\ oracle_storage_ok cx kw_st` by
    (irule exprOracleStorageInterfacesTheory.oracle_storage_entry_suffix >>
     qexists_tac `st` >> simp[] >>
     drule (cj 6 eval_outcome_suffix_mutual) >> simp[]) >>
  Cases_on `kw_res` >> gvs[]
  >- (Cases_on `read_results cx results kw_st` >>
      rename1 `read_results cx results kw_st = (read_res,read_st)` >>
      `read_st = kw_st` by metis_tac[read_results_state] >> gvs[] >>
      Cases_on `read_res` >> gvs[]
      >- metis_tac[vyperOracleCallStorageTheory.eval_ext_call_oracle_storage_preserved] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_ext_call_capture_storage:
  (!r s. eval_expr_results cx es st = (r,s) ==>
    contract_storage_well_formed cx s) /\
  (!rs s r s'. eval_expr_results cx es st = (INL rs,s) /\
    runtime_storage_consistent env cx s /\ IS_SOME s.outcomes /\
    oracle_storage_ok cx s /\ eval_exprs cx kws s = (r,s') ==>
    contract_storage_well_formed cx s') /\
  well_typed_exprs env es /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs es) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  bind (eval_expr_results cx es) (\results.
    bind (eval_exprs cx kws) (\kwargs.
      bind (read_results cx results) (\vs.
        eval_ext_call cx static skip_check sig opts (target ++ vs ++ kwargs)))) st =
    (res,st') ==> contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `bind _ _ st = _` mp_tac >>
  simp_tac (srw_ss()) [Once bind_apply] >>
  Cases_on `eval_expr_results cx es st` >>
  rename1 `eval_expr_results cx es st = (cap_res,cap_st)` >>
  `contract_storage_well_formed cx cap_st` by metis_tac[] >>
  `runtime_consistent env cx cap_st` by
    (`runtime_consistent env cx st` by
       metis_tac[runtime_storage_consistent_runtime] >>
     qpat_x_assum `runtime_consistent env cx st` mp_tac >>
     simp[runtime_consistent_def] >> strip_tac >>
     drule_all (cj 1 (SPEC_ALL (cj 11
       vyperTypeEvalSoundnessTheory.eval_scc_type_sound_results_mutual))) >>
     simp[runtime_consistent_def]) >>
  `outcome_suffix st.outcomes cap_st.outcomes` by
    (drule eval_expr_results_outcome_suffix >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  Cases_on `cap_res` >> gvs[]
  >- (rpt strip_tac >> irule body_ext_call_kwargs_storage >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_ext_call_storage:
  (!r s. eval_exprs cx (TAKE 1 es) st = (r,s) ==>
    contract_storage_well_formed cx s) /\
  (!target s r s'. eval_exprs cx (TAKE 1 es) st = (INL target,s) /\
    runtime_storage_consistent env cx s /\ IS_SOME s.outcomes /\
    oracle_storage_ok cx s /\
    eval_expr_results cx (TAKE (LENGTH argtys) (DROP 1 es)) s = (r,s') ==>
    contract_storage_well_formed cx s') /\
  (!target s rs s1 r s'. eval_exprs cx (TAKE 1 es) st = (INL target,s) /\
    eval_expr_results cx (TAKE (LENGTH argtys) (DROP 1 es)) s = (INL rs,s1) /\
    runtime_storage_consistent env cx s1 /\ IS_SOME s1.outcomes /\
    oracle_storage_ok cx s1 /\
    eval_exprs cx (DROP (1 + LENGTH argtys) es) s1 = (r,s') ==>
    contract_storage_well_formed cx s') /\
  well_typed_exprs env es /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs es) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_expr cx (Call ty (ExtCall static skip_check (nm,argtys,retty) opts) es extra)
    st = (res,st') ==> contract_storage_well_formed cx st'
Proof
  strip_tac >>
  `well_typed_exprs env (TAKE 1 es) /\
   well_typed_exprs env (TAKE (LENGTH argtys) (DROP 1 es))` by
    metis_tac[vyperTypeEvalSoundnessTheory.well_typed_exprs_TAKE,
              vyperTypeEvalSoundnessTheory.well_typed_exprs_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE 1 es)) /\
   call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH argtys) (DROP 1 es)))` by
    metis_tac[vyperTypeEvalSoundnessTheory.call_evaluation_safe_exprs_TAKE,
              vyperTypeEvalSoundnessTheory.call_evaluation_safe_exprs_DROP] >>
  qpat_x_assum `eval_expr _ (Call _ (ExtCall _ _ _ _) _ _) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, Once bind_apply] >>
  Cases_on `eval_exprs cx (TAKE 1 es) st` >>
  rename1 `eval_exprs cx (TAKE 1 es) st = (tgt_res,tgt_st)` >>
  `contract_storage_well_formed cx tgt_st` by metis_tac[] >>
  `runtime_consistent env cx tgt_st` by
    metis_tac[eval_exprs_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `outcome_suffix st.outcomes tgt_st.outcomes` by
    (drule (cj 6 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  Cases_on `tgt_res` >> gvs[]
  >- (rpt strip_tac >>
      qpat_assum `bind _ _ tgt_st = _`
        (mp_then Any mp_tac body_ext_call_capture_storage) >>
      simp[] >> disch_then irule >> qexists_tac `env` >> simp[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_oracle_pop_case:
  (!tops env ty st res st'.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    well_typed_target env bt ty /\ runtime_storage_consistent env cx st /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_target bt) /\
    ~supported_target_exists expr_evm_run_root bt /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_target_place cx bt st = (res,st') ==> contract_storage_well_formed cx st') ==>
  !tops env st res st'.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr (Pop ty bt)) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr (Pop ty bt)) /\
    ~supported_expr_exists expr_evm_run_root (Pop ty bt) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr cx (Pop ty bt) st = (res,st') ==>
    (well_typed_expr env (Pop ty bt) ==> contract_storage_well_formed cx st') /\
    (!vt. type_place_expr env (Pop ty bt) = SOME vt ==>
          contract_storage_well_formed cx st')
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def, expr_evm_run_root_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  `!r s. eval_target_place cx bt st = (r,s) ==>
         contract_storage_well_formed cx s` by
    (drule well_typed_expr_Pop_dynamic_target >> strip_tac >>
     `well_typed_target env bt (ArrayT ty (Dynamic n))` by
       simp[well_typed_target_def] >> rpt strip_tac >>
     first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all body_eval_pop_storage >> simp[]
QED

Theorem body_eval_stmts_cons_storage:
  (!r s. eval_stmt cx stmt st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!u s r s'. eval_stmt cx stmt st = (INL u,s) /\
    runtime_storage_consistent env1 cx s /\ IS_SOME s.outcomes /\
    oracle_storage_ok cx s /\ eval_stmts cx ss s = (r,s') ==>
    contract_storage_well_formed cx s') /\
  type_stmt env ret_ty stmt = SOME env1 /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_stmt stmt) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_stmts cx (stmt::ss) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  qpat_x_assum `eval_stmts _ (_::_) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, ignore_bind_apply] >>
  Cases_on `eval_stmt cx stmt st` >>
  rename1 `eval_stmt cx stmt st = (head_res,head_st)` >>
  `contract_storage_well_formed cx head_st` by metis_tac[] >>
  Cases_on `head_res` >> gvs[]
  >- (`runtime_consistent env1 cx head_st` by
        (qpat_x_assum `runtime_storage_consistent env cx st` mp_tac >>
         simp[runtime_storage_consistent_def, runtime_consistent_def] >>
         strip_tac >>
         drule_all vyperTypeStmtSoundnessTheory.eval_stmt_type_preservation_success >>
         simp[runtime_consistent_def]) >>
      `storage_layout_safe cx` by
        metis_tac[runtime_storage_consistent_layout] >>
      `runtime_storage_consistent env1 cx head_st` by
        metis_tac[runtime_storage_consistent_intro] >>
      `IS_SOME head_st.outcomes /\ oracle_storage_ok cx head_st` by
        (irule exprOracleStorageInterfacesTheory.oracle_storage_entry_suffix >>
         qexists_tac `st` >> simp[] >>
         drule (cj 1 eval_outcome_suffix_mutual) >> simp[]) >>
      Cases_on `eval_stmts cx ss head_st` >>
      rename1 `eval_stmts cx ss head_st = (tail_res,tail_st)` >>
      `contract_storage_well_formed cx tail_st` by metis_tac[] >>
      Cases_on `tail_res` >> gvs[bind_def] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_return_storage:
  (!r s. eval_expr cx e st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_stmt cx (Return (SOME e)) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,expr_st)` >>
  `contract_storage_well_formed cx expr_st` by metis_tac[] >>
  Cases_on `expr_res` >> gvs[]
  >- (rename1 `eval_expr cx e st = (INL tv,expr_st)` >>
      Cases_on `read_result cx tv expr_st` >>
      rename1 `read_result cx tv expr_st = (read_res,read_st)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `read_res` >> gvs[raise_def] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_raise_reason_storage:
  (!r s. eval_expr cx e st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_stmt cx (Raise (RaiseReason e)) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,expr_st)` >>
  `contract_storage_well_formed cx expr_st` by metis_tac[] >>
  Cases_on `expr_res` >> gvs[]
  >- (rename1 `eval_expr cx e st = (INL tv,expr_st)` >>
      Cases_on `read_result cx tv expr_st` >>
      rename1 `read_result cx tv expr_st = (read_res,read_st)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `read_res` >> gvs[]
      >- (rename1 `read_result cx tv expr_st = (INL v,expr_st)` >>
          Cases_on `dest_StringV v` >>
          gvs[lift_option_type_def, bind_def, return_def, raise_def] >>
          rpt strip_tac >> gvs[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_expr_stmt_storage:
  (!r s. eval_expr cx e st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_stmt cx (Expr e) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,expr_st)` >>
  `contract_storage_well_formed cx expr_st` by metis_tac[] >>
  Cases_on `expr_res` >> gvs[type_check_def, assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem body_eval_annassign_storage:
  contract_storage_well_formed cx st /\
  (!r s. IS_SOME (evaluate_type (get_tenv cx) typ) /\
    eval_expr cx e st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_stmt cx (AnnAssign id typ e) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, lift_option_type_def] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >>
  gvs[bind_def, return_def, raise_def]
  >- (rpt strip_tac >> gvs[]) >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,expr_st)` >>
  `contract_storage_well_formed cx expr_st` by metis_tac[] >>
  Cases_on `expr_res` >> gvs[]
  >- (rename1 `eval_expr cx e st = (INL tv,expr_st)` >>
      Cases_on `read_result cx tv expr_st` >>
      rename1 `read_result cx tv expr_st = (read_res,read_st)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `read_res` >> gvs[]
      >- (rpt strip_tac >> drule (SRULE [vyperCallOutcomeFrameTheory.state_rel_frame_result] machine_frame_new_variable) >>
          simp[machine_frame_def] >> strip_tac >>
          drule_all contract_storage_well_formed_backends_frame >> simp[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_log_storage:
  (!r s. eval_exprs cx es st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_stmt cx (Log id es) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  `contract_storage_well_formed cx args_st` by metis_tac[] >>
  Cases_on `args_res` >> gvs[]
  >- (rename1 `eval_exprs cx es st = (INL vs,args_st)` >>
      Cases_on `encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs` >>
      gvs[lift_option_def, bind_def, ignore_bind_def, return_def, raise_def,
          push_log_def] >>
      Cases_on `cx.txn.is_static` >> rpt strip_tac >> gvs[] >>
      irule contract_storage_well_formed_backends_frame >>
      qexists_tac `args_st` >> simp[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_array_iterator_storage:
  (!r s. eval_expr cx e st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_iterator cx (Array e) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,expr_st)` >>
  `contract_storage_well_formed cx expr_st` by metis_tac[] >>
  Cases_on `expr_res` >> gvs[bind_def, return_def]
  >- (rename1 `eval_expr cx e st = (INL tv,expr_st)` >>
      Cases_on `read_result cx tv expr_st` >>
      rename1 `read_result cx tv expr_st = (read_res,read_st)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `read_res` >> gvs[bind_def, return_def] >>
      strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac lift_option_type_state >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_range_iterator_storage:
  (!r s. eval_expr cx e1 st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!tv v s r s'. eval_expr cx e1 st = (INL tv,s) /\
    read_result cx tv s = (INL v,s) /\ runtime_storage_consistent env cx s /\
    IS_SOME s.outcomes /\ oracle_storage_ok cx s /\
    eval_expr cx e2 s = (r,s') ==> contract_storage_well_formed cx s') /\
  well_typed_expr env e1 /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e1) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_iterator cx (Range e1 e2) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e1 st` >>
  rename1 `eval_expr cx e1 st = (first_res,first_st)` >>
  `contract_storage_well_formed cx first_st` by metis_tac[] >>
  `runtime_consistent env cx first_st` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `outcome_suffix st.outcomes first_st.outcomes` by
    (drule (cj 5 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  Cases_on `first_res` >> gvs[]
  >- (rename1 `eval_expr cx e1 st = (INL tv1,first_st)` >>
      Cases_on `read_result cx tv1 first_st` >>
      rename1 `read_result cx tv1 first_st = (read1_res,read1_st)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `read1_res` >> gvs[]
      >- (Cases_on `eval_expr cx e2 first_st` >>
          rename1 `eval_expr cx e2 first_st = (second_res,second_st)` >>
          `contract_storage_well_formed cx second_st` by metis_tac[] >>
          Cases_on `second_res` >> gvs[]
          >- (rename1 `eval_expr cx e2 first_st = (INL tv2,second_st)` >>
              Cases_on `read_result cx tv2 second_st` >>
              rename1 `read_result cx tv2 second_st = (read2_res,read2_st)` >>
              imp_res_tac read_result_state >> gvs[] >>
              Cases_on `read2_res` >> gvs[bind_def, return_def] >>
              rpt strip_tac >> gvs[AllCaseEqs()] >>
              imp_res_tac lift_sum_state >> gvs[]) >>
          rpt strip_tac >> gvs[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_finally_pop_scope_storage:
  (!r s. f st = (r,s) ==> contract_storage_well_formed cx s) /\
  finally f pop_scope st = (res,st') ==> contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [finally_def] >>
  Cases_on `f st` >> rename1 `f st = (body_res,body_st)` >>
  `contract_storage_well_formed cx body_st` by metis_tac[] >>
  Cases_on `body_res` >>
  simp[ignore_bind_apply, pop_scope_def, return_def, raise_def] >>
  Cases_on `body_st.scopes` >> rpt strip_tac >> gvs[] >>
  irule contract_storage_well_formed_backends_frame >>
  qexists_tac `body_st` >> simp[]
QED

Theorem body_eval_assert_constant_storage:
  (reason = AssertBare \/ reason = AssertUnreachable) /\
  (!r s. eval_expr cx e st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_stmt cx (Assert e reason) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> gvs[] >>
  (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,expr_st)` >>
  `contract_storage_well_formed cx expr_st` by metis_tac[] >>
  Cases_on `expr_res` >> gvs[]
  >- (rename1 `eval_expr cx e st = (INL tv,expr_st)` >>
      simp[switch_BoolV_def, bind_def] >>
      Cases_on `read_result cx tv expr_st` >>
      rename1 `read_result cx tv expr_st = (read_res,read_st)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `read_res` >>
      gvs[COND_RATOR, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[])
QED

Theorem body_push_scope_entry:
  runtime_storage_consistent env cx st /\ IS_SOME st.outcomes /\
  oracle_storage_ok cx st ==>
  runtime_storage_consistent env cx (st with scopes updated_by CONS FEMPTY) /\
  IS_SOME (st with scopes updated_by CONS FEMPTY).outcomes /\
  oracle_storage_ok cx (st with scopes updated_by CONS FEMPTY)
Proof
  strip_tac >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx (st with scopes updated_by CONS FEMPTY)` by
    (fs[runtime_consistent_def] >> rpt conj_tac
     >- (irule vyperTypeEnvPreservationTheory.push_scope_env_consistent >> simp[])
     >- (irule vyperTypeStatePreservationTheory.push_scope_preserves_state_well_typed >>
         qexistsl_tac [`st`, `()`] >> simp[push_scope_def, return_def]) >>
     simp[]) >>
  `contract_storage_well_formed cx st` by
    metis_tac[runtime_storage_consistent_storage] >>
  `contract_storage_well_formed cx (st with scopes updated_by CONS FEMPTY)` by
    (irule contract_storage_well_formed_backends_frame >>
     qexists_tac `st` >> simp[]) >>
  conj_tac
  >- metis_tac[runtime_storage_consistent_intro,
               runtime_storage_consistent_layout] >>
  gvs[oracle_storage_ok_payload]
QED

Theorem body_scoped_switch_storage:
  runtime_storage_consistent env cx st /\ IS_SOME st.outcomes /\
  oracle_storage_ok cx st /\
  (!r s. read_result cx tv st = (INL (BoolV T),st) /\
    runtime_storage_consistent env cx (st with scopes updated_by CONS FEMPTY) /\
    IS_SOME (st with scopes updated_by CONS FEMPTY).outcomes /\
    oracle_storage_ok cx (st with scopes updated_by CONS FEMPTY) /\
    f (st with scopes updated_by CONS FEMPTY) = (r,s) ==>
    contract_storage_well_formed cx s) /\
  (!r s. read_result cx tv st = (INL (BoolV F),st) /\
    runtime_storage_consistent env cx (st with scopes updated_by CONS FEMPTY) /\
    IS_SOME (st with scopes updated_by CONS FEMPTY).outcomes /\
    oracle_storage_ok cx (st with scopes updated_by CONS FEMPTY) /\
    g (st with scopes updated_by CONS FEMPTY) = (r,s) ==>
    contract_storage_well_formed cx s) /\
  switch_BoolV cx tv f g (st with scopes updated_by CONS FEMPTY) = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> drule_all body_push_scope_entry >> strip_tac >>
  qpat_assum `switch_BoolV _ _ _ _ _ = _`
    (mp_then Any mp_tac body_switch_bool_storage) >>
  simp[] >> disch_then irule >>
  `st with scopes updated_by CONS FEMPTY =
   st with scopes := FEMPTY::st.scopes` by
    (Cases_on `st` >> simp[evaluation_state_fn_updates]) >>
  gvs[read_result_empty_scope] >>
  metis_tac[runtime_storage_consistent_storage, read_result_state,
            pairTheory.PAIR]
QED

Theorem body_eval_if_stmt_storage:
  (!r s. eval_expr cx e st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!tv s r s'. eval_expr cx e st = (INL tv,s) /\
    runtime_storage_consistent env cx s /\ IS_SOME s.outcomes /\
    oracle_storage_ok cx s /\
    switch_BoolV cx tv (eval_stmts cx ss1) (eval_stmts cx ss2)
      (s with scopes updated_by CONS FEMPTY) = (r,s') ==>
    contract_storage_well_formed cx s') /\
  well_typed_expr env e /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_stmt cx (If e ss1 ss2) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, push_scope_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (cond_res,cond_st)` >>
  `contract_storage_well_formed cx cond_st` by metis_tac[] >>
  `runtime_consistent env cx cond_st` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `outcome_suffix st.outcomes cond_st.outcomes` by
    (drule (cj 5 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  Cases_on `cond_res` >> gvs[]
  >- (simp[ignore_bind_apply, push_scope_def, return_def] >> strip_tac >>
      qpat_assum `finally _ _ _ = _`
        (mp_then Any mp_tac body_finally_pop_scope_storage) >> simp[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_assert_reason_storage:
  (!r s. eval_expr cx e st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!tv s r s'. eval_expr cx e st = (INL tv,s) /\
    read_result cx tv s = (INL (BoolV F),s) /\
    runtime_storage_consistent env cx s /\ IS_SOME s.outcomes /\
    oracle_storage_ok cx s /\ eval_expr cx se s = (r,s') ==>
    contract_storage_well_formed cx s') /\
  well_typed_expr env e /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_stmt cx (Assert e (AssertReason se)) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,expr_st)` >>
  `contract_storage_well_formed cx expr_st` by metis_tac[] >>
  `runtime_consistent env cx expr_st` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `outcome_suffix st.outcomes expr_st.outcomes` by
    (drule (cj 5 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  Cases_on `expr_res` >> gvs[]
  >- (rename1 `eval_expr cx e st = (INL tv,expr_st)` >>
      simp[switch_BoolV_def, bind_def] >>
      Cases_on `read_result cx tv expr_st` >>
      rename1 `read_result cx tv expr_st = (read_res,read_st)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `read_res` >> gvs[]
      >- (rename1 `read_result cx tv expr_st = (INL v,expr_st)` >>
          Cases_on `v = BoolV F` >> gvs[return_def, raise_def]
          >- (Cases_on `eval_expr cx se expr_st` >>
              rename1 `eval_expr cx se expr_st = (reason_res,reason_st)` >>
              `contract_storage_well_formed cx reason_st` by metis_tac[] >>
              Cases_on `reason_res` >> gvs[bind_def, return_def, raise_def]
              >- (Cases_on `read_result cx x reason_st` >>
                  imp_res_tac read_result_state >> gvs[] >>
                  rpt strip_tac >>
                  gvs[AllCaseEqs(), return_def, raise_def] >>
                  imp_res_tac lift_option_type_state >> gvs[]) >>
              rpt strip_tac >> gvs[]) >>
          Cases_on `v = BoolV T` >> gvs[return_def, raise_def] >>
          rpt strip_tac >> gvs[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_assign_base_write_storage:
  well_typed_target env bt tty /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_result_typed (env,cx,st) pv (Type ty) /\ live_memory_result st pv /\
  type_widens_to env.type_defs ty tty /\
  eval_target_place cx bt st = (INL p,target_st) /\
  contract_storage_well_formed cx target_st /\
  (do v <- read_result cx pv; write_place cx p v od) target_st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  `typed_scope_transition st target_st` by
    (fs[runtime_consistent_def] >>
     drule_all (cj 2 (SPEC_ALL (cj 8
       vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))) >> simp[]) >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame st target_st` by
    (drule (cj 8 vyperImmutableMetadataFrameTheory.eval_metadata_frame_mutual) >> simp[]) >>
  `eval_result_typed (env,cx,target_st) pv (Type ty)` by
    (Cases_on `pv` >> gvs[eval_result_typed_def] >>
     metis_tac[vyperTypeEvalSoundnessTheory.runtime_place_typed_transport]) >>
  `live_memory_result target_st pv` by
    (irule vyperTypeEvalSoundnessTheory.live_result_transport >> qexists_tac `st` >> simp[]) >>
  `runtime_consistent env cx target_st` by
    (fs[runtime_consistent_def] >>
     metis_tac[cj 1 (SPEC_ALL (cj 8
       vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))]) >>
  qpat_x_assum `do _ od _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `read_result cx pv target_st` >>
  rename1 `read_result cx pv target_st = (read_res,read_st)` >>
  imp_res_tac read_result_state >> gvs[] >>
  Cases_on `read_res` >> gvs[]
  >- (rename1 `read_result cx pv target_st = (INL v,target_st)` >>
      `value_runtime_typed env ty v` by
        (fs[runtime_consistent_def] >>
         drule_all vyperTypeEvalSoundnessTheory.read_live_result_success_type >> simp[]) >>
      `value_runtime_typed env tty v` by
        (fs[value_runtime_typed_def] >>
         drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> simp[]) >>
      drule eval_target_place_region >> strip_tac >>
      strip_tac >>
      `storage_layout_safe cx` by
        metis_tac[runtime_storage_consistent_layout] >>
      gvs[eval_result_typed_def, value_runtime_typed_def] >>
      drule_all write_place_preserves_contract_storage >> simp[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_assign_base_storage:
  (!r s. eval_expr cx e st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!pv s r s'. eval_expr cx e st = (INL pv,s) /\
    runtime_storage_consistent env cx s /\ IS_SOME s.outcomes /\
    oracle_storage_ok cx s /\ eval_target_place cx bt s = (r,s') ==>
    contract_storage_well_formed cx s') /\
  well_typed_expr env e /\ well_typed_target env bt tty /\
  type_widens_to env.type_defs (expr_type e) tty /\
  runtime_storage_consistent env cx st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_stmt cx (Assign (BaseTarget bt) e) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (rhs_res,rhs_st)` >>
  `contract_storage_well_formed cx rhs_st` by metis_tac[] >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx rhs_st` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  `outcome_suffix st.outcomes rhs_st.outcomes` by
    (drule (cj 5 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  Cases_on `rhs_res` >> gvs[]
  >- (drule_all eval_expr_success_storage_facts >> strip_tac >>
      Cases_on `eval_target_place cx bt rhs_st` >>
      rename1 `eval_target_place cx bt rhs_st = (target_res,target_st)` >>
      `contract_storage_well_formed cx target_st` by metis_tac[] >>
      Cases_on `target_res` >> gvs[]
      >- (strip_tac >>
          qpat_assum `do _ od _ = _`
            (mp_then Any mp_tac body_assign_base_write_storage) >> simp[] >>
          simp[bind_def] >> disch_then drule_all >> simp[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_eval_assign_tuple_storage:
  (!r s. eval_expr cx e st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!tv v s r s'. eval_expr cx e st = (INL tv,s) /\
    read_result cx tv s = (INL v,s) /\
    runtime_storage_consistent env cx s /\ IS_SOME s.outcomes /\
    oracle_storage_ok cx s /\ value_runtime_typed env (expr_type e) v /\
    assign_tuple_targets cx (TupleTarget gs) v s = (r,s') ==>
    contract_storage_well_formed cx s') /\
  well_typed_expr env e /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_stmt cx (Assign (TupleTarget gs) e) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (rhs_res,rhs_st)` >>
  `contract_storage_well_formed cx rhs_st` by metis_tac[] >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx rhs_st` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  `outcome_suffix st.outcomes rhs_st.outcomes` by
    (drule (cj 5 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  Cases_on `rhs_res` >> gvs[]
  >- (drule_all eval_expr_success_storage_facts >> strip_tac >>
      rename1 `eval_expr cx e st = (INL tv,rhs_st)` >>
      Cases_on `read_result cx tv rhs_st` >>
      rename1 `read_result cx tv rhs_st = (read_res,read_st)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `read_res` >> gvs[]
      >- (rename1 `read_result cx tv rhs_st = (INL v,rhs_st)` >>
          `value_runtime_typed env (expr_type e) v` by
            (fs[runtime_consistent_def] >>
             drule_all vyperTypeEvalSoundnessTheory.read_live_result_success_type >>
             simp[]) >>
          strip_tac >> first_x_assum drule_all >> simp[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_assign_tuple_base_storage:
  (!r s. eval_target_place cx bt st = (r,s) ==>
    contract_storage_well_formed cx s) /\
  well_typed_target env bt ty /\ value_runtime_typed env ty v /\
  runtime_storage_consistent env cx st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_target bt) /\
  assign_tuple_targets cx (BaseTarget bt) v st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,target_st)` >>
  `contract_storage_well_formed cx target_st` by metis_tac[] >>
  Cases_on `target_res` >> gvs[]
  >- (`runtime_consistent env cx st` by
        metis_tac[runtime_storage_consistent_runtime] >>
      drule_all eval_target_place_success_storage_type >> strip_tac >>
      drule eval_target_place_region >> strip_tac >>
      `storage_layout_safe cx` by metis_tac[runtime_storage_consistent_layout] >>
      strip_tac >>
      gvs[eval_result_typed_def, value_runtime_typed_def] >>
      drule_all write_place_preserves_contract_storage >> simp[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_assign_tuple_cons_storage:
  (!r s. assign_tuple_targets cx g v st = (r,s) ==>
    contract_storage_well_formed cx s) /\
  (!s r s'. assign_tuple_targets cx g v st = (INL (),s) /\
    runtime_storage_consistent env cx s /\ IS_SOME s.outcomes /\
    oracle_storage_ok cx s /\ assign_tuple_target_list cx gs vs s = (r,s') ==>
    contract_storage_well_formed cx s') /\
  well_typed_atarget env g ty /\ value_runtime_typed env ty v /\
  runtime_storage_consistent env cx st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_atarget g) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  assign_tuple_target_list cx (g::gs) (v::vs) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `assign_tuple_target_list _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, ignore_bind_apply] >>
  Cases_on `assign_tuple_targets cx g v st` >>
  rename1 `assign_tuple_targets cx g v st = (head_res,head_st)` >>
  `contract_storage_well_formed cx head_st` by metis_tac[] >>
  `runtime_consistent env cx head_st` by
    (fs[runtime_consistent_def, runtime_storage_consistent_def] >>
     metis_tac[cj 9 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual]) >>
  `outcome_suffix st.outcomes head_st.outcomes` by
    (drule (cj 9 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  Cases_on `head_res` >> gvs[]
  >> rpt strip_tac >> gvs[]
QED


Theorem body_try_handle_function_predicate:
  (!r s. f st = (r,s) ==> P s) /\
  try (do f; return NoneV od) handle_function st = (res,st') ==> P st'
Proof
  strip_tac >> Cases_on `f st` >> rename1 `f st = (body_res,body_st)` >>
  `P body_st` by metis_tac[] >>
  Cases_on `body_res` >>
  gvs[try_def, ignore_bind_apply, return_def, raise_def] >>
  Cases_on `y` >> gvs[handle_function_def, return_def, raise_def]
QED

Theorem body_intcall_cleanup_storage:
  contract_storage_well_formed cx st /\ storage_layout_safe cx /\
  (do pop_function prev; unlock_if_nr cx nr is_view od) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  `contract_storage_well_formed cx (st with scopes := prev)` by
    (irule contract_storage_well_formed_backends_frame >>
     qexists_tac `st` >> simp[]) >>
  Cases_on `nr /\ ~is_view` >>
  gvs[unlock_if_nr_def, pop_function_def, ignore_bind_apply, set_scopes_def,
      return_def]
  >- (Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
      drule_all release_nonreentrant_lock_preserves_contract_storage_well_formed >>
      simp[])
QED

Theorem body_intcall_finally_storage:
  (!r s. eval_stmts cxf ss st = (r,s) ==> contract_storage_well_formed cx s) /\
  storage_layout_safe cx /\
  finally (try (do eval_stmts cxf ss; return NoneV od) handle_function)
    (do pop_function prev; unlock_if_nr cx nr is_view od) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [finally_def] >>
  Cases_on `try (do eval_stmts cxf ss; return NoneV od) handle_function st` >>
  rename1 `try _ _ st = (body_res,body_st)` >>
  `contract_storage_well_formed cx body_st` by
    (qpat_assum `try _ _ st = _`
       (mp_then Any mp_tac body_try_handle_function_predicate) >>
     disch_then irule >> simp[]) >>
  Cases_on `(do pop_function prev; unlock_if_nr cx nr is_view od) body_st` >>
  rename1 `(do pop_function prev; unlock_if_nr cx nr is_view od) body_st =
               (cleanup_res,cleanup_st)` >>
  `contract_storage_well_formed cx cleanup_st` by
    (drule_all body_intcall_cleanup_storage >> simp[]) >>
  Cases_on `body_res` >> Cases_on `cleanup_res` >>
  gvs[ignore_bind_apply, bind_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem body_intcall_return_storage:
  (!r s. eval_stmts cxf ss st = (r,s) ==> contract_storage_well_formed cx s) /\
  storage_layout_safe cx /\
  (do rv <- finally
        (try (do eval_stmts cxf ss; return NoneV od) handle_function)
        (do pop_function prev; unlock_if_nr cx nr is_view od);
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv) od) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `do _ od _ = _` mp_tac >>
  simp_tac (srw_ss()) [bind_def] >>
  Cases_on `finally
    (try (do eval_stmts cxf ss; return NoneV od) handle_function)
    (do pop_function prev; unlock_if_nr cx nr is_view od) st` >>
  rename1 `finally _ _ st = (call_res,call_st)` >>
  `contract_storage_well_formed cx call_st` by
    (drule_all body_intcall_finally_storage >> simp[]) >>
  Cases_on `call_res` >> gvs[]
  >- (rpt strip_tac >> gvs[AllCaseEqs(), return_def] >>
      imp_res_tac lift_option_type_state >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_intcall_lock_storage:
  contract_storage_well_formed cx st /\ storage_layout_safe cx /\
  lock_if_nr cx nr is_view st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> Cases_on `nr` >> gvs[lock_if_nr_def, return_def]
  >- (Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
      gvs[ignore_bind_def, bind_def, AllCaseEqs()] >>
      drule_all acquire_nonreentrant_lock_preserves_contract_storage_well_formed >>
      Cases_on `is_view` >> gvs[return_def])
QED

Theorem body_intcall_lock_oracle_entry:
  contract_storage_well_formed cx st /\ storage_layout_safe cx /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  lock_if_nr cx nr is_view st = (res,st') ==>
  contract_storage_well_formed cx st' /\ IS_SOME st'.outcomes /\
  oracle_storage_ok cx st'
Proof
  strip_tac >>
  `contract_storage_well_formed cx st'` by
    (drule_all body_intcall_lock_storage >> simp[]) >>
  `st'.outcomes = st.outcomes` by
    (Cases_on `nr` >>
     gvs[lock_if_nr_def, return_def] >>
     Cases_on `cx.nonreentrant_slot` >>
     gvs[raise_def, ignore_bind_def, bind_def, acquire_nonreentrant_lock_eq,
         AllCaseEqs()] >>
     gvs[return_def, COND_RATOR, AllCaseEqs()]) >>
  gvs[oracle_storage_ok_payload]
QED


Theorem body_assign_base_consumer:
  (!s0 pv s1. eval_expr cx e s0 = (INL pv,s1) ==>
    !tops env ty st res st'.
      well_typed_target env bt ty /\ supported_program tops /\
      get_module_code cx NONE = SOME tops /\
      ~supported_target_exists expr_evm_run_root bt /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_target bt) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_target bt) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_target_place cx bt st = (res,st') ==>
      contract_storage_well_formed cx st') /\
  (!tops env st res st'.
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr e) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_expr cx e st = (res,st') ==>
      (well_typed_expr env e ==> contract_storage_well_formed cx st') /\
      (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st')) ==>
  !tops env ret_ty env' st res st'.
    type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmt_expr_exists expr_evm_run_root (Assign (BaseTarget bt) e) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt (Assign (BaseTarget bt) e)) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget bt) e)) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx (Assign (BaseTarget bt) e) st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
  gvs[int_calls_stmt_def, int_calls_atarget_def,
      supported_stmt_expr_exists_def, supported_assignment_exists_def,
      expr_has_evm_run_def] >>
  Cases_on `type_place_target env bt` >> gvs[] >>
  rename1 `type_place_target env bt = SOME vt` >> Cases_on `vt` >> gvs[] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_assum `eval_stmt _ _ _ = _`
    (mp_then Any mp_tac body_eval_assign_base_storage) >>
  disch_then irule >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  rename1 `type_place_target env bt = SOME (Type tty)` >>
  qexistsl_tac [`env`, `tty`] >> simp[well_typed_target_def] >>
  rpt strip_tac >>
  qpat_x_assum `!s0 pv s1. eval_expr _ _ _ = _ ==> _` drule >>
  disch_then irule >> simp[] >>
  qexistsl_tac [`env`, `r`, `s`, `tty`] >> simp[well_typed_target_def]
QED

Theorem body_if_consumer:
  (!s0 tv s1 s2 x s3.
    eval_expr cx e s0 = (INL tv,s1) /\ push_scope s2 = (INL x,s3) ==>
    !tops env ret_ty env' st res st'.
      type_stmts env ret_ty ss1 = SOME env' /\
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~supported_stmts_expr_exists expr_evm_run_root ss1 /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts ss1) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_stmts ss1) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_stmts cx ss1 st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!s0 tv s1 s2 x s3.
    eval_expr cx e s0 = (INL tv,s1) /\ push_scope s2 = (INL x,s3) ==>
    !tops env ret_ty env' st res st'.
      type_stmts env ret_ty ss2 = SOME env' /\
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~supported_stmts_expr_exists expr_evm_run_root ss2 /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts ss2) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_stmts ss2) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_stmts cx ss2 st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!tops env st res st'.
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr e) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_expr cx e st = (res,st') ==>
      (well_typed_expr env e ==> contract_storage_well_formed cx st') /\
      (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st')) ==>
  !tops env ret_ty env' st res st'.
    type_stmt env ret_ty (If e ss1 ss2) = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmt_expr_exists expr_evm_run_root (If e ss1 ss2) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt (If e ss1 ss2)) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (If e ss1 ss2)) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx (If e ss1 ss2) st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, AllCaseEqs()] >>
  Cases_on `type_stmts env ret_ty ss1` >> gvs[] >>
  Cases_on `type_stmts env ret_ty ss2` >> gvs[] >>
  gvs[int_calls_stmt_def, supported_stmt_expr_exists_def, expr_has_evm_run_def] >>
  `call_evaluation_safe cx (int_calls_stmts ss2)` by
    metis_tac[call_evaluation_safe_append_right] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  qpat_assum `eval_stmt _ _ _ = _`
    (mp_then Any mp_tac body_eval_if_stmt_storage) >>
  disch_then irule >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  qexists_tac `env` >> simp[] >> rpt strip_tac >>
  qpat_assum `switch_BoolV _ _ _ _ _ = _`
    (mp_then Any mp_tac body_scoped_switch_storage) >>
  disch_then irule >> simp[] >>
  qexists_tac `env` >> simp[] >>
  qpat_x_assum `!s0 tv s1 s2 s3. _ /\ _ ==> _`
    (qspecl_then [`st`, `tv`, `s`, `s`, `s with scopes updated_by CONS FEMPTY`] mp_tac) >>
  simp[push_scope_def, return_def] >> strip_tac >>
  qpat_x_assum `!s0 tv s1 s2 s3. _ /\ _ ==> _`
    (qspecl_then [`st`, `tv`, `s`, `s`, `s with scopes updated_by CONS FEMPTY`] mp_tac) >>
  simp[push_scope_def, return_def] >> strip_tac >>
  conj_tac >> rpt strip_tac >>
  `IS_SOME (s with scopes updated_by CONS FEMPTY).outcomes` by simp[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem body_append_write_storage:
  well_typed_expr env e /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  eval_result_typed (env,cx,st) (PlaceR p) (Type (ArrayT elem_ty (Dynamic n))) /\
  storage_place_region cx p /\ type_widens_to env.type_defs (expr_type e) elem_ty /\
  eval_expr cx e st = (INL pv,st1) /\ contract_storage_well_formed cx st1 /\
  (do v <- read_result cx pv; append_place cx p v od) st1 = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  `typed_scope_transition st st1` by
    (fs[runtime_consistent_def] >>
     qspecl_then [`cx`,`e`] strip_assume_tac
       (cj 5 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual) >>
     qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
       (qspecl_then [`env`,`st`,`INL pv`,`st1`] mp_tac) >> simp[]) >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame st st1` by
    (drule (cj 5 vyperImmutableMetadataFrameTheory.eval_metadata_frame_mutual) >> simp[]) >>
  `?elem_tv. evaluate_type env.type_defs elem_ty = SOME elem_tv /\
     runtime_place_typed cx st p (ArrayTV elem_tv (Dynamic n))` by
    gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
  `runtime_place_typed cx st1 p (ArrayTV elem_tv (Dynamic n))` by
    (drule_all vyperTypeEvalSoundnessTheory.runtime_place_typed_transport >> simp[]) >>
  qpat_x_assum `do _ od _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `read_result cx pv st1` >>
  rename1 `read_result cx pv st1 = (read_res,read_st)` >>
  imp_res_tac read_result_state >> gvs[] >>
  Cases_on `read_res` >> gvs[]
  >- (rename1 `read_result cx pv st1 = (INL v,st1)` >>
      `value_runtime_typed env (expr_type e) v` by
        (fs[runtime_consistent_def] >>
         drule_all vyperTypeEvalSoundnessTheory.read_live_result_success_type >> simp[]) >>
      strip_tac >>
      `value_has_type elem_tv v` by
        (gvs[value_runtime_typed_def] >>
         drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
         strip_tac >> gvs[]) >>
      `storage_layout_safe cx` by metis_tac[runtime_storage_consistent_layout] >>
      gvs[bind_def] >>
      drule_all append_place_preserves_contract_storage >> simp[]) >>
  rpt strip_tac >> gvs[bind_def]
QED

Theorem body_eval_append_storage:
  (!r s. eval_target_place cx bt st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!p s r s'. eval_target_place cx bt st = (INL p,s) /\
    runtime_storage_consistent env cx s /\ IS_SOME s.outcomes /\
    oracle_storage_ok cx s /\ eval_expr cx e s = (r,s') ==>
    contract_storage_well_formed cx s') /\
  well_typed_target env bt (ArrayT elem_ty (Dynamic n)) /\ well_typed_expr env e /\
  type_widens_to env.type_defs (expr_type e) elem_ty /\
  runtime_storage_consistent env cx st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_stmt cx (Append bt e) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,target_st)` >>
  `contract_storage_well_formed cx target_st` by metis_tac[] >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx target_st` by
    (fs[runtime_consistent_def] >>
     metis_tac[cj 1 (SPEC_ALL (cj 8
       vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))]) >>
  `outcome_suffix st.outcomes target_st.outcomes` by
    (drule (cj 8 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  Cases_on `target_res` >> gvs[]
  >- (drule_all eval_target_place_success_storage_type >> strip_tac >>
      drule eval_target_place_region >> strip_tac >>
      Cases_on `eval_expr cx e target_st` >>
      rename1 `eval_expr cx e target_st = (rhs_res,rhs_st)` >>
      `contract_storage_well_formed cx rhs_st` by metis_tac[] >>
      Cases_on `rhs_res` >> gvs[]
      >- (strip_tac >>
          qpat_assum `do _ od _ = _`
            (mp_then Any mp_tac body_append_write_storage) >>
          simp[bind_def] >> disch_then irule >>
          qexistsl_tac [`elem_ty`, `env`, `n`, `x`, `res`] >> simp[] >>
          qexists_tac `tv` >> simp[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem body_append_consumer:
  (!s0 p s1. eval_target_place cx bt s0 = (INL p,s1) ==>
    !tops env st res st'.
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr e) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_expr cx e st = (res,st') ==>
      (well_typed_expr env e ==> contract_storage_well_formed cx st') /\
      (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st')) /\
  (!tops env ty st res st'.
      well_typed_target env bt ty /\ supported_program tops /\
      get_module_code cx NONE = SOME tops /\
      ~supported_target_exists expr_evm_run_root bt /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_target bt) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_target bt) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_target_place cx bt st = (res,st') ==>
      contract_storage_well_formed cx st') ==>
  !tops env ret_ty env' st res st'.
    type_stmt env ret_ty (Append bt e) = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmt_expr_exists expr_evm_run_root (Append bt e) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt (Append bt e)) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (Append bt e)) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx (Append bt e) st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once type_stmt_def] >>
  Cases_on `type_place_target env bt` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME vt` >> Cases_on `vt` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type ty)` >> Cases_on `ty` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty bd))` >>
  Cases_on `bd` >> simp[NoAsms] >> strip_tac >> gvs[] >>
  gvs[int_calls_stmt_def, supported_stmt_expr_exists_def, expr_has_evm_run_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_assum `eval_stmt _ _ _ = _`
    (mp_then Any mp_tac body_eval_append_storage) >>
  disch_then irule >> simp[] >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty (Dynamic n)))` >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[] >>
      qexistsl_tac [`env`, `r`, `st`, `ArrayT elem_ty (Dynamic n)`] >>
      simp[well_typed_target_def]) >>
  qexistsl_tac [`elem_ty`, `env`, `n`] >> simp[well_typed_target_def] >>
  rpt strip_tac >>
  qpat_x_assum `!s0 p s1. eval_target_place _ _ _ = _ ==> _` drule >>
  disch_then drule_all >> simp[]
QED

Theorem body_augassign_rhs_storage:
  well_typed_expr env e /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  runtime_place_typed cx st p ptv /\ storage_place_region cx p /\
  evaluate_type env.type_defs ty = SOME ptv /\ value_has_type ptv cur /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  eval_expr cx e st = (INL rhs,st1) /\ contract_storage_well_formed cx st1 /\
  (do v <- read_result cx rhs;
      result <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0) ptv bop cur v);
      write_place cx p result od) st1 = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  `typed_scope_transition st st1` by
    (fs[runtime_consistent_def] >>
     qspecl_then [`cx`,`e`] strip_assume_tac
       (cj 5 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual) >>
     qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
       (qspecl_then [`env`,`st`,`INL rhs`,`st1`] mp_tac) >> simp[]) >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame st st1` by
    (drule (cj 5 vyperImmutableMetadataFrameTheory.eval_metadata_frame_mutual) >> simp[]) >>
  `runtime_place_typed cx st1 p ptv` by
    (drule_all vyperTypeEvalSoundnessTheory.runtime_place_typed_transport >> simp[]) >>
  `storage_layout_safe cx` by metis_tac[runtime_storage_consistent_layout] >>
  `state_well_typed st1` by gvs[runtime_consistent_def] >>
  drule_all update_place_tail_preserves_storage >> simp[]
QED

Theorem body_eval_augassign_storage:
  (!r s. eval_target_place cx bt st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!p s cur ptv r s'. eval_target_place cx bt st = (INL p,s) /\
    read_place cx p s = (INL cur,s) /\ place_type_value cx p s = (INL ptv,s) /\
    runtime_storage_consistent env cx s /\ IS_SOME s.outcomes /\
    oracle_storage_ok cx s /\ eval_expr cx e s = (r,s') ==>
    contract_storage_well_formed cx s') /\
  well_typed_target env bt ty /\ well_typed_expr env e /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  runtime_storage_consistent env cx st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_stmt cx (AugAssign ty bt bop e) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,target_st)` >>
  `contract_storage_well_formed cx target_st` by metis_tac[] >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx target_st` by
    (fs[runtime_consistent_def] >>
     metis_tac[cj 1 (SPEC_ALL (cj 8
       vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))]) >>
  `outcome_suffix st.outcomes target_st.outcomes` by
    (drule (cj 8 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  reverse (Cases_on `target_res`) >- (simp[] >> strip_tac >> gvs[]) >>
  rename1 `eval_target_place cx bt st = (INL p,target_st)` >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  `live_memory_result target_st (PlaceR p)` by
    (fs[runtime_consistent_def] >>
     qspecl_then [`cx`,`bt`] strip_assume_tac
       (cj 8 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual) >>
     qpat_x_assum `!env ty st res st'. _ ==> (case _ of INL p => live_memory_result _ _ | INR _ => T)`
       (qspecl_then [`env`,`ty`,`st`,`INL p`,`target_st`] mp_tac) >> simp[]) >>
  gvs[eval_result_typed_def] >>
  `place_type_value cx p target_st = (INL tv,target_st)` by
    gvs[runtime_place_typed_def] >>
  `state_well_typed target_st` by gvs[runtime_consistent_def] >>
  simp_tac (srw_ss()) [] >> Cases_on `read_place cx p target_st` >>
  rename1 `read_place cx p target_st = (read_res,read_st)` >>
  drule_all vyperTypeEvalSoundnessTheory.live_place_read_sound >> strip_tac >> gvs[] >>
  reverse (Cases_on `read_res`) >- (simp[] >> strip_tac >> gvs[]) >>
  suspend "rhs"
QED

Resume body_eval_augassign_storage[rhs]:
  gvs[] >>
  Cases_on `eval_expr cx e read_st` >>
  rename1 `eval_expr cx e read_st = (rhs_res,rhs_st)` >>
  `contract_storage_well_formed cx rhs_st` by metis_tac[] >>
  reverse (Cases_on `rhs_res`) >- (simp[] >> strip_tac >> gvs[]) >>
  rename1 `eval_expr cx e read_st = (INL rhs,rhs_st)` >>
  drule eval_target_place_region >> strip_tac >>
  simp[] >> strip_tac >>
  qpat_assum `eval_expr _ _ _ = _`
    (mp_then Any mp_tac body_augassign_rhs_storage) >>
  simp[bind_def] >> disch_then irule >>
  qexistsl_tac [`bop`, `x`, `env`, `p`, `tv`, `res`, `ty`] >> gvs[bind_def]
QED
Finalise body_eval_augassign_storage

Theorem body_augassign_consumer:
  (!s0 p s1 s2 cur s3 s4 ptv s5.
    eval_target_place cx bt s0 = (INL p,s1) /\
    read_place cx p s2 = (INL cur,s3) /\ place_type_value cx p s4 = (INL ptv,s5) ==>
    !tops env st res st'.
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr e) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_expr cx e st = (res,st') ==>
      (well_typed_expr env e ==> contract_storage_well_formed cx st') /\
      (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st')) /\
  (!tops env ty st res st'.
      well_typed_target env bt ty /\ supported_program tops /\
      get_module_code cx NONE = SOME tops /\
      ~supported_target_exists expr_evm_run_root bt /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_target bt) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_target bt) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_target_place cx bt st = (res,st') ==>
      contract_storage_well_formed cx st') ==>
  !tops env ret_ty env' st res st'.
    type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmt_expr_exists expr_evm_run_root (AugAssign ty bt bop e) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt (AugAssign ty bt bop e)) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty bt bop e)) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx (AugAssign ty bt bop e) st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, int_calls_stmt_def,
      supported_stmt_expr_exists_def, expr_has_evm_run_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_assum `eval_stmt _ _ _ = _`
    (mp_then Any mp_tac body_eval_augassign_storage) >>
  disch_then irule >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  qexists_tac `env` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!s0 p s1 s2 cur s3 s4 ptv s5. _ ==> _` drule_all >> simp[]
QED

Theorem body_eval_raise_custom_storage:
  contract_storage_well_formed cx st /\
  (!id positional kwargs decls params es r s.
    err = CustomError id positional kwargs /\
    get_module_code cx (FST id) = SOME decls /\
    lookup_custom_error_args_in (SND id) decls = SOME params /\
    order_custom_error_args params err = SOME es /\
    eval_exprs cx es st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_stmt cx (Raise (RaiseCustomError err)) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> Cases_on `err` >>
  rename1 `CustomError id positional kwargs` >>
  Cases_on `get_module_code cx (FST id)`
  >- gvs[Once evaluate_def, raise_def] >>
  rename1 `get_module_code cx (FST id) = SOME decls` >>
  Cases_on `lookup_custom_error_args_in (SND id) decls`
  >- gvs[Once evaluate_def, raise_def] >>
  rename1 `lookup_custom_error_args_in (SND id) decls = SOME params` >>
  Cases_on `order_custom_error_args params (CustomError id positional kwargs)`
  >- gvs[Once evaluate_def, raise_def] >>
  rename1 `order_custom_error_args params _ = SOME es` >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,st1)` >>
  `contract_storage_well_formed cx st1` by
    (first_x_assum irule >> metis_tac[]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `args_res` >> simp[raise_def] >>
  Cases_on `build_custom_error_data (get_tenv cx) (SND id) (MAP SND params) x` >>
  gvs[lift_option_def, bind_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem body_exprs_main_calls_every:
  !P es. EVERY P (int_calls_exprs es) <=>
         EVERY (\e. EVERY P (int_calls_expr e)) es
Proof
  Induct_on `es` >> simp[int_calls_expr_def]
QED

Theorem body_exprs_syntax_perm:
  PERM xs ys /\ ~supported_exprs_exists expr_evm_run_root xs /\
  EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs xs) ==>
  ~supported_exprs_exists expr_evm_run_root ys /\
  EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs ys)
Proof
  pure_rewrite_tac[supported_exprs_exists_every, body_exprs_main_calls_every,
                   EXISTS_MEM, EVERY_MEM] >>
  rpt strip_tac >> drule sortingTheory.PERM_MEM_EQ >>
  strip_tac >> metis_tac[]
QED

Theorem body_raise_custom_consumer:
  (!id positional kwargs decls params es.
    err = CustomError id positional kwargs /\
    get_module_code cx (FST id) = SOME decls /\
    lookup_custom_error_args_in (SND id) decls = SOME params /\
    order_custom_error_args params err = SOME es ==>
    !tops env st res st'.
      well_typed_exprs env es /\ supported_program tops /\
      get_module_code cx NONE = SOME tops /\
      ~supported_exprs_exists expr_evm_run_root es /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs es) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_exprs es) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_exprs cx es st = (res,st') ==> contract_storage_well_formed cx st') ==>
  !tops env ret_ty env' st res st'.
    type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmt_expr_exists expr_evm_run_root (Raise (RaiseCustomError err)) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt (Raise (RaiseCustomError err))) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err))) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx (Raise (RaiseCustomError err)) st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, well_typed_custom_error_def,
      supported_stmt_expr_exists_def, supported_raise_exists_def,
      int_calls_stmt_def, int_calls_raise_reason_def] >>
  qpat_assum `eval_stmt _ _ _ = _`
    (mp_then (Pos last) mp_tac body_eval_raise_custom_storage) >>
  disch_then irule >>
  reverse conj_tac >- metis_tac[runtime_storage_consistent_def] >>
  rpt gen_tac >> strip_tac >>
  `PERM (custom_error_exprs err) es` by
    (drule order_custom_error_args_perm >> simp[]) >>
  `well_typed_exprs env es` by metis_tac[vyperTypeEvalSoundnessTheory.well_typed_exprs_perm] >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    metis_tac[vyperTypeEvalSoundnessTheory.call_evaluation_safe_exprs_perm] >>
  `~supported_exprs_exists expr_evm_run_root (custom_error_exprs err)` by
    fs[supported_exprs_exists_every] >>
  drule_all body_exprs_syntax_perm >> strip_tac >>
  qpat_x_assum `!id positional kwargs decls params es. _` drule_all >> simp[]
QED

Theorem body_assert_custom_unfold:
  eval_stmt cx (Assert e (AssertCustomError err)) =
  bind (eval_expr cx e) (\tv.
    switch_BoolV cx tv (return ())
      (eval_stmt cx (Raise (RaiseCustomError err))))
Proof
  simp[Once evaluate_def] >> simp[Once evaluate_def]
QED

Theorem body_eval_assert_custom_storage:
  (!r s. eval_expr cx e st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!tv s r s'. eval_expr cx e st = (INL tv,s) /\
     eval_stmt cx (Raise (RaiseCustomError err)) s = (r,s') ==>
     contract_storage_well_formed cx s') /\
  eval_stmt cx (Assert e (AssertCustomError err)) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[body_assert_custom_unfold, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  `contract_storage_well_formed cx st1` by metis_tac[] >>
  reverse (Cases_on `expr_res`)
  >- (simp[raise_def] >> rpt strip_tac >> gvs[]) >>
  rename1 `eval_expr cx e st = (INL tv,st1)` >>
  simp[switch_BoolV_def, bind_def] >>
  Cases_on `read_result cx tv st1` >>
  rename1 `read_result cx tv st1 = (read_res,st2)` >>
  imp_res_tac read_result_state >> gvs[] >>
  reverse (Cases_on `read_res`)
  >- (simp[raise_def] >> rpt strip_tac >> gvs[]) >>
  rename1 `read_result cx tv st1 = (INL v,st1)` >>
  Cases_on `v = BoolV T` >> simp[return_def] >>
  Cases_on `v = BoolV F` >> simp[raise_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem body_assert_custom_consumer:
  (!s0 tv s1 id positional kwargs decls params es.
    eval_expr cx e s0 = (INL tv,s1) /\ err = CustomError id positional kwargs /\
    get_module_code cx (FST id) = SOME decls /\
    lookup_custom_error_args_in (SND id) decls = SOME params /\
    order_custom_error_args params err = SOME es ==>
    !tops env st res st'.
      well_typed_exprs env es /\ supported_program tops /\
      get_module_code cx NONE = SOME tops /\
      ~supported_exprs_exists expr_evm_run_root es /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs es) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_exprs es) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_exprs cx es st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!tops env st res st'.
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr e) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_expr cx e st = (res,st') ==>
      (well_typed_expr env e ==> contract_storage_well_formed cx st') /\
      (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st')) ==>
  !tops env ret_ty env' st res st'.
    type_stmt env ret_ty (Assert e (AssertCustomError err)) = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmt_expr_exists expr_evm_run_root (Assert e (AssertCustomError err)) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt (Assert e (AssertCustomError err))) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (Assert e (AssertCustomError err))) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx (Assert e (AssertCustomError err)) st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, supported_stmt_expr_exists_def,
      supported_assert_exists_def, int_calls_stmt_def, int_calls_assert_reason_def,
      expr_has_evm_run_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_assum `eval_stmt _ _ _ = _`
    (mp_then (Pos last) mp_tac body_eval_assert_custom_storage) >>
  disch_then irule >> reverse conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `contract_storage_well_formed cx s` by
    (first_x_assum drule_all >> simp[]) >>
  `runtime_consistent env cx s` by
    metis_tac[eval_expr_preserves_runtime_consistent, runtime_storage_consistent_runtime] >>
  `outcome_suffix st.outcomes s.outcomes` by
    (drule (cj 5 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> strip_tac >>
  qpat_assum `eval_stmt cx (Raise _) _ = _`
    (mp_then (Pos last) mp_tac body_raise_custom_consumer) >>
  disch_then (qspecl_then [`tops`, `env`, `ret_ty`, `env`] irule) >>
  simp[Once type_stmt_def, supported_stmt_expr_exists_def,
       supported_raise_exists_def, int_calls_stmt_def, int_calls_raise_reason_def,
       supported_exprs_exists_every] >>
  reverse conj_tac >- (qexists_tac `env` >> simp[]) >>
  gns[supported_exprs_exists_every] >> rpt strip_tac >>
  qpat_x_assum `!s0 tv s1 id positional kwargs decls params es. _` drule_all >> simp[]
QED

Theorem body_eval_for_nil_storage:
  contract_storage_well_formed cx st /\
  eval_for cx tyv id body_stmts [] st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  simp[Once evaluate_def, return_def] >> rpt strip_tac >> gvs[]
QED

Theorem body_eval_for_entry_storage:
  contract_storage_well_formed cx st /\
  (!r s. eval_iterator cx it st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!tyv vs s r s'. evaluate_type (get_tenv cx) ty = SOME tyv /\
    eval_iterator cx it st = (INL vs,s) /\ compatible_bound (Dynamic n) (LENGTH vs) /\
    eval_for cx tyv id body_stmts vs s = (r,s') ==> contract_storage_well_formed cx s') /\
  eval_stmt cx (For id ty it n body_stmts) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, lift_option_type_def] >>
  Cases_on `evaluate_type (get_tenv cx) ty`
  >- (simp[bind_def, raise_def] >> rpt strip_tac >> gvs[]) >>
  rename1 `evaluate_type (get_tenv cx) ty = SOME tyv` >>
  simp[bind_def, return_def] >>
  Cases_on `eval_iterator cx it st` >>
  rename1 `eval_iterator cx it st = (iter_res,st1)` >>
  `contract_storage_well_formed cx st1` by metis_tac[] >>
  reverse (Cases_on `iter_res`)
  >- (simp[raise_def] >> rpt strip_tac >> gvs[]) >>
  rename1 `eval_iterator cx it st = (INL vs,st1)` >>
  Cases_on `compatible_bound (Dynamic n) (LENGTH vs)` >>
  simp[check_def, assert_def, ignore_bind_apply, return_def, raise_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem body_iterator_success_entry:
  well_typed_iterator env ty it /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_iterator it) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  contract_storage_well_formed cx st' /\
  eval_iterator cx it st = (INL vs,st') ==>
  runtime_storage_consistent env cx st' /\ IS_SOME st'.outcomes /\
  oracle_storage_ok cx st' /\
  ?tyv. evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs
Proof
  strip_tac >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  `env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
   accounts_well_typed st.accounts` by fs[runtime_consistent_def] >>
  drule_all (cj 3 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual) >>
  strip_tac >>
  `runtime_consistent env cx st'` by simp[runtime_consistent_def] >>
  `outcome_suffix st.outcomes st'.outcomes` by
    (drule (cj 3 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> gvs[]
QED

Theorem body_for_entry_consumer:
  (!tenv s0 tyv t s1 vs t1 s2 x t2.
    tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv ty) "For evaluate_type" s0 = (INL tyv,t) /\
    eval_iterator cx it s1 = (INL vs,t1) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s2 = (INL x,t2) ==>
    !tops env ret_ty ty env_after st res st'.
      evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs /\
      id NOTIN FDOM env.var_types /\
      type_stmts (extend_local env id ty F) ret_ty body_stmts = SOME env_after /\
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~supported_stmts_expr_exists expr_evm_run_root body_stmts /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts body_stmts) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_stmts body_stmts) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_for cx tyv id body_stmts vs st = (res,st') ==>
      contract_storage_well_formed cx st') /\
  (!tenv s0 tyv t. tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv ty) "For evaluate_type" s0 = (INL tyv,t) ==>
    !tops env ty st res st'.
      well_typed_iterator env ty it /\ supported_program tops /\
      get_module_code cx NONE = SOME tops /\
      ~supported_iterator_exists expr_evm_run_root it /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_iterator it) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_iterator it) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_iterator cx it st = (res,st') ==> contract_storage_well_formed cx st') ==>
  !tops env ret_ty env' st res st'.
    type_stmt env ret_ty (For id ty it n body_stmts) = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmt_expr_exists expr_evm_run_root (For id ty it n body_stmts) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt (For id ty it n body_stmts)) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (For id ty it n body_stmts)) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx (For id ty it n body_stmts) st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, supported_stmt_expr_exists_def, int_calls_stmt_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `evaluate_type (get_tenv cx) ty`
  >- (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, lift_option_type_def, bind_def, raise_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[runtime_storage_consistent_storage]) >>
  gns[lift_option_type_def, return_def, check_def, assert_def,
      raise_def, AllCaseEqs()] >>
  qpat_assum `eval_stmt _ _ _ = _`
    (mp_then (Pos last) mp_tac body_eval_for_entry_storage) >>
  disch_then irule >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  reverse conj_tac
  >- metis_tac[runtime_storage_consistent_storage] >>
  rpt gen_tac >> strip_tac >>
  `contract_storage_well_formed cx s` by
    (first_x_assum drule_all >> simp[]) >>
  drule_all body_iterator_success_entry >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[runtime_storage_consistent_def, runtime_consistent_def,
       env_consistent_def, env_context_consistent_def] >>
  gvs[] >>
  qpat_x_assum `IS_SOME (type_stmts _ _ _)` mp_tac >>
  rewrite_tac[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qpat_x_assum `!s1 vs t1. eval_iterator _ _ _ = _ /\ _ ==> _`
    (qspecl_then [`st`, `vs`, `s`] mp_tac) >>
  simp[] >> disch_then irule >> simp[] >> metis_tac[]
QED

Theorem body_push_loop_var_entry:
  runtime_storage_consistent env cx st /\
  evaluate_type env.type_defs ty = SOME tyv /\ value_has_type tyv v /\
  id NOTIN FDOM env.var_types /\ IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  push_scope_with_var id tyv v st = (INL (),stp) ==>
  runtime_storage_consistent (extend_local env id ty F) cx stp /\
  IS_SOME stp.outcomes /\ oracle_storage_ok cx stp
Proof
  strip_tac >>
  qpat_x_assum `push_scope_with_var _ _ _ _ = _` mp_tac >>
  simp[push_scope_with_var_def, return_def] >> strip_tac >> gvs[] >>
  `well_formed_type_value tyv` by metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  `env_consistent env cx st` by fs[runtime_consistent_def] >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  qmatch_goalsub_abbrev_tac `runtime_storage_consistent _ cx pushed` >>
  `env_consistent (extend_local env id ty F) cx pushed` by
    (simp[Abbr `pushed`] >> irule vyperTypeEnvPreservationTheory.push_scope_with_var_env_consistent >> metis_tac[]) >>
  `state_well_typed pushed` by
    fs[Abbr `pushed`, runtime_consistent_def, state_well_typed_def,
       scope_well_typed_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `runtime_consistent (extend_local env id ty F) cx pushed` by
    (simp[runtime_consistent_def] >> fs[Abbr `pushed`, runtime_consistent_def]) >>
  `contract_storage_well_formed cx st` by
    metis_tac[runtime_storage_consistent_storage] >>
  `contract_storage_well_formed cx pushed` by
    (irule contract_storage_well_formed_backends_frame >> qexists_tac `st` >>
     simp[Abbr `pushed`]) >>
  conj_tac
  >- metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
  gvs[Abbr `pushed`, oracle_storage_ok_payload]
QED

Theorem body_loop_iteration_storage:
  push_scope_with_var id tyv v st = (INL (),stp) /\
  finally (try (do eval_stmts cx body_stmts; return F od) handle_loop_exception)
    pop_scope stp = (loop_res,sa) /\
  (!r s. eval_stmts cx body_stmts stp = (r,s) ==> contract_storage_well_formed cx s) ==>
  contract_storage_well_formed cx sa /\
  eval_for cx tyv id body_stmts [v] st =
    ((case loop_res of INL b => INL () | INR ex => INR ex),sa)
Proof
  strip_tac >> conj_tac
  >- (qpat_assum `finally _ _ _ = _`
        (mp_then (Pos last) mp_tac body_finally_pop_scope_storage) >>
      disch_then irule >> rpt gen_tac >>
      simp[try_def, ignore_bind_apply] >>
      Cases_on `eval_stmts cx body_stmts stp` >>
      rename1 `eval_stmts cx body_stmts stp = (body_res,body_st)` >>
      `contract_storage_well_formed cx body_st` by metis_tac[] >>
      Cases_on `body_res` >> simp[return_def] >>
      rename1 `eval_stmts cx body_stmts stp = (INR ex,body_st)` >>
      simp[handle_loop_exception_def] >>
      Cases_on `ex = ContinueException` >> simp[return_def] >>
      Cases_on `ex = BreakException` >> simp[return_def, raise_def] >>
      rpt strip_tac >> gvs[]) >>
  simp[Once evaluate_def, ignore_bind_apply] >>
  Cases_on `loop_res` >> simp[bind_def, return_def, Once evaluate_def]
QED

Theorem body_for_restored_entry:
  evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs /\
  id NOTIN FDOM env.var_types /\
  type_stmts (extend_local env id ty F) ret_ty body_stmts = SOME env_after /\
  runtime_storage_consistent env cx st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmts body_stmts) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  contract_storage_well_formed cx st' /\
  eval_for cx tyv id body_stmts vs st = (res,st') ==>
  runtime_storage_consistent env cx st' /\ IS_SOME st'.outcomes /\ oracle_storage_ok cx st'
Proof
  strip_tac >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx st'` by
    (fs[runtime_consistent_def] >>
     drule_all (cj 4 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual) >> simp[]) >>
  `outcome_suffix st.outcomes st'.outcomes` by
    (drule (cj 4 eval_outcome_suffix_mutual) >> simp[]) >>
  drule_all body_oracle_storage_entry_transfer >> simp[]
QED

Theorem body_for_cons_consumer:
  (!s0 x t s1 broke t1.
    push_scope_with_var id tyv v s0 = (INL x,t) /\
    finally (try (do eval_stmts cx body_stmts; return F od) handle_loop_exception)
      pop_scope s1 = (INL broke,t1) /\ ~broke ==>
    !tops env ret_ty ty env_after st res st'.
      evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs /\
      id NOTIN FDOM env.var_types /\
      type_stmts (extend_local env id ty F) ret_ty body_stmts = SOME env_after /\
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~supported_stmts_expr_exists expr_evm_run_root body_stmts /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts body_stmts) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_stmts body_stmts) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_for cx tyv id body_stmts vs st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!s0 x t. push_scope_with_var id tyv v s0 = (INL x,t) ==>
    !tops env ret_ty env_after st res st'.
      type_stmts env ret_ty body_stmts = SOME env_after /\
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~supported_stmts_expr_exists expr_evm_run_root body_stmts /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts body_stmts) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_stmts body_stmts) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_stmts cx body_stmts st = (res,st') ==> contract_storage_well_formed cx st') ==>
  !tops env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) (v::vs) /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body_stmts = SOME env_after /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmts_expr_exists expr_evm_run_root body_stmts /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts body_stmts) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body_stmts) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_for cx tyv id body_stmts (v::vs) st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[EVERY_DEF] >>
  qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def,
    push_scope_with_var_def, return_def] >>
  qmatch_goalsub_abbrev_tac `finally loop_body pop_scope stp` >>
  Cases_on `finally loop_body pop_scope stp` >>
  rename1 `finally loop_body pop_scope stp = (loop_res,sa)` >> strip_tac >>
  `push_scope_with_var id tyv v st = (INL (),stp)` by
    simp[push_scope_with_var_def, return_def, Abbr `stp`] >>
  drule_all body_push_loop_var_entry >> strip_tac >>
  `!r s. eval_stmts cx body_stmts stp = (r,s) ==> contract_storage_well_formed cx s` by
    (rpt strip_tac >>
     qpat_x_assum `!s0 t. push_scope_with_var _ _ _ _ = _ ==> _` drule >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  gvs[Abbr `loop_body`, ignore_bind_def] >>
  drule_all (SRULE [ignore_bind_def] body_loop_iteration_storage) >> strip_tac >>
  `EVERY (value_has_type tyv) [v]` by simp[] >>
  drule_all body_for_restored_entry >> strip_tac >>
  Cases_on `loop_res` >> gvs[bind_def, return_def] >>
  rename1 `finally _ _ stp = (INL broke,sa)` >> Cases_on `broke` >> gvs[return_def] >>
  qpat_x_assum `!s0 t s1 t1. push_scope_with_var _ _ _ _ = _ /\ _ ==> _` drule >>
  simp[] >> disch_then irule >> simp[] >> metis_tac[]
QED

Theorem body_stmts_cons_consumer:
  (!s0 x t. eval_stmt cx stmt s0 = (INL x,t) ==>
    !tops env ret_ty env_after st res st'.
      type_stmts env ret_ty ss = SOME env_after /\
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~supported_stmts_expr_exists expr_evm_run_root ss /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts ss) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_stmts ss) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_stmts cx ss st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!tops env ret_ty env_after st res st'.
      type_stmt env ret_ty stmt = SOME env_after /\
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~supported_stmt_expr_exists expr_evm_run_root stmt /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt stmt) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_stmt stmt) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_stmt cx stmt st = (res,st') ==> contract_storage_well_formed cx st') ==>
  !tops env ret_ty env_after st res st'.
    type_stmts env ret_ty (stmt::ss) = SOME env_after /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmts_expr_exists expr_evm_run_root (stmt::ss) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts (stmt::ss)) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts (stmt::ss)) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmts cx (stmt::ss) st = (res,st') ==> contract_storage_well_formed cx st'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def, AllCaseEqs()] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_assum `eval_stmts _ (_::_) _ = _`
    (mp_then (Pos last) mp_tac body_eval_stmts_cons_storage) >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`env`, `env'`, `ret_ty`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!s0 t. eval_stmt _ _ _ = _ ==> _` drule >>
  disch_then irule >> simp[] >> metis_tac[]
QED

Theorem body_single_expr_stmt_consumer:
  (!tops env st res st'.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr cx e st = (res,st') ==>
    (well_typed_expr env e ==> contract_storage_well_formed cx st') /\
    (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st')) ==>
  !s tops env ret_ty env' st res st'.
    (s = Expr e \/ s = Return (SOME e) \/ s = Raise (RaiseReason e) \/
     s = Assert e AssertBare \/ s = Assert e AssertUnreachable) /\
    type_stmt env ret_ty s = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmt_expr_exists expr_evm_run_root s /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt s) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx s st = (res,st') ==> contract_storage_well_formed cx st'
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, supported_stmt_expr_exists_def,
      supported_raise_exists_def, supported_assert_exists_def, int_calls_stmt_def,
      int_calls_raise_reason_def, int_calls_assert_reason_def, expr_has_evm_run_def,
      supported_expr_exists_def, int_calls_expr_def, AllCaseEqs()] >>
  `!r s. eval_expr cx e st = (r,s) ==> contract_storage_well_formed cx s` by
    (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  metis_tac[body_eval_expr_stmt_storage, body_eval_return_storage,
            body_eval_raise_reason_storage, body_eval_assert_constant_storage]
QED

Theorem body_annassign_consumer:
  (!tenv s0 tyv t. tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s0 = (INL tyv,t) ==>
    !tops env st res st'.
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr e) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_expr cx e st = (res,st') ==>
      (well_typed_expr env e ==> contract_storage_well_formed cx st') /\
      (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st')) ==>
  !tops env ret_ty env' st res st'.
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmt_expr_exists expr_evm_run_root (AnnAssign id typ e) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt (AnnAssign id typ e)) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx (AnnAssign id typ e) st = (res,st') ==> contract_storage_well_formed cx st'
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def, expr_has_evm_run_def, AllCaseEqs()] >>
  qpat_assum `eval_stmt _ _ _ = _`
    (mp_then (Pos last) mp_tac body_eval_annassign_storage) >>
  disch_then irule >> simp[] >> reverse conj_tac
  >- metis_tac[runtime_storage_consistent_storage] >>
  rpt strip_tac >> gvs[optionTheory.IS_SOME_EXISTS] >>
  first_x_assum (qspecl_then [`env`, `st`, `r`, `s`] mp_tac) >> simp[]
QED

Theorem body_log_consumer:
  (!tops env st res st'.
    well_typed_exprs env es /\ supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_exprs_exists expr_evm_run_root es /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs es) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_exprs cx es st = (res,st') ==> contract_storage_well_formed cx st') ==>
  !tops env ret_ty env' st res st'.
    type_stmt env ret_ty (Log id es) = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmt_expr_exists expr_evm_run_root (Log id es) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt (Log id es)) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (Log id es)) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx (Log id es) st = (res,st') ==> contract_storage_well_formed cx st'
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def, AllCaseEqs()] >>
  qpat_assum `eval_stmt _ _ _ = _`
    (mp_then (Pos last) mp_tac body_eval_log_storage) >>
  disch_then irule >> rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem body_terminal_stmt_storage:
  (s = Pass \/ s = Continue \/ s = Break \/ s = Return NONE \/
   s = Raise RaiseBare \/ s = Raise RaiseUnreachable) /\
  contract_storage_well_formed cx st /\ eval_stmt cx s st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> gvs[Once evaluate_def, return_def, raise_def]
QED

Theorem body_stmts_nil_storage:
  contract_storage_well_formed cx st /\ eval_stmts cx [] st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  simp[Once evaluate_def, return_def] >> rpt strip_tac >> gvs[]
QED

Theorem body_array_iterator_consumer:
  (!tops env st res st'.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr cx e st = (res,st') ==>
    (well_typed_expr env e ==> contract_storage_well_formed cx st') /\
    (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st')) ==>
  !tops env ty st res st'.
    well_typed_iterator env ty (Array e) /\ supported_program tops /\
    get_module_code cx NONE = SOME tops /\
    ~supported_iterator_exists expr_evm_run_root (Array e) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_iterator (Array e)) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_iterator (Array e)) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_iterator cx (Array e) st = (res,st') ==> contract_storage_well_formed cx st'
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  gvs[well_typed_iterator_def, supported_iterator_exists_def,
      int_calls_iterator_def, expr_has_evm_run_def] >>
  qpat_assum `eval_iterator _ _ _ = _`
    (mp_then (Pos last) mp_tac body_eval_array_iterator_storage) >>
  disch_then irule >> rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem body_range_iterator_consumer:
  (!s0 tv1 s1 sread v1 s2.
    eval_expr cx e1 s0 = (INL tv1,s1) /\
    read_result cx tv1 sread = (INL v1,s2) ==>
    !tops env st res st'.
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~expr_has_evm_run e2 /\ EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e2) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr e2) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_expr cx e2 st = (res,st') ==>
      (well_typed_expr env e2 ==> contract_storage_well_formed cx st') /\
      (!vt. type_place_expr env e2 = SOME vt ==> contract_storage_well_formed cx st')) /\
  (!tops env st res st'.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~expr_has_evm_run e1 /\ EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e1) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e1) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr cx e1 st = (res,st') ==>
    (well_typed_expr env e1 ==> contract_storage_well_formed cx st') /\
    (!vt. type_place_expr env e1 = SOME vt ==> contract_storage_well_formed cx st')) ==>
  !tops env ty st res st'.
    well_typed_iterator env ty (Range e1 e2) /\ supported_program tops /\
    get_module_code cx NONE = SOME tops /\
    ~supported_iterator_exists expr_evm_run_root (Range e1 e2) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_iterator (Range e1 e2)) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_iterator (Range e1 e2)) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_iterator cx (Range e1 e2) st = (res,st') ==> contract_storage_well_formed cx st'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[well_typed_iterator_def, supported_iterator_exists_def,
      int_calls_iterator_def, expr_has_evm_run_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_assum `eval_iterator _ _ _ = _`
    (mp_then (Pos last) mp_tac body_eval_range_iterator_storage) >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  qexists_tac `env` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!s0 tv1 s1 sread v1 s2. _` drule_all >> simp[]
QED

Theorem body_assert_reason_consumer:
  (!s0 tv s1. eval_expr cx e s0 = (INL tv,s1) ==>
    !tops env st res st'.
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~expr_has_evm_run se /\ EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr se) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr se) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      eval_expr cx se st = (res,st') ==>
      (well_typed_expr env se ==> contract_storage_well_formed cx st') /\
      (!vt. type_place_expr env se = SOME vt ==> contract_storage_well_formed cx st')) /\
  (!tops env st res st'.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr cx e st = (res,st') ==>
    (well_typed_expr env e ==> contract_storage_well_formed cx st') /\
    (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st')) ==>
  !tops env ret_ty env' st res st'.
    type_stmt env ret_ty (Assert e (AssertReason se)) = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmt_expr_exists expr_evm_run_root (Assert e (AssertReason se)) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt (Assert e (AssertReason se))) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason se))) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx (Assert e (AssertReason se)) st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, supported_stmt_expr_exists_def,
      supported_assert_exists_def, int_calls_stmt_def, int_calls_assert_reason_def,
      expr_has_evm_run_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_assum `eval_stmt _ _ _ = _`
    (mp_then (Pos last) mp_tac body_eval_assert_reason_storage) >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  qexists_tac `env` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!s0 tv s1. eval_expr _ _ _ = (INL _,_) ==> _` drule_all >> simp[]
QED

Theorem body_tuple_base_consumer:
  (!tops env ty st res st'.
    well_typed_target env bt ty /\ supported_program tops /\
    get_module_code cx NONE = SOME tops /\
    ~supported_target_exists expr_evm_run_root bt /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_target bt) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_target_place cx bt st = (res,st') ==> contract_storage_well_formed cx st') ==>
  !tops env ty st res st'.
    well_typed_atarget env (BaseTarget bt) ty /\ value_runtime_typed env ty v /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_assignment_exists expr_evm_run_root (BaseTarget bt) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_atarget (BaseTarget bt)) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget (BaseTarget bt)) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    assign_tuple_targets cx (BaseTarget bt) v st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  gvs[well_typed_atarget_def, supported_assignment_exists_def, int_calls_atarget_def] >>
  qpat_assum `assign_tuple_targets _ _ _ _ = _`
    (mp_then (Pos last) mp_tac body_assign_tuple_base_storage) >>
  disch_then irule >> simp[] >> reverse conj_tac
  >- (qexistsl_tac [`env`, `ty`] >> simp[]) >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem body_tuple_nested_consumer:
  (!vs. v = ArrayV (TupleV vs) ==> !tops env tys st res st'.
    LIST_REL (\t ty. well_typed_atarget env t ty) gs tys /\
    LIST_REL (value_runtime_typed env) tys vs /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_assignments_exists expr_evm_run_root gs /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_atargets gs) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets gs) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    assign_tuple_target_list cx gs vs st = (res,st') ==> contract_storage_well_formed cx st') ==>
  !tops env ty st res st'.
    well_typed_atarget env (TupleTarget gs) ty /\ value_runtime_typed env ty v /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_assignment_exists expr_evm_run_root (TupleTarget gs) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_atarget (TupleTarget gs)) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget (TupleTarget gs)) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    assign_tuple_targets cx (TupleTarget gs) v st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  gvs[well_typed_atarget_def, supported_assignment_exists_def, int_calls_atarget_def] >>
  drule vyperTypeEvalSoundnessTheory.value_runtime_typed_tuple_components >> strip_tac >> gvs[] >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem body_tuple_list_cons_consumer:
  (!s0 s1. assign_tuple_targets cx g v s0 = (INL (),s1) ==>
    !tops env tys st res st'.
      LIST_REL (\t ty. well_typed_atarget env t ty) gs tys /\
      LIST_REL (value_runtime_typed env) tys vs /\
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~supported_assignments_exists expr_evm_run_root gs /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_atargets gs) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_atargets gs) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      assign_tuple_target_list cx gs vs st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!tops env ty st res st'.
    well_typed_atarget env g ty /\ value_runtime_typed env ty v /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_assignment_exists expr_evm_run_root g /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_atarget g) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget g) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    assign_tuple_targets cx g v st = (res,st') ==> contract_storage_well_formed cx st') ==>
  !tops env tys st res st'.
    LIST_REL (\t ty. well_typed_atarget env t ty) (g::gs) tys /\
    LIST_REL (value_runtime_typed env) tys (v::vs) /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_assignments_exists expr_evm_run_root (g::gs) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_atargets (g::gs)) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets (g::gs)) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    assign_tuple_target_list cx (g::gs) (v::vs) st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `tys` >- gvs[] >>
  rename1 `LIST_REL _ (g::gs) (ty::tys)` >>
  gvs[LIST_REL_CONS1, supported_assignment_exists_def, int_calls_atarget_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_assum `assign_tuple_target_list _ _ _ _ = _`
    (mp_then (Pos last) mp_tac body_assign_tuple_cons_storage) >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  qexistsl_tac [`env`, `ty`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!s0 s1. assign_tuple_targets _ _ _ _ = _ ==> _` drule_all >> simp[]
QED

Theorem body_assign_tuple_consumer:
  (!s0 tv s1 sread v s2.
    eval_expr cx e s0 = (INL tv,s1) /\ read_result cx tv sread = (INL v,s2) ==>
    !tops env ty st res st'.
      well_typed_atarget env (TupleTarget gs) ty /\ value_runtime_typed env ty v /\
      supported_program tops /\ get_module_code cx NONE = SOME tops /\
      ~supported_assignment_exists expr_evm_run_root (TupleTarget gs) /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_atarget (TupleTarget gs)) /\
      runtime_storage_consistent env cx st /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_atarget (TupleTarget gs)) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
      assign_tuple_targets cx (TupleTarget gs) v st = (res,st') ==>
      contract_storage_well_formed cx st') /\
  (!tops env st res st'.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr cx e st = (res,st') ==>
    (well_typed_expr env e ==> contract_storage_well_formed cx st') /\
    (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st')) ==>
  !tops env ret_ty env' st res st'.
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmt_expr_exists expr_evm_run_root (Assign (TupleTarget gs) e) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx (Assign (TupleTarget gs) e) st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def, expr_has_evm_run_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_assum `eval_stmt _ _ _ = _`
    (mp_then (Pos last) mp_tac body_eval_assign_tuple_storage) >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  qexists_tac `env` >> simp[] >> rpt strip_tac >>
  `well_typed_atarget env (TupleTarget gs) (expr_type e)` by
    gvs[atarget_accepts_def, well_typed_atarget_def] >>
  qpat_x_assum `!s0 tv s1 sread v s2. _` drule_all >> simp[]
QED


Theorem body_intcall_runtime_frame:
  runtime_storage_consistent env cx st /\ functions_well_typed cx /\
  env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members /\
  scope_well_typed call_env /\
  env_scopes_consistent env_body cx (st with scopes := [call_env]) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  lock_if_nr cx nr is_view st = (INL (),lock_st) ==>
  runtime_storage_consistent env_body
    (cx with stk updated_by CONS (env_body.current_src,fn))
    (lock_st with scopes := [call_env]) /\
  IS_SOME (lock_st with scopes := [call_env]).outcomes /\
  oracle_storage_ok (cx with stk updated_by CONS (env_body.current_src,fn))
    (lock_st with scopes := [call_env])
Proof
  strip_tac >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `contract_storage_well_formed cx st /\ storage_layout_safe cx` by
    metis_tac[runtime_storage_consistent_storage, runtime_storage_consistent_layout] >>
  `env_context_consistent env_body
     (cx with stk updated_by CONS (env_body.current_src,fn)) /\
   env_immutables_consistent env_body
     (cx with stk updated_by CONS (env_body.current_src,fn)) st /\
   context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn))` by
    (fs[runtime_consistent_def] >>
     drule vyperTypeEvalSoundnessTheory.intcall_default_env_side_conditions >>
     disch_then (qspecl_then [`env_body`, `env_body.current_src`, `fn`] mp_tac) >>
     simp[]) >>
  `env_consistent env_body
     (cx with stk updated_by CONS (env_body.current_src,fn))
     (lock_st with scopes := [call_env]) /\
   state_well_typed (lock_st with scopes := [call_env]) /\
   accounts_well_typed (lock_st with scopes := [call_env]).accounts` by
    (fs[runtime_consistent_def] >>
     drule vyperTypeEvalSoundnessTheory.intcall_live_pushed_body_preconditions >>
     disch_then (qspecl_then
       [`env_body`, `st`, `lock_st`, `call_env`, `fn`, `nr`, `is_view`] mp_tac) >>
     fs[lock_if_nr_def, env_scopes_consistent_def, vyperContextTheory.get_tenv_def] >>
     disch_then irule >> metis_tac[]) >>
  drule_all body_intcall_lock_oracle_entry >> strip_tac >>
  drule_all body_oracle_storage_frame_entry >>
  disch_then (qspecl_then [`[call_env]`, `CONS (env_body.current_src,fn)`] mp_tac) >>
  simp[runtime_storage_consistent_def, runtime_consistent_def]
QED

Theorem body_intcall_guard_apply:
  (!s0 results t0 prev s1 dflt_vs t1 s2 vs t2 s3 call_env t3
      s4 rtv t4 s5 t5 s6 cxf t6.
    eval_expr_results cx es s0 = (INL results,t0) /\
    finally (do set_scopes [FEMPTY]; eval_exprs (cx with stk updated_by CONS (NONE,fn)) [] od)
      (set_scopes prev.scopes) s1 = (INL dflt_vs,t1) /\
    read_results cx results s2 = (INL vs,t2) /\
    lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
      "IntCall bind_arguments" s3 = (INL call_env,t3) /\
    lift_option_type (evaluate_type (get_tenv cx) ret)
      "IntCall eval ret" s4 = (INL rtv,t4) /\
    lock_if_nr cx nr (is_view_mut mut) s5 = (INL (),t5) /\
    push_function (NONE,fn) call_env cx s6 = (INL cxf,t6) ==> (!tops env ret_ty env' st res st'.
      type_stmts env ret_ty ss = SOME env' /\
      supported_program tops /\ get_module_code cxf NONE = SOME tops /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
        (int_calls_stmts ss) /\
      runtime_storage_consistent env cxf st /\ functions_well_typed cxf /\
      call_evaluation_safe cxf (int_calls_stmts ss) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cxf st /\
      eval_stmts cxf ss st = (res,st') ==> contract_storage_well_formed cxf st')) /\
  eval_expr_results cx es st = (INL results,args_st) /\
  read_results cx results args_st = (INL vs,args_st) /\
  bind_arguments (get_tenv cx) args vs = SOME call_env /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  lock_if_nr cx nr (is_view_mut mut) args_st = (INL (),lock_st) /\
  push_function (NONE,fn) call_env cx lock_st = (INL cxf,body_st) ==> (!tops env ret_ty env' st res st'.
      type_stmts env ret_ty ss = SOME env' /\
      supported_program tops /\ get_module_code cxf NONE = SOME tops /\
      EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
        (int_calls_stmts ss) /\
      runtime_storage_consistent env cxf st /\ functions_well_typed cxf /\
      call_evaluation_safe cxf (int_calls_stmts ss) /\
      IS_SOME st.outcomes /\ oracle_storage_ok cxf st /\
      eval_stmts cxf ss st = (res,st') ==> contract_storage_well_formed cxf st')
Proof
  strip_tac >> first_x_assum match_mp_tac >>
  goal_assum $ drule_at Any >>
  goal_assum $ drule_at Any >>
  goal_assum $ drule_at Any >>
  goal_assum $ drule_at Any >>
  qexistsl_tac [`args_st`, `args_st`, `[]`, `args_st`, `args_st`, `args_st`,
               `args_st`, `rtv`, `args_st`] >>
  simp[eval_empty_defaults_finally, lift_option_type_def, return_def]
QED
