(*
 * Source-body helpers for callable lookup, supported syntax and evaluation.
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
  supported_pure_exprs tops defaults /\ ?bindings. supported_stmts tops bindings stmts
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

Theorem int_calls_target_indices[local]:
  !t. int_calls_target t = FLAT (MAP int_calls_expr (target_indices t))
Proof
  measureInduct_on `base_assignment_target_size t` >>
  Cases_on `t` >> simp[int_calls_expr_def, target_indices_def] >>
  gvs[expr_size_def]
QED

Theorem supported_function_decl_main:
  IS_SOME (supported_function_decl tops id vis) ==> FST id = NONE
Proof
  Cases_on `id` >> CCONTR_TAC >>
  gvs[supported_lookup_other_module]
QED

Theorem supported_pure_main_calls:
  (!tops e. supported_pure_expr tops e ==>
    EVERY (\c. FST c = NONE ==>
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e)) /\
  (!tops es. supported_pure_exprs tops es ==>
    EVERY (\c. FST c = NONE ==>
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs es)) /\
  (!tops fields. supported_pure_fields tops fields ==>
    EVERY (\c. FST c = NONE ==>
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_named_exprs fields)) /\
  (!tops e. supported_place_expr tops e ==>
    EVERY (\c. FST c = NONE ==>
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e))
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  simp[supported_pure_expr_def, int_calls_expr_def, EVERY_APPEND] >>
  rpt conj_tac >> rpt gen_tac >>
  TRY (Cases_on `base`) >> TRY (Cases_on `target`) >>
  simp[supported_pure_expr_def, int_calls_expr_def, EVERY_APPEND] >>
  simp[int_calls_target_indices, EVERY_FLAT, EVERY_MAP, EVERY_MEM] >>
  rw[] >> TRY (Cases_on `default`) >>
  gvs[int_calls_expr_def, target_indices_def, MEM_FLAT, MEM_MAP, PULL_EXISTS, EVERY_MEM] >>
  metis_tac[supported_function_decl_main]
QED

Theorem supported_effect_main_calls:
  (!tops e. supported_effect_expr tops e ==>
    EVERY (\c. FST c = NONE ==>
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e)) /\
  (!tops e. supported_effect_place_expr tops e ==>
    EVERY (\c. FST c = NONE ==>
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e))
Proof
  ho_match_mp_tac supported_effect_expr_ind >>
  simp[supported_effect_expr_def, int_calls_expr_def, EVERY_APPEND,
       int_calls_target_indices, EVERY_FLAT, EVERY_MAP, EVERY_MEM] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  TRY (Cases_on `default`) >>
  gvs[int_calls_expr_def, MEM_FLAT, MEM_MAP, PULL_EXISTS, EVERY_MEM,
      EVERY_APPEND] >>
  imp_res_tac supported_function_decl_main >>
  imp_res_tac supported_pure_main_calls >>
  gvs[EVERY_MEM] >>
  metis_tac[REWRITE_RULE [EVERY_MEM] supported_pure_main_calls]
QED

Theorem supported_expr_main_calls:
  supported_expr tops e ==> EVERY (\c. FST c = NONE ==>
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e)
Proof
  simp[supported_expr_def] >>
  metis_tac[supported_pure_main_calls, supported_effect_main_calls]
QED

Theorem supported_target_info_main_calls:
  !tops bindings t.
    IS_SOME (supported_target_info tops bindings t) ==>
    ~supported_target_exists expr_evm_run_root t /\
    EVERY (\c. FST c = NONE ==>
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_target t)
Proof
  rpt gen_tac >>
  map_every qid_spec_tac [`bindings`, `tops`, `t`] >>
  measureInduct_on `base_assignment_target_size t` >>
  Cases_on `t` >>
  simp[supported_target_info_def, supported_expr_exists_def,
       int_calls_expr_def, EVERY_APPEND] >>
  rpt gen_tac >> simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  gvs[AllCaseEqs(), expr_size_def] >>
  qmatch_goalsub_rename_tac `int_calls_target tgt` >>
  first_x_assum (qspec_then `tgt` mp_tac) >> simp[] >>
  simp[GSYM optionTheory.IS_SOME_EXISTS] >>
  metis_tac[supported_expr_no_evm_run, expr_has_evm_run_def,
            supported_expr_main_calls, optionTheory.IS_SOME_EXISTS]
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
      Cases_on `LENGTH vs = 1` >>
      Cases_on `dest_BytesV (HD vs)` >>
      gvs[lift_option_type_def, lift_option_def, return_def, raise_def,
          AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
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

Theorem body_eval_array_iterator_storage:
  (!r s. eval_expr cx e st = (r,s) ==> contract_storage_well_formed cx s) /\
  eval_iterator cx (Array e) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,expr_st)` >>
  `contract_storage_well_formed cx expr_st` by metis_tac[] >>
  Cases_on `expr_res` >> simp[] >> strip_tac >>
  imp_res_tac array_iterator_results_state >> gvs[]
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

(* The source call after its arguments and omitted defaults evaluated. *)
Theorem supported_exprs_exists_DROP:
  !es n. ~supported_exprs_exists p es ==> ~supported_exprs_exists p (DROP n es)
Proof
  Induct >> rw[supported_expr_exists_def] >>
  Cases_on `n` >> simp[supported_expr_exists_def]
QED

Theorem int_calls_exprs_DROP_EVERY:
  !es n. EVERY P (int_calls_exprs es) ==> EVERY P (int_calls_exprs (DROP n es))
Proof
  Induct >> rw[int_calls_expr_def] >>
  Cases_on `n` >> gvs[int_calls_expr_def, EVERY_APPEND]
QED

Theorem eval_expr_intcall_defaults_step:
  ~MEM (NONE,fn) cx.stk /\ get_module_code cx NONE = SOME tops /\
  lookup_callable_function cx.in_deploy fn tops = SOME (mut,nr,args,dflts,ret,ss) /\
  LENGTH es <= LENGTH args /\ LENGTH args <= LENGTH es + LENGTH dflts /\
  eval_exprs cx es st = (args_res,args_st) ==>
  eval_expr cx (Call ty (IntCall (NONE,fn)) es kw) st =
  case args_res of
    INR e => (INR e,args_st)
  | INL vs =>
    case finally (do set_scopes [FEMPTY];
                     eval_exprs (cx with stk updated_by CONS (NONE,fn))
                       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) od)
           (set_scopes args_st.scopes) args_st of
      (INR e,d_st) => (INR e,d_st)
    | (INL dflt_vs,d_st) =>
      (do call_env <- lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
            "IntCall bind_arguments";
          rtv <- lift_option_type (evaluate_type (get_tenv cx) ret) "IntCall eval ret";
          lock_if_nr cx nr (is_view_mut mut);
          cxf <- push_function (NONE,fn) call_env cx;
          rv <- finally_unless_halt
            (finally (try (do eval_stmts cxf ss; return NoneV od) handle_function)
              (pop_function args_st.scopes))
            (unlock_if_nr cx nr (is_view_mut mut));
          crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
          return (Value crv) od) d_st
Proof
  strip_tac >>
  simp[Once evaluate_def, type_check_def, assert_def, lift_option_type_def,
       bind_apply, ignore_bind_apply, return_def, get_scopes_def] >>
  Cases_on `args_res` >> simp[] >>
  rename1 `finally _ _ args_st` >>
  Cases_on `finally (do set_scopes [FEMPTY];
                       eval_exprs (cx with stk updated_by CONS (NONE,fn))
                         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) od)
              (set_scopes args_st.scopes) args_st` >>
  rename1 `_ = (d_res,d_st)` >> Cases_on `d_res` >>
  gvs[bind_apply, ignore_bind_apply]
QED
