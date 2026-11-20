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
  simp[supported_pure_expr_def, int_calls_expr_def, EVERY_APPEND] >>
  simp[int_calls_target_indices, EVERY_FLAT, EVERY_MAP, EVERY_MEM] >>
  rw[] >> TRY (Cases_on `default`) >> gvs[int_calls_expr_def] >>
  metis_tac[EVERY_MEM]
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
    ~supported_target_exists expr_halt_root target /\
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
  metis_tac[supported_expr_no_halt, supported_expr_no_evm_run, expr_has_evm_run_def,
            supported_expr_main_calls, supported_expr_no_call_operand_effects, optionTheory.IS_SOME_EXISTS]
QED

Theorem supported_target_storage_syntax:
  supported_target tops bindings target ==>
  ~supported_target_exists expr_halt_root target /\
  ~supported_target_exists expr_evm_run_root target /\
  ~supported_target_exists call_operands_effect_root target /\
  EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_target target)
Proof
  Cases_on `target` >>
  simp[supported_target_def, supported_expr_exists_def, call_operands_effect_root_def, int_calls_expr_def] >>
  qmatch_goalsub_rename_tac `supported_target_exists _ tgt` >> Cases_on `tgt` >>
  simp[supported_expr_exists_def, call_operands_effect_root_def, int_calls_expr_def] >>
  metis_tac[supported_expr_no_halt, supported_expr_no_evm_run, expr_has_evm_run_def,
            supported_expr_main_calls, supported_expr_no_call_operand_effects]
QED

Theorem supported_assignment_storage_syntax:
  supported_assignment tops bindings tgt e ==>
  ~supported_assignment_exists expr_halt_root tgt /\
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
  ~supported_iterator_exists expr_halt_root iter /\
  ~supported_iterator_exists expr_evm_run_root iter /\
  ~supported_iterator_exists call_operands_effect_root iter /\
  EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_iterator iter)
Proof
  Cases_on `iter`
  >- (simp[supported_iterator_exists_def, int_calls_iterator_def] >>
      qmatch_goalsub_rename_tac `int_calls_expr arr` >>
      Cases_on `arr`
      >~ [`Name _ _`]
      >- simp[supported_expr_exists_def, call_operands_effect_root_def,
              expr_halt_root_def, expr_evm_run_root_def, int_calls_expr_def]
      >~ [`TopLevelName _ _`]
      >- simp[supported_expr_exists_def, call_operands_effect_root_def,
              expr_halt_root_def, expr_evm_run_root_def, int_calls_expr_def] >>
      simp[supported_iterator_def] >> strip_tac >>
      metis_tac[supported_expr_main_calls, supported_expr_no_halt, supported_expr_no_evm_run,
                supported_expr_no_call_operand_effects, expr_has_evm_run_def]) >>
  simp[supported_iterator_def, supported_iterator_exists_def,
       int_calls_iterator_def, EVERY_APPEND] >>
  qmatch_goalsub_rename_tac `~supported_expr_exists _ lo /\ ~supported_expr_exists _ hi` >>
  strip_tac >>
  `supported_pure_expr tops lo /\ supported_pure_expr tops hi` suffices_by
    metis_tac[supported_pure_main_calls, supported_expr_no_halt, supported_expr_no_evm_run,
              supported_expr_no_call_operand_effects,
              supported_expr_def, expr_has_evm_run_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[supported_pure_expr_def]
QED

Theorem supported_string_reason_storage_syntax:
  supported_string_reason tops e ==>
  ~supported_expr_exists expr_halt_root e /\
  ~supported_expr_exists expr_evm_run_root e /\
  ~supported_expr_exists call_operands_effect_root e /\
  EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e)
Proof
  strip_tac >>
  `supported_pure_expr tops e` suffices_by
    metis_tac[supported_pure_main_calls, supported_expr_no_halt, supported_expr_no_evm_run,
              supported_expr_no_call_operand_effects,
              supported_expr_def, expr_has_evm_run_def] >>
  Cases_on `e` >> gvs[supported_string_reason_def] >>
  rename1 `Literal _ lit` >> Cases_on `lit` >>
  gvs[supported_string_reason_def, supported_pure_expr_def]
QED

Theorem supported_reasons_storage_syntax:
  (!tops reason. supported_assert_reason tops reason ==>
    ~supported_assert_exists expr_halt_root reason /\
    ~supported_assert_exists expr_evm_run_root reason /\
    ~supported_assert_exists call_operands_effect_root reason /\
    EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_assert_reason reason)) /\
  (!tops reason. supported_raise_reason tops reason ==>
    ~supported_raise_exists expr_halt_root reason /\
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
  ~supported_exprs_exists expr_halt_root es /\
  ~supported_exprs_exists expr_evm_run_root es /\
  ~supported_exprs_exists call_operands_effect_root es /\
  EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs es)
Proof
  Induct_on `es` >>
  simp[supported_pure_expr_def, supported_expr_exists_def, call_operands_effect_root_def,
       int_calls_expr_def, EVERY_APPEND] >>
  metis_tac[supported_expr_no_halt, supported_expr_no_evm_run, supported_expr_def,
            expr_has_evm_run_def, supported_pure_main_calls,
            supported_expr_no_call_operand_effects]
QED

Theorem supported_append_target_storage_syntax:
  supported_append_target tops tgt ==>
  ~supported_target_exists expr_halt_root tgt /\
  ~supported_target_exists expr_evm_run_root tgt /\
  ~supported_target_exists call_operands_effect_root tgt /\
  EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_target tgt)
Proof
  `(!e:expr. T) /\
   !bt. supported_target_pure tops bt ==>
     EVERY (\c. FST c = NONE /\
       IS_SOME (supported_function_decl tops c Internal)) (int_calls_target bt)` by
    (ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
     simp[supported_target_pure_def, int_calls_expr_def, EVERY_APPEND] >>
     metis_tac[supported_pure_main_calls]) >>
  Cases_on `tgt` >>
  simp[supported_append_target_def, supported_target_pure_def,
       supported_expr_exists_def,
       call_operands_effect_root_def, int_calls_expr_def, EVERY_APPEND] >>
  metis_tac[supported_target_pure_expr_exclusion, supported_expr_no_halt,
            supported_expr_no_evm_run,
            supported_expr_no_call_operand_effects, supported_expr_def,
            expr_has_evm_run_def, supported_pure_main_calls]
QED

Theorem supported_aug_target_storage_syntax:
  supported_aug_target tops bindings tgt ==>
  ~supported_target_exists expr_halt_root tgt /\
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
    ~supported_stmt_expr_exists expr_halt_root s /\
    ~supported_stmt_expr_exists expr_evm_run_root s /\
    ~supported_stmt_expr_exists call_operands_effect_root s /\
    EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt s)) /\
  (!tops bindings ss. supported_stmts tops bindings ss ==>
    ~supported_stmts_expr_exists expr_halt_root ss /\
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
  imp_res_tac supportedExprTraverseTheory.supported_expr_no_halt >>
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
  ~supported_exprs_exists expr_halt_root defaults /\
  ~supported_exprs_exists expr_evm_run_root defaults /\
  EVERY (\c. FST c = NONE /\
             IS_SOME (supported_function_decl tops c Internal))
    (int_calls_exprs defaults) /\
  ~supported_stmts_expr_exists expr_halt_root stmts /\
  ~supported_stmts_expr_exists expr_evm_run_root stmts /\
  EVERY (\c. FST c = NONE /\
             IS_SOME (supported_function_decl tops c Internal))
    (int_calls_stmts stmts)
Proof
  strip_tac >> drule_all supported_callable_body_contract >> strip_tac >>
  drule supported_pure_exprs_storage_syntax >>
  drule (CONJUNCT2 supported_stmts_storage_syntax) >> simp[] >>
  simp[EVERY_MEM] >> metis_tac[]
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
