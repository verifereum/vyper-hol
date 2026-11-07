(* Shared expression-call and body-precondition boundaries. *)
Theory bodyExprPreFacts
Ancestors
  bodyStorageCases
  exprSimSource bodySim allocLimitsProps stmtLowering stmtLoweringMono
  fragExec stmtSimProps
  loweringPosts supportedStmtTraverse vyperCallOutcomeStorage vyperTypeExprSoundness
  vyperTypeSystem vyperTypeEnvPreservation vyperTypeContractStaticMaps
  vyperTypeEvalSoundness vyperTypeInvariants vyperTypeAssignContext
  vyperTypeStoragePreservation vyperStorageLayoutSafety vyperStorageBackend
  vyperEvalOutcomeSuffix bodyStoragePreservation stmtPoppedKeys placeTypingProps
  finite_map list exprLoweringProps compileVyper
  exprSimHypsDefs gasContext vyperABI
  supportedExprTraverse supportedExprs supportedDecls supportedStmts
  vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperInterpreter vyperState compileEnv allocLimits
Libs
  monadsyntax

(* An expression with no internal call in it has no internal calls to
   make.  Reasons and conditions are pure (supported_pure_no_internal_call). *)
Theorem no_internal_call_int_calls:
  (!e. ~supported_expr_exists expr_internal_call_root e ==>
       int_calls_expr e = []) /\
  (!t. ~supported_target_exists expr_internal_call_root t ==>
       int_calls_target t = []) /\
  (!es. ~supported_exprs_exists expr_internal_call_root es ==>
        int_calls_exprs es = []) /\
  (!eo. ~supported_opt_exists expr_internal_call_root eo ==>
        int_calls_opt eo = []) /\
  (!kes. ~supported_fields_exists expr_internal_call_root kes ==>
         int_calls_named_exprs kes = [])
Proof
  ho_match_mp_tac int_calls_expr_ind >>
  rw[int_calls_expr_def, supported_expr_exists_def,
     expr_internal_call_root_def]
QED


Theorem supported_pure_int_calls:
  !tops e. supported_pure_expr tops e ==> int_calls_expr e = []
Proof
  metis_tac[supported_pure_no_internal_call, expr_has_internal_call_def,
            no_internal_call_int_calls]
QED

(* supported_function_decl finds only the main module's functions. *)

(* An expression with no effect in it has no internal calls to make. *)
Theorem no_effect_int_calls[local]:
  (!e. ~supported_expr_exists expr_effect_root e ==> int_calls_expr e = []) /\
  (!es. ~supported_exprs_exists expr_effect_root es ==>
        int_calls_exprs es = [])
Proof
  `!x. expr_internal_call_root x ==> expr_effect_root x` by
    (Cases >> simp[expr_internal_call_root_def, expr_effect_root_def]) >>
  conj_tac >> rpt strip_tac
  >- (irule (cj 1 no_internal_call_int_calls) >>
      metis_tac[supported_expr_exists_mono]) >>
  irule (cj 3 no_internal_call_int_calls) >>
  metis_tac[supported_expr_exists_mono]
QED

Theorem supported_pure_forms_int_calls[local]:
  (!tops e. supported_pure_expr tops e ==> int_calls_expr e = []) /\
  (!tops es. supported_pure_exprs tops es ==> int_calls_exprs es = []) /\
  (!tops e. supported_place_expr tops e ==> int_calls_expr e = [])
Proof
  metis_tac[no_effect_int_calls, supported_pure_no_effect]
QED

Theorem supported_effect_main_int_calls[local]:
  (!tops e. supported_effect_expr tops e ==>
      EVERY (\c. FST c = NONE /\
                 IS_SOME (supported_function_decl tops c Internal))
        (int_calls_expr e)) /\
  (!tops e. supported_effect_place_expr tops e ==>
      EVERY (\c. FST c = NONE /\
                 IS_SOME (supported_function_decl tops c Internal))
        (int_calls_expr e))
Proof
  ho_match_mp_tac supported_effect_expr_ind >>
  rw[supported_effect_expr_def, int_calls_expr_def] >>
  imp_res_tac supported_pure_forms_int_calls >>
  imp_res_tac supported_function_decl_main >> gvs[]
QED

Theorem no_effect_call_operands:
  !e. ~expr_has_effect e ==>
      ~supported_expr_exists call_operands_effect_root e
Proof
  `!e. call_operands_effect_root e ==> expr_effect_root e` by
    (Cases >> simp[call_operands_effect_root_def, expr_effect_root_def] >>
     rename1 `Call ty target args dflt` >> Cases_on `target` >>
     simp[call_operands_effect_root_def, expr_effect_root_def]) >>
  rw[expr_has_effect_def] >>
  metis_tac[supported_expr_exists_mono]
QED

Theorem supported_pure_list_call_operands[local]:
  supported_pure_exprs tops args ==>
  EVERY (\e. ~expr_has_effect e) args /\
  EVERY (\e. ~supported_expr_exists call_operands_effect_root e) args
Proof
  simp[supported_pure_exprs_every, listTheory.EVERY_MEM] >> strip_tac >>
  conj_tac >> rpt strip_tac >>
  `supported_pure_expr tops e` by (first_x_assum irule >> simp[]) >>
  drule supported_pure_expr_effect_free >>
  metis_tac[no_effect_call_operands]
QED

Theorem effect_free_drop[local]:
  EVERY (\e. ~expr_has_effect e) args ==>
  ~EXISTS expr_has_effect (DROP n args)
Proof
  rw[listTheory.EVERY_MEM, listTheory.EXISTS_MEM] >>
  drule rich_listTheory.MEM_DROP_IMP >> metis_tac[]
QED

Theorem supported_effect_no_call_operand_effects[local]:
  (!tops e. supported_effect_expr tops e ==>
    ~supported_expr_exists call_operands_effect_root e) /\
  (!tops e. supported_effect_place_expr tops e ==>
    ~supported_expr_exists call_operands_effect_root e)
Proof
  ho_match_mp_tac supported_effect_expr_ind >>
  simp[supported_effect_expr_def, supported_expr_exists_def,
       call_operands_effect_root_def] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  imp_res_tac supported_pure_no_effect >>
  gvs[GSYM expr_has_effect_def] >>
  imp_res_tac supported_pure_list_call_operands >>
  imp_res_tac effect_free_drop >>
  imp_res_tac supported_pure_expr_effect_free >>
  imp_res_tac no_effect_call_operands >>
  gvs[supported_exprs_exists_every, listTheory.EXISTS_MEM,
      listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem supported_expr_no_call_operand_effects:
  supported_expr tops e ==>
  ~supported_expr_exists call_operands_effect_root e
Proof
  rw[supported_expr_def] >>
  metis_tac[supported_pure_expr_effect_free, no_effect_call_operands,
            supported_effect_no_call_operand_effects]
QED

(* A supported expression runs no EVM code, and its internal calls are to
   internal functions of the main module, as expr_body_pre asks. *)
(* A supported expression is no bare .code: supported_builtin_form
   rejects Acc Code. *)
Theorem supported_expr_not_extcode[local]:
  !tops e. supported_expr tops e ==> ~is_extcode e
Proof
  rpt gen_tac >> Cases_on `is_extcode e` >> simp[] >>
  Cases_on `e` >> gvs[exprLoweringTheory.is_extcode_def] >>
  rename1 `Builtin _ b l` >> Cases_on `b` >>
  gvs[exprLoweringTheory.is_extcode_def] >>
  rename1 `Acc a` >> Cases_on `a` >>
  gvs[exprLoweringTheory.is_extcode_def] >>
  Cases_on `l` >> gvs[exprLoweringTheory.is_extcode_def] >>
  rename1 `_ :: tl` >> Cases_on `tl` >>
  gvs[exprLoweringTheory.is_extcode_def,
      supportedExprsTheory.supported_expr_def,
      supportedExprsTheory.supported_pure_expr_def,
      supportedExprsTheory.supported_effect_expr_def,
      supportedExprFormsTheory.supported_builtin_form_def]
QED

Theorem supported_expr_body_calls:
  !tops e. supported_expr tops e ==>
    ~expr_has_evm_run e /\
    ~supported_expr_exists call_operands_effect_root e /\
    EVERY (\c. FST c = NONE) (int_calls_expr e) /\
    EVERY (\c. IS_SOME (supported_function_decl tops c Internal))
      (int_calls_expr e) /\
    ~is_extcode e
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[supported_expr_no_evm_run] >>
  conj_tac >- metis_tac[supported_expr_no_call_operand_effects] >>
  PURE_ONCE_REWRITE_TAC[CONJ_ASSOC] >>
  reverse conj_tac >- metis_tac[supported_expr_not_extcode] >>
  pop_assum mp_tac >> simp[supportedExprsTheory.supported_expr_def] >> strip_tac >>
  imp_res_tac supported_pure_int_calls >>
  imp_res_tac supported_effect_main_int_calls >>
  gvs[listTheory.EVERY_CONJ]
QED

(* The same for a reason, which may also be a string literal. *)
Theorem supported_string_reason_body_calls:
  !tops e. supported_string_reason tops e ==>
    ~expr_has_evm_run e /\
    ~supported_expr_exists call_operands_effect_root e /\
    EVERY (\c. FST c = NONE) (int_calls_expr e) /\
    EVERY (\c. IS_SOME (supported_function_decl tops c Internal))
      (int_calls_expr e) /\
    ~is_extcode e
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?t str. e = Literal t (StringL str)`
  >- gvs[expr_has_evm_run_def, supported_expr_exists_def,
         expr_evm_run_root_def, int_calls_expr_def,
         exprLoweringTheory.is_extcode_def] >>
  irule supported_expr_body_calls >>
  simp[supportedExprsTheory.supported_expr_def] >>
  Cases_on `e` >> gvs[supported_string_reason_def] >>
  rename1 `Literal _ lit` >> Cases_on `lit` >>
  gvs[supported_string_reason_def]
QED

(* A statement's expression meets expr_body_pre. *)
Theorem stmt_expr_body_pre:
  !cenv cx env e es calls.
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    ~supported_expr_exists
       (\e. ~is_extcode e /\
             ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) e /\
    ~is_extcode e /\
    ~supported_expr_exists call_operands_effect_root e /\
    call_evaluation_safe cx (int_calls_expr e ++ calls) /\
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE) (int_calls_expr e) /\
    (int_calls_expr e <> [] ==>
     ?tops. supported_program tops /\ get_module_code cx NONE = SOME tops /\
            EVERY (\c. IS_SOME (supported_function_decl tops c Internal))
              (int_calls_expr e)) /\
    (!target. supported_expr_exists
       (expr_abi_decode_target_root target) e ==>
       occurs_abi_decode_target target (cx_tops cx)) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)) ==>
    expr_body_pre cenv cx env e es
Proof
  rpt gen_tac >> strip_tac >>
  `byte_widths_expr e /\ alloc_limits_expr cenv e` by
    (CCONTR_TAC >>
     qpat_x_assum `~supported_expr_exists (\e. ~is_extcode e /\ _) _` mp_tac >>
     simp[] >> irule supported_expr_exists_root >> metis_tac[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    metis_tac[call_evaluation_safe_append_left] >>
  simp[expr_body_pre_def] >>
  Cases_on `int_calls_expr e` >> gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem stmts_env_cs_mono:
  !cenv lctx ty ss. cs_mono (stmts_env cenv lctx ty ss)
Proof
  rw[cs_mono_def] >>
  `compile_stmts cenv lctx ty ss sa = ((), sb)` by simp[compile_stmts_env] >>
  qspecl_then [`cenv`, `lctx`, `ty`, `ss`] mp_tac (cj 2 compile_stmt_cs_mono) >>
  simp[cs_mono_def] >> disch_then drule >> simp[]
QED

Theorem stmt_env_declare:
  !cenv lctx ty s sa c sm.
    stmt_env cenv lctx ty s sa = (c, sm) ==>
    ?sm0. declare_stmt_local cenv s sa = (c, sm0)
Proof
  simp[stmt_env_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]
QED

Theorem declare_stmt_local_other:
  !cenv s sa c sm.
    ~(?id typ e. s = AnnAssign id typ e) /\
    declare_stmt_local cenv s sa = (c, sm) ==> c = cenv
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, comp_return_def]
QED

Theorem type_stmt_other:
  !env ret_ty s env'.
    ~(?id typ e. s = AnnAssign id typ e) /\
    type_stmt env ret_ty s = SOME env' ==> env' = env
Proof
  rpt gen_tac >> Cases_on `s` >> simp[] >>
  TRY (rename1 `Raise rs` >> Cases_on `rs`) >>
  TRY (rename1 `Assert _ ak` >> Cases_on `ak`) >>
  TRY (rename1 `Return eo` >> Cases_on `eo`) >>
  rw[type_stmt_def, AllCaseEqs()]
QED

Theorem same_frame_trans:
  !c1 c2 c3. same_frame c1 c2 /\ same_frame c2 c3 ==> same_frame c1 c3
Proof
  rw[same_frame_def] >> fs[compile_env_component_equality] >>
  Cases_on `FLOOKUP c2.ce_vars n = FLOOKUP c1.ce_vars n` >> gvs[] >>
  metis_tac[]
QED

Theorem same_frame_struct_fields:
  !cenv c. same_frame cenv c ==> c.ce_struct_fields = cenv.ce_struct_fields
Proof
  rw[same_frame_def] >> qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem body_inv_same_frame:
  !tops ctx cenv c cx.
    body_inv tops ctx cenv cx /\ same_frame cenv c ==>
    body_inv tops ctx c cx
Proof
  rpt strip_tac >>
  fs[body_inv_def, cenv_module_pins_def, same_frame_def,
     compile_env_component_equality] >>
  metis_tac[]
QED

Theorem frame_ret_ok_same_frame:
  !ctx func cx RetQ cenv c ret_ty.
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\ same_frame cenv c ==>
    frame_ret_ok ctx func cx RetQ c ret_ty
Proof
  rw[frame_ret_ok_def] >> first_x_assum irule >>
  metis_tac[same_frame_trans]
QED

Theorem stmt_exprs_ok_same_frame:
  !cenv c. same_frame cenv c ==> stmt_exprs_ok c = stmt_exprs_ok cenv
Proof
  rw[same_frame_def] >>
  `c.ce_struct_fields = cenv.ce_struct_fields /\
   c.ce_func_return_type = cenv.ce_func_return_type` by
    (qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]) >>
  `alloc_limits_expr c = alloc_limits_expr cenv` by
    (rw[FUN_EQ_THM] >> irule (cj 1 alloc_limits_struct_fields) >> simp[]) >>
  `alloc_env_agree cenv c` by
    (qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >>
     simp[alloc_env_agree_def]) >>
  `alloc_limits_stmt c = alloc_limits_stmt cenv` by
    (rw[FUN_EQ_THM] >> irule (cj 1 alloc_limits_stmt_struct_fields) >>
     simp[]) >>
  `c.ce_is_external = cenv.ce_is_external /\
   c.ce_raw_return = cenv.ce_raw_return /\
   return_buffer_ok c = return_buffer_ok cenv` by
    (qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >>
     simp[return_buffer_ok_def]) >>
  simp[FUN_EQ_THM, stmt_exprs_ok_def]
QED

Theorem stmts_exprs_ok_EVERY:
  !cenv ss.
    EVERY (stmt_exprs_ok cenv) ss <=>
    ~supported_stmts_expr_exists
       (\e. ~is_extcode e /\
             ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) ss /\
    alloc_limits_stmts cenv ss /\
    (stmts_valued_return ss /\ cenv.ce_is_external /\ ~cenv.ce_raw_return ==>
       return_buffer_ok cenv)
Proof
  gen_tac >> Induct >>
  simp[supported_stmt_expr_exists_def, stmt_exprs_ok_def,
       alloc_limits_stmt_def, stmt_valued_return_def] >>
  metis_tac[]
QED

(* ===== The source state after a statement ===== *)

(* Evaluating a statement keeps popped_keys_indexed, as
   eval_expr_popped_keys_indexed shows for an expression: stmtPoppedKeys. *)
Theorem eval_stmts_popped_keys_indexed:
  (!cx s env ret_ty env' es res es'.
     type_stmt env ret_ty s = SOME env' /\
     runtime_consistent env cx es /\ functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmt s) /\
     eval_stmt cx s es = (res, es') /\
     popped_keys_indexed es.scopes ==>
     popped_keys_indexed es'.scopes) /\
  (!cx ss env ret_ty env' es res es'.
     type_stmts env ret_ty ss = SOME env' /\
     runtime_consistent env cx es /\ functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmts ss) /\
     eval_stmts cx ss es = (res, es') /\
     popped_keys_indexed es.scopes ==>
     popped_keys_indexed es'.scopes)
Proof
  metis_tac[cj 1 eval_statement_loop_popped_keys_indexed,
            cj 2 eval_statement_loop_popped_keys_indexed]
QED

(* The storage conjuncts of expr_sim_inv do not look at the scopes. *)
Theorem storage_conjs_scopes:
  !cx es f.
    contract_storage_well_formed cx es /\ oracle_storage_ok cx es ==>
    contract_storage_well_formed cx (es with scopes updated_by f) /\
    oracle_storage_ok cx (es with scopes updated_by f)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule vyperStorageLayoutSafetyTheory.contract_storage_well_formed_storage_frame >>
      qexists_tac `es` >> rw[] >> Cases_on `b` >>
      simp[vyperStorageBackendTheory.get_storage_def]) >>
  `(es with scopes updated_by f).outcomes = es.outcomes` by simp[] >>
  metis_tac[vyperTypeStoragePreservationTheory.oracle_storage_ok_outcomes]
QED

(* The storage conjuncts of expr_sim_inv after a supported statement, or a
   list of them (bodyStoragePreservation). *)
Theorem eval_stmts_storage_conjs:
  (!tops bindings cx s env ret_ty env' st res st'.
     supported_program tops /\ get_module_code cx NONE = SOME tops /\
     supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' /\
     runtime_storage_consistent env cx st /\ functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmt s) /\
     IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
     eval_stmt cx s st = (res, st') ==>
     contract_storage_well_formed cx st' /\ oracle_storage_ok cx st' /\
     IS_SOME st'.outcomes) /\
  (!tops bindings cx ss env ret_ty env' st res st'.
     supported_program tops /\ get_module_code cx NONE = SOME tops /\
     supported_stmts tops bindings ss /\ type_stmts env ret_ty ss = SOME env' /\
     runtime_storage_consistent env cx st /\ functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmts ss) /\
     IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
     eval_stmts cx ss st = (res, st') ==>
     contract_storage_well_formed cx st' /\ oracle_storage_ok cx st' /\
     IS_SOME st'.outcomes)
Proof
  conj_tac >> rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (drule_all (cj 1 eval_stmts_body_oracle_storage) >> simp[])
  >- (irule oracle_storage_ok_suffix >> qexists_tac `st` >>
      simp[] >> drule_then irule (cj 1 eval_outcome_suffix_mutual))
  >- (drule (cj 1 eval_outcome_suffix_mutual) >>
      rw[outcome_suffix_def] >> gvs[])
  >- (drule_all (cj 2 eval_stmts_body_oracle_storage) >> simp[])
  >- (irule oracle_storage_ok_suffix >> qexists_tac `st` >>
      simp[] >> drule_then irule (cj 2 eval_outcome_suffix_mutual)) >>
  drule (cj 2 eval_outcome_suffix_mutual) >>
  rw[outcome_suffix_def] >> gvs[]
QED

Theorem expr_sim_inv_push_scope:
  !cenv cx env es.
    expr_sim_inv cenv cx env es ==>
    expr_sim_inv cenv cx env (es with scopes := FEMPTY :: es.scopes)
Proof
  rpt strip_tac >>
  `es with scopes := FEMPTY :: es.scopes =
   es with scopes updated_by CONS FEMPTY` by
    simp[evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `expr_sim_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  `env_consistent env cx (es with scopes updated_by CONS FEMPTY)` by
    (irule push_scope_env_consistent >> simp[]) >>
  `state_well_typed (es with scopes updated_by CONS FEMPTY)` by
    fs[state_well_typed_def, scope_well_typed_def] >>
  `popped_keys_indexed (es with scopes updated_by CONS FEMPTY).scopes` by
    fs[popped_keys_indexed_def] >>
  drule_all storage_conjs_scopes >>
  disch_then (qspec_then `CONS FEMPTY` strip_assume_tac) >>
  ASM_REWRITE_TAC [expr_sim_inv_def] >> simp[]
QED

(* After a statement that completes, expr_sim_inv holds at the type
   environment its typing gives and the compile environment its
   declaration gives. *)
Theorem expr_sim_inv_stmt:
  !tops bindings cenv cx env ret_ty s env' es es1 lctx sa c sm.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    supported_stmt tops bindings s /\
    expr_sim_inv cenv cx env es /\ cenv.ce_alloca_locals /\
    type_stmt env ret_ty s = SOME env' /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    eval_stmt cx s es = (INL (), es1) /\
    stmt_env cenv lctx ret_ty s sa = (c, sm) ==>
    expr_sim_inv c cx env' es1
Proof
  rpt strip_tac >>
  `contract_storage_well_formed cx es1 /\ oracle_storage_ok cx es1 /\
   IS_SOME es1.outcomes` by
    (qspecl_then [`tops`, `bindings`, `cx`, `s`, `env`, `ret_ty`, `env'`,
                  `es`, `INL ()`, `es1`] mp_tac (cj 1 eval_stmts_storage_conjs) >>
     impl_tac >- gvs[expr_sim_inv_def, runtime_storage_consistent_def,
                     runtime_consistent_def] >>
     simp[]) >>
  drule stmt_env_declare >> strip_tac >>
  qspecl_then [`cx`, `s`, `env`, `ret_ty`, `env'`, `es`, `INL ()`, `es1`]
    mp_tac (cj 1 eval_scc_type_sound_mutual) >>
  impl_tac >- fs[expr_sim_inv_def] >> simp[] >> strip_tac >>
  `outcomes_accounts_typed es1.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 1 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >>
     gvs[expr_sim_inv_def, outcomes_accounts_typed_def]) >>
  `popped_keys_indexed es1.scopes` by
    (`runtime_consistent env cx es` by
       fs[expr_sim_inv_def, runtime_consistent_def] >>
     fs[expr_sim_inv_def] >>
     drule_all (cj 1 eval_stmts_popped_keys_indexed) >> simp[]) >>
  Cases_on `?id typ e. s = AnnAssign id typ e`
  >- (gvs[type_stmt_def, declare_stmt_local_def] >>
      drule_all declare_local_ptr >> strip_tac >>
      `c.ce_var_type = (id =+ SOME typ) cenv.ce_var_type` by
        (qpat_x_assum `declare_local _ _ _ _ = _` mp_tac >> strip_tac >>
         gvs[declare_local_def, fresh_var_def, comp_bind_def,
             comp_return_def, LET_THM]) >>
      `!n ty. FLOOKUP (extend_local env id typ T).var_types n = SOME ty ==>
              ?p sz. FLOOKUP c.ce_vars n = SOME (PtrVar (Var p) sz)` by
        (rpt gen_tac >> Cases_on `n = id` >>
         simp[extend_local_def, FLOOKUP_UPDATE, combinTheory.C_THM] >>
         strip_tac >> fs[expr_sim_inv_def] >> metis_tac[]) >>
      `!n ty. FLOOKUP (extend_local env id typ T).var_types n = SOME ty ==>
              c.ce_var_type n = SOME ty` by
        (rpt gen_tac >> Cases_on `n = id` >>
         simp[extend_local_def, FLOOKUP_UPDATE, combinTheory.C_THM,
              combinTheory.APPLY_UPDATE_THM] >>
         fs[expr_sim_inv_def]) >>
      qpat_x_assum
        `_ with <| ce_vars := _; ce_var_type := _;
                   ce_dynarray_capacity := _ |> = cenv`
        (strip_assume_tac o
         SIMP_RULE (srw_ss()) [compile_env_component_equality]) >>
      `(place_map_tables_agree_on_defined c (extend_local env id typ T) <=>
        place_map_tables_agree_on_defined cenv env) /\
       (extend_local env id typ T).bare_globals = env.bare_globals` by
        (conj_tac >- (irule placeTypingPropsTheory.place_map_tables_agree_on_defined_cong >> fs[extend_local_def]) >>
         simp[extend_local_def]) >>
      qpat_x_assum `expr_sim_inv _ _ _ es`
        (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
      ASM_REWRITE_TAC [expr_sim_inv_def, extend_local_bare_globals]) >>
  drule_all declare_stmt_local_other >> strip_tac >>
  drule_all type_stmt_other >> strip_tac >> gvs[] >>
  qpat_x_assum `expr_sim_inv _ _ _ es`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  ASM_REWRITE_TAC [expr_sim_inv_def]
QED

(* A declaration keeps ce_locals_declared: it binds its name as the typing
   adds it. *)
Theorem ce_locals_declared_declare_local:
  !cenv env id ty st c st1 a.
    ce_locals_declared cenv env /\ declare_local cenv id ty st = (c, st1) ==>
    ce_locals_declared c (extend_local env id ty a)
Proof
  rpt gen_tac >> strip_tac >>
  `!n. n <> id ==> FLOOKUP c.ce_vars n = FLOOKUP cenv.ce_vars n` by
    (qpat_x_assum `declare_local _ _ _ _ = _` mp_tac >>
     rw[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def,
        LET_THM] >> simp[FLOOKUP_UPDATE]) >>
  fs[ce_locals_declared_def, extend_local_def, combinTheory.C_THM] >>
  rpt strip_tac >> Cases_on `n = id` >> simp[] >> metis_tac[]
QED

(* After a statement, ce_locals_declared holds at the type environment its
   typing gives and the compile environment its declaration gives. *)
Theorem ce_locals_declared_stmt:
  !cenv env ret_ty s env' lctx sa c sm.
    ce_locals_declared cenv env /\ type_stmt env ret_ty s = SOME env' /\
    stmt_env cenv lctx ret_ty s sa = (c, sm) ==>
    ce_locals_declared c env'
Proof
  rpt strip_tac >> drule stmt_env_declare >> strip_tac >>
  Cases_on `?id typ e. s = AnnAssign id typ e`
  >- (gvs[type_stmt_def, declare_stmt_local_def] >>
      irule ce_locals_declared_declare_local >> metis_tac[]) >>
  drule_all declare_stmt_local_other >> strip_tac >>
  drule_all type_stmt_other >> strip_tac >> gvs[]
QED

(* A local declared at a type below the limit keeps locals_alloc_ok, in a
   compile env with the same struct sizes. *)
Theorem locals_alloc_ok_extend:
  !cenv c env id ty a.
    locals_alloc_ok cenv env /\ type_memory_bytes cenv ty < 2 ** 64 /\
    c.ce_struct_fields = cenv.ce_struct_fields ==>
    locals_alloc_ok c (extend_local env id ty a)
Proof
  rw[locals_alloc_ok_def, extend_local_def, combinTheory.C_THM,
     FLOOKUP_UPDATE] >>
  drule_then assume_tac type_memory_bytes_frame >>
  gvs[locals_alloc_ok_def, AllCaseEqs()] >> metis_tac[]
QED

(* After a statement, locals_alloc_ok holds at the type environment its
   typing gives and the compile environment its declaration gives: a
   declaration's type is below the limit by alloc_limits_stmt. *)
Theorem locals_alloc_ok_stmt:
  !cenv env ret_ty s env' lctx sa c sm.
    locals_alloc_ok cenv env /\ stmt_exprs_ok cenv s /\
    type_stmt env ret_ty s = SOME env' /\
    stmt_env cenv lctx ret_ty s sa = (c, sm) ==>
    locals_alloc_ok c env'
Proof
  rpt strip_tac >> drule stmt_env_declare >> strip_tac >>
  Cases_on `?id typ e. s = AnnAssign id typ e`
  >- (gvs[type_stmt_def, declare_stmt_local_def, AllCaseEqs()] >>
      `c.ce_struct_fields = cenv.ce_struct_fields` by
        (qpat_x_assum `declare_local _ _ _ _ = _` mp_tac >>
         rw[declare_local_def, fresh_var_def, comp_bind_def,
            comp_return_def, LET_THM] >> simp[]) >>
      irule locals_alloc_ok_extend >> qexists_tac `cenv` >>
      gvs[stmt_exprs_ok_def, alloc_limits_stmt_def]) >>
  drule_all declare_stmt_local_other >> strip_tac >>
  drule_all type_stmt_other >> strip_tac >> gvs[]
QED

