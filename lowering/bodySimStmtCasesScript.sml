(*
 * The body simulation of S1: statement cases (#637)
 *
 * One lemma for each statement case of evaluate_ind that bodySimMain's
 * body_sim_mutual does not close in a line or two.  Those marked GAP are
 * cheated; their comments name the existing lemmas they dispatch to and
 * what is left.  A case whose covered forms are proved dispatches the rest
 * to a cheated lemma marked RESIDUAL, whose comment names the premises
 * missing for the remaining forms.  The declarations, AnnAssign and For,
 * are in bodySimDeclCases, and Log in bodySimLog.
 *
 * TOP-LEVEL:
 *   body_*_case       — one case of the induction each
 *   body_*_other      — the residual forms of a case
 *   body_assign_local_memory — x = e for a local x held in memory
 *   stmt_expr_body_pre — a statement's expression meets expr_body_pre
 *   supported_expr_body_calls, supported_string_reason_body_calls — a
 *                       supported expression or reason runs no EVM code
 *                       and calls only the main module's functions
 *   reason_covered    — a reason compiles to a form the reason lemmas take
 *   supported_reason_code — a supported reason they don't take is an
 *                       immutable's, a pointer into code
 *   no_internal_call_int_calls, supported_pure_int_calls — no internal
 *                       call means int_calls_* = []
 *   expr_body_pre_eval_result, expr_body_pre_eval — evaluation keeps
 *                       expr_sim_inv and types the value
 *   type_widens_to_word — widening to a word type is equality
 *   expr_sim_inv_stmt  — expr_sim_inv after a statement, at the type
 *                        environment and compile environment it gives
 *   ce_locals_declared_declare_local, ce_locals_declared_stmt — the same
 *                        for ce_locals_declared
 *   locals_alloc_ok_extend, locals_alloc_ok_stmt — the same for
 *                        locals_alloc_ok
 *   compile_expr_open  — a supported expression that evaluates compiles
 *                        without terminating its block
 *   eval_stmts_popped_keys_indexed — statement evaluation keeps
 *                        popped_keys_indexed
 *
 * Helper:
 *   stmts_env_cs_mono, stmt_env_declare, declare_stmt_local_other,
 *   type_stmt_other    — stmt_env and type_stmt of a statement
 *   same_frame_trans, body_inv_same_frame, frame_ret_ok_same_frame,
 *   stmt_exprs_ok_same_frame, stmts_exprs_ok_EVERY — the frame facts
 *                        at a later compile env of the same body
 *   expr_sim_inv_push_scope — expr_sim_inv in a new scope
 *   body_inv_mcopy     — the frame's target has MCOPY
 *)

Theory bodySimStmtCases
Ancestors
  vyperStorageLayoutSafety vyperLookupStorage
  list finite_map bodySim allocLimits allocLimitsProps exprSim exprSimHyps exprLoweringProps stmtSim
  stmtSimIf stmtLoweringMono stmtLowering compileEnv fragExec
  supportedExprTraverse supportedStmtTraverse supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness stmtSimReason stmtSimReasonExpr
  stmtSimReasonStorage stmtSimReasonCode supportedExprs stmtSimAssign stmtSimDeclStore
  stmtSimAugAssign vyperTypeEvalSoundness vyperTypeInvariants
  vyperTypeExprSoundness vyperEvalOutcomeSuffix exprSimMain
  exprReasonOperand
  vyperTypeValues vyperTyping vyperTypeDefaults stmtSimAssignTuple
  vyperTypeEnvPreservation bodySimExprCases bodyStoragePreservation
  vyperCallOutcomeStorage vyperTypeStoragePreservation
  stmtSimAssignStorage supportedDecls vyperTypeContractStaticMaps
  vyperTypeContract compileVyper supportedTypes stmtSimAssignAttr
  stmtSimAssignStorageCopy
  stmtSimAugAssignAttr stmtSimAssignAttrStorage stmtSimAugAssignStorage
  stmtSimAugAssignAttrStorage stmtSimAssignMem stmtSimAssignTupleMem
  memoryLocalRhsProps stmtPoppedKeys exprOpenMain targetPlaceSim targetPlaceSimCases
  bodySimAugPlaceLoad bodySimAugPlaceLive bodySimAugPlaceStore
Libs
  monadsyntax

(* ===== Helpers ===== *)

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
Theorem supported_function_decl_main[local]:
  !tops id vis. IS_SOME (supported_function_decl tops id vis) ==> FST id = NONE
Proof
  Cases >> rpt gen_tac >> PairCases_on `id` >>
  simp[supported_function_decl_def] >>
  Cases_on `id0` >> simp[]
QED

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
      EVERY (\c. FST c = NONE) (int_calls_expr e)) /\
  (!tops e. supported_effect_place_expr tops e ==>
      EVERY (\c. FST c = NONE) (int_calls_expr e))
Proof
  ho_match_mp_tac supported_effect_expr_ind >>
  rw[supported_effect_expr_def, int_calls_expr_def] >>
  imp_res_tac supported_pure_forms_int_calls >>
  imp_res_tac supported_function_decl_main >> gvs[]
QED

(* A supported expression runs no EVM code, and its internal calls are to
   the main module, as expr_body_pre asks. *)
Theorem supported_expr_body_calls:
  !tops e. supported_expr tops e ==>
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE) (int_calls_expr e)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[supported_expr_no_evm_run] >>
  pop_assum mp_tac >> simp[supported_expr_def] >> strip_tac >>
  imp_res_tac supported_pure_int_calls >>
  imp_res_tac supported_effect_main_int_calls >> gvs[]
QED

(* The same for a reason, which may also be a string literal. *)
Theorem supported_string_reason_body_calls:
  !tops e. supported_string_reason tops e ==>
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE) (int_calls_expr e)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?t str. e = Literal t (StringL str)`
  >- gvs[expr_has_evm_run_def, supported_expr_exists_def,
         expr_evm_run_root_def, int_calls_expr_def] >>
  irule supported_expr_body_calls >> qexists_tac `tops` >>
  simp[supported_expr_def] >>
  Cases_on `e` >> gvs[supported_string_reason_def] >>
  rename1 `Literal _ lit` >> Cases_on `lit` >>
  gvs[supported_string_reason_def]
QED

(* A statement's expression meets expr_body_pre. *)
Theorem stmt_expr_body_pre:
  !cenv cx env e es calls.
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    ~supported_expr_exists
       (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) e /\
    call_evaluation_safe cx (int_calls_expr e ++ calls) /\
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE) (int_calls_expr e) /\
    (int_calls_expr e <> [] ==>
     ?tops. supported_program tops /\ get_module_code cx NONE = SOME tops) ==>
    expr_body_pre cenv cx env e es
Proof
  rpt gen_tac >> strip_tac >>
  `byte_widths_expr e /\ alloc_limits_expr cenv e` by
    (CCONTR_TAC >> qpat_x_assum `~supported_expr_exists _ _` mp_tac >>
     simp[] >> irule supported_expr_exists_root >> metis_tac[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    metis_tac[call_evaluation_safe_append_left] >>
  simp[expr_body_pre_def] >>
  Cases_on `int_calls_expr e` >> gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

(* ===== The compile environment after a statement ===== *)

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
  fs[body_inv_def, same_frame_def, compile_env_component_equality] >>
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
  `c.ce_struct_fields = cenv.ce_struct_fields` by
    (qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]) >>
  `alloc_limits_expr c = alloc_limits_expr cenv` by
    (rw[FUN_EQ_THM] >> irule (cj 1 alloc_limits_struct_fields) >> simp[]) >>
  `c.ce_event_info = cenv.ce_event_info` by
    (qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]) >>
  `alloc_limits_stmt c = alloc_limits_stmt cenv` by
    (rw[FUN_EQ_THM] >> irule (cj 1 alloc_limits_stmt_struct_fields) >>
     simp[]) >>
  simp[FUN_EQ_THM, stmt_exprs_ok_def]
QED

Theorem stmts_exprs_ok_EVERY:
  !cenv ss.
    EVERY (stmt_exprs_ok cenv) ss <=>
    ~supported_stmts_expr_exists
       (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) ss /\
    alloc_limits_stmts cenv ss
Proof
  gen_tac >> Induct >>
  simp[supported_stmt_expr_exists_def, stmt_exprs_ok_def,
       alloc_limits_stmt_def] >>
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
      ASM_REWRITE_TAC [expr_sim_inv_def]) >>
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

(* compile_expr leaves its block open for a supported expression of the
   frame that evaluates.  Not every expression does: the lowering's
   fallbacks end their block in INVALID.  Which fallback a module variable
   takes depends on cenv.ce_module_vars, so the storage and transient bindings
   that state_rel gives are premises.  The induction is exprOpenMain's
   compile_expr_open_general. *)
Theorem compile_expr_open:
  !tops ctx cenv cx env e es tv es1 sa vv sb.
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_body_pre cenv cx env e es /\
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    eval_expr cx e es = (INL tv, es1) /\
    compile_expr cenv (expr_type e) e sa = (vv, sb) /\
    ~block_is_terminated sa ==>
    ~block_is_terminated sb
Proof
  metis_tac[compile_expr_open_general]
QED

(* An assertion with no reason: stmtSimIf's compile_assert_frag. *)
Theorem body_assert_case:
  !cx e ak.
    (ak = AssertBare \/ ak = AssertUnreachable) /\ body_expr_ok cx e ==>
    body_stmt_ok cx (Assert e ak)
Proof
  rw[body_stmt_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def, supported_expr_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assert_exists_def, int_calls_stmt_def,
         int_calls_assert_reason_def] >>
     qexists_tac `[]` >> simp[]) >>
  irule compile_assert_frag >> gvs[type_stmt_def] >>
  fs[body_expr_ok_def] >> metis_tac[compile_expr_grows]
QED

(* ===== Cases ===== *)

(* ===== Statements ===== *)

Theorem body_pass_case:
  !cx. body_stmt_ok cx Pass
Proof
  rw[body_stmt_ok_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, return_def] >> rw[compile_pass_frag]
QED

Theorem body_continue_case:
  !cx. body_stmt_ok cx Continue
Proof
  rw[body_stmt_ok_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, raise_def] >> rw[] >>
  Cases_on `lctx` >> simp[compile_continue_frag] >>
  simp[stmt_frag_def, stmt_res_ok_def]
QED

Theorem body_break_case:
  !cx. body_stmt_ok cx Break
Proof
  rw[body_stmt_ok_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, raise_def] >> rw[] >>
  Cases_on `lctx` >> simp[compile_break_frag] >>
  simp[stmt_frag_def, stmt_res_ok_def]
QED

(* The frame's RetQ (frame_ret_ok). *)
Theorem body_return_none_case:
  !cx. body_stmt_ok cx (Return NONE)
Proof
  rw[body_stmt_ok_def, frame_ret_ok_def] >>
  first_x_assum irule >> simp[same_frame_refl] >>
  qexists_tac `env` >> simp[]
QED

Theorem body_return_case:
  !cx e. body_expr_ok cx e ==> body_stmt_ok cx (Return (SOME e))
Proof
  rw[body_stmt_ok_def, frame_ret_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  first_x_assum irule >> fs[body_expr_ok_def] >>
  conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]
QED

(* ===== Reasons ===== *)

(* The reason's compiled value is one the revert's encoder takes: a
   word or a memory buffer (stmtSimReasonExpr), or a storage or transient
   pointer (stmtSimReasonStorage). *)
Definition reason_covered_def:
  reason_covered cenv r <=>
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_vv_ok vv) \/
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_storage_vv vv)
End

Theorem well_typed_literal_string[local]:
  !ty s. well_typed_literal ty (StringL s) ==> ?n. ty = BaseT (StringT n)
Proof
  Cases >> simp[well_typed_literal_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[well_typed_literal_def]
QED

(* A supported reason is a string expression (supported_string_reason),
   so it compiles to a memory or stack value, a storage or transient
   pointer, or a pointer into code (compile_expr_string_reason):
   expr_sim_inv holds each local through a variable pointer.  The first
   two are reason_covered. *)
Theorem supported_reason_code:
  !cenv cx env es tops e.
    expr_sim_inv cenv cx env es /\
    supported_string_reason tops e /\ well_typed_expr env e /\
    ~reason_covered cenv e ==>
    !sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) ==>
               reason_code_vv vv
Proof
  rpt gen_tac >> strip_tac >>
  `?n. expr_type e = BaseT (StringT n)` by
    (Cases_on `?t str. e = Literal t (StringL str)`
     >- (gvs[well_typed_expr_def, expr_type_def] >>
         metis_tac[well_typed_literal_string]) >>
     `case expr_type e of BaseT (StringT _) => T | _ => F` by
       (Cases_on `e` >> fs[supported_string_reason_def] >>
        rename1 `Literal _ lit` >> Cases_on `lit` >>
        fs[supported_string_reason_def]) >>
     Cases_on `expr_type e` >> fs[] >>
     rename1 `BaseT b` >> Cases_on `b` >> fs[]) >>
  qspecl_then [`cenv`, `env`, `e`, `n`] mp_tac compile_expr_string_reason >>
  impl_tac >- (fs[expr_sim_inv_def] >> metis_tac[]) >>
  fs[reason_covered_def] >> metis_tac[]
QED

(* A reason read from an immutable, whose compiled value is a pointer into
   code (supported_reason_code): the revert's encoder copies it out of code
   (stmtSimReasonCode), the body being runtime code (body_inv).  A string
   literal goes to stmtSimReason. *)
Theorem body_raise_reason_other:
  !ctx func cx lctx RetQ cenv tops bindings env ret_ty e es res es'.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Raise (RaiseReason e)) /\
    expr_sim_inv cenv cx env es /\
    IS_SOME (type_stmt env ret_ty (Raise (RaiseReason e))) /\
    stmt_exprs_ok cenv (Raise (RaiseReason e)) /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e))) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (Raise (RaiseReason e)) es = (res, es') /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    (!sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseReason e))) es res es'
Proof
  rpt strip_tac >> `~cenv.ce_is_ctor` by fs[body_inv_def] >>
  Cases_on `?ml str. e = Literal (BaseT (StringT ml)) (StringL str)`
  >- (gvs[] >> irule compile_raise_reason_lit_frag >> simp[]) >>
  irule compile_raise_code_reason_frag >> gvs[] >> metis_tac[]
QED

(* A string literal reason (stmtSimReason), one whose compiled value
   reason_covered covers (stmtSimReasonExpr, stmtSimReasonStorage), or a
   pointer into code (body_raise_reason_other). *)
Theorem body_raise_reason_case:
  !cx e. body_expr_ok cx e ==> body_stmt_ok cx (Raise (RaiseReason e))
Proof
  rw[body_stmt_ok_def] >>
  Cases_on `?ml str. e = Literal (BaseT (StringT ml)) (StringL str)`
  >- (gvs[] >> irule compile_raise_reason_lit_frag >> simp[]) >>
  `supported_string_reason tops e` by
    gvs[supported_stmt_def, supported_raise_reason_def] >>
  drule_then strip_assume_tac supported_string_reason_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_raise_exists_def, int_calls_stmt_def,
         int_calls_raise_reason_def] >>
     qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_ok_def] >>
  Cases_on `reason_covered cenv e`
  >- (gvs[reason_covered_def]
      >- (irule compile_raise_reason_frag >> simp[] >> metis_tac[])
      >- (irule compile_raise_storage_reason_frag >> simp[] >> metis_tac[])) >>
  irule body_raise_reason_other >> simp[] >>
  reverse conj_tac >-
    (conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule supported_reason_code >>
  gvs[supported_stmt_def, supported_raise_reason_def, type_stmt_def] >>
  metis_tac[]
QED

(* As body_raise_reason_other, after the condition fails. *)
Theorem body_assert_reason_other:
  !ctx func cx lctx RetQ cenv tops bindings env ret_ty e se es res es'.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assert e (AssertReason se)) /\
    expr_sim_inv cenv cx env es /\
    IS_SOME (type_stmt env ret_ty (Assert e (AssertReason se))) /\
    stmt_exprs_ok cenv (Assert e (AssertReason se)) /\
    call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason se))) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (Assert e (AssertReason se)) es = (res, es') /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
             (INL (BoolV F), es1) ==>
           expr_vv_sim ctx func cenv cx (expr_type se) se es1) /\
    (!sa vv sb. compile_expr cenv (expr_type se) se sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assert e (AssertReason se))) es res es'
Proof
  rpt strip_tac >> `~cenv.ce_is_ctor` by fs[body_inv_def] >>
  `expr_type e = BaseT BoolT` by gvs[type_stmt_def] >>
  Cases_on `?ml str. se = Literal (BaseT (StringT ml)) (StringL str)`
  >- (gvs[] >> irule compile_assert_reason_lit_frag >> simp[] >>
      metis_tac[compile_expr_grows]) >>
  irule compile_assert_code_reason_frag >> gvs[] >> metis_tac[]
QED

(* The reason simulates where the condition is false: both are pure, so
   the condition's evaluation keeps expr_sim_inv (expr_sim_pre_eval). *)
Theorem assert_reason_vv_sim[local]:
  !cx e se tops ctx func cenv env es es1.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_ok cx se) /\
    body_inv tops ctx cenv cx /\ expr_sim_pre cenv cx env e es /\
    well_typed_expr env se /\ int_calls_expr se = [] /\
    ~expr_has_evm_run se /\
    ~supported_expr_exists
       (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) se /\
    (do raw <- eval_expr cx e; read_result cx raw od) es =
      (INL (BoolV F), es1) ==>
    expr_vv_sim ctx func cenv cx (expr_type se) se es1
Proof
  rpt strip_tac >> drule_all expr_sim_pre_eval >> strip_tac >>
  `?tv t. eval_expr cx e es = (INL tv, t)` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_expr_ok cx se` by metis_tac[] >>
  `expr_body_pre cenv cx env se es1` by
    (gvs[expr_body_pre_def, expr_sim_pre_def] >>
     CCONTR_TAC >> qpat_x_assum `~supported_expr_exists _ _` mp_tac >>
     simp[] >> irule supported_expr_exists_root >> metis_tac[]) >>
  metis_tac[body_expr_ok_def]
QED

(* As body_raise_reason_case, after compile_assert_frag's condition. *)
Theorem body_assert_reason_case:
  !cx e se.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_ok cx se) /\
    body_expr_ok cx e ==>
    body_stmt_ok cx (Assert e (AssertReason se))
Proof
  rw[body_stmt_ok_def] >>
  `supported_pure_expr tops e /\ supported_string_reason tops se` by
    gvs[supported_stmt_def, supported_assert_reason_def] >>
  `expr_type e = BaseT BoolT /\ well_typed_expr env e /\
   well_typed_expr env se` by gvs[type_stmt_def] >>
  `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
  `supported_expr tops e` by simp[supported_expr_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `~expr_has_evm_run se` by
    metis_tac[supported_string_reason_body_calls] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >>
     qexists_tac `int_calls_assert_reason (AssertReason se)` >> simp[]) >>
  `expr_sim ctx func cenv cx (BaseT BoolT) e es` by
    metis_tac[body_expr_ok_def] >>
  Cases_on `?ml str. se = Literal (BaseT (StringT ml)) (StringL str)`
  >- (gvs[] >> irule compile_assert_reason_lit_frag >> simp[] >>
      metis_tac[compile_expr_grows]) >>
  `int_calls_expr se = []` by
    (Cases_on `?t str. se = Literal t (StringL str)`
     >- gvs[int_calls_expr_def] >>
     `supported_pure_expr tops se` suffices_by
       metis_tac[supported_pure_int_calls] >>
     Cases_on `se` >> gvs[supported_string_reason_def] >>
     rename1 `Literal _ lit` >> Cases_on `lit` >>
     gvs[supported_string_reason_def]) >>
  `!es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
           (INL (BoolV F), es1) ==>
         expr_vv_sim ctx func cenv cx (expr_type se) se es1` by
    (rpt strip_tac >> irule assert_reason_vv_sim >>
     gvs[expr_sim_pre_body, stmt_exprs_ok_def,
         supported_stmt_expr_exists_def, supported_assert_exists_def] >>
     metis_tac[]) >>
  Cases_on `reason_covered cenv se`
  >- (gvs[reason_covered_def]
      >- (irule compile_assert_reason_frag >> simp[] >> metis_tac[])
      >- (irule compile_assert_storage_reason_frag >> simp[] >>
          metis_tac[])) >>
  irule body_assert_reason_other >> simp[] >>
  reverse conj_tac >-
    (conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule supported_reason_code >> simp[] >> metis_tac[]
QED

(* RESIDUAL (#637 append): an append to a storage or transient DynArray,
   the only target supported_append_target admits.  It waits on the
   storage statement of #713, which relates the array's slots. *)
Theorem body_append_storage_other:
  !cx nid e.
    (!s'' p t'. eval_target_place cx (TopLevelNameTarget nid) s'' = (INL p,t') ==>
                body_expr_ok cx e) ==>
    body_stmt_ok cx (Append (TopLevelNameTarget nid) e)
Proof
  cheat
QED

(* supported_append_target admits no local, subscript or attribute target
   (#549, #559), so the storage root is the only form. *)
Theorem body_append_case:
  !cx t e.
    (!s'' p t'. eval_target_place cx t s'' = (INL p,t') ==> body_expr_ok cx e) /\
    body_base_target_ok cx t ==>
    body_stmt_ok cx (Append t e)
Proof
  rpt strip_tac >> Cases_on `?nid. t = TopLevelNameTarget nid`
  >- (gvs[] >> irule body_append_storage_other >> first_assum ACCEPT_TAC) >>
  Cases_on `t` >> gvs[] >>
  rw[body_stmt_ok_def, supported_stmt_def, supported_append_target_def]
QED

(* ===== Assignments ===== *)

(* expr_sim_pre_eval_result and expr_sim_pre_eval under expr_body_pre
   (exprSimHyps' expr_body_pre_eval_result). *)
Theorem expr_body_pre_eval_result:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_sim_inv cenv cx env es'
Proof
  metis_tac[exprSimHypsTheory.expr_body_pre_eval_result]
QED

Theorem expr_body_pre_eval:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\
    (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\
    !v. res = INL v ==> value_runtime_typed env (expr_type e) v
Proof
  rpt strip_tac >>
  `state_well_typed es' /\
   (case res of INL v => value_runtime_typed env (expr_type e) v | INR _ => T)` by
    (drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
     disch_then (qspec_then `env` mp_tac) >>
     gvs[expr_body_pre_def, expr_sim_inv_def]) >>
  gvs[] >>
  qpat_x_assum `(do result <- eval_expr _ _; read_result _ result od) _ = _` mp_tac >>
  simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  drule_all expr_body_pre_eval_result >> simp[]
QED

(* A word type takes no wider type (type_widens_to). *)
Theorem type_widens_to_word:
  !tenv t u. type_widens_to tenv t u /\ is_word_type u ==> t = u
Proof
  rw[type_widens_to_def] >>
  Cases_on `t` >> Cases_on `u` >> gvs[arg_type_fits_def, is_word_type_def] >>
  rename1 `arg_type_fits (BaseT b1) (BaseT b2)` >>
  Cases_on `b1` >> Cases_on `b2` >> gvs[arg_type_fits_def, is_word_type_def] >>
  rename1 `arg_type_fits (BaseT (BytesT d1)) (BaseT (BytesT d2))` >>
  Cases_on `d1` >> Cases_on `d2` >> gvs[arg_type_fits_def, is_word_type_def]
QED

(* An assignment to a word local: stmtSimAssign's
   compile_assign_local_stmt_frag. *)
Theorem body_assign_local_word[local]:
  !cx id e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'
   ty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (res, es') /\
    FLOOKUP env.var_types id = SOME ty /\ is_word_type ty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      es res es'
Proof
  rpt strip_tac >>
  `well_typed_expr env e /\ expr_type e = ty` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_expr_def,
         AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >>
     Cases_on `asg` >> gvs[] >> metis_tac[type_widens_to_word]) >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, int_calls_stmt_def,
         int_calls_atarget_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  drule_all expr_sim_inv_local >> strip_tac >>
  irule compile_assign_local_stmt_frag >> simp[] >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  `expr_sim ctx func cenv cx ty e es` by metis_tac[body_expr_ok_def] >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by metis_tac[] >>
  simp[] >> rpt strip_tac >>
  drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[value_runtime_typed_def] >>
  qspecl_then [`cenv`, `cx`, `env`, `es1`, `id`, `expr_type e`] mp_tac
    expr_sim_inv_local >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[store_lays_out_typed]
QED

(* A storage declaration found by name is a variable declaration of tops
   under that name. *)
Theorem find_var_decl_storage_mem[local]:
  !ts id tr typ id_str.
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) ==>
    id_str = id /\ ?vis mut init. MEM (VariableDecl vis mut id typ init) ts
Proof
  Induct >> simp[find_var_decl_by_name_def] >> Cases >>
  rw[find_var_decl_by_name_def] >> metis_tac[]
QED

Theorem find_var_decl_storage_some[local]:
  !ts vis mut id ty init.
    MEM (VariableDecl vis mut id ty init) ts /\
    (mut = Storage \/ mut = Transient) ==>
    find_var_decl_by_name id ts <> NONE
Proof
  Induct >> simp[] >> Cases >> rw[find_var_decl_by_name_def] >> metis_tac[]
QED

Theorem supported_variable_decl_mem[local]:
  !tops src id vis mut ty slot.
    supported_variable_decl tops (src, id) = SOME (vis, mut, ty, slot) ==>
    src = NONE /\ MEM (VariableDecl vis mut id ty slot) tops
Proof
  Induct >> simp[supported_variable_decl_def] >> Cases >>
  rw[supported_variable_decl_def] >> metis_tac[]
QED

Theorem build_hashmap_info_absent[local]:
  !tops id.
    ~MEM (NONE, id)
       (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) ==>
    build_hashmap_info tops (NONE, id) = NONE
Proof
  Induct >> simp[build_hashmap_info_def] >> Cases >>
  simp[build_hashmap_info_def, toplevel_vtype_keys_toplevel_def]
QED

(* With distinct names, cenv's maps at a module variable's key are its
   declaration's. *)
Theorem build_maps_variable[local]:
  !tops vis mut id ty init.
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
    MEM (VariableDecl vis mut id ty init) tops ==>
    build_hashmap_info tops (NONE, id) = NONE /\
    build_var_type_map tops (NONE, id) = SOME ty
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> Cases_on `h` >>
  gvs[build_hashmap_info_def, build_var_type_map_def,
      toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  metis_tac[build_hashmap_info_absent, module_toplevel_vtype_key_MEM_Variable]
QED

Theorem env_assignable_find_NONE[local]:
  !env cx st src id ty.
    env_consistent env cx st /\
    FLOOKUP env.bare_global_assignable (src, id) = SOME ty ==>
    ?ts. get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE
Proof
  rw[env_consistent_def, env_context_consistent_def] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

(* A supported scalar target is a word variable of tops in storage or
   transient storage. *)
Theorem supported_scalar_target_decl[local]:
  !tops src id.
    supported_scalar_target tops (src, id) ==>
    src = NONE /\ find_var_decl_by_name id tops <> NONE /\
    ?vis mut ty slot. MEM (VariableDecl vis mut id ty slot) tops /\
                      is_word_type ty
Proof
  rpt gen_tac >> simp[supported_scalar_target_def] >>
  Cases_on `supported_variable_decl tops (src, id)` >> simp[] >>
  rename1 `SOME x` >> PairCases_on `x` >>
  Cases_on `x0` >> Cases_on `x1` >> Cases_on `x3` >> simp[] >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >>
  `find_var_decl_by_name id tops <> NONE` by
    metis_tac[find_var_decl_storage_some] >>
  gvs[supported_full_word_type_def] >> first_assum (irule_at Any) >>
  simp[is_word_type_def]
QED

(* An assignment to a word storage or transient variable:
   stmtSimAssignStorage's compile_assign_storage_typed_stmt_frag.  The
   typing finds the variable's declaration and layout slot, and body_inv's
   module clauses give cenv's view of it. *)
Theorem body_assign_toplevel_word[local]:
  !cx src id e tops ctx func cenv env env' ret_ty lctx RetQ es res es'.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_scalar_target tops (src, id) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (src, id))) e) =
      SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget (src, id))) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget (src, id))) e)) /\
    eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e) es =
      (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (TopLevelNameTarget (src, id))) e)) es res es'
Proof
  rpt strip_tac >>
  drule supported_scalar_target_decl >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  Cases_on `type_place_target env (TopLevelNameTarget (NONE, id))` >>
  gvs[type_stmt_def, atarget_accepts_def] >>
  rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `t = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> rename1 `FLOOKUP env.toplevel_vtypes _ = SOME (Type ty)` >>
  `expr_type e = ty` by metis_tac[type_widens_to_word] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, int_calls_stmt_def,
         int_calls_atarget_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `expr_sim ctx func cenv cx ty e es` by metis_tac[body_expr_ok_def] >>
  irule compile_assign_storage_typed_stmt_frag >> simp[] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  rename1 `lookup_var_slot_from_layout _ _ _ _ = SOME slot'` >>
  rename1 `evaluate_type _ ty = SOME tvt` >>
  qexistsl_tac [`slot'`, `tvt`] >> simp[] >> rpt strip_tac >>
  drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  gvs[value_runtime_typed_def]
QED

(* An assignment to a local in memory of the local's own type, a bytestring
   (a narrower one widens: Bytes[10] into Bytes[64]), or an empty value of a
   type with a length word: stmtSimAssignMem's
   compile_assign_local_memory_stmt_frag and the same for the widening and
   for the empty value, as stmtSimDeclMem's and stmtSimDeclEmpty's
   declarations.  The local's size is below 2 ** 64 (locals_alloc_ok), so
   its buffer and a bytestring copy's length word fit below 2 ** 256. *)
Theorem body_assign_local_rhs_pre[local]:
  !cx id e tops bindings ctx cenv env env' ret_ty es ty.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty ==>
    supported_expr tops e /\ well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) ty /\
    expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) ty` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_expr_def, AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >> Cases_on `asg` >> gvs[]) >>
  simp[] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, int_calls_stmt_def,
      int_calls_atarget_def, int_calls_expr_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem body_assign_local_memory_read[local]:
  !cenv cx env e es tops id ty tyv v es1 entry.
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    FLOOKUP env.var_types id = SOME ty /\
    type_widens_to env.type_defs (expr_type e) ty /\
    (expr_type e = ty \/ is_bytestring_type ty) /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) /\
    lookup_scopes id es1.scopes = SOME entry ==>
    entry.type = tyv /\ value_has_type tyv v /\
    val_footprint tyv v <= type_memory_bytes cenv (lowered_value_type cenv e)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `entry.type = tyv` by metis_tac[memory_rhs_read_local_type] >>
  simp[] >> irule memory_rhs_read_destination_footprint >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`cx`, `env`, `es`, `es1`, `ty`] >> simp[]
QED

Theorem body_assign_local_memory:
  !cx id e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'
   ty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (res, es') /\
    FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    (expr_type e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      es res es'
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all body_assign_local_rhs_pre >> strip_tac >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by metis_tac[] >>
  `type_memory_bytes cenv ty = type_memory_size entry.type` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv ty < 2 ** 64` by
    metis_tac[locals_alloc_ok_def] >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
  >- (`has_length_word ty` by metis_tac[type_widens_to_has_length_word] >>
      irule compile_assign_local_empty_stmt_frag >> simp[] >>
      qexists_tac `ty` >> simp[] >>
      irule memory_rhs_empty_read_destination >> simp[] >>
      qexistsl_tac [`env`, `ty`] >> simp[]) >>
  `expr_type e = ty \/ is_bytestring_type ty` by metis_tac[] >>
  `0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
   type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_bytes cenv ty` by
    metis_tac[memory_rhs_destination_bound] >>
  `type_memory_size entry.type + 64 < dimword (:256)` by
    metis_tac[allocation_limit_word_room] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256)` by
    decide_tac >>
  `expr_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_ok_def] >>
  drule expr_body_pre_type_evaluates >>
  disch_then (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  irule compile_assign_local_memory_widen_stmt_frag >> gns[] >>
  rpt conj_tac >>~- ([`val_footprint _ _ <= _`],
    rpt gen_tac >> strip_tac >> metis_tac[body_assign_local_memory_read, type_widens_to_def]) >>
  metis_tac[lowered_value_type_shape, type_widens_to_def,
            arg_type_fits_bytestring_source]
QED

(* An assignment to a word field of a local struct: stmtSimAssignAttr's
   compile_assign_attr_local_case. *)
Theorem body_assign_attr_local[local]:
  !cx id fld e tops ctx func cenv env env' ret_ty lctx RetQ es res es' sid
   fty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) =
      SOME env' /\
    stmt_exprs_ok cenv
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) /\
    eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
      es = (res, es') /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    attribute_type env.type_defs (StructT sid) fld = SOME fty /\
    is_word_type fty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      es res es'
Proof
  rpt strip_tac >>
  `well_typed_expr env e /\ expr_type e = fty` by
    (Cases_on `type_place_target env (AttributeTarget (NameTarget id) fld)` >>
     gvs[type_stmt_def, atarget_accepts_def] >>
     rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
     gvs[vyperTypeEnvTheory.type_place_target_AttributeTarget,
         vyperTypeEnvTheory.type_place_target_NameTarget] >>
     metis_tac[type_widens_to_word]) >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, supported_expr_exists_def,
         int_calls_stmt_def, int_calls_atarget_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim ctx func cenv cx fty e es` by metis_tac[body_expr_ok_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                    (nsid_to_string sid)) fld = SOME (fty, fsz)` by
    metis_tac[attribute_type_struct_field] >>
  irule compile_assign_attr_local_case >> simp[] >> metis_tac[]
QED

(* A struct field write the supported subset admits is to a storage or
   transient struct of the main module, tops. *)
Theorem supported_storage_field_write_decl[local]:
  !tops src id fld.
    supported_storage_field_write tops (src, id) fld ==>
    src = NONE /\ find_var_decl_by_name id tops <> NONE /\
    ?mut sid slot. MEM (VariableDecl Private mut id (StructT sid) slot) tops
Proof
  rpt gen_tac >>
  simp[supported_storage_field_write_def,
       supportedExprFormsTheory.supported_storage_fields_def] >>
  Cases_on `supported_variable_decl tops (src, id)` >> simp[] >>
  rename1 `SOME x` >> PairCases_on `x` >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  Cases_on `x0` >> Cases_on `x1` >> Cases_on `x2` >> Cases_on `x3` >> simp[] >>
  metis_tac[find_var_decl_storage_some]
QED

(* An assignment to a word field of a storage or transient struct:
   stmtSimAssignAttrStorage's compile_assign_attr_storage_case.  The
   supported subset puts the struct in tops with a slot, the typing finds
   its declaration and layout slot, and body_inv's module clauses give
   cenv's view of it. *)
Theorem body_assign_attr_storage[local]:
  !cx src id fld e tops ctx func cenv env env' ret_ty lctx RetQ es res es'
   fty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    supported_storage_field_write tops (src, id) fld /\
    type_place_target env
      (AttributeTarget (TopLevelNameTarget (src, id)) fld) =
      SOME (Type fty) /\
    is_word_type fty /\
    type_stmt env ret_ty
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) = SOME env' /\
    stmt_exprs_ok cenv
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e)) /\
    eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) es = (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e)) es res es'
Proof
  rpt strip_tac >>
  `well_typed_expr env e /\ expr_type e = fty` by
    (gvs[type_stmt_def, atarget_accepts_def] >>
     metis_tac[type_widens_to_word]) >>
  drule supported_storage_field_write_decl >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[vyperTypeEnvTheory.type_place_target_AttributeTarget,
      vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ tgt_ty fld = SOME _` >>
  `tgt_ty = StructT sid` by
    metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> drule_all build_maps_variable >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                    (nsid_to_string sid)) fld = SOME (expr_type e, fsz)` by
    metis_tac[attribute_type_struct_field] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, supported_expr_exists_def,
         int_calls_stmt_def, int_calls_atarget_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_ok_def] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  irule compile_assign_attr_storage_case >> simp[] >> metis_tac[]
QED

Theorem body_assign_copy_rhs_pre[local]:
  !tops ctx cenv cx e env es ret_ty nsid env'.
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) =
      SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) ==>
    expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `well_typed_expr env e` by
    gvs[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, int_calls_stmt_def,
      int_calls_atarget_def, int_calls_expr_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem body_assign_copy_region[local]:
  !cx mid id tr off tvt.
    storage_layout_safe cx /\
    storage_var_info cx mid id = SOME (tr,off,tvt) /\
    0 < type_slot_size tvt ==>
    off + type_slot_size tvt <= dimword (:256) /\
    (!mid' n' subs' k' tv'.
      declared_storage_region cx mid' n' subs' = SOME (tr,k',tv') /\
      (k',tv') <> (n2w off,tvt) ==>
      ranges_disjoint off (type_slot_size tvt) (w2n k') (type_slot_size tv'))
Proof
  rpt gen_tac >> strip_tac >>
  `off + type_slot_size tvt <= dimword (:256)` by
    (drule storage_layout_safe_layout >>
     simp[well_formed_layout_def] >> metis_tac[]) >>
  `off < dimword (:256)` by decide_tac >>
  `w2n (n2w off : 256 word) = off` by simp[] >>
  drule declared_storage_region_ordinary >> strip_tac >>
  simp[] >> rpt strip_tac >>
  `(mid,id,[]) <> (mid',n',subs')` by
    (strip_tac >> gvs[]) >>
  drule_all storage_layout_safe_region_separation >> simp[]
QED

Theorem body_assign_copy_target[local]:
  !tops ctx cenv cx src id mut ty ast_slot env es ret_ty e env'.
    body_inv tops ctx cenv cx /\
    supported_variable_decl tops (src,id) = SOME (Private,mut,ty,SOME ast_slot) /\
    (mut = Storage \/ mut = Transient) /\ expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) =
      SOME env' ==>
    src = NONE /\ get_module_code cx NONE = SOME tops /\
    cenv.ce_hashmap_info (NONE,id) = NONE /\
    cenv.ce_module_var_type (NONE,id) = SOME ty /\
    ?tr id_str off tvt.
      find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,id_str) /\
      lookup_var_slot_from_layout cx tr NONE id_str = SOME off /\
      evaluate_type (get_tenv cx) ty = SOME tvt
Proof
  rpt gen_tac >> strip_tac >> (
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `find_var_decl_by_name id tops <> NONE` by
    metis_tac[find_var_decl_storage_some] >>
  Cases_on `type_place_target env (TopLevelNameTarget (NONE,id))` >>
  gvs[type_stmt_def, atarget_accepts_def] >>
  rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `t = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  metis_tac[])
QED

(* An assignment to a private storage or transient variable of a type that
   is not a word, not a DynArray and not empty, from a value of exactly that
   type: stmtSimAssignStorageCopy's compile_assign_storage_copy_stmt_frag.
   The region separation it asks for comes from storage_layout_safe in
   expr_sim_inv. *)
Theorem body_assign_toplevel_copy[local]:
  !cx nsid e tops ctx func cenv env env' ret_ty lctx RetQ es res es' mut ty
   slot.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
    (mut = Storage \/ mut = Transient) /\
    ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
    0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
    supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) =
      SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
    eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e) es =
      (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es res es'
Proof
  rpt gen_tac >> Cases_on `nsid` >>
  rename1 `supported_variable_decl tops (src,id)` >> strip_tac >> (
  drule_at (Pos (el 2)) body_assign_copy_target >>
  disch_then drule >> simp[] >> disch_then drule >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule_all body_assign_copy_rhs_pre >> strip_tac >>
  drule_all exprSimHypsTheory.expr_sim_inv_memory_size >> strip_tac >>
  `0 < type_slot_size tvt` by
    gvs[storageDecodeMemoryTheory.type_memory_size_slots] >>
  `storage_layout_safe cx /\ env_consistent env cx es` by
    fs[expr_sim_inv_def] >>
  `storage_var_info cx NONE id = SOME (tr,off,tvt)` by
    simp[storage_var_info_def] >>
  drule_all body_assign_copy_region >> strip_tac >>
  `expr_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_ok_def] >>
  `!ann t args. e = TypeBuiltin ann Empty t args ==> t = expr_type e` by
    (rpt strip_tac >> gvs[type_stmt_def, atarget_accepts_def,
       well_typed_expr_def, type_builtin_result_ok_def, expr_type_def,
       AllCaseEqs()]) >>
  irule compile_assign_storage_copy_stmt_frag >> asm_rewrite_tac[] >>
  qexistsl_tac [`id_str`, `off`, `tr`, `tops`, `tvt`, `expr_type e`] >>
  asm_rewrite_tac[] >>
  rpt strip_tac >> drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  gvs[value_runtime_typed_def])
QED

(* A local assigned to takes memory: its type is a widening of the assigned
   value's type, which is assignable. *)
Theorem assign_local_memory_bytes_pos[local]:
  !cenv cx env es ret_ty id e env' ty.
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    FLOOKUP env.var_types id = SOME ty ==>
    0 < type_memory_bytes cenv ty
Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `assignable_type env.type_defs ty` by
    (gvs[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
     Cases_on `type_place_target env (NameTarget id)` >> gvs[] >>
     rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
     gvs[vyperTypeEnvTheory.type_place_target_NameTarget] >>
     metis_tac[vyperTypeArgFitsTheory.type_widens_to_assignable_type]) >>
  irule exprSimAggregateLayoutTheory.expr_sim_inv_memory_bytes_pos >>
  metis_tac[]
QED

(* Assignments to a field or an element (an AttributeTarget or a
   SubscriptTarget, of any base), through the target/place judgment
   (targetPlaceSimCases' target_case_all and target_place_sim): the
   target's fragment leaves the place's pointer, location and type, and the
   value is stored there as compile_assign_value does by the target's
   location.  The supported subset gives such a target a local, storage or
   transient root (never an immutable: supported_place_root).  Split by
   whether the target's type is a word.  GAP: cheated, for alan. *)
Theorem body_assign_place_word:
  !cx t e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es' ty.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ok cx t) /\
    body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (Assign (BaseTarget t) e) es = (res, es') /\
    ((?bt fld. t = AttributeTarget bt fld) \/ (?bt k. t = SubscriptTarget bt k)) /\
    type_place_target env t = SOME (Type ty) /\ is_word_type ty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e)) es res es'
Proof
  cheat
QED

Theorem body_assign_place_copy:
  !cx t e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es' ty.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ok cx t) /\
    body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (Assign (BaseTarget t) e) es = (res, es') /\
    ((?bt fld. t = AttributeTarget bt fld) \/ (?bt k. t = SubscriptTarget bt k)) /\
    type_place_target env t = SOME (Type ty) /\ ~is_word_type ty /\
    (expr_type e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e)) es res es'
Proof
  cheat
QED

(* RESIDUAL (#637 assignments): the other base targets.
   - A local in memory that body_assign_local_memory leaves: a value
     that widens to a type other than a bytestring (type_widens_to: a
     DynArray of a smaller bound, elementwise) has no statement lemma.
   - A storage or transient variable that is not a word, other than
     body_assign_toplevel_copy's: a DynArray (compile_dynarray_to_storage),
     a value of a narrower type (a widened bytestring), or a type of size
     0: no statement lemma.
   - An immutable (supported_target's supported_immutable_type): no
     statement lemma.
   - A field or element target (body_assign_place_word/_copy take the
     rest) of an aggregate type the value widens to other than a
     bytestring: no statement lemma, as for a local. *)
Theorem body_assign_other:
  !cx t e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ok cx t) /\
    body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (Assign (BaseTarget t) e) es = (res, es') /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) /\
    ~(((?bt fld. t = AttributeTarget bt fld) \/
       (?bt k. t = SubscriptTarget bt k)) /\
      ?ty. type_place_target env t = SOME (Type ty) /\
           (is_word_type ty \/
            expr_type e = ty \/ is_bytestring_type ty \/
            has_length_word (expr_type e) /\ is_empty_value_expr e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e)) es res es'
Proof
  cheat
QED

Theorem body_assign_case:
  !cx t e.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ok cx t) /\
    body_expr_ok cx e ==>
    body_stmt_ok cx (Assign (BaseTarget t) e)
Proof
  rw[body_stmt_ok_def] >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  Cases_on `?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
                    is_word_type ty`
  >- (gvs[] >> irule body_assign_local_word >> metis_tac[]) >>
  Cases_on `?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
                    ~is_word_type ty /\
                    (expr_type e = ty \/ is_bytestring_type ty \/
                     has_length_word (expr_type e) /\ is_empty_value_expr e)`
  >- (`!id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty ==>
              0 < type_memory_bytes cenv ty` by
        (rpt strip_tac >> gvs[] >>
         metis_tac[assign_local_memory_bytes_pos]) >>
      gvs[] >> irule body_assign_local_memory >> metis_tac[]) >>
  Cases_on `?nsid. t = TopLevelNameTarget nsid /\
                   supported_scalar_target tops nsid`
  >- (gvs[] >> rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      irule body_assign_toplevel_word >> metis_tac[]) >>
  Cases_on `?nsid mut ty slot.
              t = TopLevelNameTarget nsid /\
              supported_variable_decl tops nsid =
                SOME (Private, mut, ty, SOME slot) /\
              (mut = Storage \/ mut = Transient) /\
              ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
              0 < type_memory_bytes cenv ty /\ expr_type e = ty`
  >- (gvs[] >> irule body_assign_toplevel_copy >> metis_tac[]) >>
  Cases_on `?id fld sid fty.
              t = AttributeTarget (NameTarget id) fld /\
              FLOOKUP env.var_types id = SOME (StructT sid) /\
              attribute_type env.type_defs (StructT sid) fld = SOME fty /\
              is_word_type fty`
  >- (gvs[] >> irule body_assign_attr_local >> metis_tac[]) >>
  Cases_on `?nsid fld fty.
              t = AttributeTarget (TopLevelNameTarget nsid) fld /\
              supported_storage_field_write tops nsid fld /\
              type_place_target env t = SOME (Type fty) /\ is_word_type fty`
  >- (gvs[] >> rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      irule body_assign_attr_storage >> metis_tac[]) >>
  Cases_on `((?bt fld. t = AttributeTarget bt fld) \/
             (?bt k. t = SubscriptTarget bt k)) /\
            ?ty. type_place_target env t = SOME (Type ty) /\
                 (is_word_type ty \/
                  expr_type e = ty \/ is_bytestring_type ty \/
                  has_length_word (expr_type e) /\ is_empty_value_expr e)`
  >- (qpat_x_assum `(_ \/ _) /\ ?ty. _`
        (CONJUNCTS_THEN2 assume_tac
           (qx_choose_then `ty` (CONJUNCTS_THEN assume_tac))) >>
      Cases_on `is_word_type ty`
      >- (irule body_assign_place_word >> metis_tac[]) >>
      irule body_assign_place_copy >> metis_tac[]) >>
  irule body_assign_other >> simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`bindings`, `env`, `env'`, `tops`] >> fs[]
QED

(* The frame's target has MCOPY: the unit's policy target, which
   run_lowering requires to have it (lowering_policy_ok). *)
Theorem body_inv_mcopy[local]:
  !tops ctx cenv cx. body_inv tops ctx cenv cx ==> cenv.ce_target CapMcopy
Proof
  rw[body_inv_def] >>
  gvs[lower_vyper_runtime_unit_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[vyperCompilerTheory.run_lowering_def, AllCaseEqs(),
      vyperCompilerTheory.lowering_policy_ok_def]
QED

(* A local of a tuple target, of a type with a size that is not 0: held
   through a pointer at its own type, and if in memory, with a size below
   2 ** 64 (locals_alloc_ok), so a bytestring copy's 64 bytes of rounding
   fit below 2 ** 256. *)
Theorem tuple_target_local_ptr[local]:
  !cenv cx env es id ty tv.
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    FLOOKUP env.var_types id = SOME ty /\ 0 < type_memory_bytes cenv ty /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    ?p sz vt.
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type id = SOME vt /\
      if is_word_type ty then is_word_type vt
      else
        (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
        type_memory_bytes cenv ty = type_memory_size tv /\
        ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
              type_memory_bytes cenv vt = type_memory_size vtv /\
              0 < type_memory_size vtv /\
              type_memory_size vtv + 64 < dimword (:256)
Proof
  rpt strip_tac >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    metis_tac[expr_sim_inv_local] >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  qexistsl_tac [`p`, `sz`, `ty`] >> simp[] >>
  Cases_on `is_word_type ty` >> simp[] >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv ty < 2 ** 64` by metis_tac[locals_alloc_ok_def] >>
  metis_tac[allocation_limit_word_room]
QED

(* After the source is read, a local of a tuple target holds a value of its
   own type: a word as stored, otherwise at the type its pointer has. *)
Theorem tuple_target_local_lays_out[local]:
  !cenv cx env es1 id ty tv v entry.
    expr_sim_inv cenv cx env es1 /\ FLOOKUP env.var_types id = SOME ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    lookup_scopes id es1.scopes = SOME entry ==>
    if is_word_type ty then store_lays_out tv entry.type v
    else
      ?vt. cenv.ce_var_type id = SOME vt /\
           evaluate_type (get_tenv cx) vt = SOME entry.type /\
           value_has_type entry.type v
Proof
  rpt strip_tac >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by
    metis_tac[expr_sim_inv_local] >>
  `entry.type = tv` by metis_tac[optionTheory.SOME_11] >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  IF_CASES_TAC >> simp[] >> metis_tac[store_lays_out_typed]
QED

(* The buffer a tuple assignment stages a memory view's value in fits
   below 2 ** 256: alloc_limits_stmt bounds it by 2 ** 64. *)
Theorem tuple_staging_bound[local]:
  !cenv cx env es g e tys tvs.
    expr_sim_inv cenv cx env es /\
    stmt_exprs_ok cenv (Assign (TupleTarget g) e) /\
    expr_type e = TupleT tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    is_memory_view e ==>
    type_memory_size (TupleTV tvs) < dimword (:256)
Proof
  rpt strip_tac >>
  `type_memory_bytes cenv (TupleT tys) < 2 ** 64` by
    gvs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size (TupleTV tvs)` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_size (TupleTV tvs) + 64 < dimword (:256)` by
    metis_tac[allocation_limit_word_room] >>
  decide_tac
QED

(* A tuple of locals of types with sizes that are not 0 (a word's is 32):
   stmtSimAssignTupleMem's compile_assign_tuple_locals_memory_stmt_frag.
   The target has MCOPY (body_inv_mcopy). *)
Theorem body_assign_tuple_locals[local]:
  !cx ids e tops ctx func cenv env env' ret_ty lctx RetQ es res es'.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) =
      SOME env' /\
    stmt_exprs_ok cenv
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) /\
    eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)
      es = (res, es') /\
    ids <> [] /\
    EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                     0 < type_memory_bytes cenv ty) ids ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      es res es'
Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tys. expr_type e = TupleT tys /\ well_typed_expr env e /\
         assignable_type (get_tenv cx) (TupleT tys) /\
         LENGTH tys = LENGTH ids /\
         !i. i < LENGTH ids ==>
             FLOOKUP env.var_types (EL i ids) = SOME (EL i tys)` by
    gvs[type_stmt_def, atarget_accepts_def, well_typed_atarget_def,
        LIST_REL_EL_EQN, EL_MAP, well_typed_target_def,
        well_typed_expr_def, AllCaseEqs()] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >>
     qexists_tac `[]` >> simp[] >>
     metis_tac[call_evaluation_safe_append_right]) >>
  `?tup_tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tup_tv` by
    fs[assignable_type_def, well_formed_type_def,
       optionTheory.IS_SOME_EXISTS] >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  irule compile_assign_tuple_locals_memory_stmt_frag >>
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`tvs`, `tys`] >> rpt conj_tac
  >~ [`expr_sim _ _ _ _ _ _ _`] >- metis_tac[body_expr_ok_def]
  >~ [`cenv.ce_target CapMcopy`] >- metis_tac[body_inv_mcopy]
  >~ [`type_memory_size (TupleTV _) < _`]
  >- (strip_tac >> irule tuple_staging_bound >> metis_tac[])
  >~ [`FLOOKUP cenv.ce_vars _`]
  >- (rpt strip_tac >>
      `FLOOKUP env.var_types (EL i ids) = SOME (EL i tys)` by simp[] >>
      `0 < type_memory_bytes cenv (EL i tys)` by
        (qpat_x_assum `EVERY _ ids` mp_tac >> simp[EVERY_EL] >>
         disch_then drule >> strip_tac >> gvs[]) >>
      irule tuple_target_local_ptr >> fs[LIST_REL_EL_EQN] >> metis_tac[])
  >~ [`store_lays_out _ _ _`]
  >- (rpt strip_tac >> drule_all expr_body_pre_eval >> strip_tac >>
      `value_has_type (EL i tvs) (EL i vs)` by
        gvs[value_runtime_typed_def, value_has_type_def,
            values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
      irule tuple_target_local_lays_out >> fs[LIST_REL_EL_EQN] >> metis_tac[])
  >~ [`value_has_type (TupleTV _) _`]
  >- (rpt strip_tac >> drule_all expr_body_pre_eval >> strip_tac >>
      gvs[value_runtime_typed_def]) >>
  first_assum ACCEPT_TAC
QED

(* The locals a tuple is assigned to take memory: their types are the
   tuple's element types, which are assignable, so they take a storage slot
   (assignable_type_slot_size_pos). *)
Theorem assign_tuple_locals_bytes_pos[local]:
  !cenv cx env es ret_ty ids e env'.
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) =
      SOME env' ==>
    EVERY (\id. !ty. FLOOKUP env.var_types id = SOME ty ==>
                     0 < type_memory_bytes cenv ty) ids
Proof
  rpt strip_tac >>
  `?tys. LIST_REL (\tgt ty. well_typed_atarget env tgt ty)
           (MAP (BaseTarget o NameTarget) ids) tys /\
         assignable_type env.type_defs (TupleT tys)` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_atarget_def,
         AllCaseEqs()] >> metis_tac[]) >>
  `EVERY (assignable_type env.type_defs) tys` by fs[assignable_type_def, EVERY_MEM] >>
  rw[EVERY_EL] >>
  `n < LENGTH tys /\
   well_typed_atarget env (BaseTarget (NameTarget (EL n ids))) (EL n tys)` by
    (fs[LIST_REL_EL_EQN] >> first_x_assum (qspec_then `n` mp_tac) >>
     simp[EL_MAP]) >>
  `ty = EL n tys` by
    gvs[well_typed_atarget_def, well_typed_target_def, vyperTypeEnvTheory.type_place_target_NameTarget,
        AllCaseEqs()] >>
  `assignable_type env.type_defs ty` by metis_tac[EVERY_EL] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  irule exprSimAggregateLayoutTheory.expr_sim_inv_memory_bytes_pos >>
  metis_tac[]
QED

(* RESIDUAL (#637 tuple assignments): the other tuple targets.
   - Storage, subscript and attribute elements: no statement lemma for
     compile_tuple_store_all.
   An empty tuple target is supported but has no lemma either.  A nested
   TupleTarget is not supported (supported_assignment). *)
Theorem body_assign_tuple_other:
  !cx gs e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_ok cx (TupleTarget gs) v) /\ body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (Assign (TupleTarget gs) e) es = (res, es') /\
    ~(?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
            EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e)) es res es'
Proof
  cheat
QED

Theorem body_assign_tuple_case:
  !cx gs e.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_ok cx (TupleTarget gs) v) /\ body_expr_ok cx e ==>
    body_stmt_ok cx (Assign (TupleTarget gs) e)
Proof
  rw[body_stmt_ok_def] >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  Cases_on `?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
                  EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids`
  >- (gvs[] >> drule_all assign_tuple_locals_bytes_pos >> strip_tac >>
      `EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                        0 < type_memory_bytes cenv ty) ids` by
        (fs[EVERY_MEM] >> metis_tac[]) >>
      irule body_assign_tuple_locals >> metis_tac[]) >>
  irule body_assign_tuple_other >> metis_tac[]
QED

(* ===== Augmented assignments ===== *)

(* x op= e on a local: stmtSimAugAssign's compile_augassign_local_case,
   the operand's internal calls allowed. *)
Theorem body_augassign_local[local]:
  !cx ty id bop e tops ctx func cenv env env' ret_ty lctx RetQ es res es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (NameTarget id) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (NameTarget id) bop e) /\
    call_evaluation_safe cx
      (int_calls_stmt (AugAssign ty (NameTarget id) bop e)) /\
    eval_stmt cx (AugAssign ty (NameTarget id) bop e) es = (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e))
      es res es'
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def,
         int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `FLOOKUP env.var_types id = SOME ty /\
   well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
   (bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL ==> shift_amount_ok e) /\ (bop = ShR ==> shift_amount_ok e)` by
    (gvs[type_stmt_def, well_typed_target_def, well_typed_expr_def,
         DISJ_IMP_THM, AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_types id` >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >>
     Cases_on `asg` >> gvs[]) >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `body_expr_ok cx e` by
    (first_x_assum irule >> metis_tac[eval_target_place_local]) >>
  `expr_sim_case F ctx func cenv cx e` by metis_tac[body_expr_ok_case] >>
  irule compile_augassign_local_case >> simp[DISJ_IMP_THM] >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `F` >> simp[]
QED

(* x.f op= e on a field of a local struct: stmtSimAugAssignAttr's
   compile_augassign_attr_local_case.  The typing makes f's type a word
   (well_typed_binop_augassign_word), and x.f is read wherever
   expr_sim_inv holds (augassign_attr_local_place), which gives e's
   judgment. *)
Theorem body_augassign_attr_local[local]:
  !cx ty id fld bop e tops ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (NameTarget id) fld) s'' =
         (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) =
      SOME env' /\
    stmt_exprs_ok cenv
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) /\
    eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)
      es = (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      es res es'
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def,
         int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `?sid. FLOOKUP env.var_types id = SOME (StructT sid) /\
         attribute_type env.type_defs (StructT sid) fld = SOME ty /\
         well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\
         bop <> NotIn` by
    (gvs[type_stmt_def, well_typed_target_def,
         vyperTypeEnvTheory.type_place_target_AttributeTarget,
         vyperTypeEnvTheory.type_place_target_NameTarget] >>
     rename1 `attribute_type _ tgt_ty fld = SOME _` >>
     Cases_on `tgt_ty` >> gvs[attribute_type_def]) >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                    (nsid_to_string sid)) fld = SOME (ty, fsz)` by
    metis_tac[attribute_type_struct_field] >>
  `body_expr_ok cx e` by
    (drule_all augassign_attr_local_place >> strip_tac >>
     first_x_assum irule >> metis_tac[]) >>
  `expr_sim ctx func cenv cx ty e es` by metis_tac[body_expr_ok_def] >>
  irule compile_augassign_attr_local_case >> simp[] >> metis_tac[]
QED

(* self.x op= e on a word storage or transient variable:
   stmtSimAugAssignStorage's compile_augassign_toplevel_case.  The typing
   finds x's declaration, and body_inv's module clauses give cenv's view of
   it, as for body_assign_toplevel_word; x's place is read wherever
   expr_sim_inv holds, which gives e's judgment. *)
Theorem body_augassign_toplevel_word[local]:
  !cx ty src id bop e tops ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (TopLevelNameTarget (src, id)) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_scalar_target tops (src, id) /\
    supported_expr tops e /\ expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src, id)) bop e) =
      SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src, id)) bop e) /\
    call_evaluation_safe cx
      (int_calls_stmt (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) /\
    eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e) es =
      (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) es res es'
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  drule supported_scalar_target_decl >> strip_tac >> gvs[] >>
  rename1 `MEM (VariableDecl vis mut id dty init) tops` >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `type_place_target env (TopLevelNameTarget (NONE, id)) = SOME (Type ty) /\
   well_typed_expr env e /\ assignable_type env.type_defs ty /\
   well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
   (bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL ==> shift_amount_ok e) /\ (bop = ShR ==> shift_amount_ok e)` by
    gvs[type_stmt_def, well_typed_target_def, DISJ_IMP_THM, AllCaseEqs()] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `find_var_decl_by_name id tops = SOME (StorageVarDecl tr _, _)` >>
  `dty = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `lookup_var_slot_from_layout _ _ _ _ = SOME slot` >>
  rename1 `evaluate_type _ ty = SOME tvt` >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def,
         int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `?v0. read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es)` by
    (irule exprSimLeavesTheory.toplevel_storage_read_decodes >>
     gvs[expr_sim_inv_def] >> metis_tac[]) >>
  drule_all eval_target_place_toplevel >> strip_tac >>
  `body_expr_ok cx e` by
    (first_x_assum irule >> simp[read_place_def] >> metis_tac[]) >>
  `expr_sim_case F ctx func cenv cx e` by metis_tac[body_expr_ok_case] >>
  irule compile_augassign_toplevel_case >> simp[DISJ_IMP_THM] >>
  conj_tac
  >- (qexists_tac `env` >> simp[] >>
      metis_tac[assignable_type_well_formed]) >>
  qexists_tac `F` >> simp[]
QED

(* self.x.f op= e on a word field of a storage or transient struct:
   stmtSimAugAssignAttrStorage's compile_augassign_attr_storage_case.  The
   supported subset puts the struct in tops with a slot and the typing finds
   its declaration, as for body_assign_attr_storage; x.f's slot is read
   wherever expr_sim_inv holds, which gives e's judgment. *)
Theorem body_augassign_attr_storage[local]:
  !cx ty src id fld bop e tops ctx func cenv env env' ret_ty lctx RetQ es
   res es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx
         (AttributeTarget (TopLevelNameTarget (src, id)) fld) s'' =
         (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    supported_storage_field_write tops (src, id) fld /\
    type_stmt env ret_ty
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      = SOME env' /\
    stmt_exprs_ok cenv
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop
         e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld)
            bop e)) /\
    eval_stmt cx
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      es = (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld)
            bop e)) es res es'
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  drule supported_storage_field_write_decl >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def,
         int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `?tgt_ty. type_place_target env (TopLevelNameTarget (NONE, id)) =
              SOME (Type tgt_ty) /\
            attribute_type env.type_defs tgt_ty fld = SOME ty /\
            well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\
            bop <> NotIn` by
    gvs[type_stmt_def, well_typed_target_def,
        vyperTypeEnvTheory.type_place_target_AttributeTarget, AllCaseEqs()] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `tgt_ty = StructT sid` by
    metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> drule_all build_maps_variable >> strip_tac >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                    (nsid_to_string sid)) fld = SOME (ty, fsz)` by
    metis_tac[attribute_type_struct_field] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  rename1 `lookup_var_slot_from_layout _ _ _ _ = SOME lslot` >>
  `body_expr_ok cx e` by
    (drule_all augassign_attr_storage_place >> strip_tac >>
     first_x_assum irule >> metis_tac[]) >>
  `expr_sim ctx func cenv cx ty e es` by metis_tac[body_expr_ok_def] >>
  irule compile_augassign_attr_storage_case >> simp[] >> metis_tac[]
QED

(* An augmented assignment to a field or an element, through the
   target/place judgment, as body_assign_place_word: the current word is
   loaded at the place's pointer (MLOAD, SLOAD or TLOAD by its location)
   and the result stored back there.  GAP: cheated, for alan. *)
Theorem aug_place_local_pop_index_unsupported[local]:
  !tops ty ety id key.
    ~supported_expr tops (Subscript ty (Pop ety (NameTarget id)) key)
Proof
  simp[supported_expr_def, supported_pure_expr_def,
       supported_effect_expr_def]
QED

Theorem aug_place_nested_pop_target_unsupported[local]:
  !tops bindings ty ety id outer inner bop rhs.
    ~supported_stmt tops bindings
      (AugAssign ty
        (SubscriptTarget (SubscriptTarget (NameTarget id) outer)
          (Subscript ty (Pop ety (NameTarget id)) inner)) bop rhs)
Proof
  simp[supported_stmt_def, supported_aug_target_def,
       supportedTargetsTheory.supported_target_info_def, aug_place_local_pop_index_unsupported,
       supported_target_def]
QED

Theorem aug_place_read_memory_current[local]:
  !entry path v.
    evaluate_subscripts entry.type entry.value path = INL v ==>
    read_memory_path entry path = INL v
Proof
  simp[read_memory_path_def]
QED

Theorem aug_place_typing[local]:
  !env ret_ty ty t bop e env'.
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' ==>
    type_place_target env t = SOME (Type ty) /\
    well_typed_expr env e /\
    assignable_type env.type_defs ty /\
    assignable_type env.type_defs (expr_type e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    word_value_type ty /\ word_value_type (expr_type e) /\ env' = env
Proof
  rpt gen_tac >> simp[type_stmt_def, well_typed_target_def] >>
  strip_tac >> gvs[] >> metis_tac[well_typed_binop_augassign_word]
QED

Theorem aug_place_code_parts[local]:
  !cenv lctx ret_ty ty t bop e sa c sf.
    stmt_env cenv lctx ret_ty (AugAssign ty t bop e) sa = (c,sf) ==>
    c = cenv /\
    ?r s0. compile_get_target_ptr compile_expr cenv t sa = (r,s0) /\
      ((FST (SND r) = NONE /\ emit_void INVALID [] s0 = ((),sf)) \/
       ?loc cur rhs result s1 s2 s3.
         FST (SND r) = SOME loc /\
         emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
           [FST r] s0 = (cur,s1) /\
         lower_value compile_expr cenv ty e s1 = (rhs,s2) /\
         compile_binop bop cur rhs ty NONE
           (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
         emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE)
           [FST r; result] s3 = ((),sf))
Proof
  rpt gen_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_get_target_ptr compile_expr cenv t sa` >>
  rename1 `compile_get_target_ptr _ _ _ _ = (ptr_result,cstart)` >>
  Cases_on `FST (SND ptr_result)` >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] 
  >- (Cases_on `emit_void INVALID [] cstart` >> simp[oneTheory.one]) >>
  rename1 `FST (SND ptr_result) = SOME loc` >>
  Cases_on `emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD) [FST ptr_result] cstart` >>
  rename1 `_ = (cur,s1)` >> simp[] >>
  Cases_on `lower_value compile_expr cenv ty e s1` >>
  rename1 `_ = (rhs,s2)` >> simp[] >>
  Cases_on `compile_binop bop cur rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2` >>
  rename1 `compile_binop _ _ _ _ _ _ _ = (result,cstore)` >>
  simp[] >>
  Cases_on `emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE) [FST ptr_result; result] cstore` >>
  simp[oneTheory.one]
QED

Theorem aug_place_body_target_idx[local]:
  !t cx tops ctx func cenv.
    body_base_target_ok cx t /\ body_inv tops ctx cenv cx ==>
    target_idx_case F ctx func cenv cx t
Proof
  `(!e:expr. T) /\ !t cx tops ctx func cenv.
     body_base_target_ok cx t /\ body_inv tops ctx cenv cx ==>
     target_idx_case F ctx func cenv cx t` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[body_base_target_ok_def, target_idx_case_def] >>
  metis_tac[body_expr_ok_case]
QED

Theorem aug_place_body_target_sim[local]:
  !t cx tops ctx func cenv env es.
    body_base_target_ok cx t /\ body_inv tops ctx cenv cx /\
    target_pre cenv cx env t es ==>
    target_sim ctx func cenv cx env t es
Proof
  rpt strip_tac >>
  `target_idx_case F ctx func cenv cx t` by
    metis_tac[aug_place_body_target_idx] >>
  drule target_case_all >> simp[target_case_def] >>
  disch_then irule >> simp[]
QED

Theorem aug_place_main_storage_metadata[local]:
  !tops ctx cenv cx id tr ty id_str.
    body_inv tops ctx cenv cx /\
    find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,id_str) ==>
    cenv.ce_hashmap_info (NONE,id) = NONE /\
    cenv.ce_module_var_type (NONE,id) = SOME ty
Proof
  rpt strip_tac >> drule find_var_decl_storage_mem >> strip_tac >>
  gvs[body_inv_def] >> metis_tac[build_maps_variable]
QED

Theorem aug_place_main_map_metadata[local]:
  !tops id tr kt vt id_str.
    find_var_decl_by_name id tops = SOME (HashMapVarDecl tr kt vt,id_str) ==>
    build_hashmap_info tops (NONE,id) = SOME (tr,kt,vt)
Proof
  Induct >> simp[find_var_decl_by_name_def] >> Cases >>
  simp[find_var_decl_by_name_def, build_hashmap_info_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem aug_place_defined_metadata[local]:
  !env cx cenv src id ts d id_str vt.
    env_context_consistent env cx /\
    place_map_tables_agree_on_defined cenv env /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (d,id_str) /\
    FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    (!tr ty. d = StorageVarDecl tr ty ==>
      cenv.ce_hashmap_info (src,id) = NONE) /\
    (!tr kt vty. d = HashMapVarDecl tr kt vty ==>
      ?tr'. cenv.ce_hashmap_info (src,id) = SOME (tr',kt,vty))
Proof
  rpt gen_tac >> strip_tac >>
  `OPTION_MAP (\(tr,kt,vty). (kt,vty)) (cenv.ce_hashmap_info (src,id)) =
    (case vt of HashMapT kt vty => SOME (kt,vty) | _ => NONE)` by
    metis_tac[placeTypingPropsTheory.place_map_tables_agree_on_defined_def] >>
  Cases_on `vt`
  >- (fs[env_context_consistent_def] >>
      Cases_on `FLOOKUP env.bare_globals (src,id)`
      >- (qpat_x_assum `!s i ty. FLOOKUP env.toplevel_vtypes _ = SOME (Type ty) /\ _ ==> _`
            drule_all >> strip_tac >> gvs[]) >>
      qpat_x_assum `!s i ty. FLOOKUP env.bare_globals _ = SOME ty ==> _`
        drule >> strip_tac >> gvs[]) >>
  Cases_on `cenv.ce_hashmap_info (src,id)` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  fs[env_context_consistent_def] >>
  qpat_x_assum `!s i kt vt. FLOOKUP env.toplevel_vtypes _ = SOME (HashMapT kt vt) ==> _`
    drule >> strip_tac >> gvs[]
QED

Theorem aug_place_metadata_completion[local]:
  !tops ctx cenv cx env es.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es ==>
    ?cenv'. target_env_ok cenv' cx /\
      (!id. cenv'.ce_hashmap_info (NONE,id) = cenv.ce_hashmap_info (NONE,id)) /\
      (!id. cenv'.ce_module_var_type (NONE,id) = cenv.ce_module_var_type (NONE,id)) /\
      (!nsid vt. FLOOKUP env.toplevel_vtypes nsid = SOME vt ==>
        cenv'.ce_hashmap_info nsid = cenv.ce_hashmap_info nsid) /\
      cenv' = cenv with <| ce_hashmap_info := cenv'.ce_hashmap_info;
                          ce_module_var_type := cenv'.ce_module_var_type |>
Proof
  rpt strip_tac >>
  qabbrev_tac `h = \nsid.
    if FST nsid = NONE \/ IS_SOME (FLOOKUP env.toplevel_vtypes nsid)
    then cenv.ce_hashmap_info nsid
    else case get_module_code cx (FST nsid) of
      NONE => NONE
    | SOME ts => case find_var_decl_by_name (SND nsid) ts of
        SOME (HashMapVarDecl tr kt vt,id_str) => SOME (tr,kt,vt)
      | _ => NONE` >>
  qabbrev_tac `m = \nsid.
    if FST nsid = NONE then cenv.ce_module_var_type nsid
    else case get_module_code cx (FST nsid) of
      NONE => NONE
    | SOME ts => case find_var_decl_by_name (SND nsid) ts of
        SOME (StorageVarDecl tr ty,id_str) => SOME ty
      | _ => NONE` >>
  qexists_tac `cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>` >>
  simp[] >> conj_tac
  >- (simp[target_env_ok_def] >> rpt strip_tac >> gvs[] >>
      rename1 `get_module_code cx src = SOME ts` >>
      (Cases_on `src`
      >- (`ts = tops` by fs[body_inv_def] >> gvs[] >>
          simp[Abbr `h`, Abbr `m`] >>
          metis_tac[aug_place_main_storage_metadata,
                    aug_place_main_map_metadata, body_inv_def]) >>
      rename1 `get_module_code cx (SOME mid) = SOME ts` >>
      rename1 `find_var_decl_by_name id ts = SOME _` >>
      Cases_on `FLOOKUP env.toplevel_vtypes (SOME mid,id)`
      >- simp[Abbr `h`, Abbr `m`] >>
      `env_context_consistent env cx /\ place_map_tables_agree_on_defined cenv env` by
        fs[expr_sim_inv_def, env_consistent_def] >>
      simp[Abbr `h`, Abbr `m`] >>
      qpat_x_assum `body_inv _ _ _ _` kall_tac >>
      qpat_x_assum `expr_sim_inv _ _ _ _` kall_tac >>
      drule_then strip_assume_tac aug_place_defined_metadata >>
      gvs[] >> metis_tac[])) >>
  simp[Abbr `h`, Abbr `m`]
QED

Theorem aug_place_stmt_state_rel_metadata:
  stmt_state_rel ctx func
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx es s <=>
  stmt_state_rel ctx func cenv cx es s
Proof
  eq_tac >> strip_tac >> irule stmt_state_rel_cenv_cong >>
  first_assum (irule_at Any) >> simp[]
QED

Theorem aug_place_place_ptr_rel_metadata:
  place_ptr_rel
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
    cx s pv w loc vt <=>
  place_ptr_rel cenv cx s pv w loc vt
Proof
  Cases_on `pv` >> simp[place_ptr_rel_def] >>
  rename1 `PlaceR p` >> Cases_on `p` >> simp[place_ptr_rel_def]
QED

Theorem aug_place_target_post_metadata:
  target_post ctx func
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
    cx es sa sb s0 es' pv vt r s <=>
  target_post ctx func cenv cx es sa sb s0 es' pv vt r s
Proof
  simp[target_post_def, aug_place_stmt_state_rel_metadata,
       aug_place_place_ptr_rel_metadata, local_region_def,
       locals_kept_def, dynarray_local_def]
QED

Theorem aug_place_local_ptrs_reserved_metadata:
  local_ptrs_reserved
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) sa <=>
  local_ptrs_reserved cenv sa
Proof
  simp[local_ptrs_reserved_def]
QED

Theorem aug_place_expr_sim_inv_metadata:
  (!nsid vt. FLOOKUP env.toplevel_vtypes nsid = SOME vt ==>
             h nsid = cenv.ce_hashmap_info nsid) /\
  (!nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==>
             h nsid = cenv.ce_hashmap_info nsid) ==>
  (expr_sim_inv
     (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx env es <=>
   expr_sim_inv cenv cx env es)
Proof
  strip_tac >>
  simp[expr_sim_inv_def,
       placeTypingPropsTheory.place_map_tables_agree_on_defined_def]
QED

Theorem aug_place_type_memory_bytes_cong:
  !c1 ty c2. c1.ce_struct_fields = c2.ce_struct_fields ==>
    type_memory_bytes c1 ty = type_memory_bytes c2 ty
Proof
  recInduct type_memory_bytes_ind >> rpt strip_tac >>
  simp[type_memory_bytes_def] >> AP_TERM_TAC >>
  irule MAP_CONG >> simp[]
QED

Theorem aug_place_elem_size_in_location_cong:
  !c1 c2 loc ty. c1.ce_struct_fields = c2.ce_struct_fields ==>
    elem_size_in_location c1 loc ty = elem_size_in_location c2 loc ty
Proof
  rpt strip_tac >> drule aug_place_type_memory_bytes_cong >>
  disch_then (qspec_then `ty` assume_tac) >>
  simp[elem_size_in_location_def]
QED

Theorem aug_place_compile_target_metadata:
  !t.
    (!nsid. target_root t = TopLevelNameTarget nsid ==>
       h nsid = cenv.ce_hashmap_info nsid /\
       m nsid = cenv.ce_module_var_type nsid) /\
    (!e. MEM e (target_indices t) ==>
       lower_value compile_expr
         (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
         (expr_type e) e = lower_value compile_expr cenv (expr_type e) e) ==>
    compile_get_target_ptr compile_expr
      (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) t =
    compile_get_target_ptr compile_expr cenv t
Proof
  `(!e:expr. T) /\ (!t.
    (!nsid. target_root t = TopLevelNameTarget nsid ==>
       h nsid = cenv.ce_hashmap_info nsid /\
       m nsid = cenv.ce_module_var_type nsid) /\
    (!e. MEM e (target_indices t) ==>
       lower_value compile_expr
         (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
         (expr_type e) e = lower_value compile_expr cenv (expr_type e) e) ==>
    compile_get_target_ptr compile_expr
      (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) t =
    compile_get_target_ptr compile_expr cenv t)` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[target_root_def, target_indices_def] >> rpt strip_tac >>
  `!loc ty. elem_size_in_location
      (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) loc ty =
      elem_size_in_location cenv loc ty` by
    (rpt gen_tac >> irule aug_place_elem_size_in_location_cong >> simp[]) >>
  fs[] >> simp[Ntimes exprLoweringTheory.compile_get_target_ptr_def 2]
QED

Theorem aug_place_supported_root:
  !t pt nsid.
    supported_target_info tops bindings t = SOME pt /\
    target_root t = TopLevelNameTarget nsid ==>
    supported_place_root tops nsid
Proof
  `(!e:expr. T) /\ (!t. !pt nsid.
    supported_target_info tops bindings t = SOME pt /\
    target_root t = TopLevelNameTarget nsid ==>
    supported_place_root tops nsid)` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[target_root_def, supportedTargetsTheory.supported_target_info_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem aug_place_supported_root_namespace:
  supported_place_root tops (src,id) ==> src = NONE
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule supportedDeclsTheory.supported_lookup_other_module >>
  strip_tac >> gvs[supportedExprFormsTheory.supported_place_root_def]
QED

Theorem aug_place_supported_root_metadata:
  body_inv tops ctx cenv cx /\
  supported_target_info tops bindings t = SOME pt /\
  target_root t = TopLevelNameTarget (src,id) /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (d,id_str) ==>
  (!tr typ. d = StorageVarDecl tr typ ==>
    cenv.ce_hashmap_info (src,id) = NONE /\
    cenv.ce_module_var_type (src,id) = SOME typ) /\
  (!tr kt vt. d = HashMapVarDecl tr kt vt ==>
    ?tr'. cenv.ce_hashmap_info (src,id) = SOME (tr',kt,vt))
Proof
  strip_tac >>
  `supported_place_root tops (src,id)` by
    (metis_tac[aug_place_supported_root]) >>
  drule aug_place_supported_root_namespace >> strip_tac >> gvs[] >>
  `ts = tops` by gvs[body_inv_def, vyperContextTheory.get_module_code_def] >> gvs[] >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[aug_place_main_storage_metadata]) >>
  rpt strip_tac >> gvs[] >> drule aug_place_main_map_metadata >>
  gvs[body_inv_def]
QED

Theorem aug_place_supported_root_decl:
  !tops id.
    ((?vis mut ty slot.
       supported_variable_decl tops (NONE,id) = SOME (vis,mut,ty,slot) /\
       (mut = Storage \/ mut = Transient)) \/
     (?vis tr kt vt slot.
       supported_hashmap_decl tops (NONE,id) = SOME (vis,tr,kt,vt,slot))) ==>
    IS_SOME (find_var_decl_by_name id tops)
Proof
  Induct >> simp[supportedDeclsTheory.supported_variable_decl_def,
    supportedDeclsTheory.supported_hashmap_decl_def] >>
  Cases_on `h` >>
  simp[find_var_decl_by_name_def,
    supportedDeclsTheory.supported_variable_decl_def,
    supportedDeclsTheory.supported_hashmap_decl_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem aug_place_supported_root_not_immutable:
  body_inv tops ctx cenv cx /\
  supported_target_info tops bindings t = SOME pt ==>
  ~immutable_root cx t
Proof
  strip_tac >> simp[immutable_root_def] >> rpt strip_tac >>
  `supported_place_root tops (src,id)` by metis_tac[aug_place_supported_root] >>
  drule aug_place_supported_root_namespace >> strip_tac >> gvs[] >>
  `ts = tops` by gvs[body_inv_def, vyperContextTheory.get_module_code_def] >>
  gvs[] >>
  `IS_SOME (find_var_decl_by_name id tops)` suffices_by simp[] >>
  irule aug_place_supported_root_decl >>
  gvs[supportedExprFormsTheory.supported_place_root_def] >>
  Cases_on `supported_variable_decl tops (NONE,id)`
  >- (gvs[] >> Cases_on `supported_hashmap_decl tops (NONE,id)` >> gvs[] >>
      rename1 `supported_hashmap_decl tops (NONE,id) = SOME mdecl` >>
      PairCases_on `mdecl` >> simp[]) >>
  rename1 `supported_variable_decl tops (NONE,id) = SOME vdecl` >>
  PairCases_on `vdecl` >> gvs[] >>
  Cases_on `vdecl1` >> Cases_on `vdecl3` >> gvs[] >>
  Cases_on `vdecl0` >> gvs[] >> metis_tac[]
QED

Theorem aug_place_find_storage_decl:
  !ts id tr ty id_str.
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) ==>
    id_str = id /\
    ?vis mut init. MEM (VariableDecl vis mut id ty init) ts /\
      (mut = Storage \/ mut = Transient) /\ (tr <=> mut = Transient)
Proof
  Induct >> simp[find_var_decl_by_name_def] >>
  Cases_on `h` >> simp[find_var_decl_by_name_def] >>
  rpt gen_tac >> rpt IF_CASES_TAC >> rpt strip_tac >>
  gvs[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> metis_tac[]
QED

Theorem aug_place_find_hashmap_decl:
  !ts id tr kt vt id_str.
    find_var_decl_by_name id ts = SOME (HashMapVarDecl tr kt vt,id_str) ==>
    id_str = id /\
    ?vis init. MEM (HashMapDecl vis tr id kt vt init) ts
Proof
  Induct >> simp[find_var_decl_by_name_def] >>
  Cases_on `h` >> simp[find_var_decl_by_name_def] >>
  rpt gen_tac >> rpt IF_CASES_TAC >> rpt strip_tac >>
  gvs[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> metis_tac[]
QED

Theorem aug_place_bare_decl:
  !ts id. is_bare_global_decl id ts ==>
    ?vis mut ty init. MEM (VariableDecl vis mut id ty init) ts /\
      (mut = Immutable \/ ?e. mut = Constant e)
Proof
  Induct >> simp[is_bare_global_decl_def] >>
  Cases_on `h` >> simp[is_bare_global_decl_def] >>
  TRY (rename1 `VariableDecl vis mut vid ty init` >> Cases_on `mut`) >>
  simp[is_bare_global_decl_def] >> rpt strip_tac >>
  rpt IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem aug_place_complete_storage:
  toplevel_vtypes_complete tvs cx /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
  IS_SOME (lookup_var_slot_from_layout cx tr src id_str) ==>
  FLOOKUP tvs (src,id) = SOME (Type ty)
Proof
  strip_tac >> drule aug_place_find_storage_decl >> strip_tac >> gvs[] >>
  gvs[toplevel_vtypes_complete_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  Cases_on `mut = Storage` >> gvs[]
QED

Theorem aug_place_complete_hashmap:
  toplevel_vtypes_complete tvs cx /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (HashMapVarDecl tr kt vt,id_str) /\
  IS_SOME (lookup_var_slot_from_layout cx tr src id_str) ==>
  FLOOKUP tvs (src,id) = SOME (HashMapT kt vt)
Proof
  strip_tac >> drule aug_place_find_hashmap_decl >> strip_tac >> gvs[] >>
  gvs[toplevel_vtypes_complete_def] >> metis_tac[]
QED

Theorem aug_place_complete_bare:
  toplevel_vtypes_complete tvs cx /\
  get_module_code cx src = SOME ts /\ is_bare_global_decl id ts ==>
  IS_SOME (FLOOKUP tvs (src,id))
Proof
  strip_tac >> drule aug_place_bare_decl >> strip_tac >>
  gvs[toplevel_vtypes_complete_def] >>
  `FLOOKUP tvs (src,id) = SOME (Type ty)` suffices_by simp[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> gvs[]
QED

Theorem aug_place_context_bare_domain:
  env_context_consistent env0 cx /\ env_context_consistent env1 cx /\
  FLOOKUP env1.bare_globals (src,id) = SOME ty ==>
  IS_SOME (FLOOKUP env0.toplevel_vtypes (src,id))
Proof
  strip_tac >> drule_all env_context_consistent_bare_global_find_NONE >>
  strip_tac >> irule aug_place_complete_bare >>
  gvs[env_context_consistent_def] >> metis_tac[]
QED

Theorem aug_place_context_toplevel_domain:
  env_context_consistent env0 cx /\ env_context_consistent env1 cx /\
  FLOOKUP env1.toplevel_vtypes (src,id) = SOME vt ==>
  IS_SOME (FLOOKUP env0.toplevel_vtypes (src,id))
Proof
  strip_tac >>
  `toplevel_vtypes_complete env0.toplevel_vtypes cx` by
    gvs[env_context_consistent_def] >>
  qpat_x_assum `env_context_consistent env0 cx` kall_tac >>
  Cases_on `vt`
  >- (Cases_on `FLOOKUP env1.bare_globals (src,id)`
      >- (gvs[env_context_consistent_def] >>
          qpat_x_assum `!src id ty. _ /\ _ ==> _` drule_all >>
          strip_tac >>
          `FLOOKUP env0.toplevel_vtypes (src,id) = SOME (Type t)`
            suffices_by simp[] >>
          irule aug_place_complete_storage >> metis_tac[]) >>
      drule_all env_context_consistent_bare_global_find_NONE >>
      strip_tac >> irule aug_place_complete_bare >> metis_tac[]) >>
  rename1 `FLOOKUP env1.toplevel_vtypes (src,id) = SOME (HashMapT kt value_ty)` >>
  gvs[env_context_consistent_def] >>
  qpat_x_assum `!src id kt vt. _ ==> _` drule >> strip_tac >>
  `FLOOKUP env0.toplevel_vtypes (src,id) = SOME (HashMapT kt value_ty)`
    suffices_by simp[] >>
  irule aug_place_complete_hashmap >> metis_tac[]
QED

Theorem aug_place_context_domain:
  env_context_consistent env0 cx /\ env_context_consistent env1 cx ==>
  (!nsid vt. FLOOKUP env1.toplevel_vtypes nsid = SOME vt ==>
     IS_SOME (FLOOKUP env0.toplevel_vtypes nsid)) /\
  (!nsid ty. FLOOKUP env1.bare_globals nsid = SOME ty ==>
     IS_SOME (FLOOKUP env0.toplevel_vtypes nsid))
Proof
  strip_tac >> conj_tac >> Cases >> rpt strip_tac
  >- metis_tac[aug_place_context_toplevel_domain] >>
  metis_tac[aug_place_context_bare_domain]
QED

Theorem aug_place_uniform_inv_metadata:
  env_context_consistent env0 cx /\
  (!k vt. FLOOKUP env0.toplevel_vtypes k = SOME vt ==>
     h k = cenv.ce_hashmap_info k) /\
  env_context_consistent env1 cx ==>
  (expr_sim_inv
     (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx env1 es <=>
   expr_sim_inv cenv cx env1 es)
Proof
  strip_tac >> irule aug_place_expr_sim_inv_metadata >>
  conj_tac >> rpt strip_tac >>
  `IS_SOME (FLOOKUP env0.toplevel_vtypes nsid)` by
    (Cases_on `nsid` >>
     metis_tac[aug_place_context_toplevel_domain, aug_place_context_bare_domain]) >>
  Cases_on `FLOOKUP env0.toplevel_vtypes nsid` >> gvs[] >> metis_tac[]
QED

Theorem aug_place_uniform_inv_backward:
  env_context_consistent env0 cx /\
  (!k vt. FLOOKUP env0.toplevel_vtypes k = SOME vt ==>
     h k = cenv.ce_hashmap_info k) /\
  expr_sim_inv
     (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx env1 es ==>
  expr_sim_inv cenv cx env1 es
Proof
  strip_tac >>
  `env_context_consistent env1 cx` by
    gvs[expr_sim_inv_def, env_consistent_def] >>
  metis_tac[aug_place_uniform_inv_metadata]
QED

Theorem aug_place_alloc_limits_metadata:
  (!cenv e.
    alloc_limits_expr
      (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) e =
    alloc_limits_expr cenv e) /\
  (!cenv t.
    alloc_limits_target
      (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) t =
    alloc_limits_target cenv t) /\
  (!cenv es.
    alloc_limits_exprs
      (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) es =
    alloc_limits_exprs cenv es) /\
  (!cenv e.
    alloc_limits_opt
      (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) e =
    alloc_limits_opt cenv e) /\
  (!cenv es.
    alloc_limits_named_exprs
      (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) es =
    alloc_limits_named_exprs cenv es)
Proof
  `!cenv ty. type_memory_bytes
     (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty =
     type_memory_bytes cenv ty` by
    (rpt gen_tac >> irule aug_place_type_memory_bytes_cong >> simp[]) >>
  ho_match_mp_tac alloc_limits_expr_ind >>
  simp[alloc_limits_expr_def, type_alloc_ok_def, combinTheory.o_DEF]
QED

Theorem aug_place_uniform_body_pre_backward:
  env_context_consistent env0 cx /\
  (!k vt. FLOOKUP env0.toplevel_vtypes k = SOME vt ==>
     h k = cenv.ce_hashmap_info k) /\
  expr_body_pre
     (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx env1 e es ==>
  expr_body_pre cenv cx env1 e es
Proof
  simp[expr_body_pre_def, aug_place_alloc_limits_metadata] >>
  strip_tac >> irule aug_place_uniform_inv_backward >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `m` >> simp[]
QED

Theorem aug_place_variable_decl_namespace:
  !tops src id d. supported_variable_decl tops (src,id) = SOME d ==> src = NONE
Proof
  Cases >> simp[supportedDeclsTheory.supported_variable_decl_def] >>
  rpt gen_tac >> Cases_on `src` >> simp[supportedDeclsTheory.supported_variable_decl_def]
QED

Theorem aug_place_toplevel_expr_namespace:
  supportedExprs$supported_expr tops (TopLevelName ty (src,id)) \/
  supported_place_expr tops (TopLevelName ty (src,id)) \/
  supported_effect_place_expr tops (TopLevelName ty (src,id)) ==>
  src = NONE
Proof
  Cases_on `src` >- simp[] >>
  `supported_variable_decl tops (SOME x,id) = NONE` by
    (Cases_on `tops` >> simp[supportedDeclsTheory.supported_variable_decl_def]) >>
  simp[supportedExprsTheory.supported_expr_def,
       supportedExprsTheory.supported_pure_expr_def,
       supportedExprsTheory.supported_effect_expr_def,
       supportedExprFormsTheory.supported_storage_value_def,
       supportedDeclsTheory.supported_immutable_type_def] >>
  strip_tac >> drule aug_place_supported_root_namespace >> simp[]
QED

Theorem aug_place_place_type_metadata:
  !cenv e.
    (!id. h (NONE,id) = cenv.ce_hashmap_info (NONE,id)) /\
    (supportedExprs$supported_expr tops e \/ supported_place_expr tops e \/
     supported_effect_place_expr tops e) ==>
    place_type (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) e =
    place_type cenv e
Proof
  recInduct exprLoweringTheory.place_type_ind >> rpt strip_tac >>~-
    ([`place_type _ (TopLevelName ty nsid)`],
     PairCases_on `nsid` >>
     `nsid0 = NONE` by metis_tac[aug_place_toplevel_expr_namespace] >>
     gvs[exprLoweringTheory.place_type_def]) >>
  simp[exprLoweringTheory.place_type_def] >>
  gvs[supportedExprsTheory.supported_expr_def,
      supportedExprsTheory.supported_pure_expr_def,
      supportedExprsTheory.supported_effect_expr_def] >>
  metis_tac[]
QED

Theorem aug_place_array_dynamic_metadata:
  (!id. m (NONE,id) = cenv.ce_module_var_type (NONE,id)) /\
  (supportedExprs$supported_expr tops e \/ supported_place_expr tops e \/
   supported_effect_place_expr tops e) ==>
  infer_array_is_dynamic
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) e =
  infer_array_is_dynamic cenv e
Proof
  strip_tac >> Cases_on `e` >>
  simp[exprLoweringTheory.infer_array_is_dynamic_def] >>
  rename1 `TopLevelName ty nsid` >> PairCases_on `nsid` >>
  `nsid0 = NONE` by metis_tac[aug_place_toplevel_expr_namespace] >>
  gvs[]
QED

Theorem aug_place_array_location_metadata:
  !e. infer_array_location
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) e =
    infer_array_location cenv e
Proof
  Cases >> simp[exprLoweringTheory.infer_array_location_def]
QED

Theorem aug_place_memory_bytes_metadata:
  !cenv ty. type_memory_bytes
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty =
    type_memory_bytes cenv ty
Proof
  rpt gen_tac >> irule aug_place_type_memory_bytes_cong >> simp[]
QED

Theorem aug_place_unwrap_metadata:
  !vv. unwrap_value
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) vv =
    unwrap_value cenv vv
Proof
  Cases >> simp[exprLoweringTheory.unwrap_value_def, aug_place_memory_bytes_metadata]
QED

Theorem aug_place_abi_enc_metadata:
  !sf cenv ty. type_to_abi_enc_info sf
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty =
    type_to_abi_enc_info sf cenv ty
Proof
  recInduct exprLoweringTheory.type_to_abi_enc_info_ind >> rpt strip_tac >>
  simp[exprLoweringTheory.type_to_abi_enc_info_def, aug_place_memory_bytes_metadata] >>
  rpt IF_CASES_TAC >> gvs[] >>~-
    ([`GENLIST _ n = GENLIST _ n`],
     irule GENLIST_CONG >> metis_tac[]) >>
  all_tac >>~-
    ([`MAP _ tys = MAP _ tys`],
     irule listTheory.MAP_CONG >> simp[pairTheory.FORALL_PROD] >> metis_tac[]) >>
  Cases_on `FLOOKUP sfields (nsid_to_string nsid)` >> simp[] >>
  irule listTheory.MAP_CONG >>
  simp[pairTheory.FORALL_PROD] >> metis_tac[]
QED

Theorem aug_place_abi_dec_metadata:
  !sf cenv ty. type_to_abi_dec_info sf
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty =
    type_to_abi_dec_info sf cenv ty
Proof
  recInduct exprLoweringTheory.type_to_abi_dec_info_ind >> rpt strip_tac >>
  simp[exprLoweringTheory.type_to_abi_dec_info_def, aug_place_memory_bytes_metadata] >>
  gvs[] >>~-
    ([`GENLIST _ n = GENLIST _ n`],
     irule GENLIST_CONG >> simp[] >> metis_tac[]) >>~-
    ([`MAP _ tys = MAP _ tys`],
     irule listTheory.MAP_CONG >> simp[] >> metis_tac[]) >>
  Cases_on `FLOOKUP sfields (nsid_to_string nsid)` >> simp[] >>
  irule listTheory.MAP_CONG >>
  simp[pairTheory.FORALL_PROD] >> metis_tac[]
QED

Theorem aug_place_stage_intcall_metadata:
  !cenv vs fs ts. compile_stage_intcall_args
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) vs fs ts =
    compile_stage_intcall_args cenv vs fs ts
Proof
  recInduct exprLoweringTheory.compile_stage_intcall_args_ind >>
  rpt strip_tac >>
  simp[exprLoweringTheory.compile_stage_intcall_args_def,
       aug_place_unwrap_metadata, aug_place_memory_bytes_metadata]
QED

Theorem aug_place_typed_copy_metadata:
  (!cenv dst dt src st. compile_store_memory_typed
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) dst dt src st =
    compile_store_memory_typed cenv dst dt src st) /\
  (!cenv dst src dts sts doff soff. compile_typed_copy_fields
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) dst src dts sts doff soff =
    compile_typed_copy_fields cenv dst src dts sts doff soff) /\
  (!cenv dst dt src st n. compile_copy_sarray_typed
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) dst dt src st n =
    compile_copy_sarray_typed cenv dst dt src st n) /\
  (!cenv dst dt cap src st. compile_copy_dynarray_typed
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) dst dt cap src st =
    compile_copy_dynarray_typed cenv dst dt cap src st) /\
  (!cenv dst src dfs sfs doff soff. compile_struct_typed_copy
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) dst src dfs sfs doff soff =
    compile_struct_typed_copy cenv dst src dfs sfs doff soff)
Proof
  ho_match_mp_tac contextTheory.compile_store_memory_typed_ind >>
  rpt strip_tac
  >- (once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
      Cases_on `dt` >> Cases_on `st` >>
      simp[aug_place_memory_bytes_metadata] >>
      rpt IF_CASES_TAC >> gvs[] >>
      Cases_on `b` >> Cases_on `b'` >> gvs[]) >>
  once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
  simp[aug_place_memory_bytes_metadata] >>
  gvs[] >> Cases_on `ALOOKUP sfs name` >> gvs[] >>
  pairarg_tac >> gvs[]
QED

Theorem aug_place_store_memory_metadata:
  compile_store_memory
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) src dst dt st =
    compile_store_memory cenv src dst dt st
Proof
  simp[contextTheory.compile_store_memory_def,
       cj 1 aug_place_typed_copy_metadata, aug_place_memory_bytes_metadata]
QED

Theorem aug_place_materialize_metadata:
  compile_materialize_vv
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty vv =
    compile_materialize_vv cenv ty vv
Proof
  simp[exprLoweringTheory.compile_materialize_vv_def,
       aug_place_memory_bytes_metadata, aug_place_unwrap_metadata,
       aug_place_store_memory_metadata]
QED

Theorem aug_place_extcall_store_metadata:
  !cenv vs buf off. compile_extcall_store_values
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) vs buf off =
    compile_extcall_store_values cenv vs buf off
Proof
  recInduct exprLoweringTheory.compile_extcall_store_values_ind >>
  rpt strip_tac >>
  simp[exprLoweringTheory.compile_extcall_store_values_def,
       aug_place_memory_bytes_metadata, aug_place_unwrap_metadata]
QED

Theorem aug_place_default_return_metadata:
  compile_default_return_path
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) =
    compile_default_return_path cenv
Proof
  simp[FUN_EQ_THM, exprLoweringTheory.compile_default_return_path_def,
       aug_place_store_memory_metadata]
QED

Theorem aug_place_external_kwargs_metadata:
  compile_external_call_kwargs
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) =
    compile_external_call_kwargs cenv
Proof
  simp[FUN_EQ_THM, exprLoweringTheory.compile_external_call_kwargs_def,
       aug_place_extcall_store_metadata, aug_place_default_return_metadata]
QED

Theorem aug_place_lower_value_metadata:
  (!ty. f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e =
        g cenv ty e) ==>
  lower_value f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e =
  lower_value g cenv ty e
Proof
  strip_tac >> simp[exprLoweringTheory.lower_value_def, aug_place_unwrap_metadata]
QED

Theorem aug_place_multi_vvs_metadata:
  !es. (!e ty. MEM e es ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_multi_vvs f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) es =
  compile_multi_vvs g cenv es
Proof
  Induct >> simp[exprLoweringTheory.compile_multi_vvs_def] >> rpt strip_tac >>
  gvs[]
QED

Theorem aug_place_multi_exprs_metadata:
  !es. (!e ty. MEM e es ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_multi_exprs f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) es =
  compile_multi_exprs g cenv es
Proof
  Induct >> simp[exprLoweringTheory.compile_multi_exprs_def] >> rpt strip_tac >>
  gvs[] >> simp[exprLoweringTheory.lower_value_def, SRULE [] aug_place_unwrap_metadata]
QED

Theorem aug_place_make_tuple_metadata:
  !es buf off. (!e ty. MEM e es ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_make_tuple f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) es buf off =
  compile_make_tuple g cenv es buf off
Proof
  Induct >> simp[exprLoweringTheory.compile_make_tuple_def] >> rpt strip_tac >>
  gvs[] >> simp[SRULE [] aug_place_memory_bytes_metadata,
                SRULE [] aug_place_unwrap_metadata,
                SRULE [] aug_place_store_memory_metadata]
QED

Theorem aug_place_make_array_elems_metadata:
  !es et sz haslen buf idx. (!e ty. MEM e es ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_make_array_elems f
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) es et sz haslen buf idx =
  compile_make_array_elems g cenv es et sz haslen buf idx
Proof
  Induct >> simp[exprLoweringTheory.compile_make_array_elems_def] >> rpt strip_tac >>
  gvs[] >> simp[SRULE [] aug_place_unwrap_metadata,
                SRULE [] aug_place_store_memory_metadata]
QED

Theorem aug_place_make_array_metadata:
  (!e ty. MEM e es ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_make_array f
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) es et sz haslen buf =
  compile_make_array g cenv es et sz haslen buf
Proof
  strip_tac >> gvs[] >>
  drule (SRULE [] aug_place_make_array_elems_metadata) >>
  simp[exprLoweringTheory.compile_make_array_def]
QED

Theorem aug_place_struct_lit_metadata:
  !fields ty buf off. (!name e ety. MEM (name,e) fields ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ety e = g cenv ety e) ==>
  compile_struct_lit f
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty fields buf off =
  compile_struct_lit g cenv ty fields buf off
Proof
  Induct >> simp[exprLoweringTheory.compile_struct_lit_def] >>
  qx_gen_tac `entry` >> PairCases_on `entry` >> rpt strip_tac >> gvs[] >>
  `!ty buf off. compile_struct_lit f
     (cenv with <|ce_module_var_type := m; ce_hashmap_info := h|>) ty fields buf off =
     compile_struct_lit g cenv ty fields buf off` by
    (rpt gen_tac >> first_x_assum irule >> metis_tac[]) >>
  simp[exprLoweringTheory.compile_struct_lit_def,
       SRULE [] aug_place_unwrap_metadata, SRULE [] aug_place_store_memory_metadata]
QED

Theorem aug_place_attribute_metadata:
  (!ty. f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty be =
        g cenv ty be) ==>
  compile_attribute f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) rt ty be fld =
  compile_attribute g cenv rt ty be fld
Proof
  strip_tac >> simp[exprLoweringTheory.compile_attribute_def]
QED

Theorem aug_place_elem_size_metadata:
  !loc ty. elem_size_in_location
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) loc ty =
    elem_size_in_location cenv loc ty
Proof
  rpt gen_tac >> irule aug_place_elem_size_in_location_cong >> simp[]
QED

Theorem aug_place_subscript_metadata:
  (!id. h (NONE,id) = cenv.ce_hashmap_info (NONE,id)) /\
  (supportedExprs$supported_expr tops be \/ supported_place_expr tops be \/
   supported_effect_place_expr tops be) /\
  (!e ty. (e = be \/ e = ix) ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_subscript f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) rt ty be ix =
  compile_subscript g cenv rt ty be ix
Proof
  strip_tac >>
  `place_type (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) be =
   place_type cenv be` by (irule aug_place_place_type_metadata >> simp[] >> metis_tac[]) >>
  `!loc. elem_size_in_location
     (cenv with <|ce_module_var_type := m; ce_hashmap_info := h|>) loc =
     elem_size_in_location cenv loc` by
    simp[FUN_EQ_THM, SRULE [] aug_place_elem_size_metadata] >>
  simp[exprLoweringTheory.compile_subscript_def,
       exprLoweringTheory.lower_value_def, aug_place_unwrap_metadata,
       aug_place_elem_size_metadata]
QED

Theorem aug_place_ext_kwarg_metadata:
  (!ty. f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_ext_call_kwarg f
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) rt k e =
  compile_ext_call_kwarg g cenv rt k e
Proof
  strip_tac >> simp[exprLoweringTheory.compile_ext_call_kwarg_def,
    exprLoweringTheory.lower_value_def, aug_place_materialize_metadata,
    aug_place_unwrap_metadata]
QED

Theorem aug_place_ext_kwargs_metadata:
  !es ks. (!e ty. MEM e es ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_ext_call_kwargs f
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) rt ks es =
  compile_ext_call_kwargs g cenv rt ks es
Proof
  Induct >> Cases_on `ks` >> simp[exprLoweringTheory.compile_ext_call_kwargs_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `compile_ext_call_kwarg f _ rt kw child` >>
  `!ty. f (cenv with <|ce_module_var_type := m; ce_hashmap_info := h|>) ty child =
        g cenv ty child` by metis_tac[] >>
  drule (SRULE [] aug_place_ext_kwarg_metadata) >> simp[]
QED

Theorem aug_place_acc_metadata:
  (!ty. f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_acc f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) e op =
  compile_acc g cenv e op
Proof
  strip_tac >> Cases_on `op` >>
  simp[FUN_EQ_THM, exprLoweringTheory.compile_acc_def,
       exprLoweringTheory.lower_value_def, aug_place_unwrap_metadata]
QED

Theorem aug_place_lowered_value_type_metadata:
  !cenv e. lowered_value_type
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) e =
    lowered_value_type cenv e
Proof
  recInduct exprLoweringTheory.lowered_value_type_ind >>
  simp[exprLoweringTheory.lowered_value_type_def]
QED

Theorem aug_place_ext_arg_types_metadata:
  !cenv ts es. ext_call_arg_types
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ts es =
    ext_call_arg_types cenv ts es
Proof
  recInduct exprLoweringTheory.ext_call_arg_types_ind >> rpt strip_tac >>
  simp[exprLoweringTheory.ext_call_arg_types_def, aug_place_lowered_value_type_metadata]
QED

Theorem aug_place_name_metadata:
  compile_name_vv (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) =
  compile_name_vv cenv
Proof
  simp[FUN_EQ_THM, exprLoweringTheory.compile_name_vv_def]
QED

Theorem aug_place_addmod_names_metadata:
  compile_addmod_names (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) =
  compile_addmod_names cenv
Proof
  simp[FUN_EQ_THM, exprLoweringTheory.compile_addmod_names_def,
       aug_place_name_metadata, aug_place_unwrap_metadata]
QED

Theorem aug_place_mulmod_names_metadata:
  compile_mulmod_names (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) =
  compile_mulmod_names cenv
Proof
  simp[FUN_EQ_THM, exprLoweringTheory.compile_mulmod_names_def,
       aug_place_name_metadata, aug_place_unwrap_metadata]
QED

Theorem aug_place_powmod_names_metadata:
  compile_powmod256_names (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) =
  compile_powmod256_names cenv
Proof
  simp[FUN_EQ_THM, exprLoweringTheory.compile_powmod256_names_def,
       aug_place_name_metadata, aug_place_unwrap_metadata]
QED

Theorem aug_place_intcall_metadata:
  (!e ty. MEM e args ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_call f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) rt ty
    (IntCall id) args dr = compile_call g cenv rt ty (IntCall id) args dr
Proof
  strip_tac >> drule aug_place_multi_vvs_metadata >>
  simp[FUN_EQ_THM, exprLoweringTheory.compile_call_def,
       aug_place_stage_intcall_metadata]
QED

Theorem aug_place_extcall_metadata:
  (!e ty. MEM e args ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_call f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) rt ty
    (ExtCall static skip sig opts) args dr =
  compile_call g cenv rt ty (ExtCall static skip sig opts) args dr
Proof
  strip_tac >> PairCases_on `sig` >> Cases_on `args`
  >- simp[FUN_EQ_THM, exprLoweringTheory.compile_call_def] >>
  rename1 `addr::rest` >>
  `!ty. f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty addr =
        g cenv ty addr` by metis_tac[MEM] >>
  drule aug_place_lower_value_metadata >> strip_tac >>
  `!e ty. MEM e (TAKE (LENGTH sig1) rest) ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e`
    by metis_tac[rich_listTheory.MEM_TAKE, MEM] >>
  drule aug_place_multi_vvs_metadata >> strip_tac >>
  `!e ty. MEM e (DROP (LENGTH sig1) rest) ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e`
    by metis_tac[rich_listTheory.MEM_DROP_IMP, MEM] >>
  drule aug_place_ext_kwargs_metadata >> strip_tac >>
  `type_memory_bytes (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) =
   type_memory_bytes cenv` by simp[FUN_EQ_THM, aug_place_memory_bytes_metadata] >>
  simp[FUN_EQ_THM, exprLoweringTheory.compile_call_def,
       aug_place_ext_arg_types_metadata, aug_place_abi_enc_metadata,
       aug_place_abi_dec_metadata, aug_place_external_kwargs_metadata]
QED

Theorem aug_place_send_metadata:
  (!e ty. MEM e args ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_call f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) rt ty
    (Send gas) args dr = compile_call g cenv rt ty (Send gas) args dr
Proof
  strip_tac >> Cases_on `args`
  >- simp[FUN_EQ_THM, exprLoweringTheory.compile_call_def] >>
  rename1 `addr::rest` >> Cases_on `rest`
  >- simp[FUN_EQ_THM, exprLoweringTheory.compile_call_def] >>
  rename1 `addr::value::gas_es` >>
  `!e ty. MEM e (addr::value::gas_es) ==>
    lower_value f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e =
    lower_value g cenv ty e` by
    (rpt strip_tac >> irule aug_place_lower_value_metadata >> metis_tac[]) >>
  Cases_on `gas_es` >> simp[FUN_EQ_THM, exprLoweringTheory.compile_call_def] >>
  rename1 `gas_e::tail` >> Cases_on `tail` >>
  simp[FUN_EQ_THM, exprLoweringTheory.compile_call_def]
QED

Theorem aug_place_call_metadata:
  supported_effect_expr tops (Call rt target args NONE) /\
  (!e ty. MEM e args ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_call f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) rt ty
    target args dr = compile_call g cenv rt ty target args dr
Proof
  strip_tac >> Cases_on `target`
  >- (irule aug_place_intcall_metadata >> simp[])
  >- (irule aug_place_extcall_metadata >> simp[])
  >- (irule aug_place_send_metadata >> simp[]) >>
  gvs[supported_effect_expr_def]
QED

Theorem aug_place_toplevel_ptr_metadata:
  h nsid = cenv.ce_hashmap_info nsid /\ m nsid = cenv.ce_module_var_type nsid ==>
  compile_get_target_ptr f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
    (TopLevelNameTarget nsid) = compile_get_target_ptr g cenv (TopLevelNameTarget nsid)
Proof
  strip_tac >> simp[exprLoweringTheory.compile_get_target_ptr_def]
QED

Theorem aug_place_pop_ptr_metadata:
  (!id. h (NONE,id) = cenv.ce_hashmap_info (NONE,id)) /\
  (!id. m (NONE,id) = cenv.ce_module_var_type (NONE,id)) /\
  supported_storage_dynamic_array tops nsid ==>
  compile_get_target_ptr f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
    (TopLevelNameTarget nsid) = compile_get_target_ptr g cenv (TopLevelNameTarget nsid)
Proof
  strip_tac >> PairCases_on `nsid` >>
  `nsid0 = NONE` by
    (Cases_on `supported_variable_decl tops (nsid0,nsid1)`
     >- gvs[supportedExprFormsTheory.supported_storage_dynamic_array_def] >>
     drule aug_place_variable_decl_namespace >> simp[]) >>
  gvs[] >> irule (SRULE [] aug_place_toplevel_ptr_metadata) >> simp[]
QED

Theorem aug_place_type_builtin_metadata:
  supported_type_builtin_form tops vv_ty tb rt args /\
  (!e ty. MEM e args ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_type_builtin_dispatch_body f
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) vv_ty ty tb rt args st =
  compile_type_builtin_dispatch_body g cenv vv_ty ty tb rt args st
Proof
  strip_tac >>
  `!e ty. MEM e args ==>
    lower_value f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e =
    lower_value g cenv ty e` by
    (rpt strip_tac >> irule aug_place_lower_value_metadata >> metis_tac[]) >>
  Cases_on `tb` >> Cases_on `args` >>
  gvs[supportedExprFormsTheory.supported_type_builtin_form_def] >>
  TRY (rename1 `case tail of [] => _ | _ => _` >> Cases_on `tail` >>
       gvs[supportedExprFormsTheory.supported_type_builtin_form_def]) >>
  TRY (rename1 `AbiEncode ensure method` >> Cases_on `method` >>
       gvs[supportedExprFormsTheory.supported_type_builtin_form_def]) >>
  simp[exprLoweringTheory.compile_type_builtin_dispatch_body_def,
       SRULE [] aug_place_memory_bytes_metadata,
       SRULE [] aug_place_abi_enc_metadata, SRULE [] aug_place_abi_dec_metadata,
       SRULE [] aug_place_unwrap_metadata]
QED

Theorem aug_place_makearray_dispatch_metadata:
  (!e ty. MEM e args ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_builtin_dispatch_body f
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) rt ty (MakeArray et bd) args st =
  compile_builtin_dispatch_body g cenv rt ty (MakeArray et bd) args st
Proof
  strip_tac >>
  `type_memory_bytes (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) =
   type_memory_bytes cenv` by simp[FUN_EQ_THM, aug_place_memory_bytes_metadata] >>
  drule aug_place_make_tuple_metadata >> strip_tac >>
  drule aug_place_make_array_metadata >> strip_tac >>
  Cases_on `et` >>
  simp[exprLoweringTheory.compile_builtin_dispatch_body_def]
QED

Theorem aug_place_builtin_metadata:
  supported_builtin_form tops rt bi args /\
  (!e ty. MEM e args ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e = g cenv ty e) ==>
  compile_builtin_dispatch_body f
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) rt ty bi args st =
  compile_builtin_dispatch_body g cenv rt ty bi args st
Proof
  let
    val support = gvs[supportedExprFormsTheory.supported_builtin_form_def];
    val first = namedCases_on `args` ["", "a t1"] >> support;
    val second = namedCases_on `t1` ["", "b t2"] >> support;
    val third = namedCases_on `t2` ["", "c t3"] >> support;
    val fourth = namedCases_on `t3` ["", "d t4"] >> support;
    val unary = first >> Cases_on `t1` >> support;
    val binary = first >> second >> Cases_on `t2` >> support;
    val ternary = first >> second >> third >> Cases_on `t3` >> support;
    val quaternary = first >> second >> third >> fourth >> Cases_on `t4` >> support;
    val finish = simp[exprLoweringTheory.compile_builtin_dispatch_body_def,
      SRULE [] aug_place_acc_metadata, SRULE [] aug_place_memory_bytes_metadata,
      SRULE [] aug_place_unwrap_metadata,
      oneline exprLoweringTheory.compile_invert_def];
  in
    strip_tac >>
    `!e ty. MEM e args ==>
      lower_value f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e =
      lower_value g cenv ty e` by
      (rpt strip_tac >> irule aug_place_lower_value_metadata >> metis_tac[]) >>
    Cases_on `bi` >> support
    >~ [`MakeArray et bd`] >-
      (irule (SRULE [] aug_place_makearray_dispatch_metadata) >> simp[])
    >~ [`Bop op`] >- (binary >>
       `op <> In /\ op <> NotIn` by
         (Cases_on `op` >> gvs[supportedExprFormsTheory.supported_binop_def]) >> finish)
    >~ [`Not`] >- (unary >> finish)
    >~ [`Neg`] >- (unary >> finish)
    >~ [`Abs`] >- (unary >> finish)
    >~ [`AsWeiValue denom`] >- (unary >> finish)
    >~ [`Acc item`] >- (unary >> Cases_on `item` >>
       simp[exprLoweringTheory.compile_builtin_dispatch_body_def,
            exprLoweringTheory.compile_acc_def])
    >~ [`BlockHash`] >- (unary >> finish)
    >~ [`BlobHash`] >- (unary >> finish)
    >~ [`Uint2Str n`] >- (unary >> finish)
    >~ [`CalldataSlice n`] >- (unary >> finish)
    >~ [`PowMod256`] >- (binary >> finish)
    >~ [`ECAdd`] >- (binary >> finish)
    >~ [`ECMul`] >- (binary >> finish)
    >~ [`AddMod`] >- (ternary >> finish)
    >~ [`MulMod`] >- (ternary >> finish)
    >~ [`ECRecover`] >- (quaternary >> finish) >>
    Cases_on `args` >> support >> finish
  end
QED

Theorem aug_place_compile_expr_body_builtin_generic:
  bi <> AddMod /\ bi <> MulMod /\ bi <> PowMod256 ==>
  compile_expr_body f b d cenv ty (Builtin rty bi args) st =
  b cenv rty ty bi args st
Proof
  strip_tac >> namedCases_on `args` ["", "aa t1"]
  >- simp[exprLoweringTheory.compile_expr_body_def, expr_type_def] >>
  Cases_on `aa`
  >~ [`Name aty aid`] >-
    (namedCases_on `t1` ["", "bb t2"]
     >- simp[exprLoweringTheory.compile_expr_body_def, expr_type_def] >>
     Cases_on `bb`
     >~ [`b cenv rty ty bi (Name aty aid::Name bty bid::t2) st`] >-
       (namedCases_on `t2` ["", "cc t3"]
        >- (simp[exprLoweringTheory.compile_expr_body_def, expr_type_def] >>
            gvs[AllCaseEqs()] >> csimp[] >> metis_tac[vyperASTTheory.builtin_nchotomy]) >>
        Cases_on `cc`
        >~ [`b cenv rty ty bi (Name aty aid::Name bty bid::Name cty cid::t3) st`] >-
          (Cases_on `t3` >>
           simp[exprLoweringTheory.compile_expr_body_def, expr_type_def] >>
           gvs[AllCaseEqs()] >> csimp[] >> metis_tac[vyperASTTheory.builtin_nchotomy]) >>
        simp[exprLoweringTheory.compile_expr_body_def, expr_type_def] >>
        gvs[AllCaseEqs()] >> csimp[] >> metis_tac[vyperASTTheory.builtin_nchotomy]) >>
     simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]) >>
  simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]
QED

Theorem aug_place_expr_body_metadata:
  (!id. h (NONE,id) = cenv.ce_hashmap_info (NONE,id)) /\
  (!id. m (NONE,id) = cenv.ce_module_var_type (NONE,id)) /\
  (supportedExprs$supported_expr tops e \/ supported_place_expr tops e \/
   supported_effect_place_expr tops e) /\
  (!x ty. (supportedExprs$supported_expr tops x \/ supported_place_expr tops x \/
           supported_effect_place_expr tops x) ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty x = g cenv ty x) /\
  (!rt ty bi args. supported_builtin_form tops rt bi args /\ supported_pure_exprs tops args ==>
    b (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) rt ty bi args =
    b' cenv rt ty bi args) /\
  (!rt ty tb target args.
    supported_type_builtin_form tops rt tb target args /\ supported_pure_exprs tops args ==>
    d (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) rt ty tb target args =
    d' cenv rt ty tb target args) ==>
  compile_expr_body f b d
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e st =
  compile_expr_body g b' d' cenv ty e st
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `e`
  >~ [`Name nty id`] >-
    simp[exprLoweringTheory.compile_expr_body_def, expr_type_def,
         SRULE [] aug_place_name_metadata]
  >~ [`Literal lty lit`] >-
    simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]
  >~ [`TopLevelName tty id`] >-
    simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]
  >~ [`FlagMember fty id mem`] >-
    simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]
  >~ [`Attribute aty be fld`] >- suspend "attribute"
  >~ [`Subscript aty be ix`] >- suspend "subscript"
  >~ [`IfExp ity cond yes no`] >- suspend "ifexp"
  >~ [`StructLit sty id fields`] >- suspend "structlit"
  >~ [`Call cty target args dr`] >- suspend "call"
  >~ [`Pop pty target`] >- suspend "pop"
  >~ [`TypeBuiltin rty tb target args`] >- suspend "typebuiltin"
  >~ [`Builtin rty bi args`] >- suspend "builtin"
QED

Resume aug_place_expr_body_metadata[attribute]:
  `!ety. f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ety be =
         g cenv ety be` by
    (gvs[supportedExprsTheory.supported_expr_def,
         supportedExprsTheory.supported_pure_expr_def,
         supportedExprsTheory.supported_effect_expr_def] >> metis_tac[]) >>
  drule aug_place_attribute_metadata >> strip_tac >>
  simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]
QED

Resume aug_place_expr_body_metadata[subscript]:
  `compile_subscript f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
      aty ty be ix = compile_subscript g cenv aty ty be ix` by
    (irule aug_place_subscript_metadata >>
     gvs[supportedExprsTheory.supported_expr_def,
         supportedExprsTheory.supported_pure_expr_def,
         supportedExprsTheory.supported_effect_expr_def] >> metis_tac[]) >>
  simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]
QED

Resume aug_place_expr_body_metadata[ifexp]:
  `!x ety. (x = cond \/ x = yes \/ x = no) ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ety x =
    g cenv ety x` by
    (gvs[supportedExprsTheory.supported_expr_def,
         supportedExprsTheory.supported_pure_expr_def,
         supportedExprsTheory.supported_effect_expr_def] >> metis_tac[]) >>
  `!x ety. (x = cond \/ x = yes \/ x = no) ==>
    lower_value f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ety x =
    lower_value g cenv ety x` by
    (rpt strip_tac >> irule aug_place_lower_value_metadata >> metis_tac[]) >>
  simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]
QED
Resume aug_place_expr_body_metadata[structlit]:
  `!name x ety. MEM (name,x) fields ==>
    f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ety x =
    g cenv ety x` by
    (gvs[supportedExprsTheory.supported_expr_def,
         supportedExprsTheory.supported_pure_expr_def,
         supportedExprsTheory.supported_effect_expr_def,
         supportedExprsTheory.supported_pure_fields_every, EVERY_MEM] >>
     metis_tac[pairTheory.SND]) >>
  `!buf off. compile_struct_lit f
      (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
      (StructT id) fields buf off = compile_struct_lit g cenv (StructT id) fields buf off` by
    (rpt gen_tac >> irule aug_place_struct_lit_metadata >> gvs[] >> metis_tac[]) >>
  simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]
QED
Resume aug_place_expr_body_metadata[call]:
  `supported_effect_expr tops (Call cty target args dr)` by
    gvs[supportedExprsTheory.supported_expr_def,
        supportedExprsTheory.supported_pure_expr_def,
        supportedExprsTheory.supported_effect_expr_def] >>
  `dr = NONE /\ supported_pure_exprs tops args` by
    (Cases_on `dr` >> Cases_on `target` >>
     gvs[supportedExprsTheory.supported_effect_expr_def, AllCaseEqs(),
         supportedExprsTheory.supported_pure_expr_def]
     >~ [`ExtCall static skip sig opts`] >-
       (PairCases_on `sig` >> gvs[supportedExprsTheory.supported_effect_expr_def]) >>
     rename1 `Send gas` >> Cases_on `gas` >> Cases_on `cty` >>
     gvs[supportedExprsTheory.supported_effect_expr_def] >>
     Cases_on `args` >> gvs[supportedExprsTheory.supported_effect_expr_def] >>
     rename1 `a::rest` >> Cases_on `rest` >>
     gvs[supportedExprsTheory.supported_effect_expr_def] >>
     rename1 `a::v::tail` >> Cases_on `tail` >>
     gvs[supportedExprsTheory.supported_effect_expr_def,
         supportedExprsTheory.supported_pure_expr_def] >>
     rename1 `a::v::gas_e::last` >> Cases_on `last` >>
     gvs[supportedExprsTheory.supported_effect_expr_def,
         supportedExprsTheory.supported_pure_expr_def]) >>
  `compile_call f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
      cty ty target args dr = compile_call g cenv cty ty target args dr` by
    (irule aug_place_call_metadata >> gvs[] >>
     gvs[supportedExprsTheory.supported_pure_exprs_every, EVERY_MEM] >>
     metis_tac[supportedExprsTheory.supported_expr_def]) >>
  simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]
QED
Resume aug_place_expr_body_metadata[pop]:
  Cases_on `target` >>
  gvs[supportedExprsTheory.supported_expr_def,
      supportedExprsTheory.supported_pure_expr_def,
      supportedExprsTheory.supported_effect_expr_def] >>
  `compile_get_target_ptr f (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
     (TopLevelNameTarget p) = compile_get_target_ptr g cenv (TopLevelNameTarget p)` by
    (irule aug_place_pop_ptr_metadata >> metis_tac[]) >>
  gvs[] >>
  simp[exprLoweringTheory.compile_expr_body_def, expr_type_def,
       SRULE [] aug_place_elem_size_metadata]
QED
Resume aug_place_expr_body_metadata[typebuiltin]:
  `supported_type_builtin_form tops rty tb target args /\ supported_pure_exprs tops args` by
    gvs[supportedExprsTheory.supported_expr_def,
        supportedExprsTheory.supported_pure_expr_def,
        supportedExprsTheory.supported_effect_expr_def] >>
  `d (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) rty ty tb target args =
   d' cenv rty ty tb target args` by metis_tac[] >>
  simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]
QED
Resume aug_place_expr_body_metadata[builtin]:
  `supported_builtin_form tops rty bi args /\ supported_pure_exprs tops args` by
    gvs[supportedExprsTheory.supported_expr_def,
        supportedExprsTheory.supported_pure_expr_def,
        supportedExprsTheory.supported_effect_expr_def] >>
  `b (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) rty ty bi args =
   b' cenv rty ty bi args` by metis_tac[] >>
  qpat_x_assum `supported_expr tops _ \/ _` kall_tac >>
  qpat_x_assum `!x ty. (supported_expr tops x \/ _) ==> _` kall_tac >>
  qpat_x_assum `!rt ty bi args. supported_builtin_form tops rt bi args /\ _ ==> _` kall_tac >>
  qpat_x_assum `!rt ty tb target args. supported_type_builtin_form tops rt tb target args /\ _ ==> _` kall_tac >>
  qpat_x_assum `supported_pure_exprs tops args` kall_tac >>
  Cases_on `bi`
  >~ [`AddMod`] >- suspend "addmod"
  >~ [`MulMod`] >- suspend "mulmod"
  >~ [`PowMod256`] >- suspend "powmod" >>
  gvs[] >> simp[aug_place_compile_expr_body_builtin_generic]
QED
Resume aug_place_expr_body_metadata[addmod]:
  namedCases_on `args` ["", "aa t1"] >>
  gvs[supportedExprFormsTheory.supported_builtin_form_def] >>
  namedCases_on `t1` ["", "bb t2"] >>
  gvs[supportedExprFormsTheory.supported_builtin_form_def] >>
  namedCases_on `t2` ["", "cc t3"] >>
  gvs[supportedExprFormsTheory.supported_builtin_form_def] >>
  Cases_on `t3` >> gvs[supportedExprFormsTheory.supported_builtin_form_def] >>
  Cases_on `aa`
  >~ [`Name aty aid`] >-
    (Cases_on `bb` >~ [`Builtin rty AddMod [Name aty aid; Name bty bid; cc]`] >-
      (Cases_on `cc` >>
       simp[exprLoweringTheory.compile_expr_body_def, expr_type_def,
            SRULE [] aug_place_addmod_names_metadata]) >>
     simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]) >>
  simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]
QED
Resume aug_place_expr_body_metadata[mulmod]:
  namedCases_on `args` ["", "aa t1"] >>
  gvs[supportedExprFormsTheory.supported_builtin_form_def] >>
  namedCases_on `t1` ["", "bb t2"] >>
  gvs[supportedExprFormsTheory.supported_builtin_form_def] >>
  namedCases_on `t2` ["", "cc t3"] >>
  gvs[supportedExprFormsTheory.supported_builtin_form_def] >>
  Cases_on `t3` >> gvs[supportedExprFormsTheory.supported_builtin_form_def] >>
  Cases_on `aa`
  >~ [`Name aty aid`] >-
    (Cases_on `bb` >~ [`Builtin rty MulMod [Name aty aid; Name bty bid; cc]`] >-
      (Cases_on `cc` >>
       simp[exprLoweringTheory.compile_expr_body_def, expr_type_def,
            SRULE [] aug_place_mulmod_names_metadata]) >>
     simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]) >>
  simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]
QED
Resume aug_place_expr_body_metadata[powmod]:
  namedCases_on `args` ["", "aa t1"] >>
  gvs[supportedExprFormsTheory.supported_builtin_form_def] >>
  namedCases_on `t1` ["", "bb t2"] >>
  gvs[supportedExprFormsTheory.supported_builtin_form_def] >>
  Cases_on `t2` >> gvs[supportedExprFormsTheory.supported_builtin_form_def] >>
  Cases_on `aa`
  >~ [`Name aty aid`] >-
    (Cases_on `bb` >>
     simp[exprLoweringTheory.compile_expr_body_def, expr_type_def,
          SRULE [] aug_place_powmod_names_metadata]) >>
  simp[exprLoweringTheory.compile_expr_body_def, expr_type_def]
QED
Finalise aug_place_expr_body_metadata

Theorem aug_place_compile_expr_metadata:
  !e cenv h m ty st.
  (!id. h (NONE,id) = cenv.ce_hashmap_info (NONE,id)) /\
  (!id. m (NONE,id) = cenv.ce_module_var_type (NONE,id)) /\
  (supportedExprs$supported_expr tops e \/ supported_place_expr tops e \/
   supported_effect_place_expr tops e) ==>
  compile_expr (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e st =
  compile_expr cenv ty e st
Proof
  measureInduct_on `expr_size e` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  once_rewrite_tac[exprLoweringTheory.compile_expr_raw_def] >>
  irule aug_place_expr_body_metadata >> simp[] >> qexists_tac `tops` >>
  conj_tac >- suspend "expr_callback" >>
  conj_tac >- suspend "builtin_callback" >>
  conj_tac >- suspend "type_callback" >> simp[]
QED

Resume aug_place_compile_expr_metadata[expr_callback]:
  rpt strip_tac >> simp[FUN_EQ_THM, exprCallBoundsTheory.expr_child_callback_def] >>
  gen_tac >> IF_CASES_TAC >> simp[] >>
  qpat_x_assum `!y. expr_size y < _ ==> _` (mp_tac o Q.SPEC `x`) >>
  simp[]
QED

Resume aug_place_compile_expr_metadata[builtin_callback]:
  rpt strip_tac >>
  simp[FUN_EQ_THM, exprCallBoundsTheory.builtin_child_callback_def] >>
  gen_tac >> IF_CASES_TAC >> simp[] >>
  once_rewrite_tac[exprLoweringTheory.compile_expr_raw_def] >>
  irule (SRULE [] aug_place_builtin_metadata) >>
  reverse conj_tac >- (qexists_tac `tops` >> simp[]) >>
  rpt strip_tac >>
  simp[FUN_EQ_THM, exprCallBoundsTheory.expr_child_callback_def] >>
  `expr_size e' < list_size expr_size args` by
    metis_tac[exprCallBoundsTheory.expr_list_member_bound] >>
  simp[] >> gen_tac >>
  qpat_x_assum `!y. expr_size y < _ ==> _` (mp_tac o Q.SPEC `e'`) >>
  simp[] >> disch_then irule >>
  gvs[supportedExprsTheory.supported_pure_exprs_every, EVERY_MEM,
      supportedExprsTheory.supported_expr_def] >> metis_tac[]
QED

Resume aug_place_compile_expr_metadata[type_callback]:
  rpt strip_tac >>
  simp[FUN_EQ_THM, exprCallBoundsTheory.type_child_callback_def] >>
  gen_tac >> IF_CASES_TAC >> simp[] >>
  once_rewrite_tac[exprLoweringTheory.compile_expr_raw_def] >> simp[] >>
  irule (SRULE [] aug_place_type_builtin_metadata) >>
  reverse conj_tac >- (qexists_tac `tops` >> simp[]) >>
  rpt strip_tac >>
  simp[FUN_EQ_THM, exprCallBoundsTheory.expr_child_callback_def] >>
  `expr_size e' < list_size expr_size args` by
    metis_tac[exprCallBoundsTheory.expr_list_member_bound] >>
  simp[] >> gen_tac >>
  qpat_x_assum `!y. expr_size y < _ ==> _` (mp_tac o Q.SPEC `e'`) >>
  simp[] >> disch_then irule >>
  gvs[supportedExprsTheory.supported_pure_exprs_every, EVERY_MEM,
      supportedExprsTheory.supported_expr_def] >> metis_tac[]
QED

Finalise aug_place_compile_expr_metadata

Theorem aug_place_compile_supported_expr_metadata:
  (!id. h (NONE,id) = cenv.ce_hashmap_info (NONE,id)) /\
  (!id. m (NONE,id) = cenv.ce_module_var_type (NONE,id)) /\
  supportedExprs$supported_expr tops e ==>
  compile_expr (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e =
  compile_expr cenv ty e
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  irule (SRULE [] aug_place_compile_expr_metadata) >> metis_tac[]
QED

Theorem aug_place_expr_post_metadata:
  expr_post ctx func
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
    cx e es sa sb s0 es' v op s <=>
  expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  simp[expr_post_def, aug_place_stmt_state_rel_metadata, expr_val_at_def,
       local_region_def, locals_kept_def, dynarray_local_def]
QED

Theorem aug_place_vv_holds_metadata:
  vv_holds (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
    cx t tv vv es s <=> vv_holds cenv cx t tv vv es s
Proof
  Cases_on `vv` >> simp[vv_holds_def, immutable_holds_def] >>
  CASE_TAC >> simp[immutable_holds_def]
QED

Theorem aug_place_vv_post_metadata:
  vv_post ctx func
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
    cx e es sa sb s0 es' tv vv s <=>
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s
Proof
  simp[vv_post_def, aug_place_stmt_state_rel_metadata, aug_place_vv_holds_metadata,
       vv_at_def, expr_val_at_def, local_region_def, locals_kept_def,
       dynarray_local_def] >> Cases_on `vv` >> simp[vv_at_def, expr_val_at_def,
       local_region_def, dynarray_local_def]
QED

Theorem aug_place_expr_sim_metadata:
  (!id. h (NONE,id) = cenv.ce_hashmap_info (NONE,id)) /\
  (!id. m (NONE,id) = cenv.ce_module_var_type (NONE,id)) /\
  supportedExprs$supported_expr tops e ==>
  (expr_sim ctx func
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx ty e es <=>
   expr_sim ctx func cenv cx ty e es)
Proof
  strip_tac >>
  `compile_expr (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e =
   compile_expr cenv ty e` by
    (irule aug_place_compile_supported_expr_metadata >> metis_tac[]) >>
  simp[expr_sim_def, exprLoweringTheory.lower_value_def, comp_bind_def,
       SRULE [] aug_place_unwrap_metadata,
       SRULE [] aug_place_stmt_state_rel_metadata,
       SRULE [] aug_place_local_ptrs_reserved_metadata,
       SRULE [] aug_place_expr_post_metadata]
QED

Theorem aug_place_expr_vv_sim_metadata:
  (!id. h (NONE,id) = cenv.ce_hashmap_info (NONE,id)) /\
  (!id. m (NONE,id) = cenv.ce_module_var_type (NONE,id)) /\
  supportedExprs$supported_expr tops e ==>
  (expr_vv_sim ctx func
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx ty e es <=>
   expr_vv_sim ctx func cenv cx ty e es)
Proof
  strip_tac >>
  `compile_expr (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) ty e =
   compile_expr cenv ty e` by
    (irule aug_place_compile_supported_expr_metadata >> metis_tac[]) >>
  simp[expr_vv_sim_def, SRULE [] aug_place_stmt_state_rel_metadata,
       SRULE [] aug_place_local_ptrs_reserved_metadata,
       SRULE [] aug_place_vv_post_metadata]
QED

Theorem aug_place_body_expr_cases_metadata:
  body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
  env_context_consistent env0 cx /\
  (!k vt. FLOOKUP env0.toplevel_vtypes k = SOME vt ==>
     h k = cenv.ce_hashmap_info k) /\
  (!id. h (NONE,id) = cenv.ce_hashmap_info (NONE,id)) /\
  (!id. m (NONE,id) = cenv.ce_module_var_type (NONE,id)) /\
  supportedExprs$supported_expr tops e ==>
  expr_sim_case F ctx func
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx e /\
  expr_vv_case F ctx func
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx e
Proof
  strip_tac >>
  simp[expr_sim_case_def, expr_vv_case_def] >> conj_tac >> rpt strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (irule (SRULE [] aug_place_uniform_body_pre_backward) >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `expr_sim ctx func cenv cx ty e es /\ expr_vv_sim ctx func cenv cx ty e es` by
    (gvs[body_expr_ok_def] >> first_x_assum irule >> metis_tac[]) >>
  metis_tac[SRULE [] aug_place_expr_sim_metadata,
            SRULE [] aug_place_expr_vv_sim_metadata]
QED

Theorem aug_place_target_idx_metadata:
  !t.
  body_base_target_ok cx t /\ body_inv tops ctx cenv cx /\
  env_context_consistent env0 cx /\
  (!k vt. FLOOKUP env0.toplevel_vtypes k = SOME vt ==>
     h k = cenv.ce_hashmap_info k) /\
  (!id. h (NONE,id) = cenv.ce_hashmap_info (NONE,id)) /\
  (!id. m (NONE,id) = cenv.ce_module_var_type (NONE,id)) /\
  IS_SOME (supported_target_info tops bindings t) ==>
  target_idx_case F ctx func
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx t
Proof
  `(!e:expr. T) /\ (!t.
    body_base_target_ok cx t /\ body_inv tops ctx cenv cx /\
    env_context_consistent env0 cx /\
    (!k vt. FLOOKUP env0.toplevel_vtypes k = SOME vt ==>
       h k = cenv.ce_hashmap_info k) /\
    (!id. h (NONE,id) = cenv.ce_hashmap_info (NONE,id)) /\
    (!id. m (NONE,id) = cenv.ce_module_var_type (NONE,id)) /\
    IS_SOME (supported_target_info tops bindings t) ==>
    target_idx_case F ctx func
      (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx t)`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[body_base_target_ok_def, target_idx_case_def] >>
  rpt conj_tac >> rpt gen_tac
  >~ [`IS_SOME (supported_target_info tops bindings (SubscriptTarget t e))`]
    >- suspend "subscript"
  >> suspend "attribute"
QED

Resume aug_place_target_idx_metadata[attribute]:
  simp[supportedTargetsTheory.supported_target_info_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  Cases_on `supported_target_info tops bindings t` >> gvs[]
QED

Resume aug_place_target_idx_metadata[subscript]:
  rpt gen_tac >> disch_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `supportedExprs$supported_expr tops e /\
   IS_SOME (supported_target_info tops bindings t)` by
    (qpat_x_assum `IS_SOME _` mp_tac >>
     simp[supportedTargetsTheory.supported_target_info_def] >>
     Cases_on `supportedExprs$supported_expr tops e` >> simp[] >>
     Cases_on `supported_target_info tops bindings t` >> simp[]) >>
  conj_tac >- (first_x_assum irule >> simp[]) >>
  strip_tac >> irule (SRULE [] aug_place_body_expr_cases_metadata) >>
  metis_tac[]
QED

Finalise aug_place_target_idx_metadata

Theorem aug_place_target_sim_metadata:
  compile_get_target_ptr compile_expr
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) t =
  compile_get_target_ptr compile_expr cenv t ==>
  (target_sim ctx func
    (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx env t es <=>
   target_sim ctx func cenv cx env t es)
Proof
  strip_tac >> simp[target_sim_def, SRULE [] aug_place_target_post_metadata,
    SRULE [] aug_place_stmt_state_rel_metadata,
    SRULE [] aug_place_local_ptrs_reserved_metadata]
QED

Theorem aug_place_target_indices_pre:
  !t.
    IS_SOME (type_place_target env t) /\
    IS_SOME (supported_target_info tops bindings t) /\
    ~supported_target_exists
      (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) t /\
    call_evaluation_safe cx (int_calls_target t) /\
    supported_program tops /\ get_module_code cx NONE = SOME tops ==>
    target_indices_pre cenv cx env t
Proof
  `(!e:expr. T) /\ (!t.
    IS_SOME (type_place_target env t) /\
    IS_SOME (supported_target_info tops bindings t) /\
    ~supported_target_exists
      (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) t /\
    call_evaluation_safe cx (int_calls_target t) /\
    supported_program tops /\ get_module_code cx NONE = SOME tops ==>
    target_indices_pre cenv cx env t)` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[target_indices_pre_def, supported_expr_exists_def, int_calls_expr_def] >>
  rpt conj_tac >> rpt gen_tac
  >~ [`IS_SOME (type_place_target env (SubscriptTarget t e))`]
    >- suspend "subscript"
  >> suspend "attribute"
QED

Resume aug_place_target_indices_pre[attribute]:
  simp[Once well_typed_expr_def, supportedTargetsTheory.supported_target_info_def] >>
  Cases_on `type_place_target env t` >> simp[] >>
  Cases_on `supported_target_info tops bindings t` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Resume aug_place_target_indices_pre[subscript]:
  simp[Once well_typed_expr_def, supportedTargetsTheory.supported_target_info_def] >>
  Cases_on `well_typed_expr env e` >> simp[] >>
  Cases_on `type_place_target env t` >> simp[] >>
  Cases_on `supportedExprs$supported_expr tops e` >> simp[] >>
  Cases_on `supported_target_info tops bindings t` >> simp[] >>
  rpt strip_tac
  >- (first_x_assum irule >> simp[] >>
      metis_tac[call_evaluation_safe_append_left]) >>
  irule stmt_expr_body_pre >>
  drule supported_expr_body_calls >> strip_tac >>
  simp[] >> metis_tac[call_evaluation_safe_append_right, APPEND_NIL]
QED

Finalise aug_place_target_indices_pre

Theorem aug_place_supported_indices:
  !t. IS_SOME (supported_target_info tops bindings t) ==>
    !e. MEM e (target_indices t) ==> supportedExprs$supported_expr tops e
Proof
  `(!e:expr. T) /\ (!t.
    IS_SOME (supported_target_info tops bindings t) ==>
    !e. MEM e (target_indices t) ==> supportedExprs$supported_expr tops e)`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[target_indices_def, supportedTargetsTheory.supported_target_info_def] >>
  rpt conj_tac >> rpt gen_tac >>
  Cases_on `supported_target_info tops bindings t` >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `supportedExprs$supported_expr tops e` >> gvs[] >> metis_tac[]
QED

Theorem aug_place_target_sim:
  body_base_target_ok cx t /\ body_inv tops ctx cenv cx /\
  expr_sim_inv cenv cx env es /\
  IS_SOME (type_place_target env t) /\
  supported_target_info tops bindings t = SOME pt /\
  ~supported_target_exists
    (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) t /\
  call_evaluation_safe cx (int_calls_target t) ==>
  target_sim ctx func cenv cx env t es
Proof
  strip_tac >>
  drule_all aug_place_metadata_completion >>
  disch_then (qx_choose_then `c1` strip_assume_tac) >>
  qabbrev_tac `h = c1.ce_hashmap_info` >>
  qabbrev_tac `m = c1.ce_module_var_type` >>
  `env_context_consistent env cx` by
    gvs[expr_sim_inv_def, env_consistent_def] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `(expr_sim_inv (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
     cx env es <=> expr_sim_inv cenv cx env es)` by
    (irule aug_place_uniform_inv_metadata >> simp[] >> qexists_tac `env` >> simp[]) >>
  `expr_sim_inv (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>)
     cx env es` by metis_tac[] >>
  `target_idx_case F ctx func
     (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx t` by
    (irule aug_place_target_idx_metadata >> simp[] >>
     conj_tac >- (qexists_tac `env` >> simp[]) >>
     qexistsl_tac [`bindings`, `tops`] >> simp[]) >>
  `target_indices_pre
     (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx env t` by
    (irule aug_place_target_indices_pre >>
     gvs[aug_place_alloc_limits_metadata] >> qexists_tac `bindings` >> simp[]) >>
  `~immutable_root cx t` by metis_tac[aug_place_supported_root_not_immutable] >>
  `target_sim ctx func
     (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) cx env t es` by
    (drule target_case_all >> simp[target_case_def, target_pre_def] >>
     disch_then irule >> gvs[]) >>
  `compile_get_target_ptr compile_expr
     (cenv with <|ce_hashmap_info := h; ce_module_var_type := m|>) t =
   compile_get_target_ptr compile_expr cenv t` by
    (irule aug_place_compile_target_metadata >> reverse conj_tac
     >- (rpt strip_tac >>
         `supported_place_root tops nsid` by metis_tac[aug_place_supported_root] >>
         Cases_on `nsid` >> drule aug_place_supported_root_namespace >>
         strip_tac >> gvs[]) >>
     rpt strip_tac >>
     `supportedExprs$supported_expr tops e` by metis_tac[aug_place_supported_indices, optionTheory.IS_SOME_EXISTS] >>
     irule aug_place_lower_value_metadata >>
     irule aug_place_compile_supported_expr_metadata >> metis_tac[]) >>
  metis_tac[aug_place_target_sim_metadata]
QED

Theorem aug_place_hashmap_build:
  !tops src id vis tr kt vt slot.
    supported_hashmap_decl tops (src,id) = SOME (vis,tr,kt,vt,slot) ==>
    src = NONE /\ build_hashmap_info tops (src,id) = SOME (tr,kt,vt)
Proof
  Induct >> simp[supported_hashmap_decl_def] >> Cases >>
  rw[supported_hashmap_decl_def, build_hashmap_info_def] >> metis_tac[]
QED

Theorem aug_place_variable_excludes_hashmap:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_variable_decl tops nsid = SOME (vis,mut,ty,slot) ==>
  supported_hashmap_decl tops nsid = NONE
Proof
  Cases_on `nsid` >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  drule_all build_maps_variable >> strip_tac >>
  Cases_on `supported_hashmap_decl tops (NONE,r)` >> simp[] >>
  rename1 `supported_hashmap_decl tops (NONE,r) = SOME d` >>
  PairCases_on `d` >> drule aug_place_hashmap_build >> simp[]
QED

Theorem aug_place_legacy_field_info:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_storage_field_write tops id fld ==>
  IS_SOME (supported_target_info tops bindings
    (AttributeTarget (TopLevelNameTarget id) fld))
Proof
  simp[supported_storage_field_write_def, supportedExprFormsTheory.supported_storage_fields_def] >>
  Cases_on `supported_variable_decl tops id` >> simp[] >>
  rename1 `supported_variable_decl tops id = SOME d` >> PairCases_on `d` >>
  Cases_on `d0` >> Cases_on `d1` >> Cases_on `d2` >> Cases_on `d3` >>
  simp[] >> rpt strip_tac >>
  `supported_hashmap_decl tops id = NONE` by
    metis_tac[aug_place_variable_excludes_hashmap] >>
  gvs[supportedTargetsTheory.supported_target_info_def,
      supportedExprFormsTheory.supported_place_root_def, AllCaseEqs()] >>
  Cases_on `supported_storage_type tops (StructT p)` >> gvs[] >>
  Cases_on `supported_struct_fields tops p` >> gvs[] >>
  Cases_on `ALOOKUP x' fld` >> gvs[alistTheory.ALOOKUP_NONE]
QED

Theorem aug_place_legacy_subscript_info:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supportedExprForms$supported_subscript_base tops id /\
  supportedExprs$supported_expr tops key ==>
  IS_SOME (supported_target_info tops bindings
    (SubscriptTarget (TopLevelNameTarget id) key))
Proof
  simp[supportedExprFormsTheory.supported_subscript_base_def] >>
  strip_tac
  >- suspend "array"
  >> suspend "map"
QED

Resume aug_place_legacy_subscript_info[array]:
  qpat_x_assum `supported_storage_array _ _` mp_tac >>
  simp[supportedExprFormsTheory.supported_storage_array_def] >>
  Cases_on `supported_variable_decl tops id` >> simp[] >>
  rename1 `supported_variable_decl tops id = SOME d` >> PairCases_on `d` >>
  Cases_on `d0` >> Cases_on `d1` >> Cases_on `d2` >> Cases_on `d3` >>
  simp[] >> strip_tac >>
  `supported_hashmap_decl tops id = NONE` by
    metis_tac[aug_place_variable_excludes_hashmap] >>
  simp[supportedTargetsTheory.supported_target_info_def,
       supportedExprFormsTheory.supported_place_root_def]
QED

Resume aug_place_legacy_subscript_info[map]:
  Cases_on `supported_hashmap_decl tops id` >> gvs[] >>
  rename1 `supported_hashmap_decl tops id = SOME d` >> PairCases_on `d` >>
  Cases_on `d0` >> Cases_on `d4` >> gvs[] >>
  `supported_variable_decl tops id = NONE` by
    (Cases_on `supported_variable_decl tops id` >> simp[] >>
     rename1 `supported_variable_decl tops id = SOME v` >> PairCases_on `v` >>
     metis_tac[aug_place_variable_excludes_hashmap, optionTheory.NOT_SOME_NONE]) >>
  simp[supportedTargetsTheory.supported_target_info_def,
       supportedExprFormsTheory.supported_place_root_def]
QED

Finalise aug_place_legacy_subscript_info

Theorem aug_place_supported_stmt_target_info:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
  ((?bt fld. t = AttributeTarget bt fld) \/ (?bt k. t = SubscriptTarget bt k)) ==>
  ?pt. supported_target_info tops bindings t = SOME pt
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    gvs[body_inv_def] >>
  `IS_SOME (supported_target_info tops bindings t)` suffices_by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  qpat_x_assum `supported_stmt _ _ _` mp_tac >>
  simp[supportedStmtsTheory.supported_stmt_def] >> strip_tac
  >- (gvs[supportedStmtsTheory.supported_target_def] >>
      Cases_on `bt` >> gvs[] >>
      metis_tac[aug_place_legacy_field_info, aug_place_legacy_subscript_info])
  >- (Cases_on `supported_target_info tops bindings (AttributeTarget bt fld)` >>
      gvs[supported_aug_target_def] >> pairarg_tac >> gvs[])
  >- (gvs[supportedStmtsTheory.supported_target_def] >>
      Cases_on `bt` >> gvs[] >>
      metis_tac[aug_place_legacy_subscript_info])
  >> Cases_on `supported_target_info tops bindings (SubscriptTarget bt k)` >>
     gvs[supported_aug_target_def] >> pairarg_tac >> gvs[]
QED

Theorem aug_place_stmt_target_sim:
  body_base_target_ok cx t /\ body_inv tops ctx cenv cx /\
  expr_sim_inv cenv cx env es /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
  IS_SOME (type_place_target env t) /\
  ~supported_target_exists
    (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) t /\
  call_evaluation_safe cx (int_calls_target t) /\
  ((?bt fld. t = AttributeTarget bt fld) \/ (?bt k. t = SubscriptTarget bt k)) ==>
  target_sim ctx func cenv cx env t es
Proof
  strip_tac >>
  `?pt. supported_target_info tops bindings t = SOME pt` by
    metis_tac[aug_place_supported_stmt_target_info] >>
  irule aug_place_target_sim >> simp[] >> metis_tac[]
QED

Theorem aug_place_eval_cases:
  eval_stmt cx (AugAssign ty t bop e) es = (res,es') ==>
  ?rp stp. eval_target_place cx t es = (rp,stp) /\
    case rp of
      INR ex => res = INR ex /\ es' = stp
    | INL p => ?rc stc. read_place cx p stp = (rc,stc) /\
      case rc of
        INR ex => res = INR ex /\ es' = stc
      | INL cur => ?rt stt. place_type_value cx p stc = (rt,stt) /\
        case rt of
          INR ex => res = INR ex /\ es' = stt
        | INL ptv => ?rr str.
          (do tv <- eval_expr cx e; read_result cx tv od) stt = (rr,str) /\
          case rr of
            INR ex => res = INR ex /\ es' = str
          | INL rhs =>
            case evaluate_binop
              (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
              ptv bop cur rhs of
              INR err => res = INR (Error err) /\ es' = str
            | INL v => write_place cx p v str = (res,es')
Proof
  Cases_on `eval_target_place cx t es` >> rename1 `_ = (rp,stp)` >>
  Cases_on `rp` >>
  simp[Once evaluate_def, bind_def] >>
  rename1 `eval_target_place cx t es = (INL p,stp)` >>
  Cases_on `read_place cx p stp` >>
  rename1 `read_place cx p stp = (rread,sread)` >>
  Cases_on `rread` >> simp[] >>
  rename1 `read_place cx p stp = (INL vcur,sread)` >>
  Cases_on `place_type_value cx p sread` >>
  rename1 `place_type_value cx p sread = (rtype,stype)` >>
  Cases_on `rtype` >> simp[] >>
  rename1 `place_type_value cx p sread = (INL vtype,stype)` >>
  Cases_on `eval_expr cx e stype` >> rename1 `eval_expr cx e stype = (raw,sraw)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `eval_expr cx e stype = (INL vraw,sraw)` >>
  Cases_on `read_result cx vraw sraw` >> rename1 `read_result cx vraw sraw = (rrhs,srhs)` >>
  Cases_on `rrhs` >> simp[] >>
  rename1 `read_result cx vraw sraw = (INL vrhs,srhs)` >>
  qmatch_goalsub_abbrev_tac `evaluate_binop u vtype bop vcur vrhs` >>
  Cases_on `evaluate_binop u vtype bop vcur vrhs` >>
  simp[lift_sum_def, return_def, raise_def, ignore_bind_def]
QED

Theorem aug_place_eval_bop:
  bop <> In /\ bop <> NotIn ==>
  (case evaluate_binop
     (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
     ptv bop cur rhs of
     INR err => res = INR (Error err) /\ es' = st
   | INL v => write_place cx p v st = (res,es')) =
  (case bop_result cx ty bop [ty;expr_type e] cur rhs st of
     INR ex => res = INR ex /\ es' = st
   | INL v => write_place cx p v st = (res,es'))
Proof
  strip_tac >>
  `bop_result cx ty bop [ty;expr_type e] cur rhs st =
   case evaluate_binop
     (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
     ptv bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  simp[] >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
    ptv bop cur rhs` >> simp[]
QED

Theorem aug_place_rhs_pre:
  body_inv tops ctx cenv cx /\
  supportedExprs$supported_expr tops e /\
  expr_sim_inv cenv cx env st /\
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty t bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) ==>
  expr_body_pre cenv cx env e st
Proof
  strip_tac >> drule_then strip_assume_tac supported_expr_body_calls >>
  drule aug_place_typing >> strip_tac >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Theorem aug_place_rhs_ready:
  (!s0 p s1 s2 cur s3 s4 ptv s5.
     eval_target_place cx t s0 = (INL p,s1) /\
     read_place cx p s2 = (INL cur,s3) /\
     place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_ok cx e) /\
  eval_target_place cx t es = (INL p,stp) /\
  read_place cx p stp = (INL cur,stc) /\
  place_type_value cx p stc = (INL ptv,st) /\
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e st /\
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  (do tv <- eval_expr cx e; read_result cx tv od) st = (r1,st1) ==>
  expr_sim ctx func cenv cx ty e st /\ expr_res_ok r1 /\
  expr_sim_inv cenv cx env st1 /\
  (!rhs. r1 = INL rhs ==>
    word_value rhs /\ is_word_type (expr_type e) /\
    ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         value_has_type tv rhs)
Proof
  strip_tac >> drule aug_place_typing >> strip_tac >>
  `body_expr_ok cx e` by metis_tac[] >>
  drule_all expr_body_pre_word_result >> strip_tac >>
  `expr_sim ctx func cenv cx ty e st` by metis_tac[body_expr_ok_def] >>
  simp[] >> metis_tac[exprSimOperatorsTheory.word_value_type_word]
QED

Theorem aug_place_binop_ready:
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  type_bits ty MOD 8 = 0 /\
  evaluate_type (get_tenv cx) ty = SOME tvcur /\ value_has_type tvcur cur /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvrhs /\
  value_has_type tvrhs rhs ==>
  binop_frag ctx func cenv cx bop ty ty bl el tys cur rhs st
Proof
  strip_tac >> drule aug_place_typing >> strip_tac >>
  irule exprSimBinopFragTheory.binop_frag_word_typed >> simp[] >> metis_tac[]
QED

Theorem aug_place_bop_res_ok:
  bop <> In /\ bop <> NotIn /\ stmt_res_ok lctx res /\
  (case evaluate_binop
     (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
     ptv bop cur rhs of
     INR err => res = INR (Error err) /\ es' = st
   | INL v => write_place cx p v st = (res,es')) ==>
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs st)
Proof
  strip_tac >>
  `bop_result cx ty bop [ty;expr_type e] cur rhs st =
   case evaluate_binop
     (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
     ptv bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
    ptv bop cur rhs` >> gvs[expr_res_ok_def, stmt_res_ok_def]
QED

Theorem aug_place_memory_read_typed:
  expr_sim_inv cenv cx env es /\
  supported_target_info tops bindings t = SOME info /\
  eval_target_place cx t es = (INL (MemoryPlace id path),st) /\
  read_place cx (MemoryPlace id path) st = (INL cur,st') /\
  stmt_state_rel ctx func cenv cx st s /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) /\
  is_word_type ty ==>
  ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur
Proof
  strip_tac >> drule_all aug_place_target_memory_live >> strip_tac >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    metis_tac[aug_place_target_entry_typed] >>
  `st.scopes = es.scopes` by metis_tac[aug_place_target_scopes] >>
  gvs[place_ptr_rel_def] >>
  `tv0 = entry.type` by metis_tac[aug_place_entry_type_agrees, optionTheory.SOME_11] >>
  gvs[] >>
  `cur = v` by
    gvs[read_place_def, get_scopes_def, bind_def, lift_option_type_def,
        lift_sum_def, return_def, read_memory_path_def] >>
  gvs[] >> drule mem_path_offset_sound >> strip_tac >>
  irule vyperPlaceStatePreservationTheory.evaluate_subscripts_type >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `entry.value` >> simp[]
QED

Theorem aug_place_memory_access_ready:
  expr_sim_inv cenv cx env es /\ body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
  ((?bt fld. t = AttributeTarget bt fld) \/ (?bt key. t = SubscriptTarget bt key)) /\
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  eval_target_place cx t es = (INL (MemoryPlace id path),st) /\
  read_place cx (MemoryPlace id path) st = (INL cur,stc) /\
  place_type_value cx (MemoryPlace id path) stc = (INL ptv,stt) /\
  stmt_state_rel ctx func cenv cx st s /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) ==>
  stc = st /\ stt = st /\ type_bits ty MOD 8 = 0 /\
  ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur /\
       mload (w2n w) s = typed_val_to_w256 tv cur
Proof
  strip_tac >>
  `?info. supported_target_info tops bindings t = SOME info` by
    metis_tac[aug_place_supported_stmt_target_info] >>
  drule aug_place_typing >> strip_tac >>
  `is_word_type ty` by metis_tac[exprSimOperatorsTheory.word_value_type_word] >>
  drule_all aug_place_memory_read_typed >> strip_tac >>
  drule_all aug_place_memory_load >> strip_tac >> gvs[] >>
  `type_bits ty MOD 8 = 0` by
    (irule well_formed_type_bits >> qexists_tac `get_tenv cx` >>
     simp[well_formed_type_def] >> metis_tac[]) >>
  metis_tac[read_place_state, place_type_value_state]
QED

Theorem aug_place_memory_load_frag:
  emit_op MLOAD [dst] sa = (cur,s1) /\
  local_ptrs_reserved cenv sa /\
  (!z. dst = Var z ==> not_fresh_at sa z) /\ (!l. dst <> Label l) /\
  eval_operand dst s0 = SOME a /\ mload (w2n a) s0 = val_to_w256 v1 ==>
  frag_exec ctx sa s1 (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME a /\
         eval_operand cur s = SOME (val_to_w256 v1) /\
         (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                lookup_var x s = SOME u) /\
         (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                  FLOOKUP s.vs_allocas aid = SOME b)) R
Proof
  rpt strip_tac >>
  `!out. step_inst_base (mk_inst sa.cs_next_id MLOAD [dst] [out]) s0 =
     OK (update_var out (val_to_w256 v1) s0)` by
    (gen_tac >> drule emitHelperPropsTheory.step_MLOAD >> simp[]) >>
  `frag_exec ctx sa s1 (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
     (\s. stmt_state_rel ctx func cenv cx es s /\
          eval_operand cur s = SOME (val_to_w256 v1) /\
          (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                 lookup_var x s = SOME u) /\
          (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP s.vs_allocas aid = SOME b) /\
          s.vs_memory = s0.vs_memory) R` by
    (irule loweringSliceTheory.emit_op_frag >>
     reverse conj_tac >- simp[] >>
     qexistsl_tac [`[dst]`, `MLOAD`] >>
     simp[venomInstTheory.is_terminator_def]) >>
  first_x_assum (mp_then Any irule frag_exec_weaken) >> simp[] >>
  rpt strip_tac >>
  Cases_on `dst` >> gvs[venomStateTheory.eval_operand_def] >> metis_tac[]
QED

Theorem aug_place_memory_bop_frag:
  emit_op MLOAD [dst] sa = (cur,s1) /\
  eval_operand dst s0 = SOME a /\ mload (w2n a) s0 = val_to_w256 v1 /\
  (!z. dst = Var z ==> not_fresh_at sa z) /\ (!l. dst <> Label l) /\
  cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
  (!z. cur = Var z ==> not_fresh_at s1 z) /\ (!l. cur <> Label l) /\
  lower_value compile_expr cenv ty e s1 = (rhs,s2) /\
  compile_binop bop cur rhs ty NONE el s2 = (res_op,s3) /\
  cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
  (!z. rhs = Var z ==> not_fresh_at s2 z) /\ (!l. rhs <> Label l) /\
  fn_has_code sa s3 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ expr_sim ctx func cenv cx ty e es /\
  (do result <- eval_expr cx e; read_result cx result od) es = (r1,es1) /\
  expr_res_ok r1 /\
  (!v2. r1 = INL v2 ==>
    word_value v2 /\ is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
    expr_res_ok (bop_result cx ty bop [ty;expr_type e] v1 v2 es1) /\
    binop_frag ctx func cenv cx bop ty ty NONE el [ty;expr_type e] v1 v2 es1) ==>
  frag_exec ctx sa s3 (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. ?v2 v. r1 = INL v2 /\
      bop_result cx ty bop [ty;expr_type e] v1 v2 es1 = INL v /\
      word_value v /\ stmt_state_rel ctx func cenv cx es1 s /\
      eval_operand res_op s = SOME (val_to_w256 v) /\
      eval_operand dst s = SOME a /\
      (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
             lookup_var x s = SOME u) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP s.vs_allocas aid = SOME b))
    (expr_exit (case r1 of
      INL v2 => bop_result cx ty bop [ty;expr_type e] v1 v2 es1
    | INR ex => INR ex))
Proof
  rpt strip_tac >>
  `!R. frag_exec ctx sa s1
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. stmt_state_rel ctx func cenv cx es s /\
           eval_operand dst s = SOME a /\
           eval_operand cur s = SOME (val_to_w256 v1) /\
           (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                  lookup_var x s = SOME u) /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b)) R` by
    (gen_tac >> irule aug_place_memory_load_frag >> metis_tac[]) >>
  `!z. dst = Var z ==> not_fresh_at s1 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  drule_all stmtSimAugAssignAttrTheory.augassign_load_bop_frag >> simp[]
QED

Theorem aug_place_replace_read_error:
  !path tv a old v err.
    evaluate_subscripts tv a path = INL old /\
    assign_subscripts tv a path (Replace v) = INR err ==>
    ?msg. err = TypeError msg
Proof
  Induct_on `path` >- simp[assign_subscripts_def] >>
  rpt gen_tac >> Cases_on `h`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >>
      Cases_on `a` >>
      simp[Once evaluate_subscripts_def, Once assign_subscripts_def] >>
      simp[AllCaseEqs()] >> rpt strip_tac >>
      TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
      gvs[vyperValueOperationTheory.array_set_index_def,
          vyperValueOperationTheory.array_index_def, AllCaseEqs(),
          listTheory.oEL_THM] >> metis_tac[]) >>
  Cases_on `a` >>
  simp[Once evaluate_subscripts_def, Once assign_subscripts_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem aug_place_memory_write_success:
  lookup_scopes id st.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  write_place cx (MemoryPlace id path) v st = (res,st') /\
  stmt_res_ok lctx res ==>
  res = INL ()
Proof
  strip_tac >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
  simp[write_place_def, get_scopes_def, bind_def, lift_option_type_def,
       type_check_def, assert_def, lift_sum_def, set_scopes_def,
       return_def, raise_def, AllCaseEqs()] >>
  Cases_on `find_containing_scope id st.scopes` >>
  gvs[return_def, raise_def, stmt_res_ok_def] >>
  rename1 `find_containing_scope id st.scopes = SOME fc` >> PairCases_on `fc` >>
  `fc2 = entry` by metis_tac[vyperLookupTheory.find_containing_scope_lookup, optionTheory.SOME_11] >>
  gvs[ignore_bind_def, bind_def, assert_def, return_def, raise_def,
      set_scopes_def, replace_memory_entry_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `assign_subscripts entry.type entry.value path (Replace v)` >>
  gvs[return_def, raise_def] >>
  drule_all aug_place_replace_read_error >> simp[]
QED

Theorem aug_place_memory_ptr_frame:
  place_ptr_rel cenv cx s0 (PlaceR (MemoryPlace id path)) w loc vt /\
  local_ptrs_reserved cenv sa /\
  (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
         lookup_var x s = SOME u) ==>
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc vt
Proof
  simp[place_ptr_rel_def, local_ptrs_reserved_def] >>
  rpt strip_tac >>
  qexistsl_tac [`p`, `sz`, `b`, `t0`, `tv0`, `k`, `tv`, `t`] >>
  simp[] >>
  `not_fresh_at sa p` by metis_tac[] >> metis_tac[]
QED

Theorem aug_place_memory_store_word_frag:
  emit_void MSTORE [dst;res_op] sc = ((),sf) /\
  eval_operand dst u = SOME w /\
  eval_operand res_op u = SOME (val_to_w256 v) /\ word_value v /\
  stmt_state_rel ctx func cenv cx st u /\
  place_ptr_rel cenv cx s0 (PlaceR (MemoryPlace id path)) w
    (SOME LocMemory) (Type ty) /\ local_ptrs_reserved cenv sa /\
  (!x a. not_fresh_at sa x /\ lookup_var x s0 = SOME a ==>
         lookup_var x u = SOME a) /\
  expr_sim_inv cenv cx env st /\ lookup_scopes id st.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  write_place cx (MemoryPlace id path) v st = (res,es') /\
  stmt_res_ok lctx res ==>
  frag_exec ctx sc sf (\s. s = u)
    (\s. res = INL () /\ stmt_state_rel ctx func cenv cx es' s /\
         (!x. lookup_var x s = lookup_var x u) /\
         s.vs_allocas = u.vs_allocas) R
Proof
  strip_tac >>
  `res = INL ()` by (irule aug_place_memory_write_success >> metis_tac[]) >>
  `place_ptr_rel cenv cx u (PlaceR (MemoryPlace id path)) w
     (SOME LocMemory) (Type ty)` by
    (irule aug_place_memory_ptr_frame >> metis_tac[]) >>
  `type_memory_size ptv = 32` by
    metis_tac[entryDecodeStaticPropsTheory.word_type_memory_size] >>
  `store_lays_out ptv ptv v` by
    (irule stmtSimDeclStoreTheory.store_lays_out_word_value >> metis_tac[]) >>
  `typed_val_to_w256 ptv v = val_to_w256 v` by
    metis_tac[typed_val_to_w256_word_value] >>
  simp[] >> irule aug_place_memory_store_frag >> metis_tac[]
QED

Theorem aug_place_memory_finish_frag:
  frag_exec ctx sa sc P
    (\s. ?rhs v. r1 = INL rhs /\
      bop_result cx ty bop [ty;expr_type e] cur rhs st1 = INL v /\
      word_value v /\ stmt_state_rel ctx func cenv cx st1 s /\
      eval_operand res_op s = SOME (val_to_w256 v) /\
      eval_operand dst s = SOME w /\
      (!x a. not_fresh_at sa x /\ lookup_var x s0 = SOME a ==>
             lookup_var x s = SOME a) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP s.vs_allocas aid = SOME b)) R /\
  cs_extends sa sc /\ cs_extends sc sf /\
  emit_void MSTORE [dst;res_op] sc = ((),sf) /\
  place_ptr_rel cenv cx s0 (PlaceR (MemoryPlace id path)) w
    (SOME LocMemory) (Type ty) /\ local_ptrs_reserved cenv sa /\
  expr_sim_inv cenv cx env st1 /\
  lookup_scopes id st1.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  stmt_res_ok lctx res /\
  (!rhs v. r1 = INL rhs /\
     bop_result cx ty bop [ty;expr_type e] cur rhs st1 = INL v ==>
     write_place cx (MemoryPlace id path) v st1 = (res,es')) ==>
  frag_exec ctx sa sf P
    (\s. res = INL () /\ stmt_state_rel ctx func cenv cx es' s /\
      (!x a. not_fresh_at sa x /\ lookup_var x s0 = SOME a ==>
             lookup_var x s = SOME a) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP s.vs_allocas aid = SOME b)) R
Proof
  strip_tac >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` (mp_then Any irule fragExecTheory.frag_exec_then) >>
  simp[] >> rpt strip_tac >>
  `write_place cx (MemoryPlace id path) v st1 = (res,es')` by metis_tac[] >>
  `frag_exec ctx sc sf (\s. s = t)
    (\s. res = INL () /\ stmt_state_rel ctx func cenv cx es' s /\
         (!x. lookup_var x s = lookup_var x t) /\
         s.vs_allocas = t.vs_allocas) R` by
    (drule_all aug_place_memory_store_word_frag >> simp[]) >>
  first_x_assum (mp_then Any irule frag_exec_weaken) >> simp[] >>
  metis_tac[]
QED

Theorem aug_place_memory_continue_ready:
  emit_op MLOAD [dst] sa = (cur_op,s1) /\
  eval_operand dst s0 = SOME w /\ mload (w2n w) s0 = val_to_w256 cur /\
  (!z. dst = Var z ==> not_fresh_at sa z) /\ (!l. dst <> Label l) /\
  cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
  (!z. cur_op = Var z ==> not_fresh_at s1 z) /\ (!l. cur_op <> Label l) /\
  lower_value compile_expr cenv ty e s1 = (rhs_op,s2) /\
  compile_binop bop cur_op rhs_op ty NONE el s2 = (res_op,s3) /\
  cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
  (!z. rhs_op = Var z ==> not_fresh_at s2 z) /\ (!l. rhs_op <> Label l) /\
  fn_has_code sa s3 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ expr_sim ctx func cenv cx ty e st /\
  (do result <- eval_expr cx e; read_result cx result od) st = (r1,st1) /\
  expr_res_ok r1 /\
  (!rhs. r1 = INL rhs ==>
    word_value rhs /\ is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
    expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs st1) /\
    binop_frag ctx func cenv cx bop ty ty NONE el [ty;expr_type e] cur rhs st1) /\
  cs_extends sa s3 /\ cs_extends s3 sf /\
  emit_void MSTORE [dst;res_op] s3 = ((),sf) /\
  place_ptr_rel cenv cx s0 (PlaceR (MemoryPlace id path)) w
    (SOME LocMemory) (Type ty) /\
  expr_sim_inv cenv cx env st1 /\ lookup_scopes id st1.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  stmt_res_ok lctx res /\
  (case r1 of INR ex => res = INR ex /\ es' = st1
   | INL rhs => case bop_result cx ty bop [ty;expr_type e] cur rhs st1 of
       INR ex => res = INR ex /\ es' = st1
     | INL v => write_place cx (MemoryPlace id path) v st1 = (res,es')) ==>
  frag_exec ctx sa sf (\s. s = s0 /\ stmt_state_rel ctx func cenv cx st s)
    (\s. res = INL () /\ stmt_state_rel ctx func cenv cx es' s /\
      (!x a. not_fresh_at sa x /\ lookup_var x s0 = SOME a ==>
             lookup_var x s = SOME a) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP s.vs_allocas aid = SOME b))
    (expr_exit (case r1 of
      INL rhs => bop_result cx ty bop [ty;expr_type e] cur rhs st1
    | INR ex => INR ex))
Proof
  strip_tac >>
  `!rhs v. r1 = INL rhs /\
     bop_result cx ty bop [ty;expr_type e] cur rhs st1 = INL v ==>
     write_place cx (MemoryPlace id path) v st1 = (res,es')` by
    (rpt strip_tac >> gvs[]) >>
  drule_all aug_place_memory_bop_frag >> strip_tac >>
  drule_all aug_place_memory_finish_frag >> simp[]
QED

Theorem aug_place_bop_write_result_ok:
  bop <> In /\ bop <> NotIn /\ stmt_res_ok lctx res /\
  (case bop_result cx ty bop [ty;expr_type e] cur rhs st of
     INR ex => res = INR ex /\ es' = st
   | INL v => write_place cx p v st = (res,es')) ==>
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs st)
Proof
  strip_tac >>
  `bop_result cx ty bop [ty;expr_type e] cur rhs st =
   case evaluate_binop
     (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
     NoneTV bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  Cases_on `evaluate_binop
     (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
     NoneTV bop cur rhs` >> gvs[expr_res_ok_def, stmt_res_ok_def]
QED

Theorem aug_place_memory_continue:
  (!s0 p s1 s2 cur s3 s4 ptv s5.
     eval_target_place cx t s0 = (INL p,s1) /\
     read_place cx p s2 = (INL cur,s3) /\
     place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_ok cx e) /\
  body_inv tops ctx cenv cx /\ supported_stmt tops bindings (AugAssign ty t bop e) /\
  expr_sim_inv cenv cx env es /\ target_indices_pre cenv cx env t /\
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty t bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
  ((?bt fld. t = AttributeTarget bt fld) \/ (?bt key. t = SubscriptTarget bt key)) /\
  eval_target_place cx t es = (INL (MemoryPlace id path),st) /\
  read_place cx (MemoryPlace id path) st = (INL cur,stc) /\
  place_type_value cx (MemoryPlace id path) stc = (INL ptv,stt) /\
  stmt_state_rel ctx func cenv cx st s0 /\
  place_ptr_rel cenv cx s0 (PlaceR (MemoryPlace id path)) w (SOME LocMemory) (Type ty) /\
  (do result <- eval_expr cx e; read_result cx result od) stt = (r1,st1) /\
  stmt_res_ok lctx res /\
  (case r1 of INR ex => res = INR ex /\ es' = st1
   | INL rhs => case bop_result cx ty bop [ty;expr_type e] cur rhs st1 of
       INR ex => res = INR ex /\ es' = st1
     | INL v => write_place cx (MemoryPlace id path) v st1 = (res,es')) /\
  emit_op MLOAD [dst] sa = (cur_op,s1) /\ eval_operand dst s0 = SOME w /\
  (!z. dst = Var z ==> not_fresh_at sa z) /\ (!l. dst <> Label l) /\
  cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
  (!z. cur_op = Var z ==> not_fresh_at s1 z) /\ (!l. cur_op <> Label l) /\
  lower_value compile_expr cenv ty e s1 = (rhs_op,s2) /\
  compile_binop bop cur_op rhs_op ty NONE el s2 = (res_op,s3) /\
  cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
  (!z. rhs_op = Var z ==> not_fresh_at s2 z) /\ (!l. rhs_op <> Label l) /\
  fn_has_code sa s3 func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  cs_extends sa s3 /\ cs_extends s3 sf /\
  emit_void MSTORE [dst;res_op] s3 = ((),sf) ==>
  frag_exec ctx sa sf (\s. s = s0 /\ stmt_state_rel ctx func cenv cx st s)
    (\s. res = INL () /\ stmt_state_rel ctx func cenv cx es' s /\
      (!x a. not_fresh_at sa x /\ lookup_var x s0 = SOME a ==>
             lookup_var x s = SOME a) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP s.vs_allocas aid = SOME b))
    (expr_exit (case r1 of
      INL rhs => bop_result cx ty bop [ty;expr_type e] cur rhs st1
    | INR ex => INR ex))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?info. supported_target_info tops bindings t = SOME info` by
    metis_tac[aug_place_supported_stmt_target_info] >>
  drule_all aug_place_memory_access_ready >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env st` by (irule aug_place_target_inv >> metis_tac[]) >>
  `supportedExprs$supported_expr tops e` by fs[supported_stmt_def] >>
  `expr_body_pre cenv cx env e st` by (irule aug_place_rhs_pre >> metis_tac[]) >>
  drule_all aug_place_rhs_ready >>
  disch_then (qspec_then `func` strip_assume_tac) >>
  drule_all aug_place_target_memory_live >> strip_tac >>
  drule_all aug_place_rhs_memory_entry >> strip_tac >>
  drule aug_place_typing >> strip_tac >>
  `is_word_type ty` by metis_tac[exprSimOperatorsTheory.word_value_type_word] >>
  `word_value cur` by metis_tac[exprSimHypsTheory.word_value_type_typed] >>
  `mload (w2n w) s0 = val_to_w256 cur` by metis_tac[typed_val_to_w256_word_value] >>
  `!rhs. r1 = INL rhs ==>
    expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs st1)` by
    (rpt strip_tac >>
     qpat_x_assum `case r1 of INL _ => _ | INR _ => _` mp_tac >>
     simp[] >> strip_tac >>
     drule_all aug_place_bop_write_result_ok >> simp[]) >>
  `!rhs. r1 = INL rhs ==>
    word_value rhs /\ is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
    expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs st1) /\
    binop_frag ctx func cenv cx bop ty ty NONE el [ty;expr_type e] cur rhs st1` by
    (rpt strip_tac >> gvs[] >>
     irule aug_place_binop_ready >> metis_tac[]) >>
  drule_all aug_place_memory_continue_ready >> simp[]
QED

Theorem aug_place_storage_load_frag:
  emit_op (if tr then TLOAD else SLOAD) [dst] sa = (cur,sb) /\
  eval_operand dst s0 = SOME slot /\
  storage_holds cx tr ty (Value v) slot es /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ word_value v /\
  local_ptrs_reserved cenv sa /\
  (!z. dst = Var z ==> not_fresh_at sa z) /\ (!l. dst <> Label l) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME slot /\
         eval_operand cur s = SOME (val_to_w256 v) /\
         (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                lookup_var x s = SOME u) /\
         (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                  FLOOKUP s.vs_allocas aid = SOME b) /\
         s.vs_memory = s0.vs_memory) R
Proof
  strip_tac >>
  `frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand cur s = SOME (val_to_w256 v) /\
         (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                lookup_var x s = SOME u) /\
         (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                  FLOOKUP s.vs_allocas aid = SOME b) /\
         s.vs_memory = s0.vs_memory) R` by
    (irule loweringSliceTheory.emit_op_frag >>
     reverse conj_tac >- simp[] >>
     qexistsl_tac [`[dst]`, `if tr then TLOAD else SLOAD`] >> simp[] >>
     conj_tac >- (Cases_on `tr` >> simp[venomInstTheory.is_terminator_def]) >>
     conj_tac >- (Cases_on `tr` >> simp[]) >> strip_tac >>
     `(if tr then tload slot s0 else sload slot s0) = val_to_w256 v` by
       (drule_all exprSimUnwrapTheory.storage_holds_load >>
        simp[typed_val_to_w256_word_value]) >>
     gen_tac >> Cases_on `tr` >>
     gvs[venomExecSemanticsTheory.step_inst_base_def,
         venomExecSemanticsTheory.exec_read1_def, venomInstTheory.mk_inst_def]) >>
  first_x_assum (mp_then Any irule frag_exec_weaken) >> simp[] >>
  rpt strip_tac >> Cases_on `dst` >>
  gvs[venomStateTheory.eval_operand_def] >> metis_tac[]
QED

Theorem aug_place_storage_bop_frag:
  emit_op (if tr then TLOAD else SLOAD) [dst] sa = (cur,s1) /\
  eval_operand dst s0 = SOME slot /\
  storage_holds cx tr ty (Value v1) slot es /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ word_value v1 /\
  (!z. dst = Var z ==> not_fresh_at sa z) /\ (!l. dst <> Label l) /\
  cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
  (!z. cur = Var z ==> not_fresh_at s1 z) /\ (!l. cur <> Label l) /\
  lower_value compile_expr cenv ty e s1 = (rhs,s2) /\
  compile_binop bop cur rhs ty NONE el s2 = (res_op,s3) /\
  cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
  (!z. rhs = Var z ==> not_fresh_at s2 z) /\ (!l. rhs <> Label l) /\
  fn_has_code sa s3 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ expr_sim ctx func cenv cx ty e es /\
  (do result <- eval_expr cx e; read_result cx result od) es = (r1,es1) /\
  expr_res_ok r1 /\
  (!v2. r1 = INL v2 ==>
    word_value v2 /\ is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
    expr_res_ok (bop_result cx ty bop [ty;expr_type e] v1 v2 es1) /\
    binop_frag ctx func cenv cx bop ty ty NONE el [ty;expr_type e] v1 v2 es1) ==>
  frag_exec ctx sa s3 (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. ?v2 v. r1 = INL v2 /\
      bop_result cx ty bop [ty;expr_type e] v1 v2 es1 = INL v /\
      word_value v /\ stmt_state_rel ctx func cenv cx es1 s /\
      eval_operand res_op s = SOME (val_to_w256 v) /\
      eval_operand dst s = SOME slot /\
      (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
             lookup_var x s = SOME u) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP s.vs_allocas aid = SOME b))
    (expr_exit (case r1 of
      INL v2 => bop_result cx ty bop [ty;expr_type e] v1 v2 es1
    | INR ex => INR ex))
Proof
  rpt strip_tac >>
  `!R. frag_exec ctx sa s1
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. stmt_state_rel ctx func cenv cx es s /\
           eval_operand dst s = SOME slot /\
           eval_operand cur s = SOME (val_to_w256 v1) /\
           (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
                  lookup_var x s = SOME u) /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b)) R` by
    (gen_tac >> drule_all aug_place_storage_load_frag >>
     disch_then (qspecl_then [`func`, `ctx`, `R`] mp_tac) >>
     disch_then (mp_then Any irule frag_exec_weaken) >> simp[]) >>
  `!z. dst = Var z ==> not_fresh_at s1 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  drule_all stmtSimAugAssignAttrTheory.augassign_load_bop_frag >> simp[]
QED

Theorem aug_place_storage_store_frag:
  emit_void (if tr then TSTORE else SSTORE) [dst; result] sa = ((),sf) /\
  eval_operand dst s0 = SOME slot /\ eval_operand result s0 = SOME w /\
  (!u st. storage_dead cx tr (update_storage slot u st) =
          storage_dead cx tr st) /\
  write_storage_slot cx tr slot tv v es = (res,es') /\
  encode_value tv v = SOME [(0,w)] ==>
  frag_exec ctx sa sf (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. res = INL () /\ stmt_state_rel ctx func cenv cx es' s /\
         (!x. lookup_var x s = lookup_var x s0) /\
         s.vs_allocas = s0.vs_allocas /\ s.vs_memory = s0.vs_memory) R
Proof
  strip_tac >>
  imp_res_tac emitHelperPropsTheory.emitted_insts_emit_void >> imp_res_tac emit_void_extends >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sf)` by
    (Cases_on `tr` >> gvs[venomInstTheory.mk_inst_def,
                            venomInstTheory.is_terminator_def]) >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND3] >>
  rpt strip_tac >> gvs[] >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >>
  disj1_tac >>
  `step_inst_base (mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE)
                      [dst; result] []) s0 =
     OK (if tr then tstore slot w s0 else sstore slot w s0)` by
    (Cases_on `tr` >>
     gvs[venomExecSemanticsTheory.step_inst_base_def,
         venomExecSemanticsTheory.exec_write2_def, venomInstTheory.mk_inst_def]) >>
  Cases_on `tr` >> gvs[] >>
  gvs[run_inst_seq_def, stmt_state_rel_inst_idx,
       venomStateTheory.lookup_var_def, venomStateTheory.sstore_def,
       venomStateTheory.tstore_def, LET_THM]
QED

Theorem aug_place_storage_query_metadata:
  place_ptr_rel cenv cx s (PlaceR (StoragePlace tr slot tv)) w loc (Type ty) /\
  read_place cx (StoragePlace tr slot tv) st = (INL cur,stc) /\
  place_type_value cx (StoragePlace tr slot tv) stc = (INL ptv,stt) ==>
  w = slot /\ loc = SOME (slot_loc tr) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stc = st /\ stt = st /\ ptv = tv /\
  read_storage_slot cx tr slot tv st = (INL cur,st)
Proof
  strip_tac >>
  `stc = st /\ stt = st` by
    metis_tac[read_place_state, place_type_value_state] >>
  gvs[place_ptr_rel_def, read_place_def, place_type_value_def,
      return_def]
QED

Theorem aug_place_update_lookup_other[local]:
  !(k:bytes32) u st i.
    i < dimword (:256) /\ i <> w2n k ==>
    lookup_storage (n2w i) (update_storage k u st) = lookup_storage (n2w i) st
Proof
  rpt strip_tac >>
  `(n2w i:bytes32) <> k` by
    (disch_then (mp_tac o AP_TERM ``w2n:bytes32 -> num``) >>
     asm_simp_tac pure_ss [wordsTheory.w2n_n2w,
                          arithmeticTheory.LESS_MOD] >> simp[]) >>
  simp[vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM]
QED

Theorem aug_place_dead_bytes_field_update:
  !fs fld off ctv bs k u st.
    struct_field_slot fs fld = SOME (off,ctv) /\
    bs + type_slot_size_fields fs <= dimword (:256) /\
    bs + off <= w2n k /\ w2n k < bs + off + type_slot_size ctv /\
    (!j byte. dead_bytes (update_storage k u st) (bs+off) ctv j byte <=>
              dead_bytes st (bs+off) ctv j byte) ==>
    !j byte. dead_bytes_fields (update_storage k u st) bs fs j byte <=>
             dead_bytes_fields st bs fs j byte
Proof
  Induct_on `fs` >- simp[struct_field_slot_def] >>
  Cases >> rpt gen_tac >> rename1 `(fid,fty)::fs` >>
  simp[struct_field_slot_def, vyperValueTheory.type_slot_size_def] >>
  strip_tac >> simp[dead_bytes_def] >>
  Cases_on `fid = fld` >> gvs[] >> rpt gen_tac
  >- (AP_TERM_TAC >> irule (cj 3 accountsRelPropsTheory.dead_bytes_frame) >>
      rpt strip_tac >> irule aug_place_update_lookup_other >> decide_tac) >>
  rename1 `struct_field_slot fs fld = SOME z` >> Cases_on `z` >> gvs[] >>
  rename1 `struct_field_slot fs fld = SOME (off,ctv)` >>
  `off + type_slot_size ctv <= type_slot_size_fields fs` by
    (drule vyperStoragePlaceRegionTheory.struct_field_slot_end_bound >>
     simp[vyperValueTheory.type_slot_size_def]) >>
  `dead_bytes (update_storage k u st) bs fty j byte <=>
   dead_bytes st bs fty j byte` by
    (irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >> rpt strip_tac >>
     irule aug_place_update_lookup_other >> decide_tac) >>
  simp[] >> AP_TERM_TAC >> first_x_assum irule >> simp[] >>
  qexistsl_tac [`ctv`, `fld`, `off`] >> metis_tac[]
QED

Theorem aug_place_dead_bytes_other_cell[local]:
  i < n /\ h < n /\ h <> i /\ bs+n*type_slot_size tv <= dimword (:256) /\
  bs+i*type_slot_size tv <= w2n k /\
  w2n k < bs+i*type_slot_size tv+type_slot_size tv ==>
  !j byte. dead_bytes (update_storage k u st) (bs+h*type_slot_size tv) tv j byte <=>
           dead_bytes st (bs+h*type_slot_size tv) tv j byte
Proof
  strip_tac >> rpt gen_tac >>
  `(h+1)*type_slot_size tv <= n*type_slot_size tv` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  `bs+h*type_slot_size tv+type_slot_size tv <= bs+i*type_slot_size tv \/
   bs+i*type_slot_size tv+type_slot_size tv <= bs+h*type_slot_size tv` by
    metis_tac[aug_place_cells_disjoint] >>
  irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >> rpt strip_tac >>
  irule aug_place_update_lookup_other >>
  rule_assum_tac (PURE_REWRITE_RULE [arithmeticTheory.RIGHT_ADD_DISTRIB,
                                    arithmeticTheory.MULT_CLAUSES]) >>
  decide_tac
QED

Theorem aug_place_dead_bytes_array_fixed_update[local]:
  i < n /\ bs+n*type_slot_size tv <= dimword (:256) /\
  bs+i*type_slot_size tv <= w2n k /\
  w2n k < bs+i*type_slot_size tv+type_slot_size tv /\
  (!j byte. dead_bytes (update_storage k u st) (bs+i*type_slot_size tv) tv j byte <=>
            dead_bytes st (bs+i*type_slot_size tv) tv j byte) ==>
  !j byte. dead_bytes (update_storage k u st) bs (ArrayTV tv (Fixed n)) j byte <=>
           dead_bytes st bs (ArrayTV tv (Fixed n)) j byte
Proof
  strip_tac >>
  `!h j byte. h < n ==>
     (dead_bytes (update_storage k u st) (bs+h*type_slot_size tv) tv j byte <=>
      dead_bytes st (bs+h*type_slot_size tv) tv j byte)` by
    (rpt strip_tac >> Cases_on `h = i` >- gvs[] >>
     irule aug_place_dead_bytes_other_cell >> qexistsl_tac [`i`, `n`] >> simp[]) >>
  simp[dead_bytes_def] >> metis_tac[]
QED

Theorem aug_place_dead_bytes_array_dynamic_update[local]:
  i < n /\ bs+1+n*type_slot_size tv <= dimword (:256) /\
  bs+1+i*type_slot_size tv <= w2n k /\
  w2n k < bs+1+i*type_slot_size tv+type_slot_size tv /\
  (!j byte. dead_bytes (update_storage k u st) (bs+1+i*type_slot_size tv) tv j byte <=>
            dead_bytes st (bs+1+i*type_slot_size tv) tv j byte) ==>
  !j byte. dead_bytes (update_storage k u st) bs (ArrayTV tv (Dynamic n)) j byte <=>
           dead_bytes st bs (ArrayTV tv (Dynamic n)) j byte
Proof
  strip_tac >>
  `lookup_storage (n2w bs) (update_storage k u st) = lookup_storage (n2w bs) st` by
    (irule aug_place_update_lookup_other >> decide_tac) >>
  `!h j byte. h < n ==>
     (dead_bytes (update_storage k u st) (bs+1+h*type_slot_size tv) tv j byte <=>
      dead_bytes st (bs+1+h*type_slot_size tv) tv j byte)` by
    (rpt strip_tac >> Cases_on `h = i` >- gvs[] >>
     irule aug_place_dead_bytes_other_cell >> qexistsl_tac [`i`, `n`] >> simp[]) >>
  simp[dead_bytes_def] >> rpt gen_tac >>
  eq_tac >> strip_tac >> qexists_tac `i'` >>
  Cases_on `i' < w2n (lookup_storage (n2w bs) st)` >> gvs[] >> metis_tac[]
QED

Theorem aug_place_dead_bytes_array_update:
  i < n /\
  c = (if dyn then bs+1 else bs)+i*type_slot_size tv /\
  bs+type_slot_size (ArrayTV tv (if dyn then Dynamic n else Fixed n)) <= dimword (:256) /\
  c <= w2n k /\ w2n k < c+type_slot_size tv /\
  (!j byte. dead_bytes (update_storage k u st) c tv j byte <=>
            dead_bytes st c tv j byte) ==>
  !j byte. dead_bytes (update_storage k u st) bs
             (ArrayTV tv (if dyn then Dynamic n else Fixed n)) j byte <=>
           dead_bytes st bs (ArrayTV tv (if dyn then Dynamic n else Fixed n)) j byte
Proof
  Cases_on `dyn` >> simp[vyperValueTheory.type_slot_size_def] >> strip_tac
  >- (irule aug_place_dead_bytes_array_dynamic_update >>
      reverse conj_tac >- simp[] >>
      qexists_tac `i` >> gvs[]) >>
  irule aug_place_dead_bytes_array_fixed_update >>
  reverse conj_tac >- simp[] >> qexists_tac `i` >> gvs[]
QED

Theorem aug_place_subregion_mask[local]:
  storage_subregion tv [sb] off leaf /\
  ((?fs. tv = StructTV fs) \/ (?et bd. tv = ArrayTV et bd)) /\
  bs + type_slot_size tv <= dimword (:256) /\
  bs+off <= w2n k /\ w2n k < bs+off+type_slot_size leaf /\
  (!j byte. dead_bytes (update_storage k u st) (bs+off) leaf j byte <=>
            dead_bytes st (bs+off) leaf j byte) ==>
  !j byte. dead_bytes (update_storage k u st) bs tv j byte <=>
           dead_bytes st bs tv j byte
Proof
  reverse (strip_tac >> Cases_on `tv` >> gvs[])
  >- (rename1 `ArrayTV et bd` >> Cases_on `sb` >>
      gvs[vyperStoragePlaceRegionTheory.storage_subregion_def] >>
      rename1 `ValueSubscript key` >> Cases_on `key` >>
      Cases_on `bd` >> gvs[vyperStoragePlaceRegionTheory.storage_subregion_def]
      >- (irule aug_place_dead_bytes_array_fixed_update >>
          reverse conj_tac >- gvs[vyperValueTheory.type_slot_size_def] >>
          goal_assum (drule_at Any) >> gvs[]) >>
      irule aug_place_dead_bytes_array_dynamic_update >>
      reverse conj_tac >- gvs[vyperValueTheory.type_slot_size_def] >>
      goal_assum (drule_at Any) >> gvs[]) >>
  Cases_on `sb`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >>
      gvs[vyperStoragePlaceRegionTheory.storage_subregion_def]) >>
  gvs[vyperStoragePlaceRegionTheory.storage_subregion_def] >>
  simp[dead_bytes_def] >> irule aug_place_dead_bytes_field_update >>
  conj_tac >- gvs[vyperValueTheory.type_slot_size_def] >>
  qexistsl_tac [`leaf`, `s`, `off`] >> gvs[]
QED

Theorem aug_place_storage_extend_mask:
  extend_storage_place cx tr slot tv sb es =
    (INL (StoragePlace tr child leaf),es') /\
  ((?fs. tv = StructTV fs) \/ (?et bd. tv = ArrayTV et bd)) /\
  w2n slot + type_slot_size tv <= dimword (:256) /\
  w2n child <= w2n k /\ w2n k < w2n child+type_slot_size leaf /\
  (!j byte. dead_bytes (update_storage k u st) (w2n child) leaf j byte <=>
            dead_bytes st (w2n child) leaf j byte) ==>
  !j byte. dead_bytes (update_storage k u st) (w2n slot) tv j byte <=>
           dead_bytes st (w2n slot) tv j byte
Proof
  strip_tac >>
  drule vyperStoragePlaceProvenanceTheory.extend_storage_place_subregion >>
  strip_tac >> gvs[] >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  `0 < type_slot_size leaf` by decide_tac >>
  `w2n slot + delta < dimword (:256)` by decide_tac >>
  `w2n (slot + n2w delta) = w2n slot + delta` by
    (simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
          arithmeticTheory.LESS_MOD]) >>
  irule aug_place_subregion_mask >>
  (conj_tac >- decide_tac) >> (conj_tac >- simp[]) >>
  qexistsl_tac [`leaf`, `delta`, `sb`] >> gvs[]
QED

Theorem aug_place_dead_bytes_tuple_update:
  !types i leaf bs k u st.
    oEL i types = SOME leaf /\
    bs + type_slot_size (TupleTV types) <= dimword (:256) /\
    bs + tuple_prefix_slot_size i types <= w2n k /\
    w2n k < bs + tuple_prefix_slot_size i types + type_slot_size leaf /\
    (!j byte. dead_bytes (update_storage k u st)
                (bs + tuple_prefix_slot_size i types) leaf j byte <=>
              dead_bytes st (bs + tuple_prefix_slot_size i types) leaf j byte) ==>
    !j byte. dead_bytes (update_storage k u st) bs (TupleTV types) j byte <=>
             dead_bytes st bs (TupleTV types) j byte
Proof
  Induct_on `types` >- simp[listTheory.oEL_def] >>
  rpt gen_tac >> Cases_on `i` >>
  simp[listTheory.oEL_def, tuple_prefix_slot_size_def,
       vyperValueTheory.type_slot_size_def] >> strip_tac >> gvs[] >>
  simp[dead_bytes_def] >> rpt gen_tac
  >- (AP_TERM_TAC >> irule (cj 2 accountsRelPropsTheory.dead_bytes_frame) >>
      rpt strip_tac >> irule aug_place_update_lookup_other >> decide_tac) >>
  `dead_bytes (update_storage k u st) bs h j byte <=>
   dead_bytes st bs h j byte` by
    (irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >> rpt strip_tac >>
     irule aug_place_update_lookup_other >> decide_tac) >>
  simp[] >> AP_TERM_TAC >>
  first_x_assum (irule o SRULE [dead_bytes_def, vyperValueTheory.type_slot_size_def]) >>
  conj_tac >- decide_tac >> qexistsl_tac [`n`, `leaf`] >> gvs[]
QED

Theorem aug_place_subregion_path_mask:
  !tv path off leaf. storage_subregion tv path off leaf ==>
  !bs k u st.
    bs + type_slot_size tv <= dimword (:256) /\
    bs+off <= w2n k /\ w2n k < bs+off+type_slot_size leaf /\
    (!j byte. dead_bytes (update_storage k u st) (bs+off) leaf j byte <=>
              dead_bytes st (bs+off) leaf j byte) ==>
    !j byte. dead_bytes (update_storage k u st) bs tv j byte <=>
             dead_bytes st bs tv j byte
Proof
  ho_match_mp_tac vyperStoragePlaceRegionTheory.storage_subregion_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  qpat_x_assum `storage_subregion _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [Once vyperStoragePlaceRegionTheory.storage_subregion_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> gvs[] >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac
  >- (`Num i * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
        (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
      `!j byte. dead_bytes (update_storage k u st)
          (bs + Num i * type_slot_size tv) tv j byte <=>
          dead_bytes st (bs + Num i * type_slot_size tv) tv j byte` by
        (first_x_assum irule >> conj_tac
         >- gvs[vyperValueTheory.type_slot_size_def] >>
         qexists_tac `rest` >> gvs[]) >>
      irule aug_place_dead_bytes_array_fixed_update >>
      reverse conj_tac >- gvs[vyperValueTheory.type_slot_size_def] >>
      qexists_tac `Num i` >> gvs[])
  >- (`Num i * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
        (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
      `!j byte. dead_bytes (update_storage k u st)
          (bs + 1 + Num i * type_slot_size tv) tv j byte <=>
          dead_bytes st (bs + 1 + Num i * type_slot_size tv) tv j byte` by
        (first_x_assum irule >> conj_tac
         >- gvs[vyperValueTheory.type_slot_size_def] >>
         qexists_tac `rest` >> gvs[]) >>
      irule aug_place_dead_bytes_array_dynamic_update >>
      reverse conj_tac >- gvs[vyperValueTheory.type_slot_size_def] >>
      qexists_tac `Num i` >> gvs[])
  >- (drule vyperStoragePlaceRegionTheory.struct_field_slot_end_bound >> strip_tac >>
      `!j byte. dead_bytes (update_storage k u st) (bs+delta) elem j byte <=>
                dead_bytes st (bs+delta) elem j byte` by
        (first_x_assum irule >> conj_tac >- decide_tac >>
         qexists_tac `rest` >> gvs[]) >>
      simp[dead_bytes_def] >> irule aug_place_dead_bytes_field_update >>
      conj_tac >- gvs[vyperValueTheory.type_slot_size_def] >>
      qexistsl_tac [`elem`, `id`, `delta`] >> gvs[]) >>
  drule vyperStoragePlaceRegionTheory.tuple_component_slot_end_bound >> strip_tac >>
  `!j byte. dead_bytes (update_storage k u st)
       (bs + tuple_prefix_slot_size (Num i) types) elem j byte <=>
       dead_bytes st (bs + tuple_prefix_slot_size (Num i) types) elem j byte` by
    (first_x_assum irule >> conj_tac >- decide_tac >>
     qexists_tac `rest` >> gvs[]) >>
  irule aug_place_dead_bytes_tuple_update >>
  conj_tac >- simp[] >> qexistsl_tac [`Num i`, `elem`] >> gvs[]
QED

Theorem aug_place_region_storage_dead_stable:
  storage_place_region cx (StoragePlace tr slot leaf) /\ type_slot_size leaf = 1 ==>
  !u st. storage_dead cx tr (update_storage slot u st) = storage_dead cx tr st
Proof
  simp_tac (srw_ss()) [vyperStoragePlaceProvenanceTheory.storage_place_region_def] >>
  strip_tac >> rpt gen_tac >>
  irule accountsRelPropsTheory.storage_dead_update_in_region >>
  qexistsl_tac [`root`, `mid`, `var_name`, `keys`, `tv`] >> simp[] >>
  strip_tac >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  `w2n root + delta < dimword (:256)` by decide_tac >>
  `w2n slot = w2n root + delta` by
    gvs[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
        arithmeticTheory.LESS_MOD] >>
  qpat_x_assum `slot = _` (SUBST_ALL_TAC o SYM) >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  irule aug_place_subregion_path_mask >> conj_tac >- simp[] >>
  qexistsl_tac [`leaf`, `delta`, `path`] >> simp[] >>
  rpt strip_tac >> eq_tac >> strip_tac >>
  drule (cj 1 accountsRelPropsTheory.dead_bytes_range) >> simp[]
QED

Theorem aug_place_target_storage_dead_stable:
  eval_target_place cx t es = (INL (StoragePlace tr slot leaf),es') /\
  type_slot_size leaf = 1 ==>
  !u st. storage_dead cx tr (update_storage slot u st) = storage_dead cx tr st
Proof
  strip_tac >> drule vyperStoragePlaceProvenanceTheory.eval_target_place_region >>
  strip_tac >> irule aug_place_region_storage_dead_stable >>
  qexists_tac `leaf` >> simp[]
QED

Theorem aug_place_storage_read_holds:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  read_storage_slot cx tr slot tv st = (INL cur,st) /\
  slots_in_range (get_storage cx st tr) (w2n slot) tv /\
  storage_read_live cx tr (get_storage cx st tr) slot tv ==>
  storage_holds cx tr ty (Value cur) slot st
Proof
  strip_tac >> simp[storage_holds_def, read_result_def, return_def] >>
  qexists_tac `tv` >> simp[]
QED

Theorem body_augassign_place:
  !cx ty t bop e tops bindings ctx func cenv env env' ret_ty lctx RetQ es
   res es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\ body_base_target_ok cx t /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign ty t bop e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (AugAssign ty t bop e) es = (res, es') /\
    ((?bt fld. t = AttributeTarget bt fld) \/ (?bt k. t = SubscriptTarget bt k)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e)) es res es'
Proof
  cheat
QED

(* RESIDUAL (#637 augmented assignment): a top-level target other than a
   word storage or transient variable (supported_scalar_target), that is
   an immutable (supported_target's supported_immutable_type): no
   statement lemma.  Locals, fields and elements have theirs above. *)
Theorem body_augassign_other:
  !cx ty t bop e tops bindings ctx func cenv env env' ret_ty lctx RetQ es
   res es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\ body_base_target_ok cx t /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign ty t bop e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (AugAssign ty t bop e) es = (res, es') /\
    ~(?id. t = NameTarget id) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\
             supported_scalar_target tops nsid) /\
    ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
    ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                 supported_storage_field_write tops nsid fld) /\
    ~(?bt fld. t = AttributeTarget bt fld) /\
    ~(?bt k. t = SubscriptTarget bt k) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e)) es res es'
Proof
  cheat
QED

Theorem body_augassign_case:
  !cx ty t bop e.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\ body_base_target_ok cx t ==>
    body_stmt_ok cx (AugAssign ty t bop e)
Proof
  rw[body_stmt_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  Cases_on `?id. t = NameTarget id`
  >- (gvs[] >> irule body_augassign_local >> metis_tac[]) >>
  Cases_on `?nsid. t = TopLevelNameTarget nsid /\
                   supported_scalar_target tops nsid`
  >- (gvs[] >> rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      irule body_augassign_toplevel_word >> metis_tac[]) >>
  Cases_on `?id fld. t = AttributeTarget (NameTarget id) fld`
  >- (gvs[] >> irule body_augassign_attr_local >> metis_tac[]) >>
  Cases_on `?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                       supported_storage_field_write tops nsid fld`
  >- (gvs[] >> rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      irule body_augassign_attr_storage >> metis_tac[]) >>
  Cases_on `(?bt fld. t = AttributeTarget bt fld) \/
            (?bt k. t = SubscriptTarget bt k)`
  >- (irule body_augassign_place >> metis_tac[]) >>
  irule body_augassign_other >> metis_tac[]
QED

(* stmtSimIf's compile_if_stmt_frag, with the branches' judgments at the
   pushed scope. *)
Theorem body_if_case:
  !cx e ss1 ss2.
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_ok cx ss1) /\
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_ok cx ss2) /\ body_expr_ok cx e ==>
    body_stmt_ok cx (If e ss1 ss2)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmt_ok_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
      stmt_exprs_ok_def, supported_stmt_expr_exists_def, optionTheory.IS_SOME_EXISTS] >>
  `supported_expr tops e` by simp[supported_expr_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >> simp[] >>
     qexists_tac `int_calls_stmts ss1 ++ int_calls_stmts ss2` >> simp[]) >>
  `!ty. expr_sim ctx func cenv cx ty e es /\
        expr_vv_sim ctx func cenv cx ty e es` by
    (gen_tac >>
     qpat_x_assum `body_expr_ok _ _` (mp_tac o REWRITE_RULE [body_expr_ok_def]) >>
     disch_then irule >> conj_tac
     >- (qexists_tac `tops` >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  irule compile_if_stmt_frag >> simp[stmts_env_cs_mono] >>
  reverse conj_tac >- metis_tac[compile_expr_grows] >>
  rpt strip_tac >>
  rename1 `_ = (INL (BoolV b), es1)` >>
  `?tv s1. eval_expr cx e es = (INL tv, s1)` by
    (qpat_x_assum `_ = (INL (BoolV b), es1)` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_stmts_ok cx ss1 /\ body_stmts_ok cx ss2` by
    (`push_scope es1 = (INL (), es1 with scopes updated_by CONS FEMPTY)` by
       simp[push_scope_def, return_def] >>
     metis_tac[]) >>
  `expr_sim_inv cenv cx env es1` by
    (drule_all expr_body_pre_eval >> simp[]) >>
  drule expr_sim_inv_push_scope >> strip_tac >>
  rpt (qpat_x_assum `body_stmts_ok _ _`
         (strip_assume_tac o REWRITE_RULE [body_stmts_ok_def])) >>
  Cases_on `b` >> fs[] >> first_x_assum irule >>
  gvs[stmts_exprs_ok_EVERY, stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]
QED

(* stmtSim's compile_expr_stmt_frag_ok, given the expression's
   expr_vv_sim (the IH) and compile_expr_open. *)
Theorem body_expr_stmt_case:
  !cx e. body_expr_ok cx e ==> body_stmt_ok cx (Expr e)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmt_ok_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
      stmt_exprs_ok_def, supported_stmt_expr_exists_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >> simp[] >> qexists_tac `[]` >> simp[]) >>
  `expr_sim ctx func cenv cx (expr_type e) e es /\
   expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_ok _ _` (mp_tac o REWRITE_RULE [body_expr_ok_def]) >>
     disch_then (qspecl_then [`tops`, `ctx`, `func`, `cenv`, `env`,
                              `expr_type e`, `es`] mp_tac) >>
     simp[]) >>
  irule compile_expr_stmt_frag_ok >> simp[] >>
  rpt gen_tac >> strip_tac >> irule compile_expr_open >> metis_tac[]
QED

(* ===== Statement lists ===== *)

Theorem body_stmts_nil_case:
  !cx. body_stmts_ok cx []
Proof
  rw[body_stmts_ok_def] >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, return_def] >> rw[stmt_frag_nil]
QED

(* stmtSim's stmt_frag_cons_env: the head by the IH, the tail by the IH at
   the environments the head's typing and declaration give. *)
Theorem body_stmts_cons_case:
  !cx s ss.
    (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_ok cx ss) /\
    body_stmt_ok cx s ==>
    body_stmts_ok cx (s::ss)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmts_ok_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[supported_stmt_def, type_stmt_def, AllCaseEqs(), int_calls_stmt_def] >>
  rename1 `type_stmt env ret_ty s = SOME env1` >>
  irule stmt_frag_cons_env >>
  simp[cj 1 compile_stmt_cs_mono, stmts_env_cs_mono] >> reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `body_stmt_ok _ _` (irule o REWRITE_RULE [body_stmt_ok_def]) >>
      metis_tac[call_evaluation_safe_append_left]) >>
  rpt strip_tac >>
  rename1 `stmt_env cenv lctx ret_ty s sa = (c, sm)` >>
  `same_frame cenv c` by metis_tac[cenv_top_ext_same_frame] >>
  `eval_stmts cx ss es1 = (res, es')` by
    (qpat_x_assum `eval_stmts _ (_::_) _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, ignore_bind_def]) >>
  `stmt_exprs_ok c = stmt_exprs_ok cenv` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  `expr_sim_inv c cx env1 es1` by
    (irule expr_sim_inv_stmt >> fs[body_inv_def] >>
     metis_tac[call_evaluation_safe_append_left]) >>
  `ce_locals_declared c env1` by metis_tac[ce_locals_declared_stmt] >>
  `locals_alloc_ok c env1` by metis_tac[locals_alloc_ok_stmt] >>
  `body_inv tops ctx c cx` by
    metis_tac[body_inv_same_frame] >>
  `frame_ret_ok ctx func cx RetQ c ret_ty` by
    metis_tac[frame_ret_ok_same_frame] >>
  qpat_x_assum `!s'' t. _ ==> body_stmts_ok _ _` drule >>
  simp[body_stmts_ok_def] >> disch_then irule >>
  metis_tac[call_evaluation_safe_append_right]
QED
