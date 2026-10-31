(*
 * The body simulation of S1: statement cases (#637)
 *
 * One lemma for each statement case of evaluate_ind that bodySimMain's
 * body_sim_mutual does not close in a line or two.  Those marked GAP are
 * cheated; their comments name the existing lemmas they dispatch to and
 * what is left.  A case whose covered forms are proved dispatches the rest
 * to a cheated lemma marked RESIDUAL, whose comment names the premises
 * missing for the remaining forms.  The declarations, AnnAssign and For,
 * are in bodySimDeclCases.
 *
 * TOP-LEVEL:
 *   body_*_case       — one case of the induction each
 *   body_*_other      — the residual forms of a case
 *   stmt_expr_body_pre — a statement's expression meets expr_body_pre
 *   supported_expr_body_calls, supported_string_reason_body_calls — a
 *                       supported expression or reason runs no EVM code
 *                       and calls only the main module's functions
 *   reason_covered    — a reason compiles to a form the reason lemmas take
 *   no_internal_call_int_calls, supported_pure_int_calls — no internal
 *                       call means int_calls_* = []
 *   expr_body_pre_eval_result, expr_body_pre_eval — evaluation keeps
 *                       expr_sim_inv and types the value
 *   type_widens_to_word — widening to a word type is equality
 *   expr_sim_inv_stmt  — expr_sim_inv after a statement, at the type
 *                        environment and compile environment it gives
 *   ce_locals_declared_declare_local, ce_locals_declared_stmt — the same
 *                        for ce_locals_declared
 *   compile_expr_open  — a supported expression that evaluates compiles
 *                        without terminating its block
 *   eval_stmts_popped_keys_indexed — statement evaluation keeps
 *                        popped_keys_indexed
 *   declared_name_not_module_key — GAP, the fact the statement cases still
 *                        take on trust
 *
 * Helper:
 *   stmts_env_cs_mono, stmt_env_declare, declare_stmt_local_other,
 *   type_stmt_other, declare_local_module_var_type,
 *   stmt_env_module_var_type — stmt_env and type_stmt of a statement
 *   same_frame_trans, body_inv_same_frame, frame_ret_ok_same_frame,
 *   stmt_exprs_ok_same_frame, stmts_exprs_ok_EVERY — the frame facts
 *                        at a later compile env of the same body
 *   expr_sim_inv_push_scope — expr_sim_inv in a new scope
 *)

Theory bodySimStmtCases
Ancestors
  list finite_map bodySim exprSim exprSimHyps exprLoweringProps stmtSim
  stmtSimIf stmtLoweringMono stmtLowering compileEnv fragExec
  supportedExprTraverse supportedStmtTraverse supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness stmtSimReason stmtSimReasonExpr
  stmtSimReasonStorage supportedExprs stmtSimAssign stmtSimDeclStore
  stmtSimAugAssign vyperTypeEvalSoundness vyperTypeInvariants
  vyperTypeExprSoundness vyperEvalOutcomeSuffix exprSimMain
  vyperTypeValues vyperTyping vyperTypeDefaults stmtSimAssignTuple
  vyperTypeEnvPreservation bodySimExprCases bodyStoragePreservation
  vyperCallOutcomeStorage vyperTypeStoragePreservation
  stmtSimAssignStorage supportedDecls vyperTypeContractStaticMaps
  vyperTypeContract compileVyper supportedTypes stmtPoppedKeys exprOpenMain
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

Theorem body_inv_same_frame:
  !tops ctx cenv c cx.
    body_inv tops ctx cenv cx /\ same_frame cenv c /\
    (!id. c.ce_var_type (module_var_key (NONE, id)) =
          cenv.ce_var_type (module_var_key (NONE, id))) ==>
    body_inv tops ctx c cx
Proof
  rpt strip_tac >>
  fs[body_inv_def, same_frame_def, compile_env_component_equality] >>
  metis_tac[]
QED

(* A declaration keeps cenv's type at a module key ("self." ++ name)
   unless it declares that very key. *)
Theorem declare_local_module_var_type:
  !cenv id ty st c st1 x.
    declare_local cenv id ty st = (c, st1) /\
    id <> module_var_key (NONE, x) ==>
    c.ce_var_type (module_var_key (NONE, x)) =
    cenv.ce_var_type (module_var_key (NONE, x))
Proof
  rpt gen_tac >> simp[declare_local_def] >>
  Cases_on `cenv.ce_alloca_locals` >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_return_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem stmt_env_module_var_type:
  !cenv lctx ret_ty s sa c sb id.
    stmt_env cenv lctx ret_ty s sa = (c, sb) /\
    (!t e. s <> AnnAssign (module_var_key (NONE, id)) t e) ==>
    c.ce_var_type (module_var_key (NONE, id)) =
    cenv.ce_var_type (module_var_key (NONE, id))
Proof
  rpt strip_tac >> drule stmt_env_declare >> strip_tac >>
  reverse (Cases_on `?x t e. s = AnnAssign x t e`)
  >- (drule_all declare_stmt_local_other >> simp[]) >>
  gvs[declare_stmt_local_def] >>
  drule declare_local_module_var_type >> simp[]
QED

(* GAP (#637 declarations): the typing declares no module key.  Declared
   names are dot-free (supported_function_bindings), which the body
   predicates do not carry yet, as for bodySimDeclCases's
   declared_name_unbound; module variables in compile-env fields of their
   own would make this unnecessary.  False for a local spelled as a module
   key. *)
Theorem declared_name_not_module_key:
  !env ret_ty s env' id x.
    type_stmt env ret_ty s = SOME env' /\
    ((?typ e. s = AnnAssign id typ e) \/
     (?typ it n body. s = For id typ it n body)) ==>
    id <> module_var_key (NONE, x)
Proof
  cheat
QED

Theorem frame_ret_ok_same_frame:
  !ctx func cx RetQ cenv c ret_ty.
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\ same_frame cenv c ==>
    frame_ret_ok ctx func cx RetQ c ret_ty
Proof
  rw[frame_ret_ok_def] >> first_x_assum irule >>
  metis_tac[same_frame_trans]
QED

Theorem type_memory_bytes_struct_fields[local]:
  !c ty c'. c'.ce_struct_fields = c.ce_struct_fields ==>
            type_memory_bytes c' ty = type_memory_bytes c ty
Proof
  recInduct type_memory_bytes_ind >> rw[type_memory_bytes_def] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[]
QED

Theorem type_memory_bytes_frame[local]:
  !c c'. c'.ce_struct_fields = c.ce_struct_fields ==>
         type_memory_bytes c' = type_memory_bytes c
Proof
  rw[FUN_EQ_THM] >> irule type_memory_bytes_struct_fields >> simp[]
QED

Theorem alloc_limits_struct_fields[local]:
  (!c e c'. c'.ce_struct_fields = c.ce_struct_fields ==>
            alloc_limits_expr c' e = alloc_limits_expr c e) /\
  (!c tgt c'. c'.ce_struct_fields = c.ce_struct_fields ==>
              alloc_limits_target c' tgt = alloc_limits_target c tgt) /\
  (!c es c'. c'.ce_struct_fields = c.ce_struct_fields ==>
             alloc_limits_exprs c' es = alloc_limits_exprs c es) /\
  (!c opt c'. c'.ce_struct_fields = c.ce_struct_fields ==>
              alloc_limits_opt c' opt = alloc_limits_opt c opt) /\
  (!c kes c'. c'.ce_struct_fields = c.ce_struct_fields ==>
              alloc_limits_named_exprs c' kes = alloc_limits_named_exprs c kes)
Proof
  ho_match_mp_tac alloc_limits_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> drule type_memory_bytes_frame >> strip_tac >>
  simp[alloc_limits_expr_def]
QED

Theorem stmt_exprs_ok_same_frame:
  !cenv c. same_frame cenv c ==> stmt_exprs_ok c = stmt_exprs_ok cenv
Proof
  rw[same_frame_def] >>
  `c.ce_struct_fields = cenv.ce_struct_fields` by
    (qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]) >>
  `alloc_limits_expr c = alloc_limits_expr cenv` by
    (rw[FUN_EQ_THM] >> irule (cj 1 alloc_limits_struct_fields) >> simp[]) >>
  simp[FUN_EQ_THM, stmt_exprs_ok_def]
QED

Theorem stmts_exprs_ok_EVERY:
  !cenv ss.
    EVERY (stmt_exprs_ok cenv) ss <=>
    ~supported_stmts_expr_exists
       (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) ss
Proof
  gen_tac >> Induct >> simp[supported_stmt_expr_exists_def, stmt_exprs_ok_def]
QED

(* ===== The source state after a statement ===== *)

(* Evaluating a statement keeps popped_keys_indexed, as
   eval_expr_popped_keys_indexed shows for an expression: stmtPoppedKeys. *)
Theorem eval_stmts_popped_keys_indexed:
  (!cx s es res es'.
     eval_stmt cx s es = (res, es') /\ popped_keys_indexed es.scopes ==>
     popped_keys_indexed es'.scopes) /\
  (!cx ss es res es'.
     eval_stmts cx ss es = (res, es') /\ popped_keys_indexed es.scopes ==>
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
    (drule (cj 1 eval_stmts_popped_keys_indexed) >> fs[expr_sim_inv_def]) >>
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

(* compile_expr leaves its block open for a supported expression of the
   frame that evaluates.  Not every expression does: the lowering's
   fallbacks end their block in INVALID.  Which fallback a module variable
   takes depends on cenv.ce_vars, so the storage and transient bindings
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

(* RESIDUAL (#637 raise/assert with a reason): a reason whose compiled
   value reason_covered does not cover.  Only a TopLevelName bound to an
   ImmutableLoc compiles to another form (LocCode, compile_expr's
   TopLevelName case).  A supported program declares no immutables
   (supported_immutables_constants_rejected), so build_compile_env binds
   none, but body_inv fixes only cenv's hashmaps and types at module keys,
   not its bindings: closing this needs a body_inv clause saying cenv
   binds no ImmutableLoc. *)
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
    ~reason_covered cenv e ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseReason e))) es res es'
Proof
  cheat
QED

(* A string literal reason (stmtSimReason), or one whose compiled value
   reason_covered covers (stmtSimReasonExpr, stmtSimReasonStorage). *)
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
  conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]
QED

(* RESIDUAL (#637 raise/assert with a reason): as body_raise_reason_other,
   after the condition fails. *)
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
    ~reason_covered cenv se ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assert e (AssertReason se))) es res es'
Proof
  cheat
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
  conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]
QED

(* GAP (#637 log): no statement lemma for Log yet.  body_inv ties
   ce_event_info to the program's events, and supported_log the
   arguments' types to the event's fields. *)
Theorem body_log_case:
  !cx id es. body_exprs_ok cx es ==> body_stmt_ok cx (Log id es)
Proof
  cheat
QED

(* GAP (#637 append): no statement lemma for Append yet; the target's
   pointer comes from compile_get_target_ptr. *)
Theorem body_append_case:
  !cx t e.
    (!s'' p t'. eval_target_place cx t s'' = (INL p,t') ==> body_expr_ok cx e) /\
    body_base_target_ok cx t ==>
    body_stmt_ok cx (Append t e)
Proof
  cheat
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

Theorem module_var_key_none_11[local]:
  !a b. module_var_key (NONE, a) = module_var_key (NONE, b) <=> a = b
Proof
  simp[module_var_key_def, nsid_to_string_def]
QED

Theorem build_hashmap_info_absent[local]:
  !tops id.
    ~MEM (NONE, id)
       (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) ==>
    build_hashmap_info tops (module_var_key (NONE, id)) = NONE
Proof
  Induct >> simp[build_hashmap_info_def] >> Cases >>
  simp[build_hashmap_info_def, toplevel_vtype_keys_toplevel_def,
       module_var_key_none_11]
QED

(* With distinct names, cenv's maps at a module variable's key are its
   declaration's. *)
Theorem build_maps_variable[local]:
  !tops vis mut id ty init.
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
    MEM (VariableDecl vis mut id ty init) tops ==>
    build_hashmap_info tops (module_var_key (NONE, id)) = NONE /\
    build_var_type_map tops (module_var_key (NONE, id)) = SOME ty
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> Cases_on `h` >>
  gvs[build_hashmap_info_def, build_var_type_map_def,
      toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND,
      module_var_key_none_11] >>
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
   cenv.ce_var_type (module_var_key (NONE, id)) =
     build_var_type_map tops (module_var_key (NONE, id))` by
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

(* RESIDUAL (#637 assignments): the other base targets.
   - A local in memory: stmtSimAssignMem's
     compile_assign_local_memory_stmt_frag asks of the local's type
     type_memory_size tyv + 64 < dimword (:256), which nothing in
     body_stmt_ok gives (Python bounds every allocation by 2 ** 64,
     codegen_venom's Context.allocate_buffer, which expr_sim_inv does not
     model for locals), as well as type_memory_bytes cenv vtyp =
     type_memory_size tyv and 0 < type_memory_size tyv.  It also asks
     expr_type e = vtyp and lowered_value_type cenv e = vtyp, where the
     typing lets e widen (type_widens_to), and an empty value assigned to a
     type with a length word (has_length_word, is_empty_value_expr) has no
     lemma.
   - A storage or transient variable that is not a word
     (supported_target_info's copies): no statement lemma.
   - Subscript and attribute targets: no statement lemma (the simulation
     of compile_get_target_ptr on eval_target_place). *)
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
    ~(?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid) ==>
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
  Cases_on `?nsid. t = TopLevelNameTarget nsid /\
                   supported_scalar_target tops nsid`
  >- (gvs[] >> rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      irule body_assign_toplevel_word >> metis_tac[]) >>
  irule body_assign_other >> metis_tac[]
QED

(* The i-th local of a tuple of word locals takes the i-th value as
   stored. *)
Theorem tuple_local_lays_out[local]:
  !cenv cx env es1 ids tys tvs vs i entry.
    expr_sim_inv cenv cx env es1 /\
    (!j. j < LENGTH ids ==>
         FLOOKUP env.var_types (EL j ids) = SOME (EL j tys)) /\
    LENGTH tys = LENGTH ids /\ EVERY is_word_type tys /\
    LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
    LIST_REL value_has_type tvs vs /\
    i < LENGTH ids /\ lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
    store_lays_out (EL i tvs) entry.type (EL i vs)
Proof
  rpt strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
   value_has_type (EL i tvs) (EL i vs) /\ is_word_type (EL i tys)` by
    gvs[LIST_REL_EL_EQN, EVERY_EL] >>
  `FLOOKUP env.var_types (EL i ids) = SOME (EL i tys)` by simp[] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  metis_tac[store_lays_out_typed]
QED

(* A tuple of word locals: stmtSimAssignTuple's
   compile_assign_tuple_locals_stmt_frag. *)
Theorem body_assign_tuple_locals[local]:
  !cx ids e tops ctx func cenv env env' ret_ty lctx RetQ es res es'.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
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
    EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\ is_word_type ty)
      ids ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      es res es'
Proof
  rpt strip_tac >>
  `EVERY (\id. ?p sz vt. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
                         cenv.ce_var_type id = SOME vt /\ is_word_type vt)
     ids` by
    (gvs[EVERY_MEM] >> rw[] >> rename1 `MEM x ids` >>
     qpat_x_assum `!x. MEM x ids ==> _` drule >> strip_tac >>
     rename1 `FLOOKUP env.var_types x = SOME ty` >>
     drule_all expr_sim_inv_local >> strip_tac >>
     `cenv.ce_var_type x = SOME ty` by fs[expr_sim_inv_def] >> simp[]) >>
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
  `EVERY is_word_type tys` by
    (rw[EVERY_EL] >> gvs[EVERY_EL] >> metis_tac[optionTheory.SOME_11]) >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >>
     qexists_tac `[]` >> simp[] >>
     metis_tac[call_evaluation_safe_append_right]) >>
  `expr_sim ctx func cenv cx (TupleT tys) e es` by
    metis_tac[body_expr_ok_def] >>
  `?tup_tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tup_tv` by
    fs[assignable_type_def, well_formed_type_def,
       optionTheory.IS_SOME_EXISTS] >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  `!v es1. (do result <- eval_expr cx e; read_result cx result od) es =
           (INL v, es1) ==> value_has_type (TupleTV tvs) v` by
    (rpt strip_tac >> drule_all expr_body_pre_eval >> strip_tac >>
     gvs[value_runtime_typed_def]) >>
  `!vs es1 i entry.
     (do result <- eval_expr cx e; read_result cx result od) es =
       (INL (ArrayV (TupleV vs)), es1) /\
     i < LENGTH ids /\ lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
     store_lays_out (EL i tvs) entry.type (EL i vs)` by
    (rpt strip_tac >> drule_all expr_body_pre_eval >> strip_tac >>
     gvs[value_runtime_typed_def, value_has_type_def,
         values_have_types_LIST_REL] >>
     drule_all tuple_local_lays_out >> simp[]) >>
  irule compile_assign_tuple_locals_stmt_frag >> simp[] >>
  qexistsl_tac [`tys`, `TupleTV tvs`] >> simp[]
QED

(* RESIDUAL (#637 tuple assignments): the other tuple targets.
   - Locals in memory: stmtSimAssignTupleMem's
     compile_assign_tuple_locals_memory_stmt_frag asks cenv.ce_target
     CapMcopy, which body_inv does not fix,
     type_memory_size (TupleTV tvs) < dimword (:256) and, for each
     memory local, 0 < type_memory_size vtv and
     type_memory_size vtv + 64 < dimword (:256), which nothing in
     body_stmt_ok gives (as for Assign).
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
            EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                             is_word_type ty) ids) ==>
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
                  EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                                   is_word_type ty) ids`
  >- (gvs[] >> irule body_assign_tuple_locals >> metis_tac[]) >>
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
   well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn` by
    (gvs[type_stmt_def, well_typed_target_def, well_typed_expr_def,
         AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_types id` >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >>
     Cases_on `asg` >> gvs[]) >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `body_expr_ok cx e` by
    (first_x_assum irule >> metis_tac[eval_target_place_local]) >>
  `expr_sim_case F ctx func cenv cx e` by metis_tac[body_expr_ok_case] >>
  irule compile_augassign_local_case >> simp[] >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `F` >> simp[]
QED

(* RESIDUAL (#637 augmented assignment): the targets other than a local.
   Storage, subscript and attribute targets have no statement lemma. *)
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
    ~(?id. t = NameTarget id) ==>
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
  simp[stmts_exprs_ok_EVERY] >>
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
  `body_inv tops ctx c cx` by
    metis_tac[body_inv_same_frame, stmt_env_module_var_type,
              declared_name_not_module_key] >>
  `frame_ret_ok ctx func cx RetQ c ret_ty` by
    metis_tac[frame_ret_ok_same_frame] >>
  qpat_x_assum `!s'' t. _ ==> body_stmts_ok _ _` drule >>
  simp[body_stmts_ok_def] >> disch_then irule >>
  metis_tac[call_evaluation_safe_append_right]
QED
