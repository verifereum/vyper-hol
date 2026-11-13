(* Static premises shared by residual pointer assignment composition. *)
Theory bodyPtrAssignStatic
Ancestors
  bodySim exprSimHypsDefs stmtSimDefs targetPlaceSim targetPlaceSimCasesBase
  supportedStmts supportedTargets supportedDecls supportedExprForms
  supportedStmtTraverse supportedExprTraverse supportedProgram bodyExprPreFacts gasContext bodyStorageCases
  vyperTypeInvariants vyperTypeCallStackSoundness vyperTypeCallGraph
  stmtLowering exprLowering compileEnv vyperInterpreter vyperState vyperTypeSystem

Theorem body_assign_static_typing:
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' ==>
  well_typed_expr env e /\
  ?dty. type_place_target env t = SOME (Type dty) /\
        type_widens_to env.type_defs (expr_type e) dty /\
        assignable_type env.type_defs (expr_type e)
Proof
  simp[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
  rpt strip_tac >> Cases_on `type_place_target env t` >> gvs[] >>
  rename1 `SOME pt` >> Cases_on `pt` >> gvs[]
QED

Theorem body_assign_static_alloc:
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) ==> assign_alloc_ok cenv t e
Proof
  fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def]
QED

Theorem body_assign_static_rhs_pre:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (BaseTarget t) e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) ==>
  expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e` by metis_tac[body_assign_static_typing] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env tops) target))` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def, int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Theorem supported_subscript_target_shape[local]:
  !tops bindings t k.
    supported_target tops bindings (SubscriptTarget t k) \/
    IS_SOME (supported_target_info tops bindings (SubscriptTarget t k)) ==>
    supported_expr tops k /\
    ((?id. t = TopLevelNameTarget id) \/
     IS_SOME (supported_target_info tops bindings t))
Proof
  rpt gen_tac >> Cases_on `t` >> strip_tac >>
  gvs[supported_target_def, supported_target_info_def, AllCaseEqs(),
      optionTheory.IS_SOME_EXISTS]
QED

Theorem supported_attribute_target_shape[local]:
  !tops bindings t f.
    supported_target tops bindings (AttributeTarget t f) \/
    IS_SOME (supported_target_info tops bindings (AttributeTarget t f)) ==>
    (?id. t = TopLevelNameTarget id) \/
    IS_SOME (supported_target_info tops bindings t)
Proof
  rpt gen_tac >> Cases_on `t` >> strip_tac >>
  gvs[supported_target_def, supported_target_info_def, AllCaseEqs(),
      optionTheory.IS_SOME_EXISTS]
QED

Theorem target_indices_body_pre[local]:
  !tops bindings t cenv cx env pt.
    type_place_target env t = SOME pt /\
    (supported_target tops bindings t \/
     IS_SOME (supported_target_info tops bindings t)) /\
    alloc_limits_target cenv t /\
    ~supported_target_exists
      (\e. ~is_extcode e /\
           ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) t /\
    call_evaluation_safe cx (int_calls_target t) /\
    ~supported_target_exists expr_evm_run_root t /\
    EVERY (\c. FST c = NONE) (int_calls_target t) /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    (!target. supported_target_exists (expr_abi_decode_target_root target) t ==>
       occurs_abi_decode_target target (cx_tops cx)) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)) ==>
    target_indices_pre cenv cx env t
Proof
  ntac 2 gen_tac >>
  Induct using base_assignment_target_induct >>
  simp[target_indices_pre_def, supported_expr_exists_def, int_calls_expr_def,
       allocLimitsTheory.alloc_limits_expr_def, listTheory.EVERY_APPEND] >> rpt strip_tac >>
  imp_res_tac supported_subscript_target_shape >>
  imp_res_tac supported_attribute_target_shape >>
  imp_res_tac supported_expr_body_calls >>
  gvs[Once well_typed_expr_def, AllCaseEqs()]
  >>~- ([`expr_body_pre _ _ _ _ _`],
        irule stmt_expr_body_pre >> simp[expr_has_evm_run_def] >>
        rpt conj_tac >>
        TRY (strip_tac >> qexists_tac `tops` >> simp[] >> NO_TAC) >>
        qexists_tac `[]` >> simp[] >>
        metis_tac[call_evaluation_safe_append_right]) >>
  metis_tac[call_evaluation_safe_append_left, target_indices_pre_def]
QED

Theorem body_assign_static_indices_pre:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (BaseTarget t) e) ==> occurs_abi_decode_target target tops) /\
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) ==>
  target_indices_pre cenv cx env t
Proof
  rpt strip_tac >>
  `?dty. type_place_target env t = SOME (Type dty)` by
    metis_tac[body_assign_static_typing] >>
  `supported_assignment tops bindings (BaseTarget t) e` by
    gvs[supported_stmt_def] >>
  drule_then strip_assume_tac supported_assignment_storage_syntax >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env tops) target))` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  `supported_target tops bindings t \/
   IS_SOME (supported_target_info tops bindings t)` by
    (fs[supported_assignment_def] >>
     Cases_on `supported_target_info tops bindings t` >> fs[]) >>
  `EVERY (\c. FST c = NONE) (int_calls_target t)` by
    (irule listTheory.EVERY_MONOTONIC >>
     qexists_tac `\c. FST c = NONE /\
       IS_SOME (supported_function_decl tops c Internal)` >>
     fs[int_calls_atarget_def]) >>
  irule (Q.SPECL [`tops`, `bindings`] target_indices_body_pre) >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
      allocLimitsTheory.alloc_limits_stmt_def, allocLimitsTheory.alloc_limits_assignment_def,
      supported_assignment_exists_def, int_calls_stmt_def, int_calls_atarget_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED
