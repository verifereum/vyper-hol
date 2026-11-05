(*
 * Body simulation: Assign to any place, from the body case's hypotheses
 *
 * body_assign_other's hypotheses (the body induction's judgments for e and
 * the target's indices, body_inv, the statement's support and typing) give
 * the premises of stmtSimAssignPlace's roots: the target's typing and
 * widening from type_stmt, target_case from body_base_target_ok, the
 * indices' expr_body_pre from the statement's support, and e's
 * expr_vv_sim from body_expr_ok.  An immutable target is one the
 * constructor writes (immutable_deploy_assign_case); at run time it has
 * no place.
 *
 * TOP-LEVEL:
 *   body_assign_place_case — t = e, when e's lowered value has e's type
 *     (or a bytestring type it fits)
 *)

Theory bodyAssignPlace
Ancestors
  stmtSimAssignPlace bodySim exprSimHypsDefs stmtSimDefs
  targetPlaceSim targetPlaceSimCases supportedStmts supportedTargets
  supportedStmtTraverse supportedExprTraverse supportedProgram bodyExprPreFacts gasContext bodyStorageCases
  vyperTypeInvariants vyperTypeCallStackSoundness vyperTypeCallGraph vyperCompiler
  stmtLowering exprLowering compileEnv compileVyper
  vyperInterpreter vyperState vyperTypeSystem

(* Intuition (a statement check's derivation; ignore if unhelpful):
   - typing: type_stmt_def's Assign case with atarget_accepts_def on
     BaseTarget gives type_place_target env t = SOME (Type dty), the
     widening and assignable_type.
   - target_case: an induction on t gives body_base_target_ok cx t /\
     body_inv ==> target_idx_case F ctx func cenv cx t (body_expr_ok with
     body_inv is expr_sim_case F / expr_vv_case F), then target_case_all.
   - immutable_root: the only supported immutable target is a bare
     TopLevelNameTarget (NONE,n) with supported_immutable_type; every other
     supported root has a storage/transient or hashmap declaration.  At run
     time bare_global_assignable is empty (env_context_consistent in
     expr_sim_inv), so type_place_target is NONE; in deploy it gives the
     immutable's type, for immutable_deploy_assign_case.
   - target_indices_pre and e's expr_body_pre: stmt_expr_body_pre (as
     body_assign_tuple_rhs_pre does it), with int_calls_stmt of Assign =
     int_calls_target t ++ int_calls_expr e, stmt_exprs_ok's
     supported_target_exists for the keys, and the ABI coverage premise
     with cx_tops_module.
   - CapMcopy: bodySimStmtCases' [local] body_inv_mcopy's proof;
     acyclic_struct_metadata: body_inv_def. *)
Theorem assign_place_typing[local]:
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

Theorem body_inv_mcopy[local]:
  !tops ctx cenv cx. body_inv tops ctx cenv cx ==> cenv.ce_target CapMcopy
Proof
  rw[body_inv_def] >> Cases_on `cx.in_deploy` >> gvs[]
  >- (gvs[lower_vyper_deploy_unit_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[vyperCompilerTheory.run_deploy_lowering_def, AllCaseEqs(),
          vyperCompilerTheory.lowering_policy_ok_def]) >>
  gvs[lower_vyper_runtime_unit_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[vyperCompilerTheory.run_lowering_def, AllCaseEqs(),
      vyperCompilerTheory.lowering_policy_ok_def]
QED

Theorem base_assignment_target_induct[local]:
  !P. (!id. P (NameTarget id)) /\ (!nsid. P (TopLevelNameTarget nsid)) /\
      (!bt e. P bt ==> P (SubscriptTarget bt e)) /\
      (!bt s. P bt ==> P (AttributeTarget bt s)) ==> !bt. P bt
Proof
  rpt strip_tac >>
  `(!e:expr. T) /\ !bt. P bt` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >> simp[]
QED

Theorem body_target_idx_case[local]:
  !t tops ctx func cenv cx.
    body_inv tops ctx cenv cx /\ body_base_target_ok cx t ==>
    target_idx_case F ctx func cenv cx t
Proof
  Induct using base_assignment_target_induct >>
  simp[body_base_target_ok_def, target_idx_case_def] >> rpt strip_tac >>
  gvs[expr_sim_case_def, expr_vv_case_def, body_expr_ok_def] >> metis_tac[]
QED

Theorem body_target_case[local]:
  !tops ctx func cenv cx t.
    body_inv tops ctx cenv cx /\ body_base_target_ok cx t ==>
    target_case F ctx func cenv cx t
Proof
  metis_tac[body_target_idx_case, target_case_all]
QED

Theorem body_assign_place_rhs_pre[local]:
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
  `well_typed_expr env e` by metis_tac[assign_place_typing] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env tops) target))` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def, int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Theorem target_indices_body_pre[local]:
  !t cenv cx env pt.
    type_place_target env t = SOME pt /\
    ~supported_target_exists
      (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) t /\
    call_evaluation_safe cx (int_calls_target t) /\
    ~supported_target_exists expr_evm_run_root t /\
    EVERY (\c. FST c = NONE) (int_calls_target t) /\
    (?tops. supported_program tops /\ get_module_code cx NONE = SOME tops) /\
    (!target. supported_target_exists (expr_abi_decode_target_root target) t ==>
       occurs_abi_decode_target target (cx_tops cx)) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)) ==>
    target_indices_pre cenv cx env t
Proof
  Induct using base_assignment_target_induct >>
  simp[target_indices_pre_def, supported_expr_exists_def, int_calls_expr_def,
       listTheory.EVERY_APPEND] >> rpt strip_tac >>
  gvs[Once well_typed_expr_def, AllCaseEqs()]
  >- metis_tac[call_evaluation_safe_append_left] >>
  irule stmt_expr_body_pre >> simp[expr_has_evm_run_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Theorem body_assign_place_indices_pre[local]:
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
    metis_tac[assign_place_typing] >>
  `supported_assignment tops bindings (BaseTarget t) e` by
    gvs[supported_stmt_def] >>
  drule_then strip_assume_tac supported_assignment_storage_syntax >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env tops) target))` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  irule target_indices_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, int_calls_stmt_def, int_calls_atarget_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem body_assign_place_case:
  !cx t e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ok cx t) /\
    body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
                (Assign (BaseTarget t) e) ==>
              occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  cheat
QED
