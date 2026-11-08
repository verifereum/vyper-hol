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
  targetPlaceSim targetPlaceSimCases supportedStmts supportedTargets supportedDecls supportedExprForms
  supportedStmtTraverse supportedExprTraverse supportedProgram bodyExprPreFacts gasContext bodyStorageCases bodyStorageMetadata
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
       listTheory.EVERY_APPEND] >> rpt strip_tac >>
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
  `supported_target tops bindings t \/
   IS_SOME (supported_target_info tops bindings t)` by
    (fs[supported_assignment_def] >>
     Cases_on `supported_target_info tops bindings t` >> fs[]) >>
  irule (Q.SPECL [`tops`, `bindings`] target_indices_body_pre) >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, int_calls_stmt_def, int_calls_atarget_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem supported_decl_storage_exists[local]:
  !tops src id.
    ((?vis mut ty slot.
       supported_variable_decl tops (src,id) = SOME (vis,mut,ty,slot) /\
       (mut = Storage \/ mut = Transient)) \/
     IS_SOME (supported_hashmap_decl tops (src,id))) ==>
    src = NONE /\ IS_SOME (find_var_decl_by_name id tops)
Proof
  Induct >> simp[supported_variable_decl_def, supported_hashmap_decl_def] >>
  gen_tac >> Cases_on `h` >> rpt gen_tac >> Cases_on `src` >>
  gvs[supported_variable_decl_def, supported_hashmap_decl_def,
      find_var_decl_by_name_def] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`NONE`, `id`] mp_tac) >>
  simp[] >> Cases_on `s = id` >> gvs[] >>
  Cases_on `v0 = Storage \/ v0 = Transient` >> gvs[] >> metis_tac[]
QED

Theorem supported_place_root_decl[local]:
  !tops src id. supported_place_root tops (src,id) ==>
    src = NONE /\ IS_SOME (find_var_decl_by_name id tops)
Proof
  rpt gen_tac >> simp[supported_place_root_def] >> strip_tac >>
  irule supported_decl_storage_exists >>
  Cases_on `supported_variable_decl tops (src,id)`
  >- (gvs[] >> Cases_on `supported_hashmap_decl tops (src,id)` >> gvs[]) >>
  rename1 `_ = SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >>
  gvs[] >> metis_tac[]
QED

Theorem supported_target_info_root[local]:
  !t tops bindings.
    IS_SOME (supported_target_info tops bindings t) ==>
    (?id. target_root t = NameTarget id) \/
    (?nsid. target_root t = TopLevelNameTarget nsid /\ supported_place_root tops nsid)
Proof
  Induct using base_assignment_target_induct >>
  simp[supported_target_info_def, target_root_def, optionTheory.IS_SOME_EXISTS] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[optionTheory.IS_SOME_EXISTS]
QED

Theorem supported_legacy_root_decl[local]:
  !tops src id field.
    (supported_scalar_target tops (src,id) \/
     supported_subscript_base tops (src,id) \/
     supported_storage_field_write tops (src,id) field) ==>
    src = NONE /\ IS_SOME (find_var_decl_by_name id tops)
Proof
  rpt gen_tac >> disch_tac >> irule supported_decl_storage_exists >>
  qpat_x_assum `_ \/ _` mp_tac >>
  simp[supported_scalar_target_def, supported_subscript_base_def,
       supported_storage_array_def, supported_storage_field_write_def,
       supported_storage_fields_def] >>
  Cases_on `supported_variable_decl tops (src,id)`
  >- (simp[] >> Cases_on `supported_hashmap_decl tops (src,id)` >> simp[]) >>
  rename1 `_ = SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >>
  simp[] >> Cases_on `decl2` >> simp[] >>
  Cases_on `supported_hashmap_decl tops (src,id)` >> simp[]
QED

Theorem supported_legacy_target_root[local]:
  !t tops bindings.
    supported_target tops bindings t ==>
    (?id. target_root t = NameTarget id) \/
    (?src id. target_root t = TopLevelNameTarget (src,id) /\
      src = NONE /\ IS_SOME (find_var_decl_by_name id tops)) \/
    (?nsid. t = TopLevelNameTarget nsid /\ IS_SOME (supported_immutable_type tops nsid))
Proof
  Cases >> simp[supported_target_def, target_root_def] >> rpt strip_tac
  >- (PairCases_on `p` >>
      metis_tac[supported_legacy_root_decl])
  >- simp[] >>
  Cases_on `b` >> gvs[target_root_def] >>
  PairCases_on `p` >>
  metis_tac[supported_legacy_root_decl]
QED

Theorem body_assign_immutable_target[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  immutable_root cx t ==>
  ?nsid. t = TopLevelNameTarget nsid /\
         IS_SOME (supported_immutable_type tops nsid)
Proof
  rpt strip_tac >>
  `get_module_code cx NONE = SOME tops` by gvs[body_inv_def] >>
  gvs[supported_stmt_def, supported_assignment_def]
  >- (drule_then strip_assume_tac supported_legacy_target_root >>
      gvs[immutable_root_def] >>
      metis_tac[optionTheory.NOT_IS_SOME_EQ_NONE]) >>
  `IS_SOME (supported_target_info tops bindings t)` by
    (Cases_on `supported_target_info tops bindings t` >> gvs[AllCaseEqs()]) >>
  drule_then strip_assume_tac supported_target_info_root
  >- gvs[immutable_root_def] >>
  rename1 `supported_place_root tops nsid` >> PairCases_on `nsid` >>
  drule_then strip_assume_tac supported_place_root_decl >>
  fs[immutable_root_def] >> metis_tac[optionTheory.NOT_IS_SOME_EQ_NONE]
QED

Theorem body_immutable_target_type[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_immutable_type tops nsid = SOME ity /\
  type_place_target env (TopLevelNameTarget nsid) = SOME (Type dty) ==>
  cx.in_deploy /\ dty = ity
Proof
  PairCases_on `nsid` >> strip_tac >>
  qpat_x_assum `supported_immutable_type _ _ = _` mp_tac >>
  simp[supported_immutable_type_def] >>
  Cases_on `supported_variable_decl tops (nsid0,nsid1)` >> simp[] >>
  rename1 `_ = SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >>
  simp[] >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac supported_variable_decl_mem >> gvs[] >>
  rename1 `supported_value_type tops ity` >>
  `get_module_code cx NONE = SOME tops /\
   bare_globals_complete env.bare_globals cx /\
   bare_global_assignable_complete env.bare_global_assignable cx` by
    fs[body_inv_def, expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `FLOOKUP env.bare_globals (NONE,nsid1) = SOME ity` by
    metis_tac[bare_globals_complete_def] >>
  fs[Once well_typed_expr_def] >>
  Cases_on `cx.in_deploy`
  >- ( `FLOOKUP env.bare_global_assignable (NONE,nsid1) = SOME ity` by
         metis_tac[bare_global_assignable_complete_def] >> fs[]) >>
  fs[bare_global_assignable_complete_def]
QED

Theorem body_assign_place_case:
  !cx t e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_ok cx t) /\
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
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac assign_place_typing >>
  `expr_body_pre cenv cx env e es` by metis_tac[body_assign_place_rhs_pre] >>
  `target_indices_pre cenv cx env t` by metis_tac[body_assign_place_indices_pre] >>
  `expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_ok_def] >>
  Cases_on `immutable_root cx t`
  >- (drule_all_then strip_assume_tac body_assign_immutable_target >> gvs[] >>
      rename1 `supported_immutable_type tops nsid` >>
      Cases_on `supported_immutable_type tops nsid` >> gvs[] >>
      drule_all_then strip_assume_tac body_immutable_target_type >> gvs[] >>
      metis_tac[immutable_deploy_assign_case]) >>
  `((?s pv s1 sread v s2. eval_expr cx e s = (INL pv,s1) /\
                           read_result cx pv sread = (INL v,s2)) ==>
      target_case F ctx func cenv cx t)` by metis_tac[body_target_case] >>
  `cenv.ce_target CapMcopy /\
   acyclic_struct_metadata cenv.ce_struct_fields` by
    metis_tac[body_inv_mcopy, body_inv_def] >>
  Cases_on `supported_target_pure tops t`
  >- metis_tac[compile_assign_place_case] >>
  metis_tac[assign_place_effectful_index_case]
QED
