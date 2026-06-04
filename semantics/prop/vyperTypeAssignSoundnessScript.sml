(*
 * Fresh assignment-target soundness helpers for the executable type system.
 *)

Theory vyperTypeAssignSoundness
Ancestors
  list rich_list finite_map option pair arithmetic
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeExprSoundness vyperTypeStatePreservation
  vyperTypeBuiltins vyperExprNoControl
Libs
  wordsLib markerLib

(* ===== Error-shape lemmas ===== *)

Theorem lift_sum_error:
  lift_sum x y = (INR e, s) ==> (?m. e = Error m)
Proof
  rw[lift_sum_def, CaseEq"sum", sum_CASE_rator, return_def, raise_def]
QED

Theorem lift_option_type_error:
  lift_option_type x z y = (INR e, s) ==> e = Error (TypeError z)
Proof
  rw[lift_option_type_def, CaseEq"option", option_CASE_rator, return_def, raise_def]
QED

Theorem assign_result_error:
  assign_result a b c d e = (INR x, y) ==> (?m. x = Error m)
Proof
  Cases_on `b` >> rw[assign_result_def, return_def, bind_apply] >>
  gvs[CaseEq"prod", CaseEq"sum"] >>
  TRY(drule lift_sum_error >> rw[])
QED

Theorem get_immutables_error:
  get_immutables x y z = (INR e, s) ==> (?m. e = Error (RuntimeError m))
Proof
  rw[get_immutables_def, bind_apply, AllCaseEqs(), return_def,
     get_address_immutables_def] >>
  drule lift_option_error >> rw[]
QED

Theorem set_storage_backend_no_error[simp]:
  set_storage_backend a b c st <> (INR e, f)
Proof
  Cases_on `b` >> rw[set_storage_backend_def] >>
  gvs[update_transient_def, return_def] >>
  gvs[bind_apply, AllCaseEqs(), get_accounts_def, return_def] >>
  gvs[update_accounts_def, return_def]
QED

(* TEMPORARILY CHEATED - moved into fresh assignment helper theory; the direct
   proof is routine but currently needs a small proof-control cleanup around
   write_storage_slot/get_storage_backend case splitting.
Proof attempt preserved:
Proof
  rw[write_storage_slot_def, bind_apply, AllCaseEqs()] >> gvs[]
  >- (Cases_on `encode_value d e` >> gvs[lift_option_def, return_def, raise_def]) >>
  Cases_on `b` >> gvs[get_storage_backend_def, get_accounts_def,
    get_transient_storage_def, return_def]
QED
*)
Theorem write_storage_slot_error:
  write_storage_slot a b c d e f = (INR g, h) ==> ?m. g = Error m
Proof
  rw[write_storage_slot_def, bind_apply, AllCaseEqs(), lift_option_def,
     return_def, raise_def] >> gvs[]
  >- (Cases_on `encode_value d e` >> gvs[return_def, raise_def]) >>
  Cases_on `b` >> gvs[get_storage_backend_def, get_accounts_def,
    get_transient_storage_def, bind_def, return_def]
QED

Theorem lookup_global_error:
  lookup_global a b c d = (INR e, f) ==> (?m. e = Error m)
Proof
  rw[lookup_global_def, bind_apply, AllCaseEqs(), option_CASE_rator,
     raise_def, return_def] >>
  TRY(drule lift_option_type_error >> rw[]) >>
  TRY(drule get_immutables_error >> rw[]) >>
  gvs[var_decl_info_CASE_rator, prod_CASE_rator, AllCaseEqs(),
      bind_apply, return_def] >>
  TRY(drule lift_option_type_error >> rw[]) >>
  gvs[type_value_CASE_rator, AllCaseEqs(), bind_apply, return_def] >>
  drule read_storage_slot_error >> rw[]
QED

Theorem set_global_error:
  set_global a b c d e = (INR x, y) ==> ?t. x = Error t
Proof
  rw[set_global_def, bind_apply, AllCaseEqs()] >>
  TRY(drule lift_option_type_error >> rw[]) >>
  gvs[option_CASE_rator, AllCaseEqs(), raise_def] >>
  gvs[var_decl_info_CASE_rator, AllCaseEqs(), prod_CASE_rator, raise_def] >>
  gvs[bind_apply, AllCaseEqs()] >>
  TRY(drule lift_option_type_error >> rw[]) >>
  drule write_storage_slot_error >> rw[]
QED

Theorem resolve_array_element_error:
  !a b c d e f g h. resolve_array_element a b c d e f = (INR g, h) ==> ?m. g = Error m
Proof
  ho_match_mp_tac resolve_array_element_ind >>
  rw[resolve_array_element_def, bind_apply, ignore_bind_apply, check_def,
     assert_def, return_def, raise_def, AllCaseEqs(), bound_CASE_rator] >>
  gvs[] >- (
    first_x_assum irule >>
    qexists_tac`0` >> simp[] >>
    goal_assum drule
  )
  >- (
    first_x_assum irule >>
    qexists_tac`1` >> simp[] >>
    goal_assum drule
  ) >>
  gvs[oneline get_storage_backend_def, COND_RATOR, AllCaseEqs(),
      bind_apply, return_def, get_transient_storage_def,
      get_accounts_def]
QED

(* ===== Assignment target never raises control exceptions ===== *)

Theorem get_scopes_result:
  !st r st'. get_scopes st = (r, st') ==> r = INL st.scopes /\ st' = st
Proof
  simp[get_scopes_def, return_def]
QED

Theorem assign_target_no_return:
  (!cx tgt ao st res st'.
    assign_target cx tgt ao st = (res, st') ==>
    !v. res <> INR (ReturnException v)) /\
  (!cx tgts vs st res st'.
    assign_targets cx tgts vs st = (res, st') ==>
    !v. res <> INR (ReturnException v))
Proof
  conj_tac
  >- (rpt gen_tac >> strip_tac >> gen_tac >>
      Cases_on `res` >> simp[] >>
      drule (cj 1 assign_target_no_control) >>
      rw[no_control_exc_def]) >>
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `res` >> simp[] >>
  drule (cj 2 assign_target_no_control) >>
  rw[no_control_exc_def]
QED

(* ===== Dynamic assignability side condition ===== *)

(* assign_target_assignable moved to vyperTypeStatePreservationScript.sml. *)

Theorem lookup_scopes_find_containing_scope:
  !scopes id entry.
    lookup_scopes id scopes = SOME entry ==>
    ?pre env rest.
      find_containing_scope id scopes = SOME (pre, env, entry, rest)
Proof
  Induct >> simp[lookup_scopes_def, find_containing_scope_def] >>
  rpt gen_tac >> Cases_on `FLOOKUP h id` >> gvs[] >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `h::pre` >> qexists_tac `env` >> qexists_tac `rest` >>
  simp[]
QED

Theorem well_typed_target_NameTarget_assignable:
  !env cx st id ty.
    well_typed_target env (NameTarget id) ty /\
    env_consistent env cx st ==>
    assign_target_assignable (BaseTargetV (ScopedVar id) []) st
Proof
  rw[well_typed_target_def, assign_target_assignable_def] >>
  gvs[well_typed_expr_def, AllCaseEqs(), LET_THM] >>
  fs[env_consistent_def, env_scopes_consistent_def] >>
  first_x_assum drule >> strip_tac >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  rpt (goal_assum drule) >> simp[]
QED

(* Static root lemma: if a dynamically evaluated base target returns a scoped
   variable, and the target has any static place type, then that root variable is
   statically assignable.  This deliberately separates semantic root recovery
   from the runtime state in which assignment will later happen. *)
Theorem eval_base_target_scoped_root_assignable:
  !bt cx st0 s sbs st1 env vt.
    eval_base_target cx bt st0 = (INL (ScopedVar s, sbs), st1) /\
    type_place_target env bt = SOME vt ==>
    ?ty. FLOOKUP env.var_types (string_to_num s) = SOME ty /\
         FLOOKUP env.var_assignable (string_to_num s) = SOME T
Proof
  Induct >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, return_def, raise_def, bind_apply,
      type_check_def, assert_def, lift_option_type_def]
  >- (
    qpat_x_assum `(case get_scopes _ of _ => _) = _` mp_tac >>
    Cases_on `get_scopes st0` >> Cases_on `q` >>
    simp[bind_apply, return_def, raise_def, type_check_def, assert_def] >>
    Cases_on `IS_SOME (lookup_scopes (string_to_num s) x)` >> gvs[] >>
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_apply, ignore_bind_apply, return_def, raise_def,
         type_check_def, assert_def, LET_THM] >>
    gvs[bind_apply, ignore_bind_apply, return_def, raise_def,
        type_check_def, assert_def, LET_THM] >>
    strip_tac >> gvs[] >> strip_tac >>
    pop_assum mp_tac >>
    simp_tac(srw_ss())[Once well_typed_expr_def] >> rw[AllCaseEqs()] >>
    goal_assum drule >> simp[])
  >- (
    qpat_x_assum `(case get_immutables _ _ _ of _ => _ | _ => _) = _` mp_tac >>
    Cases_on `get_immutables cx (current_module cx) st0` >> Cases_on `q` >>
    gvs[return_def, raise_def, bind_apply, type_check_def, assert_def,
        lift_option_type_def, AllCaseEqs(), option_CASE_rator,
        ignore_bind_apply])
  >- (
    rename1`TopLevelNameTarget p` >>
    Cases_on`p` >> gvs[evaluate_def,return_def] )
  >- (
    gvs[bind_apply,AllCaseEqs(),bind_def] >>
    pairarg_tac >>
    gvs[bind_apply,AllCaseEqs(),option_CASE_rator,return_def,raise_def] >>
    first_x_assum drule >> simp[] >>
    gvs[well_typed_expr_def,AllCaseEqs()]
  ) >>
    gvs[bind_def,AllCaseEqs()] >>
    pairarg_tac >> gvs[return_def] >>
    first_x_assum drule >>
    gvs[well_typed_expr_def,AllCaseEqs()]
QED

Theorem eval_base_target_scoped_assignable_place:
  !bt cx st0 s sbs st1 env vt st.
    eval_base_target cx bt st0 = (INL (ScopedVar s, sbs), st1) /\
    type_place_target env bt = SOME vt /\
    env_consistent env cx st ==>
    assign_target_assignable (BaseTargetV (ScopedVar s) sbs) st
Proof
  rw[assign_target_assignable_def, env_consistent_def, env_scopes_consistent_def] >>
  drule_all eval_base_target_scoped_root_assignable >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  rpt (goal_assum drule) >> simp[]
QED

Theorem eval_base_target_scoped_assignable:
  !bt cx st0 s sbs st1 env ty st.
    eval_base_target cx bt st0 = (INL (ScopedVar s, sbs), st1) /\
    well_typed_target env bt ty /\
    env_consistent env cx st ==>
    assign_target_assignable (BaseTargetV (ScopedVar s) sbs) st
Proof
  rw[well_typed_target_def] >>
  drule_all eval_base_target_scoped_assignable_place >> simp[]
QED

Theorem eval_target_assignable_base:
  !g cx s sbs st0 st1 env ty st.
    eval_target cx g st0 = (INL (BaseTargetV (ScopedVar s) sbs), st1) /\
    well_typed_atarget env g ty /\
    env_consistent env cx st ==>
    assign_target_assignable (BaseTargetV (ScopedVar s) sbs) st
Proof
  Cases >> gvs[Once evaluate_def, well_typed_atarget_def] >>
  rpt strip_tac >>
  qpat_x_assum `do _ od _ = _` mp_tac >>
  simp[bind_def, UNCURRY, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `x` >> gvs[] >>
  metis_tac[eval_base_target_scoped_assignable]
QED

Theorem eval_target_assignable:
  !g cx tgt st0 st1 env ty st.
    eval_target cx g st0 = (INL tgt, st1) /\
    well_typed_atarget env g ty /\
    env_consistent env cx st ==>
    assign_target_assignable tgt st
Proof
  completeInduct_on `assignment_target_size g` >> rpt strip_tac >>
  Cases_on `g` >> gvs[Once evaluate_def, well_typed_atarget_def]
  >- (qpat_x_assum `do _ od _ = _` mp_tac >>
      simp[bind_def, UNCURRY, AllCaseEqs(), return_def, raise_def] >>
      rpt strip_tac >> gvs[] >> Cases_on `x` >> gvs[] >>
      Cases_on `q` >> gvs[assign_target_assignable_def] >>
      drule_all eval_base_target_scoped_assignable >>
      simp[assign_target_assignable_def]) >>
  qpat_x_assum `do _ od _ = _` mp_tac >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[assign_target_assignable_def] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  qpat_x_assum `eval_targets _ _ _ = _` mp_tac >>
  qid_spec_tac `tys` >> qid_spec_tac `gvs` >> qid_spec_tac `st1` >> qid_spec_tac `st0` >>
  Induct_on `l` >> gvs[Once evaluate_def, return_def] >>
  rpt strip_tac >> Cases_on `tys` >> gvs[] >>
  gvs[bind_apply, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  `assign_target_assignable gv st` by (
    qpat_x_assum `!m. m < assignment_target_size h + _ ==> _`
      (qspec_then `assignment_target_size h` mp_tac) >>
    simp[] >> metis_tac[]) >>
  simp[] >>
  qpat_x_assum `(∀m. m < list_size assignment_target_size l + 1 ==> _) ==> _` mp_tac >>
  impl_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!m. m < assignment_target_size h + _ ==> _`
        (qspec_then `m` mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      first_x_assum (qspec_then `g` mp_tac) >>
      simp[] >> strip_tac >> metis_tac[]) >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem assign_target_no_type_error:
  !cx gv op st res st' env tgt ty.
    assign_target cx gv op st = (res, st') ==>
    runtime_consistent env cx st ==>
    target_runtime_typed env cx st tgt ty gv ==>
    assignable_type env.type_defs ty ==>
    assign_operation_runtime_typed env ty op ==>
    assign_operation_matches_target_shape gv op ==>
    assign_target_assignable_context cx gv st ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  imp_res_tac (cj 1 assign_target_sound_mutual) >> gvs[]
QED

Theorem assign_targets_no_type_error:
  !cx gvs vs st res st' env tgts.
    assign_targets cx gvs vs st = (res, st') ==>
    runtime_consistent env cx st ==>
    target_assignment_values_assignable env cx st tgts gvs vs ==>
    EVERY (λgv. assign_target_assignable_context cx gv st) gvs ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  imp_res_tac (cj 2 assign_target_sound_mutual) >> gvs[]
QED
Theorem assign_target_update_no_type_error:
  !cx gv st res st' env tgt ty bop rhs_ty v.
    assign_target cx gv (Update ty bop v) st = (res, st') ==>
    runtime_consistent env cx st ==>
    target_runtime_typed env cx st tgt ty gv ==>
    assignable_type env.type_defs ty ==>
    well_typed_binop ty bop ty rhs_ty ==>
    value_runtime_typed env rhs_ty v ==>
    assign_operation_matches_target_shape gv (Update ty bop v) ==>
    assign_target_assignable_context cx gv st ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  `assign_operation_runtime_typed env ty (Update ty bop v)` by (
    simp[assign_operation_runtime_typed_def] >>
    qexists_tac `rhs_ty` >> simp[]) >>
  imp_res_tac (cj 1 assign_target_sound_mutual) >> gvs[]
QED

Theorem assign_target_append_no_type_error:
  !cx gv st res st' env tgt elem_ty elem_tv n v.
    assign_target cx gv (AppendOp v) st = (res, st') ==>
    runtime_consistent env cx st ==>
    target_runtime_typed env cx st tgt (ArrayT elem_ty (Dynamic n)) gv ==>
    assignable_type env.type_defs (ArrayT elem_ty (Dynamic n)) ==>
    evaluate_type env.type_defs elem_ty = SOME elem_tv ==>
    value_has_type elem_tv v ==>
    assign_operation_matches_target_shape gv (AppendOp v) ==>
    assign_target_assignable_context cx gv st ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  `assign_operation_runtime_typed env (ArrayT elem_ty (Dynamic n)) (AppendOp v)` by (
    simp[assign_operation_runtime_typed_def] >>
    qexists_tac `elem_tv` >>
    simp[] >> qexists_tac `elem_ty` >> qexists_tac `n` >> simp[]) >>
  imp_res_tac (cj 1 assign_target_sound_mutual) >> gvs[]
QED


(* ===== Side-condition lemmas for statement assignment branches ===== *)

Theorem assign_operation_matches_target_shape_BaseTargetV:
  !loc sbs op. assign_operation_matches_target_shape (BaseTargetV loc sbs) op
Proof
  rw[assign_operation_matches_target_shape_def]
QED

Theorem assign_operation_matches_target_shape_Replace_TupleTargetV:
  !gvs vs.
    assign_operation_matches_target_shape (TupleTargetV gvs) (Replace (ArrayV (TupleV vs))) <=>
    LENGTH gvs = LENGTH vs
Proof
  rw[assign_operation_matches_target_shape_def]
QED


(* ===== Bridge lemmas: execution success => shape and assignable context ===== *)

(* When get_module_code is NONE, lookup_global returns TypeError
   because lookup_global calls lift_option_type (get_module_code ...) FIRST. *)
Theorem get_module_code_NONE_lookup_global_TypeError:
  get_module_code cx src = NONE ==>
  lookup_global cx src n st = (INR (Error (TypeError "lookup_global get_module_code")), st)
Proof
  rw[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def]
QED

Theorem assign_target_TopLevelVar_no_type_error_imp_get_module_code:
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st = (res, st') ==>
  no_type_error_result res ==>
  ?code. get_module_code cx src = SOME code
Proof
  rw[no_type_error_result_def] >>
  CCONTR_TAC >> fs[] >>
  Cases_on `get_module_code cx src` >> gvs[] >>
  drule get_module_code_NONE_lookup_global_TypeError >> strip_tac >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[assign_target_def, bind_def, LET_THM] >>
  gvs[]
QED

(* If assign_target for TopLevelVar returns INL, lookup_global must have returned INL.
   This follows because assign_target starts with bind (lookup_global ...) and
   if lookup_global returns INR, bind passes it through as INR. *)
Theorem assign_target_TopLevelVar_success_imp_lookup_global_INL:
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st = (INL res, st') ==>
  ?tv r. lookup_global cx src (string_to_num id) st = (INL tv, r)
Proof
  rpt gen_tac >> CCONTR_TAC >> fs[] >>
  Cases_on `lookup_global cx src (string_to_num id) st` >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[assign_target_def, bind_def, LET_THM] >>
  gvs[]
QED



(* ===== Bridge lemma: target_runtime_typed + assign_target success => assignable context ===== *)

(* Small helper: env_scopes_consistent + FLOOKUP var_assignable = SOME T
   implies the scope entry exists and is assignable. This avoids expanding
   env_scopes_consistent_def in the main proof context. *)
Theorem env_scopes_consistent_var_assignable_imp[local]:
  !env cx st n.
    env_scopes_consistent env cx st ==>
    FLOOKUP env.var_assignable n = SOME T ==>
    ?entry. lookup_scopes n st.scopes = SOME entry ∧ entry.assignable
Proof
  rw[env_scopes_consistent_def] >> metis_tac[]
QED

(* For a ScopedVar target: well_typed_target + target value shape for ScopedVar
   implies the variable is assignable. Proved by induction on bt since
   base_target_value_shape is recursive through AttributeTarget/SubscriptTarget. *)
Theorem well_typed_target_ScopedVar_imp_var_assignable[local]:
  !env bt loc sbs vt.
    base_target_value_shape env bt loc sbs ==>
    type_place_target env bt = SOME vt ==>
    !id. loc = ScopedVar id ==>
    FLOOKUP env.var_assignable (string_to_num id) = SOME T
Proof
  recInduct base_target_value_shape_ind >>
  rw[] >>
  gvs[base_target_value_shape_def]
  >- metis_tac[type_place_target_NameTarget]
  >- metis_tac[type_place_target_AttributeTarget]
  >- metis_tac[type_place_target_SubscriptTarget]
QED

(* Bridge: target_runtime_typed for a ScopedVar directly implies var_assignable.
   Isolates definition expansion inside this lemma so the main proof context
   stays clean for the well_typed_target_ScopedVar_imp_var_assignable application. *)
Theorem target_runtime_typed_ScopedVar_imp_var_assignable[local]:
  !env cx st tgt ty v sbs.
    target_runtime_typed env cx st tgt ty (BaseTargetV (ScopedVar v) sbs) ==>
    FLOOKUP env.var_assignable (string_to_num v) = SOME T
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `tgt` >> gvs[target_runtime_typed_def] >>
  (* Expand inner predicates in assumptions only *)
  gvs[target_value_shape_def, well_typed_atarget_def, well_typed_target_def] >>
  (* Now have base_target_value_shape + type_place_target in assumptions *)
  metis_tac[well_typed_target_ScopedVar_imp_var_assignable]
QED

(* Direct boundary lemma: target_runtime_typed + env_consistent for ScopedVar
   implies the full assign_target_assignable_context. Proves the ScopedVar branch
   of assign_target_INL_imp_assign_target_assignable_context in one step. *)
Theorem target_runtime_typed_ScopedVar_imp_assignable_context:
  !env cx st tgt ty v sbs.
    target_runtime_typed env cx st tgt ty (BaseTargetV (ScopedVar v) sbs) ==>
    env_consistent env cx st ==>
    assign_target_assignable_context cx (BaseTargetV (ScopedVar v) sbs) st
Proof
  rpt strip_tac >>
  simp[assign_target_assignable_context_def, assign_target_assignable_def] >>
  `FLOOKUP env.var_assignable (string_to_num v) = SOME T` by
    metis_tac[target_runtime_typed_ScopedVar_imp_var_assignable] >>
  metis_tac[env_scopes_consistent_var_assignable_imp,
    lookup_scopes_find_containing_scope, env_consistent_def]
QED

(* Deriving assignable_context from assign_target INL success for arbitrary targets
   requires eval_target success info (not just target_runtime_typed + runtime_consistent)
   for the TopLevelVar branches, because we need to know the assign_target call actually
   reached lookup_global successfully. The statement-level bridge lemma
   assign_target_INL_imp_assignable_context_stmt in vyperTypeStmtSoundnessScript.sml
   has the eval_target hypothesis and handles this correctly. *)

(* ===== Component lemmas for TopLevelVar assignable context ===== *)

(* If lookup_global for a var returns INL, then get_module_code is SOME
   and find_var_decl_by_num is SOME (because lookup_global binds both
   in sequence, and INL means no TypeError was raised). *)
Theorem lookup_global_INL_imp_decl_facts:
  !cx src n st tv r.
    lookup_global cx src n st = (INL tv, r) ==>
    ?code. get_module_code cx src = SOME code
Proof
  rpt gen_tac >> strip_tac >>
  CCONTR_TAC >> fs[] >>
  Cases_on `get_module_code cx src` >> gvs[] >>
  drule get_module_code_NONE_lookup_global_TypeError >> strip_tac >>
  gvs[]
QED


(* ===== C5.2.4: INL success implies assignable context ===== *)

(* If lookup_global returns INL with a non-Value constructor (HashMapRef or ArrayRef),
   then find_var_decl_by_num must return SOME. This follows from lookup_global_def:
   the NONE branch of find_decl goes through immutables and can only produce Value or
   TypeError; HashMapRef/ArrayRef only come from SOME declarations. *)
Theorem lookup_global_INL_not_Value_imp_find_decl_SOME:
  !cx src n st code tv r.
    get_module_code cx src = SOME code /\
    lookup_global cx src n st = (INL tv, r) /\
    ¬is_Value tv ==>
    ?p. find_var_decl_by_num n code = SOME p
Proof
  rpt gen_tac >> strip_tac >> CCONTR_TAC >> fs[] >>
  (* CCONTR_TAC gives us find_var_decl_by_num n code = NONE *)
  Cases_on `find_var_decl_by_num n code` >> gvs[]
  >- (
    (* NONE case: lookup_global goes to immutable path, returns only Value or INR *)
    qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
    simp[lookup_global_def, bind_def, lift_option_type_def, LET_THM, return_def, raise_def] >>
    Cases_on `get_immutables cx src st` >> Cases_on `q` >> gvs[] >>
    Cases_on `FLOOKUP x n` >> gvs[raise_def, return_def] >>
    Cases_on `tv` >> gvs[is_Value_def])
QED

(* If assign_target TopLevelVar returns INL, find_var_decl_by_num must return SOME.
   Proof: Case split on lookup_global's tv result.
   - If tv is Value: assign_target's Value branch does OPTION_BIND (find_decl ...) which
     with NONE gives NONE → lift_option_type NONE = INR TypeError. Contradiction.
   - If tv is HashMapRef/ArrayRef: find_decl must be SOME (from the above lemma).
     But then assign_target's continuation succeeds. Contradiction with our CCONTR. *)
Theorem assign_target_TopLevelVar_INL_imp_find_decl_SOME:
  !cx src id sbs op st res st' code.
    get_module_code cx src = SOME code /\
    assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st = (INL res, st') ==>
    ?p. find_var_decl_by_num (string_to_num id) code = SOME p
Proof
  rpt gen_tac >> strip_tac >> CCONTR_TAC >> fs[] >>
  drule assign_target_TopLevelVar_success_imp_lookup_global_INL >> strip_tac >>
  (* Case split on tv to show each branch contradicts find_decl = NONE *)
  Cases_on `tv` >> gvs[is_Value_def]
  >- (
    (* tv = Value v. The Value branch does find_var_decl AGAIN via OPTION_BIND.
       With find_decl = NONE, OPTION_BIND NONE _ = NONE -> lift_option_type NONE -> TypeError *)
    qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
    simp[assign_target_def, bind_def, LET_THM, lift_option_type_def,
         return_def, raise_def, OPTION_BIND_def] >>
    CASE_TAC >> gvs[raise_def, AllCaseEqs()])
  >- (
    (* tv = HashMapRef. ¬is_Value HashMapRef, so lemma gives ∃p; contradicts ∀p.≠ *)
    metis_tac[lookup_global_INL_not_Value_imp_find_decl_SOME, is_Value_def])
  >- (
    (* tv = ArrayRef. Same as HashMapRef. *)
    metis_tac[lookup_global_INL_not_Value_imp_find_decl_SOME, is_Value_def])
QED

(* If lookup_global returns INL and find_var_decl is SOME(StorageVarDecl ...),
   then evaluate_type and lookup_var_slot_from_layout must return SOME.
   This follows from lookup_global_def: both are called via lift_option_type
   before the storage read, so INL implies success of both. *)
Theorem lookup_global_INL_StorageVarDecl_imp_IS_SOME:
  !cx src n st code is_transient typ id_str tv r.
    get_module_code cx src = SOME code /\
    lookup_global cx src n st = (INL tv, r) /\
    find_var_decl_by_num n code = SOME (StorageVarDecl is_transient typ, id_str) ==>
    IS_SOME (evaluate_type (get_tenv cx) typ) /\
    IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, LET_THM, return_def, raise_def] >>
  Cases_on `lookup_var_slot_from_layout cx is_transient src id_str` >> gvs[return_def, raise_def] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> gvs[return_def, raise_def]
QED

(* If lookup_global returns INL and find_var_decl is SOME(HashMapVarDecl ...),
   then lookup_var_slot_from_layout must return SOME.
   This follows from lookup_global_def: it calls lift_option_type on
   lookup_var_slot_from_layout before returning HashMapRef. *)
Theorem lookup_global_INL_HashMapVarDecl_imp_IS_SOME:
  !cx src n st code is_transient kt vt id_str tv r.
    get_module_code cx src = SOME code /\
    lookup_global cx src n st = (INL tv, r) /\
    find_var_decl_by_num n code = SOME (HashMapVarDecl is_transient kt vt, id_str) ==>
    IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, LET_THM, return_def, raise_def] >>
  Cases_on `lookup_var_slot_from_layout cx is_transient src id_str` >> gvs[return_def, raise_def]
QED

(* If assign_target TopLevelVar returns INL and find_var_decl is SOME(HashMapVarDecl ...),
   then sbs must be non-empty.
   Proof: By lookup_global_INL + the HashMapRef branch of assign_target:
   REVERSE sbs is case-split, and [] produces lift_option_type NONE = INR TypeError. *)
Theorem assign_target_TopLevelVar_INL_HashMapVarDecl_imp_sbs_ne:
  !cx src id sbs op st res st' code is_transient kt vt id_str.
    get_module_code cx src = SOME code /\
    assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st = (INL res, st') /\
    find_var_decl_by_num (string_to_num id) code = SOME (HashMapVarDecl is_transient kt vt, id_str) ==>
    sbs ≠ []
Proof
  rpt gen_tac >> strip_tac >> CCONTR_TAC >> fs[] >>
  (* sbs = [] is now in assumptions *)
  drule assign_target_TopLevelVar_success_imp_lookup_global_INL >> strip_tac >>
  (* Case split on lookup_global result FIRST, before expanding assign_target_def *)
  Cases_on `tv` >> gvs[is_Value_def]
  >- (
    (* tv = Value: HashMapVarDecl can't produce Value from lookup_global.
       Use lookup_global_def to show contradiction - no need for assign_target_def. *)
    qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
    simp[lookup_global_def, bind_def, lift_option_type_def, LET_THM,
         return_def, raise_def] >>
    Cases_on `lookup_var_slot_from_layout cx is_transient src id_str` >> gvs[return_def, raise_def])
  >- (
    (* tv = HashMapRef: REVERSE [] = NONE → lift_option_type NONE → TypeError.
       Now tv = HashMapRef is in assumptions, so expanding assign_target_def
       should resolve the case split and only leave the HashMapRef branch. *)
    qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
    simp[assign_target_def, bind_def, LET_THM, lift_option_type_def,
         return_def, raise_def] >>
    simp[bind_def, return_def, raise_def])
  >- (
    (* tv = ArrayRef: HashMapVarDecl can't produce ArrayRef from lookup_global.
       Use lookup_global_def to show contradiction - no need for assign_target_def. *)
    qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
    simp[lookup_global_def, bind_def, lift_option_type_def, LET_THM,
         return_def, raise_def] >>
    Cases_on `lookup_var_slot_from_layout cx is_transient src id_str` >> gvs[return_def, raise_def] >>
    Cases_on `evaluate_type (get_tenv cx) typ` >> gvs[return_def, raise_def])
QED
