(*
 * Fresh assignment-target soundness helpers for the executable type system.
 *)

Theory vyperTypeAssignSoundness
Ancestors
  list rich_list finite_map option pair arithmetic
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeValues
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
  cheat
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

(* TEMPORARILY CHEATED - copied into fresh assignment helper theory.  The old
   proof almost works but needs deterministic witnesses in the recursive storage
   array branch; keep the attempted structure for repair.
Proof
  ho_match_mp_tac resolve_array_element_ind >>
  rw[resolve_array_element_def, raise_def, return_def] >>
  gvs[bind_apply, AllCaseEqs(), bound_CASE_rator, ignore_bind_apply,
      return_def, check_def, assert_def, raise_def] >>
  first_x_assum irule >>
  TRY(qexists_tac `0` >> simp[] >> goal_assum drule) >>
  qexists_tac `1` >> simp[] >>
  gvs[wordsTheory.word_add_n2w] >>
  goal_assum drule
QED
*)
Theorem resolve_array_element_error:
  !a b c d e f g h. resolve_array_element a b c d e f = (INR g, h) ==> ?m. g = Error m
Proof
  cheat
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

Definition assign_target_assignable_def:
  assign_target_assignable (BaseTargetV loc sbs) st =
    (case loc of
     | ScopedVar id =>
         ?pre env entry rest.
           find_containing_scope (string_to_num id) st.scopes =
             SOME (pre, env, entry, rest) /\
           entry.assignable
     | _ => T) /\
  assign_target_assignable (TupleTargetV tgts) st =
    EVERY (\tgt. assign_target_assignable tgt st) tgts
End

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
  (!g. !cx tgt st0 st1 v st res st' env ty.
    eval_target cx g st0 = (INL tgt, st1) /\
    well_typed_atarget env g ty /\
    assign_target_assignable tgt st /\
    assign_target cx tgt (Replace v) st = (res, st') /\
    state_well_typed st /\
    env_consistent env cx st /\
    (?tyv. evaluate_type (get_tenv cx) ty = SOME tyv /\
           value_has_type tyv v) ==>
    !s. res <> INR (Error (TypeError s))) /\
  (!gs. !cx gvs st0 st1 vs st res st' env tys.
    eval_targets cx gs st0 = (INL gvs, st1) /\
    LIST_REL (well_typed_atarget env) gs tys /\
    EVERY (\tgt. assign_target_assignable tgt st) gvs /\
    assign_targets cx gvs vs st = (res, st') /\
    state_well_typed st /\
    env_consistent env cx st /\
    LIST_REL (\ty v. ?tyv. evaluate_type (get_tenv cx) ty = SOME tyv /\
              value_has_type tyv v) tys vs ==>
    !s. res <> INR (Error (TypeError s)))
Proof
  cheat
QED

Theorem assign_target_update_no_type_error:
  !cx bt loc sbs st0 st1 target_ty ty bop v st res st' env et.
    eval_base_target cx bt st0 = (INL (loc,sbs), st1) /\
    well_typed_target env bt target_ty /\
    assign_target_assignable (BaseTargetV loc sbs) st /\
    assign_target cx (BaseTargetV loc sbs) (Update ty bop v) st = (res, st') /\
    state_well_typed st /\
    env_consistent env cx st /\
    well_typed_binop ty bop ty et /\
    bop <> In /\ bop <> NotIn ==>
    !s. res <> INR (Error (TypeError s))
Proof
  cheat
QED

Theorem assign_target_append_no_type_error:
  !cx bt loc sbs st0 st1 v st res st' env elem_ty bd.
    eval_base_target cx bt st0 = (INL (loc,sbs), st1) /\
    well_typed_target env bt (ArrayT elem_ty bd) /\
    assign_target cx (BaseTargetV loc sbs) (AppendOp v) st = (res, st') /\
    state_well_typed st /\
    env_consistent env cx st /\
    (?tyv. evaluate_type (get_tenv cx) elem_ty = SOME tyv /\
           value_has_type tyv v) ==>
    !s. res <> INR (Error (TypeError s))
Proof
  cheat
QED
