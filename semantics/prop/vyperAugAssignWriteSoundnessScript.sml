(* TOP-LEVEL: the post-RHS AugAssign write boundary. The saved old value and
   saved place type are used after RHS effects; target bounds are not repeated. *)
Theory vyperAugAssignWriteSoundness
Ancestors
  list option pair sum finite_map vyperState vyperMisc vyperTyping
  vyperTypeValues vyperTypeExprSoundness vyperTypeBuiltins vyperTypeStatePreservation
  vyperTypeExprResult vyperTypeInvariants vyperTypeSystem
  vyperPlaceTyping vyperPlaceWriteSoundness vyperTargetPlaceWrite
  vyperStatePreservation vyperExprNoControl

Theorem update_get_Value_sound:
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  expr_result_typed env e rhs /\
  get_Value rhs st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  case res of INL v => value_runtime_typed env (expr_type e) v | INR _ => T
Proof
  rpt gen_tac >> strip_tac >> imp_res_tac get_Value_state >> gvs[] >>
  Cases_on `res` >> simp[no_type_error_result_def]
  >- (Cases_on `rhs` >>
      gvs[get_Value_def, return_def, raise_def, expr_result_typed_def,
          expr_runtime_typed_def, value_runtime_typed_def, toplevel_value_typed_def]) >>
  gvs[expr_result_typed_def, expr_runtime_typed_def] >>
  drule_all well_typed_binop_not_In_second_type >> strip_tac >>
  drule_all evaluate_type_not_ArrayT_imp_not_ArrayTV >> strip_tac >>
  drule_all evaluate_type_not_NoneT_imp_not_NoneTV >> strip_tac >>
  drule_all get_Value_no_type_error >> simp[no_type_error_result_def]
QED

Theorem update_place_tail_no_control:
  (do
    v <- get_Value rhs;
    result <- lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0) ptv bop cur v);
    write_place cx p result
  od) st = (INR exn,st') ==> no_control_exc exn
Proof
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
  metis_tac[get_Value_no_control, lift_sum_no_control, write_place_no_control]
QED

Theorem update_place_tail_sound:
  runtime_consistent env cx st /\
  runtime_place_typed cx st p ptv /\ runtime_place_writable cx st p /\
  evaluate_type env.type_defs ty = SOME ptv /\ value_has_type ptv cur /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  expr_result_typed env e rhs /\
  (do
    v <- get_Value rhs;
    result <- lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0) ptv bop cur v);
    write_place cx p result
  od) st = (res,st') ==>
  runtime_consistent env cx st' /\ no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `do _ od _ = _` mp_tac >>
  simp_tac (srw_ss()) [bind_def] >>
  Cases_on `get_Value rhs st` >>
  rename1 `get_Value rhs st = (answer,middle)` >>
  drule_all update_get_Value_sound >> strip_tac >> gvs[] >>
  reverse (Cases_on `answer`)
  >- (simp[] >> strip_tac >> gvs[no_type_error_result_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  qmatch_assum_rename_tac `get_Value rhs input = (INL right,input)` >>
  fs[value_runtime_typed_def] >>
  qmatch_assum_rename_tac `evaluate_type env.type_defs (expr_type e) = SOME rhs_tv` >>
  `!msg. evaluate_binop
    (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0) ptv bop cur right <>
    INR (TypeError msg)` by
    (irule well_typed_binop_no_type_error >>
     qexistsl_tac [`ptv`,`ty`,`expr_type e`,`env.type_defs`,`ptv`,`rhs_tv`,`ty`] >> simp[]) >>
  qpat_x_assum `_ = (res,st')` mp_tac >>
  simp_tac (srw_ss()) [bind_def, lift_sum_def] >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0) ptv bop cur right` >>
  simp[return_def, raise_def] >> strip_tac >> gvs[no_type_error_result_def]
  >- (qmatch_assum_rename_tac `evaluate_binop _ ptv bop cur right = INL result` >>
      `value_has_type ptv result` by
        (irule well_typed_binop_success_type >>
         qexistsl_tac [`bop`,`ty`,`expr_type e`,`env.type_defs`,`ptv`,`ptv`,`rhs_tv`,`ty`,
           `case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0`,
           `cur`,`right`] >> simp[]) >>
      drule_all write_place_sound >> simp[no_type_error_result_def])
QED
