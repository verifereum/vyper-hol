(*
 * Expression, iterator, and assignment-target type soundness skeleton for the
 * fresh executable Vyper type system.
 *)

Theory vyperTypeExprSoundness
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeValues
  vyperTypeEnv vyperTypeBuiltins
Libs
  wordsLib

(* ===== Result predicates ===== *)

Definition no_type_error_result_def:
  no_type_error_result r <=> !msg. r <> INR (Error (TypeError msg))
End

Definition no_type_error_eval_def:
  no_type_error_eval res <=> no_type_error_result (FST res)
End

Theorem lift_option_type_some_no_type_error:
  opt = SOME v ==> no_type_error_eval (lift_option_type opt msg st)
Proof
  rw[lift_option_type_def, no_type_error_eval_def, no_type_error_result_def, return_def]
QED

Theorem lift_option_type_no_type_error_result:
  opt = SOME v ==> FST (lift_option_type opt msg st) <> INR (Error (TypeError m))
Proof
  rw[lift_option_type_def, return_def]
QED

Theorem type_check_true_no_type_error:
  b ==> no_type_error_eval (type_check b msg st)
Proof
  rw[type_check_def, assert_def, no_type_error_eval_def, no_type_error_result_def, return_def]
QED

Theorem switch_BoolV_assert_no_type_error:
  toplevel_value_typed tv (BaseTV BoolT) /\
  (!msg. exn <> Error (TypeError msg)) /\
  switch_BoolV tv (return ()) (raise exn) st = (res, st') ==>
  no_type_error_result res
Proof
  rw[] >>
  drule toplevel_value_typed_BoolTV >> strip_tac >>
  Cases_on `b` >> gvs[switch_BoolV_def, return_def, raise_def, no_type_error_result_def]
QED

Theorem switch_BoolV_no_type_error:
  toplevel_value_typed tv (BaseTV BoolT) /\
  switch_BoolV tv k1 k2 st = (res, st') /\
  (!msg. FST (k1 st) <> INR (Error (TypeError msg))) /\
  (!msg. FST (k2 st) <> INR (Error (TypeError msg))) ==>
  no_type_error_result res
Proof
  rw[] >>
  drule toplevel_value_typed_BoolTV >> strip_tac >>
  Cases_on `b` >> gvs[switch_BoolV_def, no_type_error_result_def]
QED

Theorem lift_option_error:
  lift_option x y z = (INR e, s) ==> e = Error (RuntimeError y)
Proof
  Cases_on `x` >> rw[lift_option_def, return_def, raise_def]
QED

Theorem get_storage_backend_no_error:
  get_storage_backend cx is_trans st <> (INR e, s)
Proof
  Cases_on `is_trans` >>
  rw[get_storage_backend_def, bind_def, get_transient_storage_def, get_accounts_def, return_def]
QED

Theorem read_storage_slot_error:
  read_storage_slot x y z w a = (INR e, s) ==>
  ?m. e = Error (RuntimeError m)
Proof
  rw[read_storage_slot_def, bind_def, AllCaseEqs()] >>
  TRY (drule lift_option_error >> rw[]) >>
  gvs[get_storage_backend_no_error]
QED

Theorem materialise_no_type_error:
  materialise cx tv st = (INR e, st') ==>
  (!tyv. toplevel_value_typed tv tyv ==> tyv = NoneTV) \/
  (!m. e <> Error (TypeError m))
Proof
  Cases_on `tv` >>
  simp[materialise_def, return_def, raise_def]
  >- (rw[toplevel_value_typed_def]) >>
  strip_tac >> gvs[bind_def, AllCaseEqs(), return_def] >>
  drule read_storage_slot_error >> strip_tac >> gvs[]
QED

Theorem materialise_Value_no_type_error:
  materialise cx (Value v) st <> (INR (Error (TypeError m)), st')
Proof
  simp[materialise_def, return_def]
QED

Theorem materialise_type_error_imp_HashMapRef:
  materialise cx tv st = (INR (Error (TypeError m)), st') ==>
  is_HashMapRef tv
Proof
  Cases_on `tv` >> gvs[materialise_def, return_def, raise_def, is_HashMapRef_def] >>
  strip_tac >> gvs[bind_def, AllCaseEqs(), return_def] >>
  drule read_storage_slot_error >> strip_tac >> gvs[is_HashMapRef_def]
QED

Theorem materialise_not_HashMapRef_no_type_error:
  ~is_HashMapRef tv ==> materialise cx tv st <> (INR (Error (TypeError m)), st')
Proof
  metis_tac[materialise_type_error_imp_HashMapRef]
QED

Theorem materialise_typed_non_none_no_type_error:
  materialise cx tv st = (INR e, st') /\ toplevel_value_typed tv tyv /\ tyv <> NoneTV ==>
  !m. e <> Error (TypeError m)
Proof
  metis_tac[materialise_no_type_error]
QED

Definition expr_runtime_typed_def:
  expr_runtime_typed env e tvl <=>
    ?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
         toplevel_value_typed tvl tv
End

Theorem materialise_runtime_typed_no_type_error:
  expr_runtime_typed env e tv /\ evaluate_type env.type_defs (expr_type e) = SOME tyv /\ tyv <> NoneTV /\
  materialise cx tv st = (INR err, st') ==>
  !m. err <> Error (TypeError m)
Proof
  rw[expr_runtime_typed_def] >> gvs[] >> metis_tac[materialise_no_type_error]
QED

Definition value_runtime_typed_def:
  value_runtime_typed env ty v <=>
    ?tv. evaluate_type env.type_defs ty = SOME tv /\ value_has_type tv v
End

Definition exprs_runtime_typed_def:
  exprs_runtime_typed env es vs <=>
    ?tvs. LIST_REL (\e tv. evaluate_type env.type_defs (expr_type e) = SOME tv) es tvs /\
          LIST_REL value_has_type tvs vs
End

Definition base_target_value_shape_def:
  base_target_value_shape env (NameTarget id) (ScopedVar id') sbs =
    (id = id' /\ sbs = []) /\
  base_target_value_shape env (NameTarget id) _ _ = F /\
  base_target_value_shape env (BareGlobalNameTarget id) (ImmutableVar id') sbs =
    (id = id' /\ sbs = []) /\
  base_target_value_shape env (BareGlobalNameTarget id) _ _ = F /\
  base_target_value_shape env (TopLevelNameTarget nsid) (TopLevelVar src id) sbs =
    (nsid = (src,id) /\ sbs = []) /\
  base_target_value_shape env (TopLevelNameTarget nsid) _ _ = F /\
  base_target_value_shape env (AttributeTarget tgt id) loc sbs =
    (?rest. sbs = AttrSubscript id :: rest /\
            base_target_value_shape env tgt loc rest) /\
  base_target_value_shape env (SubscriptTarget tgt e) loc sbs =
    (well_typed_expr env e /\
     ?sb rest. sbs = sb :: rest /\ base_target_value_shape env tgt loc rest)
Termination
  WF_REL_TAC `measure (\(env, bt, loc, sbs). base_assignment_target_size bt)` >>
  rw[]
End

Definition target_value_shape_def:
  target_value_shape env (BaseTarget bt) (BaseTargetV loc sbs) =
    base_target_value_shape env bt loc sbs /\
  target_value_shape env (BaseTarget bt) (TupleTargetV gvs) = F /\
  target_value_shape env (TupleTarget tgts) (BaseTargetV loc sbs) = F /\
  target_value_shape env (TupleTarget tgts) (TupleTargetV gvs) =
    target_values_shape env tgts gvs /\
  target_values_shape env [] [] = T /\
  target_values_shape env [] (gv::gvs) = F /\
  target_values_shape env (tgt::tgts) [] = F /\
  target_values_shape env (tgt::tgts) (gv::gvs) =
    (target_value_shape env tgt gv /\ target_values_shape env tgts gvs)
Termination
  WF_REL_TAC `measure (\x. case x of
    | INL (env, tgt, gv) => assignment_target_size tgt
    | INR (env, tgts, gvs) => list_size assignment_target_size tgts)` >>
  rw[]
End

Definition runtime_consistent_def:
  runtime_consistent env cx st <=>
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts
End

Definition location_runtime_typed_def:
  (location_runtime_typed env cx st (ScopedVar id) vt <=>
    (?entry ty. vt = Type ty /\
                lookup_scopes (string_to_num id) st.scopes = SOME entry /\
                FLOOKUP env.var_types (string_to_num id) = SOME ty /\
                evaluate_type env.type_defs ty = SOME entry.type)) /\
  (location_runtime_typed env cx st (ImmutableVar id) vt <=>
    (?imms v ty tv. vt = Type ty /\
                    get_immutables cx (current_module cx) st = (INL imms, st) /\
                    FLOOKUP imms (string_to_num id) = SOME (tv, v) /\
                    FLOOKUP env.bare_globals (env.current_src, string_to_num id) = SOME ty /\
                    evaluate_type env.type_defs ty = SOME tv)) /\
  (location_runtime_typed env cx st (TopLevelVar src_id_opt id) vt <=>
    FLOOKUP env.toplevel_vtypes (src_id_opt, string_to_num id) = SOME vt)
End

Definition place_leaf_typed_def:
  (place_leaf_typed env (Type base_ty) sbs ty final_tv <=>
    (?base_tv. evaluate_type env.type_defs base_ty = SOME base_tv /\
               final_tv = leaf_type base_tv (REVERSE sbs) /\
               evaluate_type env.type_defs ty = SOME final_tv)) /\
  (place_leaf_typed env (HashMapT kt vt) [] ty final_tv <=> F) /\
  (place_leaf_typed env (HashMapT kt vt) (sb::sbs) ty final_tv <=>
    place_leaf_typed env vt sbs ty final_tv)
End

Definition target_runtime_typed_def:
  target_runtime_typed env cx st tgt ty gv <=>
    well_typed_atarget env tgt ty /\ target_value_shape env tgt gv /\
    case gv of
    | BaseTargetV loc sbs =>
        ?vt final_tv. location_runtime_typed env cx st loc vt /\
          place_leaf_typed env vt sbs ty final_tv
    | TupleTargetV gvs => T
End

Theorem target_values_shape_LIST_REL:
  !env tgts gvs. target_values_shape env tgts gvs <=> LIST_REL (target_value_shape env) tgts gvs
Proof
  Induct_on `tgts` >> Cases_on `gvs` >> simp[target_value_shape_def]
QED

Definition assign_operation_runtime_typed_def:
  (assign_operation_runtime_typed env ty (Replace v) <=> value_runtime_typed env ty v) /\
  (assign_operation_runtime_typed env ty (Update target_ty bop v) <=>
     target_ty = ty /\ ?rhs_ty. value_runtime_typed env rhs_ty v /\ well_typed_binop ty bop ty rhs_ty) /\
  (assign_operation_runtime_typed env ty (AppendOp v) <=>
     ?elem_tv elem_ty n. evaluate_type env.type_defs elem_ty = SOME elem_tv /\
       ty = ArrayT elem_ty (Dynamic n) /\ value_has_type elem_tv v) /\
  (assign_operation_runtime_typed env ty PopOp <=> T)
End

(* ===== Expression soundness ===== *)

Theorem eval_expr_no_type_error:
  well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_expr cx e st)
Proof
  cheat
QED

Theorem eval_expr_type_preservation:
  well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_expr cx e st = (INL tvl, st') ==>
  state_well_typed st' /\ expr_runtime_typed env e tvl
Proof
  cheat
QED

Theorem eval_expr_state_preservation_on_error:
  well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_expr cx e st = (INR exn, st') ==>
  state_well_typed st'
Proof
  cheat
QED

Theorem eval_exprs_no_type_error:
  well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_exprs cx es st)
Proof
  cheat
QED

Theorem eval_exprs_type_preservation:
  well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_exprs cx es st = (INL vs, st') ==>
  state_well_typed st' /\ exprs_runtime_typed env es vs
Proof
  cheat
QED

(* ===== Iterator soundness ===== *)

Theorem eval_iterator_no_type_error:
  well_typed_iterator env ty it /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_iterator cx it st)
Proof
  cheat
QED

Theorem eval_iterator_type_preservation:
  well_typed_iterator env ty it /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_iterator cx it st = (INL vs, st') ==>
  state_well_typed st' /\
  ?tv. evaluate_type env.type_defs ty = SOME tv /\ EVERY (value_has_type tv) vs
Proof
  cheat
QED

(* ===== Target soundness ===== *)

Theorem eval_base_target_no_type_error:
  type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts ==>
  no_type_error_eval (eval_base_target cx bt st)
Proof
  cheat
QED

Theorem eval_target_no_type_error:
  well_typed_atarget env tgt ty /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts ==>
  no_type_error_eval (eval_target cx tgt st)
Proof
  cheat
QED

Theorem eval_targets_no_type_error:
  LIST_REL (\t ty. well_typed_atarget env t ty) tgts tys /\
  env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts ==>
  no_type_error_eval (eval_targets cx tgts st)
Proof
  cheat
QED

Theorem eval_base_target_state_preservation:
  type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
  eval_base_target cx bt st = (INL loc_sbs, st') ==>
  state_well_typed st'
Proof
  cheat
QED

