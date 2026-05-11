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

Theorem switch_BoolV_post:
  toplevel_value_typed tv (BaseTV BoolT) /\
  switch_BoolV tv kt kf st = (res, st') /\
  (!res1 st1. kt st = (res1, st1) ==> P res1 st1) /\
  (!res1 st1. kf st = (res1, st1) ==> P res1 st1) ==>
  P res st'
Proof
  rw[] >>
  drule toplevel_value_typed_BoolTV >> strip_tac >>
  Cases_on `b` >> gvs[switch_BoolV_def]
QED

Theorem get_Value_no_type_error:
  toplevel_value_typed tv tyv /\ tyv <> NoneTV /\ (!t b. tyv <> ArrayTV t b) /\
  get_Value tv st = (res, st') ==>
  no_type_error_result res
Proof
  rw[] >>
  drule_all toplevel_value_typed_not_ArrayRef >> strip_tac >>
  gvs[get_Value_def, return_def, no_type_error_result_def]
QED

Theorem get_Value_String_no_type_error:
  toplevel_value_typed tv (BaseTV (StringT n)) /\
  get_Value tv st = (res, st') ==>
  no_type_error_result res
Proof
  rw[] >>
  drule toplevel_value_typed_StringTV >> strip_tac >>
  gvs[get_Value_def, return_def, no_type_error_result_def]
QED

Theorem get_Value_String_success:
  toplevel_value_typed tv (BaseTV (StringT n)) /\
  get_Value tv st = (INL v, st') ==>
  ?s. v = StringV s
Proof
  rw[] >> drule toplevel_value_typed_StringTV >> strip_tac >> gvs[get_Value_def, return_def]
QED

Theorem dest_StringV_String_no_type_error:
  dest_StringV v = SOME s ==> no_type_error_eval (lift_option_type (dest_StringV v) msg st)
Proof
  rw[lift_option_type_def, return_def, no_type_error_eval_def, no_type_error_result_def]
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

Definition target_path_step_type_def:
  target_path_step_type env cur_vt sb next_vt <=>
    case cur_vt of
    | HashMapT kt vt => next_vt = vt
    | Type ty =>
        case ty of
        | ArrayT elem_ty len => next_vt = Type elem_ty
        | StructT s =>
            case sb of
            | AttrSubscript id =>
                ?field_ty. next_vt = Type field_ty /\
                  attribute_type env.type_defs (StructT s) id = SOME field_ty
            | _ => F
        | _ => F
End

Definition target_path_type_def:
  (target_path_type env loc_vt [] vt <=> loc_vt = vt) /\
  (target_path_type env loc_vt (sb::sbs) vt <=>
    ?mid_vt. target_path_type env loc_vt sbs mid_vt /\
             target_path_step_type env mid_vt sb vt)
End

Definition place_leaf_path_typed_def:
  (place_leaf_path_typed env (Type base_ty) path ty final_tv <=>
    (?base_tv. evaluate_type env.type_defs base_ty = SOME base_tv /\
               final_tv = leaf_type base_tv path /\
               evaluate_type env.type_defs ty = SOME final_tv)) /\
  (place_leaf_path_typed env (HashMapT kt vt) [] ty final_tv <=> F) /\
  (place_leaf_path_typed env (HashMapT kt vt) (sb::path) ty final_tv <=>
    place_leaf_path_typed env vt path ty final_tv)
End

Definition place_leaf_typed_def:
  place_leaf_typed env loc_vt sbs ty final_tv <=>
    place_leaf_path_typed env loc_vt (REVERSE sbs) ty final_tv
End

Definition place_vtype_path_typed_def:
  (place_vtype_path_typed env loc_vt path (Type ty) <=>
    ?final_tv. place_leaf_path_typed env loc_vt path ty final_tv) /\
  (place_vtype_path_typed env loc_vt path (HashMapT kt vt) <=>
    !sb. place_vtype_path_typed env loc_vt (path ++ [sb]) vt)
Termination
  WF_REL_TAC `measure (value_type_size o SND o SND o SND)` >>
  rw[]
End

Theorem target_path_type_refl:
  target_path_type env vt [] vt
Proof
  simp[target_path_type_def]
QED

Theorem target_path_type_attr_cons:
  target_path_type env loc_vt sbs (Type (StructT s)) /\
  attribute_type env.type_defs (StructT s) id = SOME field_ty ==>
  target_path_type env loc_vt (AttrSubscript id::sbs) (Type field_ty)
Proof
  rw[target_path_type_def, target_path_step_type_def] >>
  qexists_tac `Type (StructT s)` >> simp[]
QED

Theorem target_path_type_hashmap_cons:
  target_path_type env loc_vt sbs (HashMapT kt vt) ==>
  target_path_type env loc_vt (sb::sbs) vt
Proof
  rw[target_path_type_def, target_path_step_type_def] >>
  qexists_tac `HashMapT kt vt` >> simp[]
QED

Theorem target_path_type_array_cons:
  target_path_type env loc_vt sbs (Type (ArrayT elem_ty len)) ==>
  target_path_type env loc_vt (sb::sbs) (Type elem_ty)
Proof
  rw[target_path_type_def, target_path_step_type_def] >>
  qexists_tac `Type (ArrayT elem_ty len)` >> simp[]
QED

Theorem target_path_type_subscript_cons:
  target_path_type env loc_vt sbs vt /\
  subscript_vtype vt idx_ty = SOME result_vt ==>
  target_path_type env loc_vt (sb::sbs) result_vt
Proof
  strip_tac >>
  Cases_on `vt`
  >- (
    Cases_on `t` >> gvs[subscript_vtype_def] >>
    drule_then (qspec_then `sb` mp_tac) target_path_type_array_cons >> simp[] >>
    NO_TAC) >>
  gvs[subscript_vtype_def] >>
  drule_then (qspec_then `sb` mp_tac) target_path_type_hashmap_cons >> simp[]
QED

Theorem leaf_type_append:
  !base_tv xs ys.
    leaf_type base_tv (xs ++ ys) = leaf_type (leaf_type base_tv xs) ys
Proof
  Induct_on `xs` >> simp[leaf_type_def] >>
  Cases_on `h` >> simp[leaf_type_def] >>
  TRY(Cases_on `v` >> simp[leaf_type_def]) >>
  Cases_on `base_tv` >> simp[leaf_type_def] >>
  TRY(Cases_on `b` >> simp[leaf_type_def]) >>
  TRY(Cases_on `ALOOKUP l s` >> simp[leaf_type_def]) >>
  Cases_on `ys` >> simp[leaf_type_def]
QED

Theorem OPT_MMAP_ALOOKUP_ZIP:
  !f (args:('k # 'a) list) ys field_id ty.
    OPT_MMAP f (MAP SND args) = SOME ys /\
    ALOOKUP args field_id = SOME ty ==>
    ?tv. f ty = SOME tv /\
         ALOOKUP (ZIP(MAP FST args, ys)) field_id = SOME tv
Proof
  Induct_on `args` >> simp[] >>
  Cases >> simp[OPT_MMAP_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `q = field_id` >> gvs[]
QED

Theorem evaluate_type_mono:
  (!tenv ty tv k.
    evaluate_type (tenv \\ k) ty = SOME tv ==>
    evaluate_type tenv ty = SOME tv) /\
  (!tenv ts acc tvs k.
    evaluate_types (tenv \\ k) ts acc = SOME tvs ==>
    evaluate_types tenv ts acc = SOME tvs)
Proof
  ho_match_mp_tac evaluate_type_ind
  >> conj_tac >- simp[evaluate_type_def]
  >> conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[evaluate_type_def, AllCaseEqs()] >>
    first_x_assum drule >> simp[])
  >> conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[evaluate_type_def, AllCaseEqs()] >>
    first_x_assum drule >> simp[])
  >> conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[evaluate_type_def, AllCaseEqs(), DOMSUB_FLOOKUP_THM, DOMSUB_COMMUTES] >>
    first_x_assum drule >>
    strip_tac >> goal_assum drule >> gvs[])
  >> conj_tac >- (
    rpt gen_tac >> rpt gen_tac >>
    simp[evaluate_type_def, AllCaseEqs(), DOMSUB_FLOOKUP_THM] >>
    rpt strip_tac >> gvs[])
  >> conj_tac >- simp[evaluate_type_def]
  >> conj_tac >- simp[evaluate_type_def]
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >>
  strip_tac >>
  first_x_assum (fn th => drule (cj 1 th)) >> strip_tac >> simp[] >>
  first_x_assum drule >> simp[] >>
  disch_then irule >> goal_assum drule
QED

Theorem attribute_type_evaluates:
  !tenv struct_ty field_id result_ty ftypes.
    attribute_type tenv struct_ty field_id = SOME result_ty /\
    evaluate_type tenv struct_ty = SOME (StructTV ftypes) ==>
    ?tv. evaluate_type tenv result_ty = SOME tv /\
         ALOOKUP ftypes field_id = SOME tv
Proof
  Cases_on `struct_ty` >> simp[attribute_type_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), LET_THM, evaluate_types_OPT_MMAP] >>
  Cases_on `ALOOKUP args field_id` >> gvs[] >>
  drule_all OPT_MMAP_ALOOKUP_ZIP >> strip_tac >>
  metis_tac[evaluate_type_mono]
QED

Definition target_runtime_typed_def:
  target_runtime_typed env cx st tgt ty gv <=>
    well_typed_atarget env tgt ty /\ target_value_shape env tgt gv /\
    case gv of
    | BaseTargetV loc sbs =>
        ?vt. location_runtime_typed env cx st loc vt /\
             target_path_type env vt sbs (Type ty)
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



