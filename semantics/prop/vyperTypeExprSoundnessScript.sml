(*
 * Expression, iterator, and assignment-target type soundness for the
 * executable Vyper type system.
 *
 * This file contains the expression-level type-soundness development,
 * including result-shape helpers, iterator facts, assignment-target cases, and
 * the exported expression soundness theorems.
 *)

Theory vyperTypeExprSoundness
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
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
  value_result_typed tv (BaseTV BoolT) /\
  (!msg. exn <> Error (TypeError msg)) /\
  switch_BoolV cx tv (return ()) (raise exn) st = (res, st') ==>
  no_type_error_result res
Proof
  rw[] >>
  drule value_result_typed_BoolTV >> strip_tac >>
  Cases_on `b` >> gvs[read_result_def, bind_def, return_def, switch_BoolV_def, return_def, raise_def, no_type_error_result_def]
QED

Theorem switch_BoolV_no_type_error:
  value_result_typed tv (BaseTV BoolT) /\
  switch_BoolV cx tv k1 k2 st = (res, st') /\
  (!msg. FST (k1 st) <> INR (Error (TypeError msg))) /\
  (!msg. FST (k2 st) <> INR (Error (TypeError msg))) ==>
  no_type_error_result res
Proof
  rw[] >>
  drule value_result_typed_BoolTV >> strip_tac >>
  Cases_on `b` >> gvs[read_result_def, bind_def, return_def, switch_BoolV_def, no_type_error_result_def]
QED

Theorem switch_BoolV_post:
  value_result_typed tv (BaseTV BoolT) /\
  switch_BoolV cx tv kt kf st = (res, st') /\
  (!res1 st1. kt st = (res1, st1) ==> P res1 st1) /\
  (!res1 st1. kf st = (res1, st1) ==> P res1 st1) ==>
  P res st'
Proof
  rw[] >>
  drule value_result_typed_BoolTV >> strip_tac >>
  Cases_on `b` >> gvs[read_result_def, bind_def, return_def, switch_BoolV_def]
QED

Theorem read_value_result_no_type_error:
  value_result_typed tv tyv /\ tyv <> NoneTV /\ (!t b. tyv <> ArrayTV t b) /\
  read_result cx tv st = (res, st') ==>
  no_type_error_result res
Proof
  rw[] >>
  drule_all value_result_is_value >> strip_tac >>
  gvs[read_result_def, return_def, no_type_error_result_def]
QED

Theorem read_value_result_String_no_type_error:
  value_result_typed tv (BaseTV (StringT n)) /\
  read_result cx tv st = (res, st') ==>
  no_type_error_result res
Proof
  rw[] >>
  drule value_result_typed_StringTV >> strip_tac >>
  gvs[read_result_def, return_def, no_type_error_result_def]
QED

Theorem read_value_result_String_success:
  value_result_typed tv (BaseTV (StringT n)) /\
  read_result cx tv st = (INL v, st') ==>
  ?s. v = StringV s
Proof
  rw[] >> drule value_result_typed_StringTV >> strip_tac >> gvs[read_result_def, return_def]
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

Theorem read_result_no_type_error:
  read_result cx tv st = (INR e, st') ==>
  (!tyv. value_result_typed tv tyv ==> tyv = NoneTV) \/
  (!m. e <> Error (TypeError m))
Proof
  Cases_on `tv` >>
  simp[read_result_def, value_result_typed_def, return_def, raise_def]
QED

Theorem read_result_Value_no_type_error:
  read_result cx (Value v) st <> (INR (Error (TypeError m)), st')
Proof
  simp[read_result_def, return_def]
QED

Theorem read_result_typed_non_none_no_type_error:
  read_result cx tv st = (INR e, st') /\ value_result_typed tv tyv /\ tyv <> NoneTV ==>
  !m. e <> Error (TypeError m)
Proof
  metis_tac[read_result_no_type_error]
QED

Definition expr_runtime_typed_def:
  expr_runtime_typed env e tvl <=>
    ?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
         value_result_typed tvl tv
End

Theorem read_result_runtime_typed_no_type_error:
  expr_runtime_typed env e tv /\ evaluate_type env.type_defs (expr_type e) = SOME tyv /\ tyv <> NoneTV /\
  read_result cx tv st = (INR err, st') ==>
  !m. err <> Error (TypeError m)
Proof
  rw[expr_runtime_typed_def] >> gvs[] >> metis_tac[read_result_no_type_error]
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

Definition runtime_consistent_def:
  runtime_consistent env cx st <=>
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts
End

Definition target_path_step_type_def:
  (target_path_step_type env (HashMapT kt vt) sb next_vt <=>
    case sb of
    | ValueSubscript key =>
        next_vt = vt /\ hashmap_key_type kt /\
        ?ktv. evaluate_type env.type_defs kt = SOME ktv /\ value_has_type ktv key
    | _ => F) /\
  (target_path_step_type env (Type (ArrayT elem_ty len)) sb next_vt <=>
    case sb of ValueSubscript (IntV _) => next_vt = Type elem_ty | _ => F) /\
  (target_path_step_type env (Type (StructT s)) sb next_vt <=>
    case sb of
    | AttrSubscript id =>
        ?field_ty. next_vt = Type field_ty /\
          attribute_type env.type_defs (StructT s) id = SOME field_ty
    | _ => F) /\
  (target_path_step_type env (Type (BaseT b)) sb next_vt <=> F) /\
  (target_path_step_type env (Type (TupleT ts)) sb next_vt <=> F) /\
  (target_path_step_type env (Type (FlagT name)) sb next_vt <=> F) /\
  (target_path_step_type env (Type NoneT) sb next_vt <=> F)
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
    !v. place_vtype_path_typed env loc_vt (path ++ [ValueSubscript v]) vt)
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
  rw[target_path_type_def] >>
  qexists_tac `Type (StructT s)` >> simp[target_path_step_type_def]
QED

Theorem target_path_type_hashmap_cons:
  target_path_type env loc_vt sbs (HashMapT kt vt) /\
  hashmap_key_type kt /\ evaluate_type env.type_defs kt = SOME ktv /\
  value_has_type ktv v ==>
  target_path_type env loc_vt (ValueSubscript v::sbs) vt
Proof
  rw[target_path_type_def] >>
  qexists_tac `HashMapT kt vt` >> simp[target_path_step_type_def] >>
  goal_assum drule
QED

Theorem target_path_type_array_cons:
  target_path_type env loc_vt sbs (Type (ArrayT elem_ty len)) ==>
  target_path_type env loc_vt (ValueSubscript (IntV i)::sbs) (Type elem_ty)
Proof
  rw[target_path_type_def] >>
  qexists_tac `Type (ArrayT elem_ty len)` >> simp[target_path_step_type_def]
QED

Theorem target_path_type_subscript_cons:
  target_path_type env loc_vt sbs vt /\
  subscript_vtype vt idx_ty = SOME result_vt /\
  (case vt of
   | HashMapT kt _ => ?v ktv. sb = ValueSubscript v /\
                              evaluate_type env.type_defs kt = SOME ktv /\
                              value_has_type ktv v
   | Type (ArrayT _ _) => ?i. sb = ValueSubscript (IntV i)
   | _ => T) ==>
  target_path_type env loc_vt (sb::sbs) result_vt
Proof
  strip_tac >>
  Cases_on `vt`
  >- (
    Cases_on `t` >> gvs[subscript_vtype_def] >>
    gvs[] >>
    simp[target_path_type_def] >>
    goal_assum drule >> simp[target_path_step_type_def]) >>
  gvs[subscript_vtype_def] >>
  gvs[] >>
  simp[target_path_type_def] >>
  qexists_tac `HashMapT idx_ty result_vt` >> simp[target_path_step_type_def] >>
  goal_assum drule
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

Theorem leaf_type_snoc:
  leaf_type base_tv (path ++ [sb]) = leaf_type (leaf_type base_tv path) [sb]
Proof
  simp[leaf_type_append]
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

Theorem place_leaf_path_typed_evaluate:
  !path loc_vt ty final_tv.
    place_leaf_path_typed env loc_vt path ty final_tv ==>
    evaluate_type env.type_defs ty = SOME final_tv
Proof
  Induct >> Cases_on `loc_vt` >> gvs[place_leaf_path_typed_def] >>
  metis_tac[]
QED

Theorem place_leaf_path_typed_array_append:
  !path loc_vt mid_tv.
    place_leaf_path_typed env loc_vt path (ArrayT elem_ty len) mid_tv ==>
    ?elem_tv. place_leaf_path_typed env loc_vt
      (path ++ [ValueSubscript (IntV i)]) elem_ty elem_tv
Proof
  Induct >> Cases_on `loc_vt` >> simp[place_leaf_path_typed_def]
  >- (
    rpt gen_tac >> strip_tac >>
    gvs[evaluate_type_def, AllCaseEqs(), leaf_type_def])
  >- (
    rpt gen_tac >> strip_tac >>
    gvs[evaluate_type_def, AllCaseEqs()] >>
    `leaf_type base_tv (h::(path ++ [ValueSubscript (IntV i)])) =
     leaf_type (leaf_type base_tv (h::path)) [ValueSubscript (IntV i)]` by
      (qspec_then `base_tv` (qspec_then `h::path` (qspec_then `[ValueSubscript (IntV i)]` mp_tac)) leaf_type_append >> simp[]) >>
    pop_assum SUBST_ALL_TAC >>
    pop_assum (SUBST1_TAC o SYM) >>
    simp[leaf_type_def]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[place_leaf_path_typed_def] >>
  goal_assum drule
QED

Theorem place_leaf_path_typed_struct_append:
  !path loc_vt mid_tv.
    place_leaf_path_typed env loc_vt path (StructT s) mid_tv /\
    attribute_type env.type_defs (StructT s) id = SOME field_ty ==>
    ?field_tv. place_leaf_path_typed env loc_vt
      (path ++ [AttrSubscript id]) field_ty field_tv
Proof
  rpt gen_tac >> strip_tac >>
  `evaluate_type env.type_defs (StructT s) = SOME mid_tv` by
    metis_tac[place_leaf_path_typed_evaluate] >>
  Cases_on `mid_tv` >> gvs[evaluate_type_def, AllCaseEqs()] >>
  `evaluate_type env.type_defs (StructT s) = SOME (StructTV (ZIP (MAP FST args,tvs)))` by
    simp[evaluate_type_def] >>
  drule_all attribute_type_evaluates >> strip_tac >>
  `ALOOKUP (ZIP (MAP FST args,tvs)) id = SOME tv` by metis_tac[] >>
  qexists_tac `tv` >>
  qpat_x_assum `place_leaf_path_typed env loc_vt path (StructT s) (StructTV (ZIP (MAP FST args,tvs)))` mp_tac >>
  qid_spec_tac `loc_vt` >> qid_spec_tac `path` >>
  Induct >> Cases_on `loc_vt` >> gvs[place_leaf_path_typed_def]
  >- (
    rpt gen_tac >> strip_tac >>
    gvs[leaf_type_append] >>
    Cases_on `base_tv` >> fs[leaf_type_def])
  >- (
    rpt gen_tac >> strip_tac >>
    gvs[leaf_type_append] >>
    `leaf_type base_tv (h::path) = StructTV (ZIP (MAP FST args,tvs))` by gvs[] >>
    `h::(path ++ [AttrSubscript id]) = (h::path) ++ [AttrSubscript id]` by simp[] >>
    pop_assum SUBST_ALL_TAC >>
    `leaf_type base_tv ((h::path) ++ [AttrSubscript id]) =
     leaf_type (leaf_type base_tv (h::path)) [AttrSubscript id]` by
      (irule leaf_type_append) >>
    pop_assum SUBST_ALL_TAC >>
    Cases_on `leaf_type base_tv (h::path)` >> fs[leaf_type_def]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[place_leaf_path_typed_def] >>
  goal_assum drule
QED

Theorem place_vtype_path_typed_hashmap_step:
  place_vtype_path_typed env loc_vt path (HashMapT kt vt) ==>
  place_vtype_path_typed env loc_vt (path ++ [ValueSubscript key]) vt
Proof
  simp[place_vtype_path_typed_def]
QED

Theorem place_vtype_path_typed_array_step:
  place_vtype_path_typed env loc_vt path (Type (ArrayT elem_ty len)) ==>
  place_vtype_path_typed env loc_vt
    (path ++ [ValueSubscript (IntV i)]) (Type elem_ty)
Proof
  simp[place_vtype_path_typed_def] >> strip_tac >>
  drule place_leaf_path_typed_array_append >> simp[]
QED

Theorem place_vtype_path_typed_struct_step:
  place_vtype_path_typed env loc_vt path (Type (StructT s)) /\
  attribute_type env.type_defs (StructT s) id = SOME field_ty ==>
  place_vtype_path_typed env loc_vt
    (path ++ [AttrSubscript id]) (Type field_ty)
Proof
  simp[place_vtype_path_typed_def] >> strip_tac >>
  drule_all place_leaf_path_typed_struct_append >> simp[]
QED

Theorem place_leaf_path_typed_hashmap_root_cons:
  !path ty final_tv.
    place_leaf_path_typed env vt path ty final_tv ==>
    place_leaf_path_typed env (HashMapT kt vt) (ValueSubscript key :: path) ty final_tv
Proof
  simp[place_leaf_path_typed_def]
QED

Theorem place_vtype_path_typed_hashmap_root_cons:
  !endpoint path.
    place_vtype_path_typed env vt path endpoint ==>
    place_vtype_path_typed env (HashMapT kt vt) (ValueSubscript key :: path) endpoint
Proof
  Induct >> rw[place_vtype_path_typed_def]
  >- metis_tac[place_leaf_path_typed_hashmap_root_cons] >>
  first_x_assum drule >>
  disch_then (qspec_then `v'` mp_tac) >>
  simp[APPEND]
QED

Theorem well_formed_vtype_place_vtype_path_typed_refl:
  !vt. well_formed_vtype env.type_defs vt ==>
       place_vtype_path_typed env vt [] vt
Proof
  Induct >> rw[well_formed_vtype_def, place_vtype_path_typed_def]
  >- (
    gvs[well_formed_type_def, IS_SOME_EXISTS] >>
    qexists_tac `x` >> simp[place_leaf_path_typed_def, leaf_type_def]) >>
  first_x_assum drule >> strip_tac >>
  drule place_vtype_path_typed_hashmap_root_cons >> simp[]
QED

Theorem place_vtype_path_typed_step:
  place_vtype_path_typed env loc_vt path mid_vt /\
  target_path_step_type env mid_vt sb next_vt ==>
  place_vtype_path_typed env loc_vt (path ++ [sb]) next_vt
Proof
  Cases_on `mid_vt` >> rw[target_path_step_type_def]
  >- (
    Cases_on `t` >> fs[target_path_step_type_def]
    >- (
      Cases_on `sb` >> fs[target_path_step_type_def] >>
      Cases_on `v` >> fs[target_path_step_type_def] >>
      drule place_vtype_path_typed_array_step >> simp[]) >>
    Cases_on `sb` >> fs[target_path_step_type_def] >>
    drule_all place_vtype_path_typed_struct_step >> simp[]) >>
  Cases_on `sb` >> fs[target_path_step_type_def] >>
  drule place_vtype_path_typed_hashmap_step >>
  simp[]
QED

Theorem target_path_type_to_place_vtype_path_typed:
  well_formed_vtype env.type_defs loc_vt /\
  target_path_type env loc_vt sbs vt ==>
  place_vtype_path_typed env loc_vt (REVERSE sbs) vt
Proof
  MAP_EVERY qid_spec_tac [`vt`, `sbs`] >>
  Induct >> rw[target_path_type_def]
  >- gvs[well_formed_vtype_place_vtype_path_typed_refl] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all place_vtype_path_typed_step >> simp[]
QED

Theorem target_path_type_Type_place_leaf_typed:
  well_formed_vtype env.type_defs loc_vt /\
  target_path_type env loc_vt sbs (Type ty) ==>
  ?final_tv. place_leaf_typed env loc_vt sbs ty final_tv
Proof
  rw[place_leaf_typed_def] >>
  drule_all target_path_type_to_place_vtype_path_typed >>
  simp[place_vtype_path_typed_def]
QED

Theorem target_path_type_Type_evaluate_leaf:
  !env t sbs ty root_tv.
    well_formed_vtype env.type_defs (Type t) ==>
    target_path_type env (Type t) sbs (Type ty) ==>
    evaluate_type env.type_defs t = SOME root_tv ==>
    evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs))
Proof
  rpt strip_tac >>
  drule target_path_type_Type_place_leaf_typed >>
  simp[] >>
  strip_tac >>
  pop_assum mp_tac >>
  simp[place_leaf_typed_def, place_leaf_path_typed_def] >>
  strip_tac >>
  gvs[]
QED

Theorem target_path_type_Type_evaluate_leaf_not_NoneTV:
  !env t sbs ty root_tv tenv.
    well_formed_vtype env.type_defs (Type t) ==>
    target_path_type env (Type t) sbs (Type ty) ==>
    evaluate_type env.type_defs t = SOME root_tv ==>
    assignable_type env.type_defs ty ==>
    leaf_type root_tv (REVERSE sbs) <> NoneTV
Proof
  rpt strip_tac >>
  drule target_path_type_Type_evaluate_leaf >>
  simp[] >>
  metis_tac[assignable_type_evaluate_not_NoneTV]
QED

Definition assign_operation_runtime_typed_def:
  (assign_operation_runtime_typed env ty (Replace v) <=> value_runtime_typed env ty v) /\
  (assign_operation_runtime_typed env ty (AppendOp v) <=>
     ?elem_tv elem_ty n. evaluate_type env.type_defs elem_ty = SOME elem_tv /\
       ty = ArrayT elem_ty (Dynamic n) /\ value_has_type elem_tv v) /\
  (assign_operation_runtime_typed env ty PopOp <=>
     ?elem_tv elem_ty n. evaluate_type env.type_defs elem_ty = SOME elem_tv /\
       ty = ArrayT elem_ty (Dynamic n))
End
