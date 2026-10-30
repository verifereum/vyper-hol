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

Theorem read_value_result_no_type_error:
  value_result_typed tv tyv /\ tyv <> NoneTV /\ (!t b. tyv <> ArrayTV t b) /\
  read_result cx tv st = (res, st') ==>
  no_type_error_result res
Proof
  rw[] >>
  drule_all value_result_is_value >> strip_tac >>
  gvs[read_result_def, return_def, no_type_error_result_def]
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

Definition expr_runtime_typed_def:
  expr_runtime_typed env e tvl <=>
    ?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
         value_result_typed tvl tv
End

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

Definition assign_operation_runtime_typed_def:
  (assign_operation_runtime_typed env ty (Replace v) <=> value_runtime_typed env ty v) /\
  (assign_operation_runtime_typed env ty (AppendOp v) <=>
     ?elem_tv elem_ty n. evaluate_type env.type_defs elem_ty = SOME elem_tv /\
       ty = ArrayT elem_ty (Dynamic n) /\ value_has_type elem_tv v) /\
  (assign_operation_runtime_typed env ty PopOp <=>
     ?elem_tv elem_ty n. evaluate_type env.type_defs elem_ty = SOME elem_tv /\
       ty = ArrayT elem_ty (Dynamic n))
End
