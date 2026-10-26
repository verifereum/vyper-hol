Theory vyperPlaceResultTyping
Ancestors
  list option pair finite_map vyperState vyperTyping vyperTypeExprResult
  vyperPlaceTyping vyperPlaceInvariants vyperTypeInvariants
  vyperTypeStatePreservation vyperPlaceStatePreservation vyperInterpreter vyperArray
  vyperScopePreservation vyperPlaceFrames vyperStatePreservation vyperTypeEnv
  vyperTypeValues vyperTypeSystem vyperTypeExprSoundness
  vyperCallOutcomeFrame vyperCallOutcome[ignore_grammar]
  vyperTypeCallStackSoundness vyperTypeCallGraph vyperTypeCallGraphSoundness
  vyperTypeStmtResult vyperCreateFrame
Libs
  wordsLib

Theorem evaluate_subscripts_typed_leaf_path:
  !path tv a v.
    value_has_type tv a /\ well_formed_type_value tv /\
    evaluate_subscripts tv a path = INL v /\ leaf_type tv path <> NoneTV ==>
    subscripts_type tv path = SOME (leaf_type tv path)
Proof
  Induct >> simp[subscripts_type_def, evaluate_subscripts_def, leaf_type_def] >>
  gen_tac >> Cases_on `h`
  >- (Cases_on `v` >> rpt gen_tac >> strip_tac >>
      gvs[evaluate_subscripts_def, AllCaseEqs()] >>
      Cases_on `tv` >> gvs[value_has_type_def, leaf_type_def,
        subscripts_type_def, subscript_type_def] >>
      drule_at (Pat `array_index _ _ _ = _`) array_index_declared_type_exists >>
      disch_then (qspec_then `ArrayTV t b` mp_tac) >> simp[] >> strip_tac >>
      gvs[subscript_type_def] >>
      rename1 `array_index (ArrayTV t b) av i = SOME child` >>
      `well_formed_type_value t` by gvs[well_formed_type_value_def] >>
      `value_has_type t child` by metis_tac[vyperAssignPreservesTypeTheory.array_index_has_type] >>
      first_x_assum irule >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[evaluate_subscripts_def, AllCaseEqs()] >>
  Cases_on `a` >> gvs[evaluate_subscripts_def, AllCaseEqs()] >>
  Cases_on `tv` >> gvs[value_has_type_def] >>
  drule_all vyperAssignPreservesTypeTheory.struct_field_has_type >> strip_tac >>
  rename1 `ALOOKUP l' s = SOME field_tv` >>
  `well_formed_type_value field_tv` by
    (irule subscript_type_well_formed >>
     qexistsl_tac [`AttrSubscript s`, `StructTV l'`] >> simp[subscript_type_def]) >>
  gvs[subscripts_type_def, subscript_type_def, leaf_type_def] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem eval_result_typed_place[simp]:
  eval_result_typed (env,cx,st) (PlaceR p) (Type ty) <=>
  ?tv. evaluate_type env.type_defs ty = SOME tv /\ runtime_place_typed cx st p tv
Proof
  simp[eval_result_typed_def]
QED

Theorem eval_result_typed_place_not_mapping[simp]:
  ~eval_result_typed (env,cx,st) (PlaceR p) (HashMapT kt vt)
Proof
  simp[eval_result_typed_def]
QED

Theorem eval_result_typed_value[simp]:
  eval_result_typed (env,cx,st) (Value v) (Type ty) <=>
  ?tv. evaluate_type env.type_defs ty = SOME tv /\ value_has_type tv v
Proof
  simp[eval_result_typed_def]
QED

Theorem eval_result_typed_mapping[simp]:
  eval_result_typed (env,cx,st) (HashMapRef tr slot kt vt) (HashMapT kt' vt') <=>
  kt = kt' /\ vt = vt'
Proof
  simp[eval_result_typed_def]
QED

(* Fresh resolved memory paths read without consulting arbitrary old history. *)
(* A direct probe of why metadata typing alone is not delayed-read validity. *)
Theorem delayed_pop_value_probe[local]:
  read_memory_path
    <|assignable := T; type := ArrayTV (BaseTV (UintT 256)) (Dynamic 3);
      value := ArrayV (DynArrayV []);
      popped := [([ValueSubscript (IntV 0)],IntV 5)]|>
    [ValueSubscript (IntV 0)] = INL (IntV 5)
Proof
  EVAL_TAC >> simp[]
QED

Theorem delayed_nested_pop_value_probe[local]:
  let tv = ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 3)) (Dynamic 3);
      entry = <|assignable := T; type := tv; value := ArrayV (DynArrayV []);
        popped := [([ValueSubscript (IntV 0)],ArrayV (DynArrayV [IntV 1]));
                   ([ValueSubscript (IntV 0); ValueSubscript (IntV 1)],IntV 2)]|>
  in read_memory_path entry [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] = INL (IntV 1) /\
     read_memory_path entry [ValueSubscript (IntV 0); ValueSubscript (IntV 1)] = INL (IntV 2)
Proof
  EVAL_TAC >> simp[subscript_type_def] >> EVAL_TAC
QED


(* A metadata frame intentionally makes no bounds claim. *)
(* Only the prefix created in a live-place region is trusted. *)
Definition memory_path_covered_def:
  memory_path_covered tv current fresh path <=>
    (?v. evaluate_subscripts tv current path = INL v) \/
    (?v. read_popped tv path fresh = SOME v)
End

Definition memory_history_region_def:
  memory_history_region entry fresh old paths <=>
    entry.popped = fresh ++ old /\
    popped_history_typed entry.type fresh /\
    EVERY (memory_path_covered entry.type entry.value fresh) paths
End

Theorem read_popped_prefix_noninterference:
  !fresh tv path v old.
    read_popped tv path fresh = SOME v ==>
    read_popped tv path (fresh ++ old) = SOME v
Proof
  Induct >> simp[read_popped_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[read_popped_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem fresh_path_covered[simp]:
  memory_path_covered tv current [] path <=>
  ?v. evaluate_subscripts tv current path = INL v
Proof
  simp[memory_path_covered_def, read_popped_def]
QED

Theorem covered_memory_read:
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  memory_history_region entry fresh old paths /\ MEM path paths /\
  subscripts_type entry.type path = SOME tv ==>
  ?v. read_memory_path entry path = INL v /\ value_has_type tv v
Proof
  simp[memory_history_region_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum (drule_then mp_tac) >>
  simp[memory_path_covered_def] >> strip_tac
  >- (simp[read_memory_path_def] >> metis_tac[evaluate_subscripts_type]) >>
  Cases_on `evaluate_subscripts entry.type entry.value path` >>
  simp[read_memory_path_def]
  >- metis_tac[evaluate_subscripts_type] >>
  drule_all read_popped_prefix_noninterference >>
  disch_then (qspec_then `old` assume_tac) >>
  `missing_dynamic_element entry.type entry.value path` by
    metis_tac[typed_traversal_failure_is_dynamic_absence] >>
  simp[] >> metis_tac[read_popped_type]
QED
Theorem record_pop_prefix_split:
  record_pop path arr p (fresh ++ old) =
  record_pop path arr p fresh ++ old
Proof
  Cases_on `arr` >> simp[record_pop_def] >>
  Cases_on `a` >> simp[]
QED

(* Proof-only alias: all declared paths, including tuple indices. *)
Definition memory_eval_path_def:
  memory_eval_path tv path <=> ?ptv. subscripts_type tv path = SOME ptv
End

Theorem tuple_literal_subscript_source_probe:
  subscript_type_ok (TupleT [BaseT BoolT])
    (Literal (BaseT (UintT 256)) (IntL 0)) (BaseT BoolT)
Proof
  EVAL_TAC
QED

Theorem memory_eval_path_tuple_extension_probe:
  lookup_scopes id st.scopes = SOME entry /\
  entry.type = TupleTV [BaseTV BoolT] /\
  entry.value = ArrayV (TupleV [BoolV T]) ==>
  extend_place cx (PlaceR (MemoryPlace id []))
    (ValueSubscript (IntV 0)) st =
    (INL (PlaceR (MemoryPlace id [ValueSubscript (IntV 0)])),st) /\
  memory_eval_path entry.type [ValueSubscript (IntV 0)]
Proof
  rpt strip_tac >>
  gvs[extend_place_def, place_type_value_def, read_place_def,
       read_memory_path_def, get_scopes_def, lift_option_type_def,
       lift_sum_def, bind_def, ignore_bind_def, return_def,
       evaluate_subscripts_def, subscripts_type_def, subscript_type_def,
       vyperValueOperationTheory.array_index_def, oEL_def,
       extend_memory_place_def, memory_eval_path_def]
QED

(* Tuple selection preserves metadata, including sparse fixed defaults. *)
Theorem tuple_sparse_metadata_probe:
  subscripts_type (TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)])
    [ValueSubscript (IntV 0)] = SOME (ArrayTV (BaseTV BoolT) (Fixed 1)) /\
  evaluate_subscripts (TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)])
    (ArrayV (TupleV [ArrayV (SArrayV [])])) [ValueSubscript (IntV 0)] =
    INL (ArrayV (SArrayV [])) /\
  evaluate_subscripts (ArrayTV (BaseTV BoolT) (Fixed 1))
    (ArrayV (SArrayV [])) [ValueSubscript (IntV 0)] = INL (BoolV F) /\
  evaluate_subscripts (TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)])
    (ArrayV (TupleV [ArrayV (SArrayV [])]))
    [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] =
    INL (BoolV F)
Proof
  EVAL_TAC
QED

Theorem tuple_metadata_present_dense_probes:
  evaluate_subscripts (TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)])
    (ArrayV (TupleV [ArrayV (SArrayV [(0,BoolV T)])]))
    [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] = INL (BoolV T) /\
  evaluate_subscripts (TupleTV [ArrayTV (BaseTV BoolT) (Dynamic 1)])
    (ArrayV (TupleV [ArrayV (DynArrayV [BoolV T])]))
    [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] = INL (BoolV T) /\
  evaluate_subscripts (TupleTV [TupleTV [BaseTV BoolT]])
    (ArrayV (TupleV [ArrayV (TupleV [BoolV T])]))
    [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] = INL (BoolV T)
Proof
  EVAL_TAC
QED

Theorem tuple_metadata_nested_sparse_probes:
  evaluate_subscripts
    (TupleTV [StructTV [("f",ArrayTV (BaseTV BoolT) (Fixed 1))]])
    (ArrayV (TupleV [StructV [("f",ArrayV (SArrayV []))]]))
    [ValueSubscript (IntV 0); AttrSubscript "f"; ValueSubscript (IntV 0)] =
    INL (BoolV F) /\
  evaluate_subscripts
    (ArrayTV (TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)]) (Dynamic 1))
    (ArrayV (DynArrayV [ArrayV (TupleV [ArrayV (SArrayV [])])]))
    [ValueSubscript (IntV 0); ValueSubscript (IntV 0); ValueSubscript (IntV 0)] =
    INL (BoolV F)
Proof
  EVAL_TAC
QED

Theorem tuple_sparse_delayed_read_probe:
  lookup_scopes id st.scopes = SOME entry /\
  entry.type = TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)] /\
  entry.value = ArrayV (TupleV [ArrayV (SArrayV [])]) /\ entry.popped = [] ==>
  extend_place cx
    (PlaceR (MemoryPlace id [ValueSubscript (IntV 0)]))
    (ValueSubscript (IntV 0)) st =
    (INL (PlaceR (MemoryPlace id
      [ValueSubscript (IntV 0); ValueSubscript (IntV 0)])),st) /\
  read_memory_path entry [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] =
    INL (BoolV F)
Proof
  rpt strip_tac >>
  gvs[extend_place_def, place_type_value_def, read_place_def, read_memory_path_def,
      get_scopes_def, lift_option_type_def, lift_sum_def, bind_def, ignore_bind_def,
      return_def, evaluate_subscripts_def, subscripts_type_def, subscript_type_def,
      vyperValueOperationTheory.array_index_def, oEL_def, vyperValueTheory.default_value_def,
      extend_memory_place_def, read_popped_def]
QED

Theorem tuple_sparse_old_history_probe:
  entry.type = TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)] /\
  entry.value = ArrayV (TupleV [ArrayV (SArrayV [])]) /\
  entry.popped = [([ValueSubscript (IntV 0); ValueSubscript (IntV 0)],IntV 7)] ==>
  read_memory_path entry [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] =
    INL (BoolV F) /\ value_has_type (BaseTV BoolT) (BoolV F)
Proof
  rpt strip_tac >>
  gvs[read_memory_path_def, read_popped_def, evaluate_subscripts_def,
      subscripts_type_def, subscript_type_def,
      vyperValueOperationTheory.array_index_def, oEL_def, value_has_type_def,
      rich_listTheory.DROP_LENGTH_APPEND, vyperValueTheory.default_value_def]
QED

Theorem tuple_sparse_trusted_parent_probe:
  entry.type = TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)] /\
  entry.value = ArrayV (TupleV [ArrayV (SArrayV [])]) ==>
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  memory_history_region entry [] entry.popped [[ValueSubscript (IntV 0)]]
Proof
  rpt strip_tac >>
  gvs[value_has_type_def, well_formed_type_value_def, memory_history_region_def,
      popped_history_typed_def, memory_path_covered_def, evaluate_subscripts_def,
      vyperValueOperationTheory.array_index_def, oEL_def] >> EVAL_TAC
QED

Theorem evaluate_subscripts_append:
  !path tv ptv a v suffix.
    subscripts_type tv path = SOME ptv /\
    evaluate_subscripts tv a path = INL v ==>
    evaluate_subscripts tv a (path ++ suffix) =
    evaluate_subscripts ptv v suffix
Proof
  Induct >> simp[subscripts_type_def, evaluate_subscripts_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[subscripts_type_def, AllCaseEqs()] >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (fn th =>
    qspecl_then [`path`,`a`] assume_tac th >>
    qspecl_then [`path ++ suffix`,`a`] assume_tac th) >>
  Cases_on `evaluate_subscripts tv a [h]` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem subscripts_type_append:
  !prefix tv ptv rest.
    subscripts_type tv prefix = SOME ptv ==>
    subscripts_type tv (prefix ++ rest) = subscripts_type ptv rest
Proof
  Induct >> simp[subscripts_type_def] >> rpt strip_tac >>
  gvs[subscripts_type_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem memory_eval_path_append:
  !prefix tv rest ptv.
    subscripts_type tv prefix = SOME ptv ==>
    (memory_eval_path tv (prefix ++ rest) <=>
     memory_eval_path tv prefix /\ memory_eval_path ptv rest)
Proof
  rpt strip_tac >> simp[memory_eval_path_def] >>
  drule subscripts_type_append >> simp[]
QED

Theorem read_popped_snapshot_extend:
  subscripts_type tv path = SOME ptv /\
  IS_PREFIX path prefix /\ subscripts_type tv prefix = SOME prefix_tv /\
  evaluate_subscripts prefix_tv saved (DROP (LENGTH prefix) path) = INL v /\
  evaluate_subscripts ptv v suffix = INL w ==>
  IS_PREFIX (path ++ suffix) prefix /\
  evaluate_subscripts prefix_tv saved
    (DROP (LENGTH prefix) (path ++ suffix)) = INL w
Proof
  simp[rich_listTheory.IS_PREFIX_APPEND] >> rpt strip_tac >> gvs[] >>
  gvs[rich_listTheory.DROP_LENGTH_APPEND] >>
  drule_all subscripts_type_append >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  drule_all evaluate_subscripts_append >> simp[]
QED

Theorem typed_snapshot_failure[local]:
  subscripts_type tv prefix = SOME ptv /\
  subscripts_type tv path = SOME vtv /\ IS_PREFIX path prefix /\
  value_has_type ptv saved /\ well_formed_type_value ptv /\
  evaluate_subscripts ptv saved (DROP (LENGTH prefix) path) = INR err ==>
  missing_dynamic_element ptv saved (DROP (LENGTH prefix) path)
Proof
  simp[rich_listTheory.IS_PREFIX_APPEND] >> rpt strip_tac >> gvs[] >>
  gvs[rich_listTheory.DROP_LENGTH_APPEND] >>
  qpat_assum `subscripts_type tv prefix = SOME ptv`
    (mp_then Any mp_tac subscripts_type_append) >>
  disch_then (qspec_then `l` assume_tac) >>
  irule typed_traversal_failure_is_dynamic_absence >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem read_popped_success_extend:
  !fresh tv path ptv v suffix w wtv.
    popped_history_typed tv fresh /\
    subscripts_type tv path = SOME ptv /\
    subscripts_type ptv suffix = SOME wtv /\
    read_popped tv path fresh = SOME v /\
    evaluate_subscripts ptv v suffix = INL w ==>
    ?z. read_popped tv (path ++ suffix) fresh = SOME z
Proof
  Induct >- simp[read_popped_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[read_popped_def] >> rpt strip_tac >>
  `popped_history_typed tv fresh` by
    gvs[popped_history_typed_def] >>
  `?htv. subscripts_type tv h0 = SOME htv /\
          well_formed_type_value htv /\ value_has_type htv h1` by
    gvs[popped_history_typed_def] >>
  `subscripts_type tv (path ++ suffix) = SOME wtv` by
    metis_tac[subscripts_type_append] >>
  gvs[AllCaseEqs()] >>
  TRY (drule_all read_popped_snapshot_extend >> strip_tac >>
       simp[] >> NO_TAC) >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `IS_PREFIX (path ++ suffix) h0` >> simp[] >>
  TRY (qexists_tac `z` >> simp[] >> NO_TAC) >>
  Cases_on `subscripts_type tv h0` >> gvs[] >>
  TRY (qexists_tac `z` >> simp[] >> NO_TAC) >>
  rename1 `subscripts_type tv h0 = SOME htv` >>
  Cases_on `evaluate_subscripts htv h1 (DROP (LENGTH h0) (path ++ suffix))` >>
  simp[] >> metis_tac[typed_snapshot_failure]
QED

Theorem memory_history_region_extend:
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  subscripts_type entry.type path = SOME ptv /\
  memory_history_region entry fresh old paths /\ MEM path paths /\
  read_memory_path entry path = INL v /\
  evaluate_subscripts ptv v suffix = INL w ==>
  memory_history_region entry fresh old ((path ++ suffix)::paths)
Proof
  rpt strip_tac >>
  `value_has_type ptv v` by
    (drule_all covered_memory_read >> strip_tac >> gvs[]) >>
  `well_formed_type_value ptv` by metis_tac[subscripts_type_well_formed] >>
  `?wtv. subscripts_type ptv suffix = SOME wtv` by
    metis_tac[evaluate_subscripts_declared_type_exists] >>
  gvs[memory_history_region_def, EVERY_MEM] >>
  simp[] >> rpt strip_tac >> gvs[] >>
  TRY (first_x_assum irule >> simp[] >> NO_TAC) >>
  qpat_x_assum `!x. MEM x paths ==> _` (qspec_then `path` mp_tac) >>
  simp[memory_path_covered_def] >> strip_tac
  >- (gvs[read_memory_path_def] >>
      disj1_tac >> metis_tac[evaluate_subscripts_append]) >>
  Cases_on `evaluate_subscripts entry.type entry.value path`
  >- (gvs[read_memory_path_def] >>
      disj1_tac >> metis_tac[evaluate_subscripts_append]) >>
  drule_all read_popped_prefix_noninterference >>
  disch_then (qspec_then `old` assume_tac) >>
  gvs[read_memory_path_def] >> disj2_tac >>
  qpat_x_assum `read_popped _ _ (fresh ++ old) = _` kall_tac >>
  drule_all read_popped_success_extend >> simp[]
QED

(* Real nested PopOp updates; the old history suffix is completely arbitrary. *)
Theorem nested_pop_region_probe[local]:
  let tv = ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 3)) (Dynamic 3);
      before = ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 1; IntV 2])]);
      middle = ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 1])]);
      child = [ValueSubscript (IntV 0)];
      fresh1 = record_pop child (ArrayV (DynArrayV [IntV 1; IntV 2])) (IntV 2) [];
      fresh2 = record_pop [] middle (ArrayV (DynArrayV [IntV 1])) fresh1;
      entry = <|assignable := T; type := tv; value := ArrayV (DynArrayV []);
                popped := fresh2 ++ old|>
  in assign_subscripts tv before child PopOp = INL middle /\
     assign_subscripts tv middle [] PopOp = INL entry.value /\
     memory_history_region entry fresh2 old
       [[ValueSubscript (IntV 0); ValueSubscript (IntV 0)];
        [ValueSubscript (IntV 0); ValueSubscript (IntV 1)]]
Proof
  simp[LET_THM, memory_history_region_def, memory_path_covered_def,
    record_pop_def, popped_history_typed_def] >>
  EVAL_TAC >> simp[subscript_type_def] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, value_has_type_def, well_formed_type_value_def] >>
  rpt strip_tac >> gvs[] >>
  simp[subscripts_type_def, subscript_type_def, vyperASTTheory.bound_length_def] >>
  EVAL_TAC >> simp[value_has_type_def, well_formed_type_value_def,
    wordsTheory.dimword_def]
QED

Theorem unrelated_pop_region_probe[local]:
  let tv = ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 3)) (Dynamic 3);
      before = ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 1]);
                                 ArrayV (DynArrayV [IntV 2])]);
      after = ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 1]);
                                ArrayV (DynArrayV [])]);
      child = [ValueSubscript (IntV 1)];
      fresh = record_pop child (ArrayV (DynArrayV [IntV 2])) (IntV 2) [];
      entry = <|assignable := T; type := tv; value := after;
                popped := fresh ++ old|>
  in assign_subscripts tv before child PopOp = INL after /\
     memory_history_region entry fresh old
       [[ValueSubscript (IntV 0); ValueSubscript (IntV 0)]]
Proof
  simp[LET_THM, memory_history_region_def, memory_path_covered_def,
    record_pop_def, popped_history_typed_def] >> EVAL_TAC >>
  rpt strip_tac >> gvs[] >>
  simp[subscripts_type_def, subscript_type_def, vyperASTTheory.bound_length_def] >>
  EVAL_TAC >> simp[value_has_type_def, well_formed_type_value_def,
    wordsTheory.dimword_def]
QED

(* Typechecks the actual twelve predicate slots without changing soundness. *)
Theorem read_popped_new_snapshot:
  subscripts_type tv prefix = SOME ptv /\ IS_PREFIX path prefix /\
  evaluate_subscripts ptv p (DROP (LENGTH prefix) path) = INL v ==>
  read_popped tv path ((prefix,p)::history) = SOME v
Proof
  simp[read_popped_def]
QED

Theorem root_pop_removed_element:
  LENGTH xs < n /\ evaluate_subscripts etv p path = INL v ==>
  read_popped (ArrayTV etv (Dynamic n))
    (ValueSubscript (IntV &(LENGTH xs))::path)
    (record_pop [] (ArrayV (DynArrayV (SNOC p xs))) p history) = SOME v
Proof
  simp[record_pop_def, evaluate_subscripts_def, LENGTH_SNOC] >> strip_tac >>
  irule read_popped_new_snapshot >>
  simp[subscripts_type_def, subscript_type_def, vyperASTTheory.bound_length_def]
QED

Theorem root_pop_current_survives:
  LENGTH xs < n /\
  evaluate_subscripts (ArrayTV etv (Dynamic n))
    (ArrayV (DynArrayV (SNOC p xs))) path = INL v ==>
  (?w. evaluate_subscripts (ArrayTV etv (Dynamic n))
         (ArrayV (DynArrayV xs)) path = INL w) \/
  (?w. read_popped (ArrayTV etv (Dynamic n)) path
         (record_pop [] (ArrayV (DynArrayV (SNOC p xs))) p []) = SOME w)
Proof
  Cases_on `path` >- simp[evaluate_subscripts_def] >>
  rename1 `sb::rest` >> Cases_on `sb` >>
  simp[evaluate_subscripts_def] >>
  rename1 `ValueSubscript a` >> Cases_on `a` >>
  simp[evaluate_subscripts_def] >>
  rename1 `IntV i` >>
  simp[vyperValueOperationTheory.array_index_def, oEL_THM,
    AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `Num i < LENGTH xs`
  >- (disj1_tac >> qexists_tac `v` >> gvs[EL_SNOC]) >>
  `Num i = LENGTH xs` by decide_tac >>
  `i = &(LENGTH xs)` by intLib.ARITH_TAC >> gvs[EL_SNOC] >>
  qexists_tac `v` >> irule root_pop_removed_element >> simp[] >>
  gvs[SNOC_APPEND, EL_APPEND_EQN]
QED

Theorem record_pop_rebase:
  record_pop (sb::popPath) arr p [] =
    MAP (\(path,v). (sb::path,v)) (record_pop popPath arr p [])
Proof
  Cases_on `arr` >> simp[record_pop_def] >>
  Cases_on `a` >> simp[]
QED

Theorem dynamic_root_pop_survival:
  LENGTH vs <= n /\
  assign_subscripts (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs)) [] PopOp = INL current' /\
  popped_value (ArrayV (DynArrayV vs)) = INL p /\
  evaluate_subscripts (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs)) path = INL v ==>
  (?w. evaluate_subscripts (ArrayTV etv (Dynamic n)) current' path = INL w) \/
  (?w. read_popped (ArrayTV etv (Dynamic n)) path
         (record_pop [] (ArrayV (DynArrayV vs)) p []) = SOME w)
Proof
  Cases_on `vs` using SNOC_CASES
  >- simp[assign_subscripts_def, vyperValueOperationTheory.pop_element_def] >>
  simp[assign_subscripts_def, vyperValueOperationTheory.pop_element_def,
    vyperValueOperationTheory.popped_value_def] >>
  rpt strip_tac >> gvs[] >> irule root_pop_current_survives >>
  simp[] >> metis_tac[]
QED

Theorem read_popped_rebase:
  !history tv etv sb path.
    subscript_type tv sb = SOME etv ==>
    read_popped tv (sb::path) (MAP (\(prefix,p). (sb::prefix,p)) history) =
    read_popped etv path history
Proof
  Induct >- simp[read_popped_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`tv`,`etv`,`sb`,`path`] mp_tac) >>
  simp[] >> disch_tac >> simp[read_popped_def, subscripts_type_def]
QED

Theorem array_child_path_survival:
  array_index (ArrayTV etv bd) av i = SOME child /\
  array_set_index (ArrayTV etv bd) av i child' = INL (ArrayV av') /\
  subscript_type (ArrayTV etv bd) (ValueSubscript (IntV i)) = SOME etv /\
  (!path v. evaluate_subscripts etv child path = INL v ==>
    (?w. evaluate_subscripts etv child' path = INL w) \/
    (?w. read_popped etv path history = SOME w)) /\
  evaluate_subscripts (ArrayTV etv bd) (ArrayV av) path = INL v ==>
  (?w. evaluate_subscripts (ArrayTV etv bd) (ArrayV av') path = INL w) \/
  (?w. read_popped (ArrayTV etv bd) path
      (MAP (\(prefix,p). (ValueSubscript (IntV i)::prefix,p)) history) = SOME w)
Proof
  strip_tac >>
  Cases_on `path` >- simp[evaluate_subscripts_def] >>
  rename1 `sb::rest` >> Cases_on `sb` >> gvs[evaluate_subscripts_def] >>
  rename1 `ValueSubscript a` >> Cases_on `a` >> gvs[evaluate_subscripts_def] >>
  rename1 `IntV j` >> Cases_on `i = j`
  >- (gvs[] >> drule array_index_after_set_same >> strip_tac >> gvs[AllCaseEqs()] >>
      first_x_assum drule >> strip_tac
      >- metis_tac[] >>
      disj2_tac >> drule read_popped_rebase >>
      disch_then (qspecl_then [`history`,`rest`] mp_tac) >> simp[]) >>
  drule_all array_index_after_set_other >> strip_tac >> gvs[] >>
  disj1_tac >> metis_tac[]
QED

Theorem struct_child_path_survival:
  ALOOKUP fields id = SOME etv /\ ALOOKUP al id = SOME child /\
  (!path v. evaluate_subscripts etv child path = INL v ==>
    (?w. evaluate_subscripts etv child' path = INL w) \/
    (?w. read_popped etv path history = SOME w)) /\
  evaluate_subscripts (StructTV fields) (StructV al) path = INL v ==>
  (?w. evaluate_subscripts (StructTV fields)
         (StructV (AFUPDKEY id (K child') al)) path = INL w) \/
  (?w. read_popped (StructTV fields) path
      (MAP (\(prefix,p). (AttrSubscript id::prefix,p)) history) = SOME w)
Proof
  strip_tac >> Cases_on `path` >- simp[evaluate_subscripts_def] >>
  rename1 `sb::rest` >> Cases_on `sb`
  >- (rename1 `ValueSubscript a` >> Cases_on `a` >> gvs[evaluate_subscripts_def]) >>
  gvs[evaluate_subscripts_def] >>
  rename1 `AttrSubscript key` >> Cases_on `key = id`
  >- (gvs[evaluate_subscripts_def, alistTheory.AFUPDKEY_ALOOKUP,
        AllCaseEqs()] >> first_x_assum drule >> strip_tac
      >- metis_tac[] >>
      disj2_tac >>
      `subscript_type (StructTV fields) (AttrSubscript id) = SOME etv` by
        simp[subscript_type_def] >>
      drule read_popped_rebase >>
      disch_then (qspecl_then [`history`,`rest`] mp_tac) >> simp[]) >>
  simp[alistTheory.AFUPDKEY_ALOOKUP] >>
  Cases_on `ALOOKUP al key` >> gvs[] >> disj1_tac >> metis_tac[]
QED

Theorem array_set_result_shape:
  array_set_index tv av i child = INL result ==> ?av'. result = ArrayV av'
Proof
  Cases_on `av` >> simp[vyperValueOperationTheory.array_set_index_def,
    AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem pop_current_path_survival:
  !popPath tv current etv n current' arr p path v.
  value_has_type tv current /\ well_formed_type_value tv /\
  subscripts_type tv popPath = SOME (ArrayTV etv (Dynamic n)) /\
  assign_subscripts tv current popPath PopOp = INL current' /\
  evaluate_subscripts tv current popPath = INL arr /\ popped_value arr = INL p /\
  evaluate_subscripts tv current path = INL v ==>
  (?w. evaluate_subscripts tv current' path = INL w) \/
  (?w. read_popped tv path (record_pop popPath arr p []) = SOME w)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[subscripts_type_def, evaluate_subscripts_def, assign_subscripts_def] >>
      Cases_on `arr` >>
      gvs[vyperValueOperationTheory.pop_element_def,
          vyperValueOperationTheory.popped_value_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      gvs[vyperValueOperationTheory.pop_element_def,
          vyperValueOperationTheory.popped_value_def] >>
      irule dynamic_root_pop_survival >>
      simp[assign_subscripts_def, vyperValueOperationTheory.pop_element_def,
        vyperValueOperationTheory.popped_value_def] >>
      gvs[value_has_type_def] >> metis_tac[]) >>
  Cases_on `h`
  >- suspend "ArrayStep"
  >> suspend "StructStep"
QED

Resume pop_current_path_survival[ArrayStep]:
  rename1 `ValueSubscript index` >> Cases_on `index` >>
  gvs[subscripts_type_def, subscript_type_def, assign_subscripts_def,
    evaluate_subscripts_def] >>
  Cases_on `tv` >> gvs[subscript_type_def] >>
  Cases_on `current` >> gvs[value_has_type_def]
  >- (rename1 `ArrayV av` >> Cases_on `av` >>
      gvs[value_has_type_def, vyperValueOperationTheory.array_set_index_def,
        AllCaseEqs()]) >>
  gvs[AllCaseEqs()] >>
  drule array_set_result_shape >> strip_tac >> gvs[] >>
  rename1 `array_index (ArrayTV t b) av i = SOME child` >>
  `subscript_type (ArrayTV t b) (ValueSubscript (IntV i)) = SOME t` by
    simp[subscript_type_def] >>
  `value_has_type t child` by
    (irule evaluate_subscripts_type >>
     qexistsl_tac [`ArrayV av`,`[ValueSubscript (IntV i)]`,`ArrayTV t b`] >>
     simp[subscripts_type_def, evaluate_subscripts_def]) >>
  `record_pop (ValueSubscript (IntV i)::popPath) arr p [] =
   MAP (\(prefix,p). (ValueSubscript (IntV i)::prefix,p))
       (record_pop popPath arr p [])` by
    (irule record_pop_rebase >> simp[evaluate_subscripts_def]) >>
  asm_rewrite_tac[] >> irule array_child_path_survival >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >> qexists_tac `vj` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[subscript_type_well_formed]
QED

Resume pop_current_path_survival[StructStep]:
  Cases_on `tv` >> gvs[subscripts_type_def, subscript_type_def] >>
  Cases_on `current` >> gvs[assign_subscripts_def, evaluate_subscripts_def,
    AllCaseEqs()] >>
  rename [`value_has_type (StructTV fields) (StructV al)`,
    `ALOOKUP fields s = SOME child_tv`, `ALOOKUP al s = SOME child`] >>
  `subscript_type (StructTV fields) (AttrSubscript s) = SOME child_tv` by
    simp[subscript_type_def] >>
  `value_has_type child_tv child` by
    (irule evaluate_subscripts_type >>
     qexistsl_tac [`StructV al`,`[AttrSubscript s]`,`StructTV fields`] >>
     simp[subscripts_type_def, evaluate_subscripts_def]) >>
  `record_pop (AttrSubscript s::popPath) arr p [] =
   MAP (\(prefix,p). (AttrSubscript s::prefix,p))
       (record_pop popPath arr p [])` by
    (irule record_pop_rebase >> simp[evaluate_subscripts_def]) >>
  asm_rewrite_tac[] >> irule struct_child_path_survival >> conj_tac
  >- (qexistsl_tac [`child`,`child_tv`] >> simp[] >>
      rpt strip_tac >> first_x_assum irule >>
      metis_tac[subscript_type_well_formed]) >>
  metis_tac[]
QED

Finalise pop_current_path_survival

Theorem read_popped_declared_type_exists:
  !history tv path v.
    popped_history_typed tv history /\ read_popped tv path history = SOME v ==>
    ?ptv. subscripts_type tv path = SOME ptv
Proof
  Induct >> simp[read_popped_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  `popped_history_typed tv history` by gvs[popped_history_typed_def] >>
  `?htv. subscripts_type tv h0 = SOME htv /\
          well_formed_type_value htv /\ value_has_type htv h1` by
    gvs[popped_history_typed_def] >>
  gvs[read_popped_def, AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> strip_tac >> goal_assum (drule_at Any) >> NO_TAC) >>
  `?suffix_tv. subscripts_type htv (DROP (LENGTH h0) path) = SOME suffix_tv` by
    metis_tac[evaluate_subscripts_declared_type_exists] >>
  gvs[rich_listTheory.IS_PREFIX_APPEND, rich_listTheory.DROP_LENGTH_APPEND] >>
  metis_tac[subscripts_type_append]
QED

Theorem read_popped_older_success:
  !fresh tv path old v ptv.
    popped_history_typed tv fresh /\ subscripts_type tv path = SOME ptv /\
    read_popped tv path old = SOME v ==>
    ?w. read_popped tv path (fresh ++ old) = SOME w
Proof
  Induct >- simp[] >> gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  strip_tac >>
  `popped_history_typed tv fresh` by gvs[popped_history_typed_def] >>
  `?htv. subscripts_type tv h0 = SOME htv /\
          well_formed_type_value htv /\ value_has_type htv h1` by
    gvs[popped_history_typed_def] >>
  first_x_assum drule_all >> strip_tac >>
  simp[read_popped_def] >>
  Cases_on `IS_PREFIX path h0` >> simp[] >>
  Cases_on `evaluate_subscripts htv h1 (DROP (LENGTH h0) path)` >> simp[] >>
  metis_tac[typed_snapshot_failure]
QED

Theorem record_pop_preserves_covered:
  popped_history_typed tv fresh /\
  value_has_type tv current /\ well_formed_type_value tv /\
  subscripts_type tv popPath = SOME (ArrayTV etv (Dynamic n)) /\
  assign_subscripts tv current popPath PopOp = INL current' /\
  evaluate_subscripts tv current popPath = INL arr /\ popped_value arr = INL p /\
  memory_path_covered tv current fresh path ==>
  memory_path_covered tv current' (record_pop popPath arr p fresh) path
Proof
  simp[memory_path_covered_def] >> strip_tac
  >- (drule_all pop_current_path_survival >> strip_tac
      >- metis_tac[] >>
      disj2_tac >>
      `record_pop popPath arr p fresh =
       record_pop popPath arr p [] ++ fresh` by
        metis_tac[record_pop_prefix_split, APPEND] >>
      metis_tac[read_popped_prefix_noninterference]) >>
  disj2_tac >>
  `record_pop popPath arr p fresh =
   record_pop popPath arr p [] ++ fresh` by
    metis_tac[record_pop_prefix_split, APPEND] >>
  `?ptv. subscripts_type tv path = SOME ptv` by
    metis_tac[read_popped_declared_type_exists] >>
  `popped_history_typed tv (record_pop popPath arr p [])` by
    (irule record_pop_history_typed >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[popped_history_typed_def] >> metis_tac[]) >>
  metis_tac[read_popped_older_success]
QED

Theorem read_popped_prefix_rebase:
  !prefix tv htv path history.
    subscripts_type tv prefix = SOME htv ==>
    read_popped tv (prefix ++ path)
      (MAP (\(q,v). (prefix ++ q,v)) history) =
    read_popped htv path history
Proof
  Induct
  >- (simp[subscripts_type_def] >> rpt gen_tac >>
      AP_TERM_TAC >> Induct_on `history` >>
      simp[pairTheory.FORALL_PROD]) >>
  rpt gen_tac >> simp[subscripts_type_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  `MAP (\(q,v). (h::(prefix ++ q),v)) history =
   MAP (\(q,v). (h::q,v)) (MAP (\(q,v). (prefix ++ q,v)) history)` by
    (simp[MAP_COMPOSE, combinTheory.o_DEF, pairTheory.UNCURRY] >>
     AP_THM_TAC >> AP_TERM_TAC >>
     simp[FUN_EQ_THM, pairTheory.FORALL_PROD]) >>
  asm_rewrite_tac[] >>
  drule read_popped_rebase >> disch_then (fn th => rewrite_tac[th]) >>
  first_x_assum irule >> simp[]
QED

Theorem record_pop_prefix_rebase:
  !prefix suffix arr p.
    record_pop (prefix ++ suffix) arr p [] =
    MAP (\(q,v). (prefix ++ q,v)) (record_pop suffix arr p [])
Proof
  rpt gen_tac >> Cases_on `arr` >> simp[record_pop_def] >>
  Cases_on `a` >> simp[APPEND_ASSOC]
QED

Theorem selected_snapshot_pop_typed:
  well_formed_type_value htv /\ value_has_type htv snapshot /\
  evaluate_subscripts htv snapshot suffix = INL arr /\
  pop_element arr = INL shortened /\
  assign_subscripts htv snapshot suffix (Replace shortened) = INL updated ==>
  value_has_type htv updated
Proof
  rpt strip_tac >> drule_all vyperLookupTheory.assign_subscripts_pop_replace >> strip_tac >>
  irule vyperAssignPreservesTypeTheory.assign_subscripts_preserves_type >>
  simp[] >> qexistsl_tac [`snapshot`,`PopOp`,`suffix`] >> simp[]
QED

Theorem selected_snapshot_pop_survival:
  subscripts_type tv prefix = SOME htv /\
  well_formed_type_value htv /\ value_has_type htv snapshot /\
  subscripts_type htv suffix = SOME (ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts htv snapshot suffix = INL arr /\
  pop_element arr = INL shortened /\ popped_value arr = INL p /\
  assign_subscripts htv snapshot suffix (Replace shortened) = INL updated /\
  evaluate_subscripts htv snapshot path = INL v ==>
  (?w. evaluate_subscripts htv updated path = INL w) \/
  (?w. read_popped tv (prefix ++ path)
    (record_pop (prefix ++ suffix) arr p []) = SOME w)
Proof
  rpt strip_tac >> drule_all vyperLookupTheory.assign_subscripts_pop_replace >> strip_tac >>
  `assign_subscripts htv snapshot suffix PopOp = INL updated` by simp[] >>
  drule_all pop_current_path_survival >> strip_tac
  >- metis_tac[] >>
  disj2_tac >> simp[record_pop_prefix_rebase] >>
  qpat_assum `subscripts_type tv prefix = SOME htv`
    (mp_then Any mp_tac read_popped_prefix_rebase) >>
  disch_then (qspecl_then [`path`,`record_pop suffix arr p []`] mp_tac) >>
  simp[]
QED

Theorem read_popped_typed_success_iff:
  !history tv path ptv.
  popped_history_typed tv history /\ subscripts_type tv path = SOME ptv ==>
  ((?w. read_popped tv path history = SOME w) <=>
   ?prefix snapshot htv w. MEM (prefix,snapshot) history /\
     IS_PREFIX path prefix /\ subscripts_type tv prefix = SOME htv /\
     evaluate_subscripts htv snapshot (DROP (LENGTH prefix) path) = INL w)
Proof
  Induct >- simp[read_popped_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  `popped_history_typed tv history` by gvs[popped_history_typed_def] >>
  `?htv. subscripts_type tv h0 = SOME htv /\
    well_formed_type_value htv /\ value_has_type htv h1` by
    gvs[popped_history_typed_def] >>
  first_x_assum (qspecl_then [`tv`,`path`,`ptv`] mp_tac) >>
  simp[] >> disch_tac >>
  Cases_on `IS_PREFIX path h0`
  >- (Cases_on `evaluate_subscripts htv h1 (DROP (LENGTH h0) path)`
      >- (gvs[read_popped_def] >> metis_tac[]) >>
      `missing_dynamic_element htv h1 (DROP (LENGTH h0) path)` by
        metis_tac[typed_snapshot_failure] >>
      gvs[read_popped_def] >> dsimp[]) >>
  gvs[read_popped_def] >> dsimp[]
QED

Theorem read_popped_typed_append_success:
  popped_history_typed tv (left ++ right) /\ subscripts_type tv path = SOME ptv ==>
  ((?w. read_popped tv path (left ++ right) = SOME w) <=>
    (?w. read_popped tv path left = SOME w) \/
    (?w. read_popped tv path right = SOME w))
Proof
  rpt strip_tac >>
  `popped_history_typed tv left /\ popped_history_typed tv right` by
    gvs[popped_history_typed_def, MEM_APPEND] >>
  simp[read_popped_typed_success_iff, MEM_APPEND] >> metis_tac[]
QED

Theorem replace_popped_trusted_prefix_transport:
  !fresh tv old popPath etv n arr shortened p history.
  popped_history_typed tv fresh /\ well_formed_type_value tv /\
  subscripts_type tv popPath = SOME (ArrayTV etv (Dynamic n)) /\
  read_popped tv popPath (fresh ++ old) = SOME arr /\
  value_has_type (ArrayTV etv (Dynamic n)) arr /\
  pop_element arr = INL shortened /\ popped_value arr = INL p /\
  replace_popped tv popPath shortened (fresh ++ old) = SOME history ==>
  ?fresh' old'. history = fresh' ++ old' /\
    popped_history_typed tv (record_pop popPath arr p fresh') /\
    (!path v. read_popped tv path fresh = SOME v ==>
      ?w. read_popped tv path (record_pop popPath arr p fresh') = SOME w)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> qexistsl_tac [`[]`,`history`] >>
      simp[read_popped_def] >>
      irule record_pop_history_typed_at_path >>
      simp[popped_history_typed_def] >>
      `well_formed_type_value (ArrayTV etv (Dynamic n))` by
        metis_tac[subscripts_type_well_formed] >>
      gvs[well_formed_type_value_def]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  `popped_history_typed tv fresh` by gvs[popped_history_typed_def] >>
  `?htv. subscripts_type tv h0 = SOME htv /\
    well_formed_type_value htv /\ value_has_type htv h1` by
    gvs[popped_history_typed_def] >>
  Cases_on `IS_PREFIX popPath h0`
  >- (Cases_on `evaluate_subscripts htv h1 (DROP (LENGTH h0) popPath)`
      >- suspend "Selected"
      >> (`missing_dynamic_element htv h1 (DROP (LENGTH h0) popPath)` by
            metis_tac[typed_snapshot_failure] >>
          suspend "SkippedPrefix")) >>
  suspend "SkippedPrefix"
QED

Resume replace_popped_trusted_prefix_transport[SkippedPrefix]:
  markerLib.RESUME_TAC >> (
  gvs[Once replace_popped_def, Once read_popped_def, AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`(h0,h1)::fresh'`,`old'`] >>
  simp[] >>
  `record_pop popPath arr p ((h0,h1)::fresh') =
    record_pop popPath arr p [] ++ [(h0,h1)] ++ fresh'` by
    (Cases_on `arr` >> simp[record_pop_def] >>
     Cases_on `a` >> simp[]) >>
  `popped_history_typed tv
      (record_pop popPath arr p ((h0,h1)::fresh'))` by
    (Cases_on `arr` >> gvs[vyperValueOperationTheory.popped_value_def] >>
     Cases_on `a` >> gvs[vyperValueOperationTheory.popped_value_def] >>
     gvs[record_pop_def, popped_history_typed_cons]) >>
  simp[] >> rpt strip_tac >>
  `?vt. subscripts_type tv path = SOME vt` by
    (irule read_popped_declared_type_exists >>
     goal_assum (drule_at Any) >>
     simp[popped_history_typed_cons] >> metis_tac[]) >>
  `popped_history_typed tv ((h0,h1)::fresh)` by
    simp[popped_history_typed_cons] >>
  `(?w. read_popped tv path [(h0,h1)] = SOME w) \/
   (?w. read_popped tv path fresh = SOME w)` by
    (`popped_history_typed tv ([(h0,h1)] ++ fresh)` by simp[] >>
     drule_all read_popped_typed_append_success >>
     simp[] >> metis_tac[])
  >- (`popped_history_typed tv [(h0,h1)]` by
        simp[popped_history_typed_cons, popped_history_typed_def] >>
      `?w. read_popped tv path [(h0,h1)] = SOME w` by metis_tac[] >>
      `popped_history_typed tv
        (record_pop popPath arr p [] ++ [(h0,h1)] ++ fresh')` by metis_tac[] >>
      qspecl_then [`[(h0,h1)]`,`tv`,`path`,`vt`] mp_tac
        read_popped_typed_success_iff >>
      simp[] >> strip_tac >>
      simp[read_popped_typed_success_iff, MEM_APPEND] >> metis_tac[]) >>
  `?w. read_popped tv path (record_pop popPath arr p fresh') = SOME w` by
    metis_tac[] >>
  `record_pop popPath arr p fresh' = record_pop popPath arr p [] ++ fresh'` by
    (Cases_on `arr` >> simp[record_pop_def] >> Cases_on `a` >> simp[]) >>
  `popped_history_typed tv
    (record_pop popPath arr p [] ++ [(h0,h1)] ++ fresh')` by metis_tac[] >>
  qspecl_then [`record_pop popPath arr p [] ++ fresh'`,`tv`,`path`,`vt`]
    mp_tac read_popped_typed_success_iff >>
  simp[] >> strip_tac >>
  simp[read_popped_typed_success_iff, MEM_APPEND] >> metis_tac[])
QED

Resume replace_popped_trusted_prefix_transport[Selected]:
  qpat_x_assum `!tv old popPath etv n arr shortened p history. _` kall_tac >>
  gvs[Once read_popped_def, Once replace_popped_def, AllCaseEqs()] >>
  rename1 `assign_subscripts htv h1 (DROP (LENGTH h0) popPath)
    (Replace shortened) = INL updated` >>
  qexistsl_tac [`(h0,updated)::fresh`,`old`] >> simp[] >>
  `value_has_type htv updated` by
    (irule selected_snapshot_pop_typed >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `popped_history_typed tv ((h0,updated)::fresh)` by
    (simp[popped_history_typed_cons] >> metis_tac[]) >>
  conj_tac
  >- (irule record_pop_history_typed_at_path >> simp[] >>
      `well_formed_type_value (ArrayTV etv (Dynamic n))` by
        metis_tac[subscripts_type_well_formed] >>
      gvs[well_formed_type_value_def]) >>
  `popped_history_typed tv (record_pop popPath arr p ((h0,updated)::fresh))` by
    (irule record_pop_history_typed_at_path >> simp[] >>
     `well_formed_type_value (ArrayTV etv (Dynamic n))` by
       metis_tac[subscripts_type_well_formed] >>
     gvs[well_formed_type_value_def]) >>
  rpt strip_tac >>
  `?vt. subscripts_type tv path = SOME vt` by
    (irule read_popped_declared_type_exists >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  qspecl_then [`(h0,h1)::fresh`,`tv`,`path`,`vt`] mp_tac
    read_popped_typed_success_iff >> simp[] >> strip_tac
  >- (gvs[] >>
      gvs[rich_listTheory.IS_PREFIX_APPEND, rich_listTheory.DROP_LENGTH_APPEND] >>
      `subscripts_type htv l = SOME (ArrayTV etv (Dynamic n))` by
        metis_tac[subscripts_type_append] >>
      drule_all selected_snapshot_pop_survival >> strip_tac
      >- (simp[read_popped_typed_success_iff] >>
          qexistsl_tac [`h0`,`updated`,`htv`,`w'`] >>
          Cases_on `arr` >> gvs[vyperValueOperationTheory.popped_value_def] >>
          Cases_on `a` >> gvs[vyperValueOperationTheory.popped_value_def] >>
          simp[record_pop_def, rich_listTheory.IS_PREFIX_APPEND,
               rich_listTheory.DROP_LENGTH_APPEND]) >>
      `popped_history_typed tv (record_pop (h0 ++ l) arr p [])` by
        (Cases_on `arr` >> simp[record_pop_def] >>
         Cases_on `a` >> fs[record_pop_def, popped_history_typed_cons,
                           popped_history_typed_def]) >>
      qspecl_then [`record_pop (h0 ++ l) arr p []`,`tv`,`h0 ++ l'`,`vt`]
        mp_tac read_popped_typed_success_iff >> simp[] >> strip_tac >>
      simp[read_popped_typed_success_iff] >>
      qexistsl_tac [`prefix`,`snapshot`,`htv'`,`w''`] >>
      Cases_on `arr` >> gvs[vyperValueOperationTheory.popped_value_def] >>
      Cases_on `a` >> gvs[vyperValueOperationTheory.popped_value_def] >>
      gvs[record_pop_def]) >>
  simp[read_popped_typed_success_iff] >>
  qexistsl_tac [`prefix`,`snapshot`,`htv'`,`w`] >>
  Cases_on `arr` >> gvs[vyperValueOperationTheory.popped_value_def] >>
  Cases_on `a` >> gvs[vyperValueOperationTheory.popped_value_def] >>
  simp[record_pop_def]
QED

Finalise replace_popped_trusted_prefix_transport

Theorem memory_history_region_pop:
  memory_history_region entry fresh old paths /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  subscripts_type entry.type popPath = SOME (ArrayTV etv (Dynamic n)) /\
  assign_subscripts entry.type entry.value popPath PopOp = INL current' /\
  evaluate_subscripts entry.type entry.value popPath = INL arr /\
  popped_value arr = INL p ==>
  memory_history_region
    (entry with <|value := current';
      popped := record_pop popPath arr p entry.popped|>)
    (record_pop popPath arr p fresh) old paths
Proof
  simp[memory_history_region_def, EVERY_MEM] >> rpt strip_tac
  >- simp[record_pop_prefix_split]
  >- metis_tac[record_pop_history_typed] >>
  first_x_assum drule >> strip_tac >>
  irule record_pop_preserves_covered >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

(* Operational evidence and typing validity are deliberately independent. *)
Definition entry_pop_step_def:
  entry_pop_step entry popPath entry' <=>
  ?arr p shortened current' history.
    read_memory_path entry popPath = INL arr /\
    popped_value arr = INL p /\ pop_element arr = INL shortened /\
    ((?live. evaluate_subscripts entry.type entry.value popPath = INL live /\
         assign_subscripts entry.type entry.value popPath (Replace shortened) =
           INL current' /\ history = entry.popped) \/
     (?err. evaluate_subscripts entry.type entry.value popPath = INR err /\
         current' = entry.value /\
         replace_popped entry.type popPath shortened entry.popped = SOME history)) /\
    entry' = entry with <|value := current';
      popped := record_pop popPath arr p history|>
End

Definition entry_pop_trace_def:
  (entry_pop_trace entry [] final <=> final = entry) /\
  (entry_pop_trace entry ((source,popPath)::events) final <=>
    source = entry /\ ?next. entry_pop_step entry popPath next /\
      entry_pop_trace next events final)
End

Definition entry_pop_event_valid_def:
  entry_pop_event_valid (entry,popPath) <=>
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
    ?etv n arr.
      subscripts_type entry.type popPath = SOME (ArrayTV etv (Dynamic n)) /\
      read_memory_path entry popPath = INL arr /\
      value_has_type (ArrayTV etv (Dynamic n)) arr
End

Definition entry_pop_trace_valid_def:
  entry_pop_trace_valid events <=> EVERY entry_pop_event_valid events
End

Theorem entry_pop_trace_empty[simp]:
  entry_pop_trace entry [] final <=> final = entry
Proof
  simp[entry_pop_trace_def]
QED

Theorem entry_pop_trace_valid_empty[simp]:
  entry_pop_trace_valid []
Proof
  simp[entry_pop_trace_valid_def]
QED

Theorem entry_pop_trace_valid_append[simp]:
  entry_pop_trace_valid (xs ++ ys) <=>
  entry_pop_trace_valid xs /\ entry_pop_trace_valid ys
Proof
  simp[entry_pop_trace_valid_def, EVERY_APPEND]
QED

Theorem entry_pop_step_region:
  entry_pop_step entry popPath entry' /\
  entry_pop_event_valid (entry,popPath) /\
  memory_history_region entry fresh old paths ==>
  ?fresh' old'. memory_history_region entry' fresh' old' paths
Proof
  simp[entry_pop_step_def, entry_pop_event_valid_def] >> rpt strip_tac >> gvs[]
  >- (`arr = live` by gvs[read_memory_path_def] >> gvs[] >>
      `assign_subscripts entry.type entry.value popPath PopOp = INL current'` by
        (drule_all vyperLookupTheory.assign_subscripts_pop_replace >> simp[]) >>
      qexistsl_tac [`record_pop popPath arr p fresh`,`old`] >>
      irule memory_history_region_pop >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[]) >>
  `read_popped entry.type popPath entry.popped = SOME arr` by
    gvs[read_memory_path_def, AllCaseEqs()] >>
  gvs[memory_history_region_def] >>
  drule_all replace_popped_trusted_prefix_transport >> strip_tac >>
  qexistsl_tac [`record_pop popPath arr p fresh'`,`old'`] >>
  simp[record_pop_prefix_split] >>
  gvs[EVERY_MEM, memory_path_covered_def] >>
  metis_tac[]
QED

Theorem entry_pop_trace_region:
  !events entry final fresh old paths.
  entry_pop_trace entry events final /\ entry_pop_trace_valid events /\
  memory_history_region entry fresh old paths ==>
  ?fresh' old'. memory_history_region final fresh' old' paths
Proof
  Induct >- (simp[entry_pop_trace_def] >> metis_tac[]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[entry_pop_trace_def, entry_pop_trace_valid_def] >> rpt strip_tac >> gvs[] >>
  drule_all entry_pop_step_region >> strip_tac >>
  first_x_assum irule >> simp[entry_pop_trace_valid_def] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED

Theorem entry_pop_step_metadata:
  entry_pop_step entry path entry' ==>
  entry'.type = entry.type /\ entry'.assignable = entry.assignable
Proof
  simp[entry_pop_step_def] >> rpt strip_tac >> gvs[]
QED

Theorem entry_pop_trace_metadata:
  !events entry final. entry_pop_trace entry events final ==>
  final.type = entry.type /\ final.assignable = entry.assignable
Proof
  Induct >- simp[entry_pop_trace_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[entry_pop_trace_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[entry_pop_step_metadata]
QED

Theorem entry_pop_trace_valid_cons[simp]:
  entry_pop_trace_valid ((entry,path)::events) <=>
  entry_pop_event_valid (entry,path) /\ entry_pop_trace_valid events
Proof
  simp[entry_pop_trace_valid_def]
QED

Definition scope_pop_step_def:
  scope_pop_step sc (id,(source,path)) sc' <=>
    ?pre frame rest next.
      find_containing_scope id sc = SOME (pre,frame,source,rest) /\
      entry_pop_step source path next /\
      sc' = pre ++ ((frame |+ (id,next)) :: rest)
End

Definition scope_pop_trace_def:
  (scope_pop_trace sc [] final <=> final = sc) /\
  (scope_pop_trace sc (ev::events) final <=>
    ?middle. scope_pop_step sc ev middle /\
      scope_pop_trace middle events final)
End

Definition entry_events_def:
  (entry_events id [] = []) /\
  (entry_events id ((name,ev)::events) =
    if name = id then ev :: entry_events id events
    else entry_events id events)
End

Theorem scope_pop_trace_append:
  !xs sc ys final.
    scope_pop_trace sc (xs ++ ys) final <=>
    ?middle. scope_pop_trace sc xs middle /\ scope_pop_trace middle ys final
Proof
  Induct >> simp[scope_pop_trace_def] >> metis_tac[]
QED

Theorem scope_pop_step_lookup:
  scope_pop_step sc (id,(source,path)) sc' ==>
  lookup_scopes id sc = SOME source /\
  ?next. lookup_scopes id sc' = SOME next /\ entry_pop_step source path next
Proof
  simp[scope_pop_step_def] >> rpt strip_tac >> gvs[] >>
  drule vyperLookupTheory.find_containing_scope_lookup >> strip_tac >>
  drule vyperLookupTheory.find_containing_scope_pre_none >> strip_tac >>
  qexists_tac `next` >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[vyperLookupTheory.lookup_scopes_update]
QED

Theorem scope_pop_step_lookup_other:
  scope_pop_step sc (name,(source,path)) sc' /\ name <> id ==>
  lookup_scopes id sc' = lookup_scopes id sc
Proof
  simp[scope_pop_step_def] >> rpt strip_tac >> gvs[] >>
  drule vyperLookupTheory.find_containing_scope_structure >> strip_tac >>
  gvs[] >> rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[vyperLookupTheory.lookup_scopes_update_other]
QED

Theorem scope_pop_trace_lookup:
  !events sc final id entry.
    scope_pop_trace sc events final /\ lookup_scopes id sc = SOME entry ==>
    ?entry'. lookup_scopes id final = SOME entry' /\
      entry_pop_trace entry (entry_events id events) entry'
Proof
  Induct >- simp[scope_pop_trace_def, entry_events_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[scope_pop_trace_def] >> rpt strip_tac >>
  Cases_on `h0 = id`
  >- (gvs[entry_events_def] >> drule scope_pop_step_lookup >> strip_tac >>
      gvs[] >> first_x_assum drule >> disch_then drule >> strip_tac >>
      qexists_tac `entry'` >> simp[entry_pop_trace_def] >> metis_tac[]) >>
  simp[entry_events_def] >>
  drule_all scope_pop_step_lookup_other >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem scope_pop_trace_region:
  scope_pop_trace sc events final /\ lookup_scopes id sc = SOME entry /\
  entry_pop_trace_valid (entry_events id events) /\
  memory_history_region entry fresh old paths ==>
  ?entry' fresh' old'. lookup_scopes id final = SOME entry' /\
    memory_history_region entry' fresh' old' paths
Proof
  rpt strip_tac >> drule_all scope_pop_trace_lookup >> strip_tac >>
  drule_all entry_pop_trace_region >> strip_tac >> metis_tac[]
QED

Theorem pop_memory_scope_trace_events:
  pop_place cx (MemoryPlace id path) st = (res,st') ==>
  ?events. scope_pop_trace st.scopes events st'.scopes /\
    (events = [] \/
     ?pre frame source rest.
       find_containing_scope id st.scopes = SOME (pre,frame,source,rest) /\
       events = [(id,(source,path))] /\
       ?arr. read_memory_path source path = INL arr)
Proof
  Cases_on `st'.scopes = st.scopes`
  >- (strip_tac >> qexists_tac `[]` >> simp[scope_pop_trace_def]) >>
  simp[pop_place_def, bind_def, get_scopes_def, lift_option_type_def] >>
  Cases_on `find_containing_scope id st.scopes` >>
  simp[return_def, raise_def] >- (strip_tac >> gvs[] >>
    simp[scope_pop_trace_def]) >>
  PairCases_on `x` >>
  simp[type_check_def, assert_def, check_def, bind_def, ignore_bind_def,
       lift_sum_def, lift_option_type_def, return_def, raise_def,
       set_scopes_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[vyperMiscTheory.sum_CASE_rator, vyperMiscTheory.option_CASE_rator,
      AllCaseEqs(), return_def, raise_def, bind_def, set_scopes_def] >>
  qexists_tac `[(id,(x2,path))]` >>
  simp[scope_pop_trace_def, scope_pop_step_def, entry_pop_step_def] >>
  metis_tac[]
QED

Theorem pop_memory_read_typed_trace:
  state_well_typed st /\
  (!entry arr. lookup_scopes id st.scopes = SOME entry /\
     read_memory_path entry path = INL arr ==>
     ?etv n. subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic n)) /\
       value_has_type (ArrayTV etv (Dynamic n)) arr) /\
  pop_place cx (MemoryPlace id path) st = (res,st') ==>
  ?events. scope_pop_trace st.scopes events st'.scopes /\
    EVERY (\ev. entry_pop_event_valid (SND ev)) events
Proof
  rpt strip_tac >> drule pop_memory_scope_trace_events >> strip_tac
  >- (qexists_tac `[]` >> gvs[]) >>
  drule vyperLookupTheory.find_containing_scope_lookup >> strip_tac >>
  `value_has_type source.type source.value /\ well_formed_type_value source.type` by
    (irule vyperTypeEnvTheory.scope_well_typed_lookup_scopes >>
     goal_assum drule >> gvs[state_well_typed_def]) >>
  qexists_tac `[(id,(source,path))]` >>
  simp[entry_pop_event_valid_def] >> metis_tac[]
QED

Theorem pop_memory_scope_trace:
  pop_place cx (MemoryPlace id path) st = (res,st') ==>
  ?events. scope_pop_trace st.scopes events st'.scopes
Proof
  metis_tac[pop_memory_scope_trace_events]
QED

Definition scope_pop_effect_def:
  scope_pop_effect f <=>
    !st res st'. f st = (res,st') ==>
      ?events. scope_pop_trace st.scopes events st'.scopes
End

Theorem scope_pop_effect_identity:
  (!st res st'. f st = (res,st') ==> st'.scopes = st.scopes) ==>
  scope_pop_effect f
Proof
  simp[scope_pop_effect_def] >> rpt strip_tac >>
  qexists_tac `[]` >> simp[scope_pop_trace_def] >> metis_tac[]
QED

Theorem scope_pop_effect_bind:
  scope_pop_effect f /\ (!v. scope_pop_effect (g v)) ==>
  scope_pop_effect (bind f g)
Proof
  simp[scope_pop_effect_def, bind_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  TRY (goal_assum (drule_at Any) >> NO_TAC) >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `events' ++ events` >>
  irule (iffRL scope_pop_trace_append) >> metis_tac[]
QED

Theorem pop_nonmemory_scopes:
  (!id path. p <> MemoryPlace id path) /\
  pop_place cx p st = (res,st') ==> st'.scopes = st.scopes
Proof
  Cases_on `p`
  >- metis_tac[vyperScopePreservationTheory.pop_storage_place_scopes_immutables]
  >- simp[] >>
  simp[pop_place_def, bind_def, ignore_bind_def,
       get_immutables_def, get_address_immutables_def,
       get_accounts_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rpt strip_tac >>
  gvs[vyperMiscTheory.sum_CASE_rator, vyperMiscTheory.option_CASE_rator,
      AllCaseEqs(), return_def, raise_def] >>
  metis_tac[set_immutable_scopes]
QED

Theorem pop_place_scope_effect:
  scope_pop_effect (pop_place cx p)
Proof
  Cases_on `p`
  >- (irule scope_pop_effect_identity >> rpt strip_tac >>
      irule pop_nonmemory_scopes >> goal_assum (drule_at Any) >> simp[])
  >- (simp[scope_pop_effect_def] >> metis_tac[pop_memory_scope_trace]) >>
  irule scope_pop_effect_identity >> rpt strip_tac >>
  irule pop_nonmemory_scopes >> goal_assum (drule_at Any) >> simp[]
QED


Theorem scope_pop_effect_return[simp]:
  scope_pop_effect (return v)
Proof
  irule scope_pop_effect_identity >> simp[return_def]
QED

Theorem scope_pop_effect_raise[simp]:
  scope_pop_effect (raise e)
Proof
  irule scope_pop_effect_identity >> simp[raise_def]
QED

Theorem scope_pop_effect_lift_sum[simp]:
  scope_pop_effect (lift_sum v)
Proof
  irule scope_pop_effect_identity >> Cases_on `v` >>
  simp[lift_sum_def, return_def, raise_def]
QED

Theorem scope_pop_effect_lift_option[simp]:
  scope_pop_effect (lift_option v msg)
Proof
  irule scope_pop_effect_identity >> Cases_on `v` >>
  simp[lift_option_def, return_def, raise_def]
QED

Theorem scope_pop_effect_lift_option_type[simp]:
  scope_pop_effect (lift_option_type v msg)
Proof
  irule scope_pop_effect_identity >> Cases_on `v` >>
  simp[lift_option_type_def, return_def, raise_def]
QED

Theorem scope_pop_effect_cond:
  scope_pop_effect (if b then f else g) <=>
    if b then scope_pop_effect f else scope_pop_effect g
Proof
  Cases_on `b` >> simp[]
QED

Theorem scope_pop_effect_primitives[simp]:
  scope_pop_effect (check b msg) /\
  scope_pop_effect (type_check b msg) /\
  scope_pop_effect (lift_sum_runtime sv) /\
  scope_pop_effect (read_result cx tv) /\
  scope_pop_effect get_scopes /\
  scope_pop_effect get_accounts /\
  scope_pop_effect get_transient_storage /\
  scope_pop_effect (lookup_global cx src id) /\
  scope_pop_effect (read_storage_slot cx transient slot tyv) /\
  scope_pop_effect (transfer_value sender dest amount) /\
  scope_pop_effect (lookup_flag_mem cx (src,id) mid) /\
  scope_pop_effect (append_logs logs) /\
  scope_pop_effect (update_accounts ua) /\
  scope_pop_effect (update_transient ut)
Proof
  rpt conj_tac >> irule scope_pop_effect_identity >>
  rpt strip_tac >>
  FIRST (map (fn th => drule th >> simp[])
    [check_scopes, type_check_scopes, lift_sum_runtime_scopes,
     read_result_state, get_scopes_scopes, get_accounts_scopes,
     get_transient_storage_scopes, lookup_global_scopes,
     read_storage_slot_scopes, transfer_value_scopes,
     lookup_flag_mem_scopes, append_logs_scopes, update_accounts_scopes,
     update_transient_scopes])
QED

Theorem scope_pop_effect_bind_guarded:
  scope_pop_effect f /\
  (!st v middle. f st = (INL v,middle) ==> scope_pop_effect (g v)) ==>
  scope_pop_effect (bind f g)
Proof
  simp[scope_pop_effect_def, bind_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[scope_pop_trace_append]
QED

Theorem eval_name_scope_effect[local]:
  scope_pop_effect (eval_expr cx (Name ty id))
Proof
  rewrite_tac[Once evaluate_def] >>
  irule scope_pop_effect_bind >> simp[] >> gen_tac >>
  rewrite_tac[ignore_bind_def] >> irule scope_pop_effect_bind >> simp[]
QED

Theorem eval_toplevel_scope_effect[local]:
  scope_pop_effect (eval_expr cx (TopLevelName ty (src,id)))
Proof
  simp[Once evaluate_def]
QED

Theorem eval_flag_scope_effect[local]:
  scope_pop_effect (eval_expr cx (FlagMember ty nsid mid))
Proof
  Cases_on `nsid` >> simp[Once evaluate_def]
QED

Theorem eval_literal_scope_effect[local]:
  scope_pop_effect (eval_expr cx (Literal ty lit))
Proof
  simp[Once evaluate_def]
QED

Theorem eval_structlit_scope_effect[local]:
  (!ks. ks = MAP FST kes ==> scope_pop_effect (eval_exprs cx (MAP SND kes))) ==>
  scope_pop_effect (eval_expr cx (StructLit ty (src,id) kes))
Proof
  strip_tac >> first_x_assum (qspec_then `MAP FST kes` mp_tac) >>
  simp[] >> strip_tac >> simp[Once evaluate_def, LET_THM] >>
  irule scope_pop_effect_bind >> simp[]
QED

Theorem scope_pop_effect_switch:
  scope_pop_effect f /\ scope_pop_effect g ==>
  scope_pop_effect (switch_BoolV cx tv f g)
Proof
  strip_tac >> rewrite_tac[switch_BoolV_def] >>
  irule scope_pop_effect_bind >> simp[] >>
  gen_tac >> simp[scope_pop_effect_cond]
QED

Theorem eval_pop_scope_effect[local]:
  scope_pop_effect (eval_target_place cx bt) ==>
  scope_pop_effect (eval_expr cx (Pop ty bt))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  irule scope_pop_effect_bind >> simp[pop_place_scope_effect]
QED

Theorem scope_pop_effect_place_primitives[simp]:
  scope_pop_effect (lookup_global cx src id) /\
  scope_pop_effect (get_place pv) /\
  scope_pop_effect (extend_place cx pv sb) /\
  scope_pop_effect (read_place cx p) /\
  scope_pop_effect (place_type_value cx p)
Proof
  rpt conj_tac >> irule scope_pop_effect_identity >> rpt strip_tac >>
  FIRST (map (fn th => drule th >> simp[])
    [lookup_global_state, get_place_state, extend_place_state, read_place_state, place_type_value_state])
QED

Theorem scope_pop_effect_selection[simp]:
  scope_pop_effect (select_result cx ty res sb)
Proof
  Cases_on `res` >> simp[select_result_def] >>
  irule scope_pop_effect_bind >> simp[] >> gen_tac >>
  irule scope_pop_effect_bind >> simp[]
QED

Theorem scope_pop_effect_conditional[simp]:
  scope_pop_effect (conditional_result cx res)
Proof
  Cases_on `res` >> simp[conditional_result_def] >>
  irule scope_pop_effect_bind >> simp[] >> gen_tac >>
  simp[scope_pop_effect_cond] >> disj2_tac >>
  irule scope_pop_effect_bind >> simp[]
QED

Theorem eval_attribute_scope_effect[local]:
  scope_pop_effect (eval_expr cx e) ==>
  scope_pop_effect (eval_expr cx (Attribute ty e id))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  irule scope_pop_effect_bind >> simp[]
QED

Theorem eval_ifexp_scope_effect[local]:
  (!st tv middle. eval_expr cx e st = (INL tv,middle) ==>
    scope_pop_effect (eval_expr cx e1)) /\
  (!st tv middle. eval_expr cx e st = (INL tv,middle) ==>
    scope_pop_effect (eval_expr cx e2)) /\
  scope_pop_effect (eval_expr cx e) ==>
  scope_pop_effect (eval_expr cx (IfExp ty e e1 e2))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  irule scope_pop_effect_bind_guarded >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule scope_pop_effect_bind >> simp[scope_pop_effect_conditional] >>
  irule scope_pop_effect_switch >>
  conj_tac >> first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem eval_exprs_empty_scope_effect[local]:
  scope_pop_effect (eval_exprs cx [])
Proof
  simp[Once evaluate_def]
QED

Theorem scope_pop_effect_saved_region:
  (!prev st res st'. st.scopes = prev /\ f prev st = (res,st') ==>
    st'.scopes = prev) ==>
  scope_pop_effect (bind get_scopes f)
Proof
  strip_tac >> irule scope_pop_effect_identity >>
  simp[bind_def, get_scopes_def, return_def] >> metis_tac[]
QED

Theorem eval_exprs_cons_scope_effect[local]:
  (!st tv middle st1 v middle1.
    eval_expr cx e st = (INL tv,middle) /\
    read_result cx tv st1 = (INL v,middle1) ==>
    scope_pop_effect (eval_exprs cx es)) /\
  scope_pop_effect (eval_expr cx e) ==>
  scope_pop_effect (eval_exprs cx (e::es))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac
  >- (first_x_assum irule >> metis_tac[]) >> simp[]
QED

Theorem eval_name_place_scope_effect[local]:
  scope_pop_effect (eval_base_place cx (NameTarget id))
Proof
  rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[] >>
  gen_tac >> rewrite_tac[ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_toplevel_place_scope_effect[local]:
  scope_pop_effect (eval_base_place cx (TopLevelNameTarget (src,id)))
Proof
  simp[Once evaluate_def]
QED

Theorem eval_attribute_base_place_scope_effect[local]:
  scope_pop_effect (eval_base_place cx bt) ==>
  scope_pop_effect (eval_base_place cx (AttributeTarget bt id))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_target_place_scope_effect[local]:
  scope_pop_effect (eval_base_place cx bt) ==>
  scope_pop_effect (eval_target_place cx bt)
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_subscript_base_place_scope_effect[local]:
  (!st pv middle. eval_base_place cx bt st = (INL pv,middle) ==>
    scope_pop_effect (eval_expr cx e)) /\
  scope_pop_effect (eval_base_place cx bt) ==>
  scope_pop_effect (eval_base_place cx (SubscriptTarget bt e))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac
  >- (first_x_assum irule >> goal_assum (drule_at Any)) >>
  gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem scope_pop_effect_array_primitives[simp]:
  scope_pop_effect (result_array_length cx tv) /\
  scope_pop_effect (eval_raw_call cx flags target calldata amount)
Proof
  rpt conj_tac >> irule scope_pop_effect_identity >> rpt strip_tac >>
  FIRST (map (fn th => drule th >> simp[])
    [result_array_length_state,
     eval_raw_call_preserves_non_accounts])
QED

Theorem eval_subscript_scope_effect[local]:
  (!st tv middle. eval_expr cx e1 st = (INL tv,middle) ==>
    scope_pop_effect (eval_expr cx e2)) /\
  scope_pop_effect (eval_expr cx e1) ==>
  scope_pop_effect (eval_expr cx (Subscript ty e1 e2))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac
  >- (first_x_assum irule >> goal_assum (drule_at Any)) >>
  gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_builtin_scope_effect[local]:
  (!st x middle.
    type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" st = (INL x,middle) /\
    bt <> Len ==> scope_pop_effect (eval_exprs cx es)) /\
  (!st x middle.
    type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" st = (INL x,middle) /\
    bt = Len ==> scope_pop_effect (eval_expr cx (HD es))) ==>
  scope_pop_effect (eval_expr cx (Builtin ty bt es))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac
  >- (Cases_on `bt = Len` >> simp[]
      >- (ho_match_mp_tac scope_pop_effect_bind >> conj_tac
          >- (first_x_assum irule >> metis_tac[]) >>
          gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> simp[]) >>
      ho_match_mp_tac scope_pop_effect_bind >> conj_tac
      >- (first_x_assum irule >> metis_tac[]) >>
      gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> simp[]) >> simp[]
QED

Theorem eval_typebuiltin_scope_effect[local]:
  (!st x middle.
    type_check (type_builtin_args_length_ok tb (LENGTH es)) "TypeBuiltin args" st = (INL x,middle)
    ==> scope_pop_effect (eval_exprs cx es)) ==>
  scope_pop_effect (eval_expr cx (TypeBuiltin ty tb typ es))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac
  >- (first_x_assum irule >> goal_assum (drule_at Any)) >>
  gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem scope_pop_effect_log_create[simp]:
  scope_pop_effect (push_log log) /\
  scope_pop_effect (eval_create cx kind has_salt rof tys vs code_size)
Proof
  conj_tac >> irule scope_pop_effect_identity >> rpt strip_tac >>
  FIRST (map (fn th => drule th >> simp[])
    [push_log_scopes, vyperCreateFrameTheory.eval_create_preserves_scopes_immutables])
QED

Theorem eval_raw_call_scope_effect[local]:
  scope_pop_effect (eval_exprs cx es) ==>
  scope_pop_effect (eval_expr cx (Call ty (RawCallTarget flags) es drv))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  rewrite_tac[ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_raw_calldata_scope_effect[local]:
  scope_pop_effect (eval_exprs cx es) ==>
  scope_pop_effect (eval_expr cx (Call ty (RawCallCalldataTarget flags) es drv))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  rewrite_tac[ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_raw_revert_scope_effect[local]:
  scope_pop_effect (eval_exprs cx es) ==>
  scope_pop_effect (eval_expr cx (Call ty RawRevert es drv))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_selfdestruct_scope_effect[local]:
  scope_pop_effect (eval_exprs cx es) ==>
  scope_pop_effect (eval_expr cx (Call ty SelfDestructTarget es drv))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  simp[LET_THM] >> ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_raw_log_scope_effect[local]:
  scope_pop_effect (eval_exprs cx es) ==>
  scope_pop_effect (eval_expr cx (Call ty RawLog es drv))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  simp[LET_THM] >> ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem scope_pop_effect_frame:
  state_rel_frame (\st st'. st'.scopes = st.scopes) f ==>
  scope_pop_effect f
Proof
  simp[state_rel_frame_def] >> strip_tac >>
  irule scope_pop_effect_identity >> rpt strip_tac >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[]
QED

Theorem scope_pop_effect_read[simp]:
  scope_pop_effect (\st. return (g st) st)
Proof
  irule scope_pop_effect_identity >> simp[return_def]
QED

Theorem scope_pop_effect_outcome_primitives[simp]:
  scope_pop_effect (vyperCallOutcome$take_call_outcome target calldata value_opt) /\
  scope_pop_effect (vyperCallOutcome$adopt_call_outcome rq co)
Proof
  conj_tac
  >- (irule scope_pop_effect_frame >> irule state_rel_frame_locals_take >> simp[]) >>
  irule scope_pop_effect_identity >>
  simp[vyperCallOutcomeTheory.adopt_call_outcome_equation, return_def] >>
  gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem scope_pop_effect_call_helpers[simp]:
  scope_pop_effect (eval_send cx has_gas vs) /\
  scope_pop_effect (eval_ext_call cx static skip_check sig opts vs) /\
  scope_pop_effect (check_create_blueprint has_salt vs)
Proof
  rpt conj_tac >> irule scope_pop_effect_identity >> rpt strip_tac >>
  FIRST (map (fn th => drule th >> simp[])
    [eval_send_preserves_non_accounts, eval_ext_call_preserves_non_accounts,
     vyperCreateFrameTheory.check_create_blueprint_result_state])
QED

Theorem eval_send_scope_effect[local]:
  (!st x middle.
    type_check (LENGTH es = if has_gas then 3 else 2) "Send args" st = (INL x,middle) ==>
    scope_pop_effect (eval_exprs cx es)) ==>
  scope_pop_effect (eval_expr cx (Call ty (Send has_gas) es drv))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac
  >- (first_x_assum irule >> goal_assum (drule_at Any)) >> simp[]
QED

(* Consume a guarded recursive IH only at an isolated effect leaf.  Facts are
   normalized once; no traversal or simplification of the quantified guard. *)
fun POP_EFFECT_GUARD_TAC (asl,w) =
  let
    val normalize = SIMP_RULE bool_ss [oneTheory.one, ignore_bind_def]
    val facts = List.concat (map (CONJUNCTS o normalize o ASSUME) asl)
    val atoms = List.filter (not o is_forall o concl) facts
    val eqs = List.filter (fn th => is_eq (concl th) andalso
      is_var (lhs (concl th))) atoms
    val facts = facts @ map (SIMP_RULE bool_ss eqs) atoms
    fun discharge th =
      if is_imp (snd (strip_forall (concl th))) then
        discharge (tryfind (MATCH_MP th) facts)
      else th
    fun close ih goal =
      if can (match_term (snd (strip_imp (snd (strip_forall (concl ih)))))) w then
        ACCEPT_TAC (discharge (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] ih)) goal
      else NO_TAC goal
  in
    FIRST (map close facts) (asl,w)
  end;

val POP_EFFECT_BIND_STEP = FIRST [
  POP_EFFECT_GUARD_TAC,
  (simp[] >> NO_TAC),
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac,
  gen_tac, strip_tac];


Theorem finally_conditional_lock_scopes:
  finally f (do pop_function prev;
    if guard then
      case slot of NONE => return ()
      | SOME s => release_nonreentrant_lock addr s
    else return () od) st = (res,st') ==> st'.scopes = prev
Proof
  `!st res st'. (if guard then
      case slot of NONE => return ()
      | SOME s => release_nonreentrant_lock addr s
    else return ()) st = (res,st') ==> st'.scopes = st.scopes` by
    (Cases_on `guard` >> Cases_on `slot` >> simp[return_def] >>
     metis_tac[release_nonreentrant_lock_scopes]) >>
  metis_tac[finally_pop_function_then_scopes]
QED

Theorem eval_mutual_scope_pop_effect:
  (!(cx:evaluation_context) (s:stmt). T) /\
  (!(cx:evaluation_context) (ss:stmt list). T) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:value list). T) /\
  (!cx e. scope_pop_effect (eval_expr cx e)) /\
  (!cx es. scope_pop_effect (eval_exprs cx es)) /\
  (!cx bt. scope_pop_effect (eval_base_place cx bt)) /\
  (!cx bt. scope_pop_effect (eval_target_place cx bt)) /\
  (!(cx:evaluation_context) (g:assignment_target) (v:value). T) /\
  (!(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  TRY (simp[] >> NO_TAC) >> rpt gen_tac >> rpt strip_tac >>
  TRY (FIRST (map (fn th => FIRST
    [MATCH_ACCEPT_TAC (GEN_ALL th),
     match_mp_tac (GEN_ALL th) >> rpt conj_tac >> first_assum ACCEPT_TAC] >> NO_TAC)
    [eval_name_scope_effect, eval_toplevel_scope_effect, eval_flag_scope_effect,
     eval_literal_scope_effect, eval_structlit_scope_effect,
     eval_pop_scope_effect, eval_attribute_scope_effect, eval_ifexp_scope_effect,
     eval_exprs_empty_scope_effect, eval_exprs_cons_scope_effect,
     eval_name_place_scope_effect, eval_toplevel_place_scope_effect,
     eval_attribute_base_place_scope_effect, eval_target_place_scope_effect,
     eval_subscript_base_place_scope_effect, eval_subscript_scope_effect,
     eval_builtin_scope_effect, eval_typebuiltin_scope_effect,
     eval_raw_call_scope_effect, eval_raw_calldata_scope_effect,
      eval_raw_revert_scope_effect,
     eval_selfdestruct_scope_effect, eval_raw_log_scope_effect, eval_send_scope_effect])) >>
  TRY (rename1 `scope_pop_effect (eval_expr _ (Call _ (ExtCall _ _ _ _) _ _))` >>
           suspend "ExtCall")
   >> TRY (rename1 `scope_pop_effect (eval_expr _ (Call _ (CreateTarget kind has_salt rof) _ _))` >>
           suspend "Create")
   >> suspend "IntCall"
QED

Resume eval_mutual_scope_pop_effect[ExtCall]:
  rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Resume eval_mutual_scope_pop_effect[Create]:
  Cases_on `kind` >> gvs[] >> simp_tac (srw_ss()) [Once evaluate_def] >>
  rpt POP_EFFECT_BIND_STEP
QED

Resume eval_mutual_scope_pop_effect[IntCall]:
  rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  ntac 3 (ho_match_mp_tac scope_pop_effect_bind_guarded >>
          conj_tac >- simp[] >> rpt gen_tac >> strip_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- POP_EFFECT_GUARD_TAC >>
  rpt gen_tac >> strip_tac >>
  simp[LET_THM] >>
  ho_match_mp_tac scope_pop_effect_saved_region >>
  map_every qx_gen_tac [`prev`,`st0`,`res`,`st1`] >> strip_tac >>
  rpt (qpat_x_assum `!a. _` kall_tac) >>
  gvs[bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac finally_set_scopes >>
  imp_res_tac lift_option_type_scopes >>
  imp_res_tac (SRULE[ignore_bind_def] finally_conditional_lock_scopes) >>
  gvs[] >>
  gvs[push_function_def, return_def, AllCaseEqs()] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  gvs[raise_def, return_def] >>
  Cases_on `FST (SND tup)` >> gvs[return_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
  drule acquire_nonreentrant_lock_scopes >> simp[]
QED

Finalise eval_mutual_scope_pop_effect

Theorem entry_events_valid:
  !events id. EVERY (\ev. entry_pop_event_valid (SND ev)) events ==>
    entry_pop_trace_valid (entry_events id events)
Proof
  Induct >> simp[entry_events_def, entry_pop_trace_valid_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  simp[entry_events_def, entry_pop_trace_valid_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[] >>
  metis_tac[entry_pop_trace_valid_def]
QED

Theorem typed_scope_trace_live_region:
  scope_pop_trace st.scopes events st'.scopes /\
  EVERY (\ev. entry_pop_event_valid (SND ev)) events /\
  lookup_scopes id st.scopes = SOME entry /\
  memory_history_region entry fresh old paths ==>
  ?entry' fresh' old'. lookup_scopes id st'.scopes = SOME entry' /\
    memory_history_region entry' fresh' old' paths
Proof
  rpt strip_tac >>
  drule entry_events_valid >> disch_then (qspec_then `id` assume_tac) >>
  drule_all scope_pop_trace_region >> simp[]
QED


Theorem typed_scope_trace_memory_read:
  scope_pop_trace st.scopes events st'.scopes /\
  EVERY (\ev. entry_pop_event_valid (SND ev)) events /\
  state_well_typed st' /\ lookup_scopes id st.scopes = SOME entry /\
  memory_history_region entry fresh old [path] /\
  subscripts_type entry.type path = SOME tv ==>
  ?v. read_place cx (MemoryPlace id path) st' = (INL v,st') /\
      value_has_type tv v
Proof
  rpt strip_tac >>
  drule_all typed_scope_trace_live_region >> strip_tac >>
  drule_all scope_pop_trace_lookup >> strip_tac >>
  drule entry_pop_trace_metadata >> strip_tac >> gvs[] >>
  `value_has_type entry'.type entry'.value /\
   well_formed_type_value entry'.type` by
    metis_tac[state_well_typed_def, lookup_scopes_well_typed_value_has_type,
      lookup_scopes_well_typed_type] >>
  `subscripts_type entry'.type path = SOME tv` by simp[] >>
  `MEM path [path]` by simp[] >>
  drule_all covered_memory_read >> strip_tac >>
  qexists_tac `v` >>
  simp[read_place_def, get_scopes_def, bind_def, lift_option_type_def,
    lift_sum_def, return_def]
QED

Theorem typed_scope_trace_append:
  scope_pop_trace sc xs middle /\
  EVERY (\ev. entry_pop_event_valid (SND ev)) xs /\
  scope_pop_trace middle ys final /\
  EVERY (\ev. entry_pop_event_valid (SND ev)) ys ==>
  scope_pop_trace sc (xs ++ ys) final /\
  EVERY (\ev. entry_pop_event_valid (SND ev)) (xs ++ ys)
Proof
  metis_tac[scope_pop_trace_append, EVERY_APPEND]
QED



val () = List.app (fn (name,th) =>
  let val (oracles,_) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Place result interface oracle debt: " ^ name)
  end) (DB.thms "vyperPlaceResultTyping");

(* Delayed global roots are typed without loading their contents. *)
Theorem lookup_global_toplevel_ready:
  FLOOKUP env.toplevel_vtypes (src,id) = SOME vt /\
  env_consistent env cx st ==>
  ?pv. lookup_global cx src id st = (INL pv,st) /\
       eval_result_typed (env,cx,st) pv vt
Proof
  strip_tac >> Cases_on `vt`
  >- (Cases_on `FLOOKUP env.bare_globals (src,id)`
      >- (drule_all env_consistent_toplevel_storage_static >> strip_tac >>
          gvs[IS_SOME_EXISTS] >>
          `env.type_defs = get_tenv cx` by
            gvs[env_consistent_def, env_context_consistent_def] >>
          simp[lookup_global_def, bind_def, lift_option_type_def,
               return_def, runtime_place_typed_storage] >>
          irule evaluate_type_well_formed_type_value >>
          goal_assum drule >>
          gvs[env_consistent_def, env_context_consistent_def,
              well_formed_vtype_def] >> metis_tac[]) >>
      drule_all env_consistent_bare_global_find_NONE >> strip_tac >> gvs[] >>
      `?imms root a. get_immutables cx src st = (INL imms,st) /\
         FLOOKUP imms id = SOME (root,a) /\
         evaluate_type env.type_defs t = SOME root` by
        (`env.type_defs = get_tenv cx` by
           gvs[env_consistent_def, env_context_consistent_def] >>
         qpat_x_assum `env_consistent _ _ _` mp_tac >>
         simp[NoAsms, env_consistent_def, env_immutables_consistent_def,
              IS_SOME_EXISTS] >> strip_tac >>
         qpat_x_assum `!src id ty. _ ==> ?v. _` drule >> strip_tac >>
         PairCases_on `x` >>
         qpat_x_assum `!src id ty tv v. _ ==> _` drule_all >> strip_tac >>
         Cases_on `ALOOKUP st.immutables cx.txn.target` >>
         gvs[get_source_immutables_def, get_immutables_def,
             get_address_immutables_def, bind_def, return_def,
             lift_option_type_def] >>
         metis_tac[]) >>
      `well_formed_type_value root` by
        (irule evaluate_type_well_formed_type_value >> goal_assum drule >>
         gvs[env_consistent_def, env_context_consistent_def,
             well_formed_vtype_def] >> metis_tac[]) >>
      qexists_tac `PlaceR (ImmutablePlace src id [])` >>
      simp[lookup_global_def, bind_def, lift_option_type_def,
           return_def, runtime_place_typed_immutable, subscripts_type_def] >>
      metis_tac[]) >>
  drule_all env_consistent_toplevel_hashmap_static >> strip_tac >>
  gvs[IS_SOME_EXISTS] >>
  simp[lookup_global_def, bind_def, lift_option_type_def,
       return_def, eval_result_typed_def] >>
  gvs[env_consistent_def, env_context_consistent_def, well_formed_vtype_def] >>
  metis_tac[]
QED

Theorem type_place_target_global_lookup:
  type_place_target env (TopLevelNameTarget (src,id)) = SOME vt /\
  env_consistent env cx st ==>
  FLOOKUP env.toplevel_vtypes (src,id) = SOME vt
Proof
  simp[type_place_target_TopLevelNameTarget] >> rpt strip_tac >> gvs[] >>
  gvs[env_consistent_def, env_context_consistent_def] >>
  qpat_x_assum `!src id ty. FLOOKUP env.bare_global_assignable _ = _ ==> _`
    drule >> strip_tac >> simp[]
QED

Theorem lookup_global_target_no_type_error:
  type_place_target env (TopLevelNameTarget (src,id)) = SOME vt /\
  env_consistent env cx st /\
  lookup_global cx src id st = (res,st') ==>
  no_type_error_result res
Proof
  strip_tac >> drule_all type_place_target_global_lookup >> strip_tac >>
  drule_all lookup_global_toplevel_ready >> strip_tac >>
  gvs[no_type_error_result_def]
QED

Theorem lookup_global_target_success_typed:
  type_place_target env (TopLevelNameTarget (src,id)) = SOME vt /\
  env_consistent env cx st /\
  lookup_global cx src id st = (INL pv,st') ==>
  eval_result_typed (env,cx,st') pv vt
Proof
  strip_tac >> drule_all type_place_target_global_lookup >> strip_tac >>
  drule_all lookup_global_toplevel_ready >> strip_tac >> gvs[]
QED

Theorem type_place_expr_global_lookup:
  type_place_expr env (TopLevelName ann (src,id)) = SOME vt ==>
  FLOOKUP env.toplevel_vtypes (src,id) = SOME vt
Proof
  simp[well_typed_expr_def, vtype_annotation_ok_def, AllCaseEqs()] >>
  rpt strip_tac >> simp[]
QED

Theorem lookup_global_expr_no_type_error:
  type_place_expr env (TopLevelName ann (src,id)) = SOME vt /\
  env_consistent env cx st /\
  lookup_global cx src id st = (res,st') ==>
  no_type_error_result res
Proof
  strip_tac >> drule type_place_expr_global_lookup >> strip_tac >>
  drule_all lookup_global_toplevel_ready >> strip_tac >>
  gvs[no_type_error_result_def]
QED

Theorem lookup_global_expr_success_typed:
  type_place_expr env (TopLevelName ann (src,id)) = SOME vt /\
  env_consistent env cx st /\
  lookup_global cx src id st = (INL pv,st') ==>
  eval_result_typed (env,cx,st') pv vt
Proof
  strip_tac >> drule type_place_expr_global_lookup >> strip_tac >>
  drule_all lookup_global_toplevel_ready >> strip_tac >> gvs[]
QED

Theorem well_typed_global_place_type:
  well_typed_expr env (TopLevelName ann (src,id)) /\
  env_consistent env cx st ==>
  type_place_expr env (TopLevelName ann (src,id)) = SOME (Type ann)
Proof
  simp[Once well_typed_expr_def] >> strip_tac >>
  TRY (drule_all env_consistent_bare_global_find_NONE >> strip_tac) >>
  simp[well_typed_expr_def, vtype_annotation_ok_def]
QED

Theorem lookup_global_ordinary_success_typed:
  well_typed_expr env (TopLevelName ann (src,id)) /\
  env_consistent env cx st /\
  lookup_global cx src id st = (INL pv,st') ==>
  eval_result_typed (env,cx,st') pv (Type ann)
Proof
  strip_tac >> drule_all well_typed_global_place_type >> strip_tac >>
  drule_all lookup_global_expr_success_typed >> simp[]
QED

(* Targets can only produce a location or an unresolved mapping, never an
   ordinary expression value.  This operational fact is independent of typing. *)
Theorem lookup_global_result_shape:
  lookup_global cx src id st = (INL pv,st') ==>
  (?p. pv = PlaceR p) \/
  (?tr slot kt vt. pv = HashMapRef tr slot kt vt)
Proof
  simp[lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator, var_decl_info_CASE_rator,
      bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs()]
QED

Theorem extend_place_result_shape:
  extend_place cx pv sb st = (INL out,st') ==>
  (?p. out = PlaceR p) \/
  (?tr slot kt vt. out = HashMapRef tr slot kt vt)
Proof
  Cases_on `pv` >> Cases_on `sb` >>
  simp[oneline extend_place_def, bind_def, ignore_bind_def,
       lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[bind_def, return_def, raise_def, lift_sum_def,
      value_type_CASE_rator, place_CASE_rator, vyperMiscTheory.sum_CASE_rator,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()]
QED

Theorem eval_base_place_result_shape:
  !bt st pv st'. eval_base_place cx bt st = (INL pv,st') ==>
  (?p. pv = PlaceR p) \/
  (?tr slot kt vt. pv = HashMapRef tr slot kt vt)
Proof
  Cases >> rpt gen_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, lift_option_type_def,
       ignore_bind_def, type_check_def, assert_def, check_def,
       return_def, raise_def, vyperMiscTheory.prod_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[bind_def, ignore_bind_def, type_check_def, assert_def, check_def,
      return_def, raise_def, AllCaseEqs()] >>
  all_tac >~ [`eval_base_place cx (TopLevelNameTarget pair) st = _`]
  >- (PairCases_on `pair` >> gvs[Once evaluate_def] >>
      metis_tac[lookup_global_result_shape]) >>
  metis_tac[extend_place_result_shape]
QED

Theorem extend_place_place_success_shape:
  extend_place cx (PlaceR p) sb st = (INL out,st') ==>
  ?q. out = PlaceR q
Proof
  Cases_on `p` >>
  simp[extend_place_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem attribute_type_runtime_step:
  attribute_type tenv ty id = SOME field_ty /\
  evaluate_type tenv ty = SOME tv ==>
  ?field_tv. evaluate_type tenv field_ty = SOME field_tv /\
             subscript_type tv (AttrSubscript id) = SOME field_tv
Proof
  strip_tac >>
  `?fields. tv = StructTV fields` by
    (Cases_on `ty` >> gvs[attribute_type_def,
      vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  gvs[] >> drule_all attribute_type_evaluates >>
  simp[subscript_type_def]
QED

Theorem extend_place_attribute_success_typed:
  eval_result_typed (env,cx,st) (PlaceR p) (Type ty) /\
  attribute_type env.type_defs ty id = SOME field_ty /\
  extend_place cx (PlaceR p) (AttrSubscript id) st = (INL out,st') ==>
  eval_result_typed (env,cx,st') out (Type field_ty)
Proof
  simp[eval_result_typed_place] >> rpt strip_tac >>
  drule_all attribute_type_runtime_step >> strip_tac >>
  drule extend_place_place_success_shape >> strip_tac >> gvs[] >>
  simp[eval_result_typed_place] >>
  drule_all extend_place_typed >> simp[]
QED

Theorem subscript_type_value_shape[local]:
  subscript_type tv (ValueSubscript x) = SOME etv /\ value_has_type tv a ==>
  ?i av. x = IntV i /\ a = ArrayV av /\
    ((?bd. tv = ArrayTV etv bd) \/ (?tvs. tv = TupleTV tvs))
Proof
  Cases_on `tv` >> Cases_on `x` >> simp[subscript_type_def] >>
  rpt strip_tac >> Cases_on `a` >> gvs[value_has_type_inv]
QED

Theorem subscript_type_attribute_shape[local]:
  subscript_type tv (AttrSubscript id) = SOME etv /\ value_has_type tv a ==>
  ?fields vals v. tv = StructTV fields /\ a = StructV vals /\
    ALOOKUP fields id = SOME etv /\ ALOOKUP vals id = SOME v /\
    value_has_type etv v
Proof
  Cases_on `tv` >> simp[subscript_type_def] >> rpt strip_tac >>
  Cases_on `a` >> gvs[value_has_type_inv] >>
  TRY (rename1 `value_has_type (StructTV _) (ArrayV av)` >>
       Cases_on `av` >> gvs[value_has_type_inv] >> NO_TAC) >>
  `?v. ALOOKUP l' id = SOME v` by
    (Cases_on `ALOOKUP l' id` >> gvs[] >>
     drule_all struct_has_type_alookup_none >> simp[]) >>
  drule_all vyperAssignPreservesTypeTheory.struct_field_has_type >>
  strip_tac >> gvs[]
QED

Theorem evaluate_subscripts_typed_error:
  !path tv mtv a ptv err.
  (mtv = tv \/ mtv = NoneTV) /\
  value_has_type tv a /\ well_formed_type_value tv /\
  subscripts_type tv path = SOME ptv /\
  evaluate_subscripts mtv a path = INR err ==>
  !msg. err <> TypeError msg
Proof
  Induct >> simp[evaluate_subscripts_def, subscripts_type_def] >>
  gen_tac >> Cases_on `h`
  >- (rpt gen_tac >> strip_tac >>
      gvs[subscripts_type_def, AllCaseEqs()] >>
      drule_all subscript_type_value_shape >> strip_tac >>
      gvs[evaluate_subscripts_def, AllCaseEqs()] >>
      `well_formed_type_value etv` by metis_tac[subscript_type_well_formed] >>
      `value_has_type etv v'` by metis_tac[array_index_type_metadata] >>
      first_x_assum irule >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> gvs[subscript_type_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[subscripts_type_def, AllCaseEqs()] >>
  drule_all subscript_type_attribute_shape >> strip_tac >>
  gvs[evaluate_subscripts_def, AllCaseEqs()] >>
  `well_formed_type_value etv` by metis_tac[subscript_type_well_formed] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem read_memory_path_typed_error:
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  subscripts_type entry.type path = SOME tv /\
  read_memory_path entry path = INR err ==>
  !msg. err <> TypeError msg
Proof
  simp[read_memory_path_def, AllCaseEqs()] >> rpt strip_tac >>
  drule_at (Pat `evaluate_subscripts _ _ _ = _`) evaluate_subscripts_typed_error >>
  simp[] >> metis_tac[]
QED

Theorem read_place_typed_error:
  state_well_typed st /\ runtime_place_typed cx st p tv /\
  read_place cx p st = (INR err,st') ==>
  !msg. err <> Error (TypeError msg)
Proof
  Cases_on `p`
  >- (simp[read_place_def] >> rpt strip_tac >>
      drule read_storage_slot_error >> strip_tac >> gvs[])
  >- (simp[runtime_place_typed_memory] >> rpt strip_tac >>
      gvs[read_place_def, bind_def, get_scopes_def, lift_option_type_def,
          lift_sum_def, vyperMiscTheory.sum_CASE_rator,
          return_def, raise_def, AllCaseEqs()] >>
      `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
        metis_tac[state_well_typed_def, lookup_scopes_well_typed_value_has_type,
                  lookup_scopes_well_typed_type] >>
      drule_all read_memory_path_typed_error >> simp[]) >>
  simp[runtime_place_typed_immutable] >> rpt strip_tac >>
  gvs[read_place_def, bind_def, lift_option_type_def, lift_sum_def,
      vyperMiscTheory.sum_CASE_rator, return_def, raise_def, AllCaseEqs()] >>
  drule_all get_immutables_success_typed >> strip_tac >>
  drule_at (Pat `evaluate_subscripts _ _ _ = _`) evaluate_subscripts_typed_error >>
  simp[] >> metis_tac[]
QED

Theorem read_nonmemory_place_success_type:
  (!id path. p <> MemoryPlace id path) /\ state_well_typed st /\
  runtime_place_typed cx st p tv /\ read_place cx p st = (INL v,st') ==>
  value_has_type tv v
Proof
  Cases_on `p`
  >- (simp[runtime_place_typed_storage, read_place_def] >>
      metis_tac[read_storage_slot_success_type])
  >- simp[] >>
  rw[runtime_place_typed_immutable, read_place_def, bind_def,
     lift_option_type_def, lift_sum_def, return_def, raise_def,
     vyperMiscTheory.sum_CASE_rator, AllCaseEqs()] >>
  gvs[return_def] >> drule_all get_immutables_success_typed >> strip_tac >>
  irule evaluate_subscripts_type >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem read_place_live_typed:
  state_well_typed st /\ runtime_place_typed cx st p tv /\
  (case p of
   | MemoryPlace id path =>
       ?entry fresh old. lookup_scopes id st.scopes = SOME entry /\
         memory_eval_path entry.type path /\
         memory_history_region entry fresh old [path]
   | _ => T) /\
  read_place cx p st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  (case res of INL v => value_has_type tv v | INR _ => T)
Proof
  rpt strip_tac
  >- metis_tac[read_place_preserves_state]
  >- (Cases_on `res` >> simp[no_type_error_result_def] >>
      metis_tac[read_place_typed_error]) >>
  Cases_on `res` >> simp[] >> rename1 `INL v` >>
  Cases_on `p`
  >- metis_tac[read_nonmemory_place_success_type, place_distinct]
  >- (gvs[runtime_place_typed_memory] >>
      `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
        metis_tac[state_well_typed_def, lookup_scopes_well_typed_value_has_type,
                  lookup_scopes_well_typed_type] >>
      `?w. read_memory_path entry l = INL w /\ value_has_type tv w` by
        metis_tac[covered_memory_read, MEM] >>
      gvs[read_place_def, bind_def, get_scopes_def, lift_option_type_def,
          lift_sum_def, return_def]) >>
  metis_tac[read_nonmemory_place_success_type, place_distinct]
QED

Theorem memory_dynamic_array_authoritative_read:
  state_well_typed st /\
  runtime_place_typed cx st (MemoryPlace id path) (ArrayTV etv (Dynamic n)) /\
  (?source fresh old. lookup_scopes id st.scopes = SOME source /\
     memory_eval_path source.type path /\
     memory_history_region source fresh old [path]) /\
  lookup_scopes id st.scopes = SOME entry /\
  read_memory_path entry path = INL arr ==>
  subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic n)) /\
  value_has_type (ArrayTV etv (Dynamic n)) arr
Proof
  simp[runtime_place_typed_memory] >> rpt strip_tac >> gvs[] >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    metis_tac[state_well_typed_def, lookup_scopes_well_typed_value_has_type,
              lookup_scopes_well_typed_type] >>
  metis_tac[covered_memory_read, MEM, sumTheory.INL_11]
QED

Theorem struct_field_slot_exists:
  !fields id tv. ALOOKUP fields id = SOME tv ==>
  ?off. struct_field_slot fields id = SOME (off,tv)
Proof
  Induct >> simp[struct_field_slot_def] >> Cases_on `h` >>
  rpt gen_tac >> simp[struct_field_slot_def] >>
  Cases_on `q = id` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem extend_storage_place_attribute_ready:
  subscript_type tv (AttrSubscript id) = SOME etv ==>
  ?p. extend_storage_place cx tr slot tv (AttrSubscript id) st = (INL p,st)
Proof
  Cases_on `tv` >> simp[subscript_type_def] >> strip_tac >>
  drule struct_field_slot_exists >> strip_tac >>
  simp[extend_storage_place_def, bind_def, lift_option_type_def, return_def]
QED

Theorem evaluate_subscripts_attribute_ready:
  value_has_type tv v /\ subscript_type tv (AttrSubscript id) = SOME etv ==>
  ?w. evaluate_subscripts tv v [AttrSubscript id] = INL w
Proof
  strip_tac >> drule_all subscript_type_attribute_shape >> strip_tac >>
  gvs[evaluate_subscripts_def]
QED

(* C4.1.2.7: complete public-boundary witness, no operational changes. *)
Definition sparse_public_cx_def:
  sparse_public_cx = empty_evaluation_context with stk := [(NONE,"f")]
End
Definition sparse_public_env_def:
  sparse_public_env = <|
    current_src := NONE;
    var_types := FEMPTY |+ ("x",TupleT [ArrayT (BaseT BoolT) (Fixed 1)])
                        |+ ("y",BaseT BoolT);
    var_assignable := FEMPTY |+ ("y",T);
    bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
    toplevel_vtypes := FEMPTY; type_defs := FEMPTY;
    fn_sigs := FEMPTY; flag_members := FEMPTY |>
End

Definition sparse_public_state_def:
  sparse_public_state = empty_state with scopes :=
    [FEMPTY |+ ("x",<| type := TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)];
      value := ArrayV (TupleV [ArrayV (SArrayV [])]); assignable := T;
      popped := [([ValueSubscript (IntV 0);ValueSubscript (IntV 0)],IntV 7)] |> )
    |+ ("y",<| type := BaseTV BoolT; value := BoolV F;
                assignable := T; popped := [] |>)]
End

Definition sparse_public_stmt_def:
  sparse_public_stmt = Assign (BaseTarget (NameTarget "y"))
    (Subscript (BaseT BoolT)
      (Subscript (ArrayT (BaseT BoolT) (Fixed 1))
        (Name (TupleT [ArrayT (BaseT BoolT) (Fixed 1)]) "x")
        (Literal (BaseT (UintT 256)) (IntL 0)))
      (Literal (BaseT (UintT 256)) (IntL 0)))
End

Theorem sparse_public_source_typing:
  type_stmt sparse_public_env NoneT sparse_public_stmt = SOME sparse_public_env
Proof
  EVAL_TAC
QED

Theorem sparse_public_env_consistent:
  env_consistent sparse_public_env sparse_public_cx sparse_public_state
Proof
  simp[sparse_public_cx_def, sparse_public_env_def, sparse_public_state_def, empty_state_def,
       vyperContextTheory.empty_evaluation_context_def,
       vyperContextTheory.empty_call_txn_def, vyperContextTheory.get_tenv_def,
       vyperContextTheory.get_module_code_def, vyperContextTheory.current_module_def,
       env_consistent_def, env_context_consistent_def,
       fn_sigs_consistent_def, fn_sigs_declared_complete_def,
       toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def,
       env_scopes_consistent_def, env_immutables_consistent_def,
       lookup_scopes_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> EVAL_TAC >> simp[]
QED

Theorem sparse_public_state_typed:
  state_well_typed sparse_public_state
Proof
  simp[sparse_public_state_def, empty_state_def, state_well_typed_def,
       scope_well_typed_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> EVAL_TAC >> simp[]
QED

Theorem sparse_public_context_typed:
  context_well_typed sparse_public_cx
Proof
  EVAL_TAC
QED

Theorem sparse_public_accounts_typed:
  accounts_well_typed sparse_public_state.accounts
Proof
  simp[sparse_public_state_def, empty_state_def, accounts_well_typed_def,
       account_well_typed_def, vfmStateTheory.lookup_account_def,
       vfmStateTheory.empty_accounts_def, vfmStateTheory.empty_account_state_def]
QED

Theorem sparse_public_functions_typed:
  functions_well_typed sparse_public_cx
Proof
  simp[sparse_public_cx_def, functions_well_typed_def,
       vyperContextTheory.empty_evaluation_context_def,
       vyperContextTheory.get_module_code_def,
       lookup_callable_function_def, lookup_function_def]
QED

Theorem sparse_public_call_safe:
  call_evaluation_safe sparse_public_cx (int_calls_stmt sparse_public_stmt)
Proof
  simp[call_evaluation_safe_def, sparse_public_cx_def,
       vyperContextTheory.empty_evaluation_context_def] >>
  qexists `[]` >>
  simp[call_stack_follows_def, functions_follow_call_graph_def,
       vyperContextTheory.get_module_code_def, lookup_callable_function_def,
       lookup_function_def, calls_follow_call_graph_def,
       sparse_public_stmt_def, int_calls_stmt_def, int_calls_expr_def,
       int_calls_atarget_def, relationTheory.irreflexive_def] >>
  gen_tac >> strip_tac >>
  drule relationTheory.TC_CASES1_E >> simp[call_edge_rel_def]
QED

(* Concrete repaired regression, not universal public soundness. Historical
   falsification source/evidence is archived under documentation/history/. *)
Definition sparse_public_repaired_after_def:
  sparse_public_repaired_after = sparse_public_state
End

Theorem sparse_public_repaired_execution:
  eval_stmt sparse_public_cx sparse_public_stmt sparse_public_state =
    (INL (),sparse_public_repaired_after)
Proof
  EVAL_TAC >> simp[FUPDATE_EQ]
QED

Theorem sparse_public_repaired_post_typed:
  state_well_typed sparse_public_repaired_after
Proof
  simp[sparse_public_repaired_after_def, sparse_public_state_typed]
QED

Theorem sparse_public_repaired_regression:
  type_stmt sparse_public_env NoneT sparse_public_stmt = SOME sparse_public_env /\
  env_consistent sparse_public_env sparse_public_cx sparse_public_state /\
  state_well_typed sparse_public_state /\
  context_well_typed sparse_public_cx /\
  accounts_well_typed sparse_public_state.accounts /\
  functions_well_typed sparse_public_cx /\
  call_evaluation_safe sparse_public_cx (int_calls_stmt sparse_public_stmt) /\
  eval_stmt sparse_public_cx sparse_public_stmt sparse_public_state =
    (INL (),sparse_public_repaired_after) /\
  state_well_typed sparse_public_repaired_after
Proof
  simp[sparse_public_source_typing, sparse_public_env_consistent,
       sparse_public_state_typed, sparse_public_context_typed,
       sparse_public_accounts_typed, sparse_public_functions_typed,
       sparse_public_call_safe, sparse_public_repaired_execution,
       sparse_public_repaired_post_typed]
QED

val _ = List.app (fn name =>
  let val th = DB.fetch "vyperPlaceResultTyping" name
      val (ors,_) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") ors then ()
     else raise Fail ("oracle dependency in " ^ name) end)
  ["sparse_public_source_typing", "sparse_public_env_consistent",
   "sparse_public_state_typed", "sparse_public_context_typed",
   "sparse_public_accounts_typed", "sparse_public_functions_typed",
   "sparse_public_call_safe", "sparse_public_repaired_execution",
   "sparse_public_repaired_post_typed", "sparse_public_repaired_regression"];

(* Non-pop errors cannot be repaired by unrelated historical values. *)
Theorem classified_nonpop_history_regressions:
  read_memory_path
    <|type := BaseTV BoolT; value := BoolV F; assignable := T;
      popped := [([ValueSubscript (IntV 0)], IntV 7)]|>
    [ValueSubscript (IntV 0)] =
      INR (TypeError "evaluate_subscripts type") /\
  read_memory_path
    <|type := ArrayTV (BaseTV BoolT) (Fixed 1);
      value := ArrayV (SArrayV []); assignable := T;
      popped := [([ValueSubscript (IntV 1)], IntV 7)]|>
    [ValueSubscript (IntV 1)] =
      INR (RuntimeError "evaluate_subscripts array_index") /\
  read_memory_path
    <|type := ArrayTV (BaseTV BoolT) (Dynamic 1);
      value := ArrayV (DynArrayV []); assignable := T;
      popped := [([ValueSubscript (IntV (-1))], IntV 7)]|>
    [ValueSubscript (IntV (-1))] =
      INR (RuntimeError "evaluate_subscripts array_index") /\
  read_memory_path
    <|type := ArrayTV (BaseTV BoolT) (Dynamic 1);
      value := ArrayV (DynArrayV []); assignable := T;
      popped := [([AttrSubscript "f"], IntV 7)]|>
    [AttrSubscript "f"] = INR (TypeError "evaluate_subscripts")
Proof
  EVAL_TAC
QED

val _ = List.app (fn name =>
  let val (ors,_) = Tag.dest_tag (Thm.tag (DB.fetch "vyperPlaceResultTyping" name))
  in if List.all (fn s => s = "DISK_THM") ors then ()
     else raise Fail ("oracle dependency in " ^ name) end)
  ["tuple_sparse_metadata_probe", "tuple_metadata_present_dense_probes",
   "tuple_metadata_nested_sparse_probes", "tuple_sparse_delayed_read_probe",
   "tuple_sparse_old_history_probe", "classified_nonpop_history_regressions"];
