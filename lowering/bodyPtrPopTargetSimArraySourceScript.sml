Theory bodyPtrPopTargetSimArraySource
Ancestors
  bodyPtrPopTargetDefs exprSimSubscriptArraySource exprSimProps
  stmtSimAugAssignPlace vyperPlaceStatePreservation vyperPlaceResultTyping vyperState
  loweringPosts compileEnv words finite_map list exprSimArith arithmeticProps
  exprSimSubscriptArraySuffix vyperTyping vyperTypeSystem vyperValue vyperValueOperation
  valueEncoding integer_word integer vyperArray vyperAST vyperStorageBackend
  vyperStoragePlaceProvenance exprSimPopStorage typedMemoryCopy

(* A live current path bypasses popped history, for both fixed and dynamic
   arrays.  In particular no frame from the pre-index source value is used. *)
Theorem target_live_memory_extend:
  lookup_scopes id es.scopes = SOME entry /\
  subscripts_type entry.type path = SOME tv /\
  evaluate_subscripts entry.type entry.value path = INL v ==>
  extend_place cx (PlaceR (MemoryPlace id path)) sub es =
    case evaluate_subscripts tv v [sub] of
    | INL w => (INL (PlaceR (MemoryPlace id (path ++ [sub]))), es)
    | INR err => (INR (Error err), es)
Proof
  strip_tac >> simp[extend_place_def, place_type_value_def,
    read_place_def, get_scopes_def, read_memory_path_def, bind_def,
    ignore_bind_def, lift_option_type_def, lift_sum_def,
    return_def, raise_def, extend_memory_place_def] >>
  Cases_on `evaluate_subscripts tv v [sub]` >> simp[return_def, raise_def]
QED

Theorem target_live_memory_child:
  lookup_scopes id es.scopes = SOME entry /\
  subscripts_type entry.type path = SOME tv /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  evaluate_subscripts tv v [sub] = INL w ==>
  extend_place cx (PlaceR (MemoryPlace id path)) sub es =
    (INL (PlaceR (MemoryPlace id (path ++ [sub]))), es) /\
  place_readable cx es (PlaceR (MemoryPlace id (path ++ [sub]))) /\
  (!G tn rb s. target_ptr_ok cenv (PlaceR (MemoryPlace id path)) rb G tn s ==>
     target_ptr_ok cenv (PlaceR (MemoryPlace id (path ++ [sub]))) rb G tn s)
Proof
  strip_tac >> drule_all target_live_memory_extend >> simp[] >> strip_tac >>
  drule_all evaluate_subscripts_append >>
  disch_then (qspec_then `[sub]` assume_tac) >>
  simp[place_readable_def, read_place_def, get_scopes_def, read_memory_path_def,
       bind_def, lift_option_type_def, lift_sum_def, return_def, target_ptr_ok_def]
QED

(* Layout transport is independent of how the source selected the child. *)
Theorem target_memory_child_layout:
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) b loc (Type ty) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  mem_step_offset tv sub = SOME (off,etv) /\
  evaluate_type (get_tenv cx) et = SOME etv ==>
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id (path ++ [sub])))
    (b + n2w off) loc (Type et)
Proof
  simp[place_ptr_rel_def] >> strip_tac >> gvs[] >>
  drule_all mem_path_offset_snoc >> strip_tac >>
  simp[GSYM word_add_n2w, WORD_ADD_ASSOC] >> metis_tac[]
QED

(* Unlike an arbitrary word, a typed source integer decodes with exactly
   the signedness used by the bounds check. *)
Theorem target_typed_index_word:
  is_int_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  ?i. v = IntV i /\
      i = (if is_signed_type ty then w2i (val_to_w256 v)
           else &(w2n (val_to_w256 v)))
Proof
  strip_tac >> qspec_then `ty` assume_tac math_val_i2w >>
  Cases_on `ty` >> gvs[is_int_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_int_type_def, evaluate_type_def, value_has_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  gvs[math_val_def, is_signed_type_def, type_bits_def, val_to_w256_def,
      within_int_bound_def] >> metis_tac[]
QED

Theorem target_typed_array_length:
  bound_length bd < dimword (:256) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) ==>
  array_length (ArrayTV etv bd) av < dimword (:256) /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n)
Proof
  Cases_on `bd` >> Cases_on `av` >>
  simp[value_has_type_def, array_length_def, bound_length_def] >>
  rpt strip_tac >> decide_tac
QED

Theorem target_typed_array_index_bounds:
  evaluate_type tenv (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  is_int_type ity /\ evaluate_type tenv ity = SOME itv /\ value_has_type itv iv ==>
  ?i. iv = IntV i /\
    (valid_index (ArrayTV etv bd) av i <=>
      idx_in_range (is_signed_type ity) (val_to_w256 iv)
        (n2w (array_length (ArrayTV etv bd) av))) /\
    (valid_index (ArrayTV etv bd) av i ==> val_to_w256 iv = n2w (Num i))
Proof
  strip_tac >> drule_all target_typed_index_word >> strip_tac >>
  qpat_x_assum `iv = IntV _` SUBST_ALL_TAC >>
  drule typed_copy_array_count_bound >> strip_tac >>
  drule_all target_typed_array_length >> strip_tac >>
  qexists_tac `i` >>
  `valid_index (ArrayTV etv bd) av i <=>
    idx_in_range (is_signed_type ity) (val_to_w256 (IntV i))
      (n2w (array_length (ArrayTV etv bd) av))` by
    (irule array_index_word_bounds >> simp[]) >> simp[] >> strip_tac >>
  `0 <= i` by fs[valid_index_def] >>
  `~(i < 0)` by intLib.ARITH_TAC >> simp[val_to_w256_def, i2w_def]
QED

Theorem target_array_step_memory_offset:
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  valid_index (ArrayTV etv bd) av i ==>
  mem_step_offset (ArrayTV etv bd) (ValueSubscript (IntV i)) =
    SOME ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
      Num i * type_memory_size etv, etv)
Proof
  Cases_on `bd` >> Cases_on `av` >>
  simp[value_has_type_def, valid_index_def, array_length_def, mem_step_offset_def] >>
  rpt strip_tac >> `i = &Num i` by simp[Once $ GSYM INT_OF_NUM] >>
  qpat_x_assum `i < _` mp_tac >> qpat_x_assum `i = &Num i` SUBST1_TAC >>
  simp[] >> decide_tac
QED

Theorem target_storage_array_extend:
  len = (case bd of Fixed n => n
         | Dynamic n => w2n (lookup_storage slot (get_storage cx es tr))) /\
  (!cap. bd = Dynamic cap ==> len <= cap) ==>
  if 0 <= i /\ Num i < len then
    extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
      (ValueSubscript (IntV i)) es =
      (INL (PlaceR (StoragePlace tr
        (slot + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) +
           Num i * type_slot_size etv)) etv)),es)
  else ?msg. extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
      (ValueSubscript (IntV i)) es = (INR (Error (RuntimeError msg)),es)
Proof
  Cases_on `bd` >> simp[] >> strip_tac >>
  simp[extend_place_def, extend_storage_place_def, resolve_array_element_def,
       bind_def, ignore_bind_def, check_def, assert_def, get_storage_backend_eq,
       return_def, raise_def, resolve_array_element_empty] >>
  rpt IF_CASES_TAC >> gvs[return_def] >> decide_tac
QED

Theorem target_storage_child_layout:
  place_ptr_rel cenv cx s (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
    b loc (Type (ArrayT et bd)) /\
  evaluate_type (get_tenv cx) et = SOME etv ==>
  place_ptr_rel cenv cx t (PlaceR (StoragePlace tr child_slot etv))
    child_slot loc (Type et) /\
  place_readable cx es (PlaceR (StoragePlace tr child_slot etv)) /\
  (!G tn rb. target_ptr_ok cenv (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
      rb G tn s ==>
    target_ptr_ok cenv (PlaceR (StoragePlace tr child_slot etv)) rb G tn t)
Proof
  simp[place_ptr_rel_def, place_readable_def, target_ptr_ok_def]
QED

Theorem target_live_memory_array_extend:
  lookup_scopes id es.scopes = SOME entry /\
  subscripts_type entry.type path = SOME (ArrayTV etv bd) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type tenv (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  is_int_type ity /\ evaluate_type tenv ity = SOME itv /\ value_has_type itv iv ==>
  ?i. iv = IntV i /\
    if idx_in_range (is_signed_type ity) (val_to_w256 iv)
         (n2w (array_length (ArrayTV etv bd) av)) then
      extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript iv) es =
        (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript iv]))),es) /\
      place_readable cx es (PlaceR (MemoryPlace id (path ++ [ValueSubscript iv]))) /\
      mem_step_offset (ArrayTV etv bd) (ValueSubscript iv) =
        SOME ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
          Num i * type_memory_size etv, etv) /\ val_to_w256 iv = n2w (Num i)
    else extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript iv) es =
      (INR (Error (RuntimeError "evaluate_subscripts array_index")),es)
Proof
  strip_tac >> drule_all target_typed_array_index_bounds >> strip_tac >>
  qpat_x_assum `iv = IntV _` SUBST_ALL_TAC >> qexists_tac `i` >> simp[] >>
  IF_CASES_TAC
  >- (`valid_index (ArrayTV etv bd) av i` by metis_tac[] >>
      drule evaluate_array_subscript_in_bounds >> strip_tac >>
      drule_all target_live_memory_child >> strip_tac >>
      drule_all target_array_step_memory_offset >> simp[]) >>
  `~valid_index (ArrayTV etv bd) av i` by metis_tac[] >>
  drule typed_copy_array_count_bound >> strip_tac >>
  drule_all target_typed_array_length >> strip_tac >>
  drule_all evaluate_array_subscript_oob >> strip_tac >>
  drule_all target_live_memory_extend >> simp[]
QED

Theorem target_typed_storage_array_extend:
  evaluate_type tenv (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  slots_in_range (get_storage cx es tr) (w2n slot) (ArrayTV etv bd) /\
  len = (case bd of Fixed n => n
         | Dynamic n => w2n (lookup_storage slot (get_storage cx es tr))) /\
  is_int_type ity /\ evaluate_type tenv ity = SOME itv /\ value_has_type itv iv ==>
  ?i. iv = IntV i /\
    if idx_in_range (is_signed_type ity) (val_to_w256 iv) (n2w len) then
      extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
        (ValueSubscript iv) es =
        (INL (PlaceR (StoragePlace tr
          (slot + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) +
             Num i * type_slot_size etv)) etv)),es) /\
      val_to_w256 iv = n2w (Num i)
    else ?msg. extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
        (ValueSubscript iv) es = (INR (Error (RuntimeError msg)),es)
Proof
  strip_tac >> drule_all target_typed_index_word >> strip_tac >>
  qpat_x_assum `iv = IntV _` SUBST_ALL_TAC >>
  `!cap. bd = Dynamic cap ==> len <= cap` by
    (rpt strip_tac >> gvs[] >> irule pop_array_length_bound >> metis_tac[]) >>
  `len < dimword (:256)` by
    (drule typed_copy_array_count_bound >> strip_tac >>
     Cases_on `bd` >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]) >>
  `idx_in_range (is_signed_type ity) (val_to_w256 (IntV i)) (n2w len) <=>
    0 <= i /\ i < &len` by
    (drule idx_in_range_integer >> disch_then (qspecl_then
      [`val_to_w256 (IntV i)`, `is_signed_type ity`] mp_tac) >> metis_tac[]) >>
  `0 <= i /\ i < &len <=> 0 <= i /\ Num i < len` by
    (Cases_on `0 <= i` >> simp[] >>
     `i = &Num i` by simp[Once $ GSYM INT_OF_NUM] >>
     pop_assum SUBST1_TAC >> simp[]) >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  qexists_tac `i` >> simp[] >>
  drule_all target_storage_array_extend >>
  disch_then (qspecl_then [`i`, `etv`] mp_tac) >>
  Cases_on `0 <= i /\ Num i < len` >> simp[] >> strip_tac
  >- (`~(i < 0)` by intLib.ARITH_TAC >> simp[val_to_w256_def, i2w_def]) >>
  metis_tac[]
QED
