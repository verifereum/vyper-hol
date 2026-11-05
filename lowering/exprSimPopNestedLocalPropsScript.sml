Theory exprSimPopNestedLocalProps
Ancestors
  loweringPosts vyperState vyperValueOperation

(* A readable place cannot come from history when fallback is excluded. *)
Theorem read_memory_path_live:
  !entry path v.
    read_memory_path entry path = INL v /\
    (!err. evaluate_subscripts entry.type entry.value path = INR err ==>
           read_popped entry.type path entry.popped = NONE) ==>
    evaluate_subscripts entry.type entry.value path = INL v
Proof
  rpt gen_tac >>
  Cases_on `evaluate_subscripts entry.type entry.value path` >>
  simp[read_memory_path_def] >>
  Cases_on `read_popped entry.type path entry.popped` >> simp[]
QED

Theorem place_readable_memory_live:
  !cx es id path.
    place_readable cx es (PlaceR (MemoryPlace id path)) /\
    (!entry err.
       lookup_scopes id es.scopes = SOME entry /\
       evaluate_subscripts entry.type entry.value path = INR err ==>
       read_popped entry.type path entry.popped = NONE) ==>
    ?entry v. lookup_scopes id es.scopes = SOME entry /\
              evaluate_subscripts entry.type entry.value path = INL v
Proof
  rpt gen_tac >>
  simp[place_readable_def, read_place_def, bind_def, get_scopes_def,
       lift_option_type_def, lift_sum_def, return_def, raise_def] >>
  Cases_on `lookup_scopes id es.scopes` >>
  simp[vyperStateTheory.raise_def, vyperStateTheory.return_def] >>
  rename1 `lookup_scopes id es.scopes = SOME entry` >>
  Cases_on `read_memory_path entry path` >>
  simp[vyperStateTheory.raise_def, vyperStateTheory.return_def] >>
  rpt strip_tac >> drule read_memory_path_live >> simp[]
QED

(* The live branch, with the exact scope update exposed to memory proofs. *)
Theorem pop_memory_place_live:
  !cx es id path pre sc entry rest vs updated.
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    entry.assignable /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
    vs <> [] /\
    assign_subscripts entry.type entry.value path
      (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated ==>
    pop_place cx (MemoryPlace id path) es =
      (INL (PlaceR (MemoryPlace id
        (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]))),
       es with scopes := pre ++ sc |+ (id,entry with
         <|value := updated;
           popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs) entry.popped|>) :: rest)
Proof
  rpt strip_tac >>
  simp[pop_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, type_check_def, assert_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       lift_sum_def, read_memory_path_def, check_def, popped_value_def,
       pop_element_def, set_scopes_def]
QED

Theorem pop_memory_place_live_empty:
  !cx es id path pre sc entry rest.
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    entry.assignable /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV [])) ==>
    pop_place cx (MemoryPlace id path) es =
      (INR (Error (RuntimeError "pop empty memory array")), es)
Proof
  rpt strip_tac >>
  simp[pop_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, type_check_def, assert_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       lift_sum_def, read_memory_path_def, check_def]
QED

Theorem read_result_recorded_pop:
  !cx es id path entry vs err tv.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value
      (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) = INR err /\
    subscripts_type entry.type
      (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) = SOME tv /\
    entry.popped = record_pop path (ArrayV (DynArrayV vs)) (LAST vs) history ==>
    read_result cx (PlaceR (MemoryPlace id
      (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]))) es =
      (INL (LAST vs), es)
Proof
  rpt strip_tac >>
  simp[read_result_def, read_place_def, bind_def, get_scopes_def,
       lift_option_type_def, lift_sum_def, vyperStateTheory.return_def,
       read_memory_path_def, record_pop_def, read_popped_def,
       evaluate_subscripts_def]
QED
