Theory exprSimPopNestedLocalProps
Ancestors
  loweringPosts vyperState vyperValueOperation exprSimPopNestedLocalPath
  vyperLookup vyperPlaceResultTyping vyperPlaceStatePreservation vyperValue
  vyperTyping vyperTypeInvariants vyperPlaceWriteSoundness

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

Theorem read_result_updated_memory_pop:
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  evaluate_subscripts entry.type updated
    (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) = INR err /\
  subscripts_type entry.type
    (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) = SOME tv ==>
  let t = es with scopes := pre ++ sc |+ (id,entry with
        <|value := updated;
          popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs) entry.popped|>) :: rest
  in read_result cx (PlaceR (MemoryPlace id
       (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]))) t = (INL (LAST vs),t)
Proof
  strip_tac >> simp[LET_THM] >>
  qmatch_goalsub_abbrev_tac `sc |+ (id,new_entry)` >>
  `lookup_scopes id (pre ++ sc |+ (id,new_entry) :: rest) = SOME new_entry` by
    (irule lookup_scopes_update >> drule find_containing_scope_pre_none >> simp[]) >>
  irule read_result_recorded_pop >> simp[] >>
  qexistsl_tac [`err`, `entry.popped`, `tv`] >> simp[Abbr `new_entry`]
QED

Theorem pop_memory_live_transition:
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\ mutable_place_path entry.type path /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  vs <> [] ==>
  ?updated.
    assign_subscripts entry.type entry.value path
      (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
    evaluate_subscripts entry.type updated path = INL (ArrayV (DynArrayV (FRONT vs))) /\
    evaluate_subscripts entry.type updated
      (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) =
        INR (RuntimeError "evaluate_subscripts array_index") /\
    subscripts_type entry.type
      (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) = SOME etv /\
    (let t = es with scopes := pre ++ sc |+ (id,entry with
           <|value := updated;
             popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs) entry.popped|>) :: rest
     in pop_place cx (MemoryPlace id path) es =
          (INL (PlaceR (MemoryPlace id
             (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]))),t) /\
        read_result cx (PlaceR (MemoryPlace id
             (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]))) t = (INL (LAST vs),t))
Proof
  strip_tac >>
  drule_all assign_subscripts_shorten_readback >> strip_tac >>
  `value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs))` by
    (drule_all evaluate_subscripts_type >> simp[]) >>
  `well_formed_type_value (ArrayTV etv (Dynamic n))` by
    (drule_all subscripts_type_well_formed >> simp[]) >>
  `0 < n /\ LENGTH vs <= n` by
    (fs[value_has_type_def, well_formed_type_value_def] >>
     Cases_on `vs` >> gvs[]) >>
  `subscripts_type entry.type
     (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) = SOME etv` by
    (drule vyperPlaceResultTypingTheory.subscripts_type_append >>
     disch_then (qspec_then `[ValueSubscript (IntV &(LENGTH vs - 1))]` SUBST1_TAC) >>
     simp[subscripts_type_def, subscript_type_def]) >>
  qexists_tac `updated` >> simp[] >> conj_tac
  >- (irule pop_memory_place_live >> simp[]) >>
  drule_all read_result_updated_memory_pop >> simp[]
QED
