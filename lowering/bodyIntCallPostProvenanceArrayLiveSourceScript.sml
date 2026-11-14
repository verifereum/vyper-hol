(* Live source selections ignore saved history when the current path succeeds. *)
Theory bodyIntCallPostProvenanceArrayLiveSource
Ancestors
  bodyIntCallPostProvenanceLiveSource exprSimSubscriptArraySource
  vyperPlaceResultTyping vyperState vyperValueOperation vyperValue list

Theorem live_memory_child_read:
  lookup_scopes id es.scopes = SOME entry /\
  subscripts_type entry.type path = SOME ptv /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  evaluate_subscripts ptv v [sb] = INL w ==>
  select_result cx ty (PlaceR (MemoryPlace id path)) sb es =
    (INL (PlaceR (MemoryPlace id (path ++ [sb]))),es) /\
  read_result cx (PlaceR (MemoryPlace id (path ++ [sb]))) es = (INL w,es)
Proof
  strip_tac >>
  `evaluate_subscripts entry.type entry.value (path ++ [sb]) = INL w` by
    (drule_all evaluate_subscripts_append >> simp[]) >>
  `read_memory_path entry path = INL v` by
    simp[read_memory_path_def] >>
  conj_tac
  >- (drule_all select_memory_result >> simp[bind_def, lift_sum_def, return_def]) >>
  simp[read_result_def, read_place_def, get_scopes_def, bind_def,
       lift_option_type_def, lift_sum_def, return_def, read_memory_path_def]
QED

(* A saved value at the selected dynamic child does not shadow live data. *)
Theorem nested_dynamic_live_over_history:
  read_popped (ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1))
    [ValueSubscript (IntV 0)]
    (<| assignable := T;
        type := ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1);
        value := ArrayV (DynArrayV [ArrayV (DynArrayV [BoolV T])]);
        popped := [([ValueSubscript (IntV 0)],
                    ArrayV (DynArrayV [BoolV F]))] |>).popped =
      SOME (ArrayV (DynArrayV [BoolV F])) /\
  read_memory_path
    <| assignable := T;
       type := ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1);
       value := ArrayV (DynArrayV [ArrayV (DynArrayV [BoolV T])]);
       popped := [([ValueSubscript (IntV 0)],
                   ArrayV (DynArrayV [BoolV F]))] |>
    [ValueSubscript (IntV 0)] = INL (ArrayV (DynArrayV [BoolV T]))
Proof
  EVAL_TAC >> simp[]
QED
