Theory bodyPtrPopSnapshotProbe
Ancestors vyperState vyperInterpreter

(* History fallback does not bypass extend_place's live-array index check. *)
Theorem pop_snapshot_empty_live_index_rejected:
  evaluate_subscripts
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2))
    (ArrayV (DynArrayV [])) [ValueSubscript (IntV 0)] =
    INR (RuntimeError "evaluate_subscripts array_index")
Proof
  EVAL_TAC
QED

Theorem pop_snapshot_empty_extension_rejected:
  entry.type = ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2) /\
  entry.value = ArrayV (DynArrayV []) /\
  lookup_scopes id es.scopes = SOME entry ==>
  extend_place cx (PlaceR (MemoryPlace id [])) (ValueSubscript (IntV 0)) es =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")),es)
Proof
  strip_tac >>
  simp[extend_place_def, place_type_value_def, read_place_def,
       read_memory_path_def, bind_def, get_scopes_def, lift_option_type_def,
       return_def, lift_sum_def, pop_snapshot_empty_live_index_rejected] >>
  EVAL_TAC >> gvs[] >> EVAL_TAC >> gvs[] >> EVAL_TAC
QED

Theorem pop_snapshot_literal_target_rejected:
  entry.type = ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2) /\
  entry.value = ArrayV (DynArrayV []) /\
  lookup_scopes id es.scopes = SOME entry ==>
  eval_target_place cx
    (SubscriptTarget (NameTarget id) (Literal (BaseT (UintT 256)) (IntL 0))) es =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")),es)
Proof
  strip_tac >>
  simp[Once evaluate_def] >>
  simp[Once evaluate_def] >>
  simp[Once evaluate_def] >>
  simp[bind_def, get_scopes_def, type_check_def, return_def] >>
  simp[ignore_bind_def, assert_def, bind_def, return_def] >>
  simp[Once evaluate_def] >>
  simp[read_result_def, return_def, bind_def,
       pop_snapshot_empty_extension_rejected] >>
  `evaluate_literal (IntL 0) = IntV 0` by EVAL_TAC >> simp[] >>
  drule_all pop_snapshot_empty_extension_rejected >> simp[]
QED
