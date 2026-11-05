Theory targetSubscriptUniversalProbe
Ancestors
  targetSubscriptProbe words vyperStorage vyperStorageBackend vyperState
  vyperInterpreter vyperContext vyperValue vfmState
Libs
  pairLib

Theorem clear_call_symbolic:
  !es.
    eval_expr probe_clear_source_context
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es =
    (INL (Value (IntV 0)),
     set_storage probe_clear_source_context es F
       (update_storage 0w 0w (get_storage probe_clear_source_context es F)))
Proof
  gen_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_storage_backend``,
    ``set_storage_backend``, ``lookup_storage``]) >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_storage_backend``,
    ``set_storage_backend``, ``lookup_storage``]) >>
  simp[get_storage_backend_eq, get_storage_scopes] >>
  simp[set_storage_backend_eq, handle_function_def, return_def,
       set_storage_def, evaluation_state_component_equality] >>
  simp[get_storage_def] >> EVAL_TAC
QED

Theorem clear_root_symbolic[local]:
  !es. eval_base_place probe_clear_source_context
    (TopLevelNameTarget (NONE,"outer")) es =
    (INL (PlaceR (StoragePlace F 0w
      (ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1))
        (Dynamic 1)) (Dynamic 1)))), es)
Proof
  gen_tac >> EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >> EVAL_TAC
QED

Theorem clear_base_symbolic:
  !es.
    eval_base_place probe_clear_source_context probe_clear_source_bt es =
    if lookup_storage 0w (get_storage probe_clear_source_context es F) = 0w
    then (INR (Error (RuntimeError "array dynamic length oob")), es)
    else
      let es' = set_storage probe_clear_source_context es F
        (update_storage 0w 0w (get_storage probe_clear_source_context es F)) in
      if lookup_storage 1w (get_storage probe_clear_source_context es F) = 0w
      then (INR (Error (RuntimeError "array dynamic length oob")), es')
      else (INL (PlaceR (StoragePlace F 2w
        (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)))), es')
Proof
  gen_tac >> simp[probe_clear_source_bt_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def, clear_root_symbolic] >>
  simp[Once evaluate_def, vyperValueOperationTheory.evaluate_literal_def,
       return_def, bind_def, read_result_def] >>
  simp[targetSubscriptSimTheory.extend_place_storage_array_index,
       wordsTheory.w2n_eq_0, clear_call_symbolic,
       read_result_def, return_def] >>
  Cases_on `lookup_storage 0w (get_storage probe_clear_source_context es F) = 0w` >>
  gvs[GSYM arithmeticTheory.NOT_ZERO_LT_ZERO, wordsTheory.w2n_eq_0] >>
  simp[targetSubscriptSimTheory.extend_place_storage_array_index,
       GSYM arithmeticTheory.NOT_ZERO_LT_ZERO, wordsTheory.w2n_eq_0,
       get_storage_after_set] >>
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM,
       wordsTheory.WORD_ADD_0, wordsTheory.word_add_n2w, dimword_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  Cases_on `get_storage probe_clear_source_context es F 1w = 0w` >> simp[]
QED
