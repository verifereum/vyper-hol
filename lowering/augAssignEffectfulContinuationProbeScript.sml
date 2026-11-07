(* Conditional execution equations for the saved fixed-array bt.  The
   premises describe executions; they do not assert a complete program. *)
Theory augAssignEffectfulContinuationProbe
Ancestors
  augAssignEffectfulOutcomeProbe vyperInterpreter vyperState
  vyperStorageBackend vyperStorage vyperValueOperation
  venomExecSemantics venomState venomInst emitHelper exprLowering finite_map

Theorem saved_fixed_index_after_effect:
  eval_base_place cx bt es =
    (INL (PlaceR (StoragePlace tr 1w
      (ArrayTV (BaseTV (UintT 8)) (Fixed 1)))), mid) /\
  eval_expr cx key mid = (INL (Value (IntV 0)), post) ==>
  eval_target_place cx (SubscriptTarget bt key) es =
    (INL (StoragePlace tr 1w (BaseTV (UintT 8))), post)
Proof
  strip_tac >>
  simp[Once evaluate_def] >>
  simp[Once evaluate_def] >>
  fs[bind_def, read_result_def, return_def, extend_place_def,
     extend_storage_place_def, resolve_array_element_def,
     ignore_bind_def, check_def, get_place_def] >>
  simp[assert_def, return_def, bind_def, ignore_bind_def,
       get_place_def, wordsTheory.WORD_ADD_0]
QED

Theorem saved_scalar_read_noncanonical:
  get_storage cx post tr = update_storage 1w 256w (\k. 0w) ==>
  read_place cx (StoragePlace tr 1w (BaseTV (UintT 8))) post =
    (INL (IntV 0), post)
Proof
  strip_tac >>
  simp[read_place_def, read_storage_slot_def, get_storage_backend_eq,
       bind_def, lift_option_def, return_def] >>
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss] >> EVAL_TAC
QED
