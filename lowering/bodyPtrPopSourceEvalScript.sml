Theory bodyPtrPopSourceEval
Ancestors
  bodyPtrPopGlobalPremises bodyPtrPopTargetFactor vyperInterpreter vyperValue vyperState

(* Check the actual index call, rather than only the callable's typing. *)
Theorem pop_global_index_evaluates:
  ?s. eval_expr pop_global_cx
    (Call (BaseT (UintT 256)) (IntCall (NONE,"replace")) [] NONE)
    pop_global_es = (INL (Value (IntV 0)),s)
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem pop_global_saved_target_evaluates:
  ?s. eval_base_place pop_global_cx
    (SubscriptTarget pop_struct_field (Literal (BaseT (UintT 256)) (IntL 0)))
    pop_global_es =
    (INL (PlaceR (StoragePlace F 1w
      (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 1)))),s)
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem pop_global_target_evaluates:
  ?s. eval_base_place pop_global_cx pop_global_target pop_global_es =
    (INL (PlaceR (StoragePlace F 2w
      (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)))),s)
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[] >> EVAL_TAC >> simp[return_def]
QED
