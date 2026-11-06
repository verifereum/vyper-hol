Theory bodyPtrPopFullFrameGas
Ancestors
  bodyPtrPopFullFrameSource bodyPtrPopFullFrameProbe bodyPtrPreds
  gasContext exprSimDefs vyperInterpreter vyperState vyperStorageBackend
  vyperValue

Theorem pop_full_frame_operand:
  body_base_target_ptr_ok pop_full_frame_cx (TopLevelNameTarget (NONE,"a"))
Proof
  simp[body_base_target_ptr_ok_def]
QED

Theorem pop_full_frame_source_eval_gas:
  eval_expr pop_full_frame_cx pop_full_frame_expr
    (pop_full_frame_es with gas_obs := gs) =
    (INL (PlaceR (StoragePlace F 1w (BaseTV (UintT 256)))),
     (set_storage pop_full_frame_cx pop_full_frame_es F
       ((0w =+ 0w) (K 0w))) with gas_obs := gs)
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC >>
  simp[FUN_EQ_THM, combinTheory.UPDATE_APPLY]
QED

Theorem pop_full_frame_read_result_gas:
  read_result pop_full_frame_cx
    (PlaceR (StoragePlace F 1w (BaseTV (UintT 256))))
    ((set_storage pop_full_frame_cx pop_full_frame_es F
       ((0w =+ 0w) (K 0w))) with gas_obs := gs) =
    (INL (IntV 0),
     (set_storage pop_full_frame_cx pop_full_frame_es F
       ((0w =+ 0w) (K 0w))) with gas_obs := gs)
Proof
  EVAL_TAC
QED

Theorem pop_full_frame_vv_gas_admissible:
  gas_admissible (eval_expr pop_full_frame_cx pop_full_frame_expr)
    expr_vv_res_ok pop_full_frame_es
Proof
  simp[gas_admissible_def, pop_full_frame_source_eval_gas,
       expr_vv_res_ok_def] >> rpt strip_tac >> gvs[]
QED

Theorem pop_full_frame_value_gas_admissible:
  gas_admissible
    (bind (eval_expr pop_full_frame_cx pop_full_frame_expr)
      (read_result pop_full_frame_cx)) expr_res_ok pop_full_frame_es
Proof
  simp[gas_admissible_def, bind_def, pop_full_frame_source_eval_gas,
       pop_full_frame_read_result_gas, expr_res_ok_def] >>
  rpt strip_tac >> gvs[]
QED
