(* Linked RawLog continuation after the topics, for fixed bytes32 data. *)
Theory bodyRawLogFixedDataMods
Ancestors
  bodyFullPostsMods bodySliceFixedAllocMods bodyForcedStorageFrameMods
  bodyWriteSubscriptSourceMods exprBodyPreTypingProps vyperTypeExtCallCore
  gasOutcomeFullBindMods gasOutcomeFullZeroPrefixMods gasOutcomeFullPostMods
  gasContext exprSimDefs exprSimFullBundleProps stmtSimForRounds
  bodyFullPredsMods exprBodyPreProps
  vyperEvent vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  vyperValue vyperTyping vyperTypeExprSoundness
Libs monadsyntax

val raw_log_next = ``\v. do
    bs <- lift_option_type (dest_BytesV v) "raw_log data";
    type_check (LENGTH vals <= 4) "raw_log too many topics";
    check_not_static cx;
    push_log (encode_raw_event_values cx.txn.target vals bs);
    return NoneV
  od``;

Theorem fixed_log_next_replay[local]:
  LENGTH vals <= 4 ==>
  (^raw_log_next) (BytesV bs) (ee with gas_obs := tail) =
    if cx.txn.is_static then
      (INR (Error (RuntimeError "write in static context")),ee with gas_obs := tail)
    else
      (INL NoneV,ee with <|logs := ee.logs ++
          [encode_raw_event_values cx.txn.target vals bs]; gas_obs := tail|>)
Proof
  simp[dest_BytesV_def, lift_option_type_def, type_check_def, check_not_static_def,
       check_def, assert_def, push_log_def, bind_def, ignore_bind_def,
       raise_def, return_def] >>
  Cases_on `cx.txn.is_static` >> simp[]
QED

Theorem fixed_log_next_frame[local]:
  storage_trace_frame ((^raw_log_next) v)
Proof
  BETA_TAC >> irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_lifts] >> gen_tac >> BETA_TAC >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_check_not_static] >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_state_updates, storage_trace_frame_return]
QED

Theorem fixed_log_data_bytes[local]:
  expr_body_pre_mods mods cenv cx env data es /\
  body_const_cells_agree_mods mods cx env es /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  bind (eval_expr cx data) (read_result cx) (es with gas_obs := obs) = (INL v,mid) ==>
  ?bs. v = BytesV bs /\ LENGTH bs = 32
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env data (es with gas_obs := obs) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := obs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac runtime_consistent_get_tenv >>
  gvs[value_runtime_typed_def, evaluate_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def]
QED
