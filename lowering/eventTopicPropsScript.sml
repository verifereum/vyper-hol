(* Word-topic lowering preserves the type-directed source encoding, including
   bytes20 versus address. The operand premise is the expression boundary. *)
Theory eventTopicProps
Ancestors
  e2eDefs stmtLowering context compileEnv valueEncoding vyperValue vyperEvent
  venomExecSemantics

Theorem word_base_topic_encoding:
  is_word_type (BaseT bt) /\ evaluate_type tenv (BaseT bt) = SOME tv ==>
  ~is_bytestring_type (BaseT bt) /\
  encode_event_topic (BaseT bt) v = SOME (typed_val_to_w256 tv v)
Proof
  Cases_on `bt` >> gvs[is_word_type_def, evaluate_type_def] >>
  TRY (rename1 `is_word_type (BaseT (BytesT bound))` >>
    Cases_on `bound` >> gvs[is_word_type_def, evaluate_type_def]) >>
  rpt strip_tac >> gvs[is_bytestring_type_def] >>
  Cases_on `v` >>
  simp[is_bytestring_type_def, encode_event_topic_def,
       is_event_bytestring_type_def, event_topic_word_def,
       typed_val_to_w256_def, event_value_to_word_eq_val_to_w256]
QED

Theorem word_topic_encoding:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv ==>
  ~is_bytestring_type ty /\
  encode_event_topic ty v = SOME (typed_val_to_w256 tv v)
Proof
  Cases_on `ty` >> gvs[is_word_type_def] >> rpt strip_tac >>
  FIRST [drule_all word_base_topic_encoding >> simp[],
    gvs[evaluate_type_def, AllCaseEqs(), is_bytestring_type_def,
        encode_event_topic_def, is_event_bytestring_type_def,
        event_topic_word_def, typed_val_to_w256_def,
        event_value_to_word_eq_val_to_w256]]
QED

Theorem compile_word_topic_correct:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  eval_operand op vs = SOME (typed_val_to_w256 tv v) ==>
  compile_encode_log_topic op (is_bytestring_type ty) cs = (op,cs) /\
  eval_operand op vs = encode_event_topic ty v
Proof
  strip_tac >> drule_all word_topic_encoding >> strip_tac >>
  simp[compile_encode_log_topic_def, comp_return_def]
QED

Theorem compile_log_primitive_topics:
  EVERY (\topic. ~SND topic) topics ==>
  compile_log_topic_ops topics cs = (MAP FST topics,cs)
Proof
  qid_spec_tac `cs` >> Induct_on `topics`
  >- simp[compile_log_topic_ops_def, comp_return_def] >>
  qx_gen_tac `topic` >> qx_gen_tac `cs` >> Cases_on `topic` >>
  simp[] >> strip_tac >>
  simp[compile_log_topic_ops_def, compile_encode_log_topic_def,
       comp_bind_def, comp_return_def]
QED
