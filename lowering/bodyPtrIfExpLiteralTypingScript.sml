Theory bodyPtrIfExpLiteralTyping
Ancestors
  exprLowering vyperInterpreter vyperState vyperValue vyperTypeSystem
  vyperValueOperation vyperTyping exprSimHypsDefs allocLimits vfmConstants
  words

Theorem ifexp_string_literal_lowered_typed:
  !cx ce env n payload es raw ee v er.
    expr_body_pre ce cx env (Literal (BaseT (StringT n)) (StringL payload)) es /\
    eval_expr cx (Literal (BaseT (StringT n)) (StringL payload)) es = (INL raw,ee) /\
    read_result cx raw ee = (INL v,er) ==>
    ?sv. evaluate_type (get_tenv cx)
      (lowered_value_type ce (Literal (BaseT (StringT n)) (StringL payload))) = SOME sv /\
      value_has_type sv v
Proof
  rpt strip_tac >>
  `literal_alloc_ok (StringL payload)` by
    gvs[expr_body_pre_def, alloc_limits_expr_def] >>
  gvs[Once evaluate_def, return_def, read_result_def,
      lowered_value_type_def, evaluate_literal_def, evaluate_type_def,
      value_has_type_def, literal_alloc_ok_def, type_slot_size_def,
      word_size_def] >>
  simp[dimword_def] >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `STRLEN payload + 31` strip_assume_tac) >>
  `(STRLEN payload + 31) MOD 32 < 32` by simp[] >>
  decide_tac
QED

Theorem ifexp_bytes_literal_lowered_typed:
  !cx ce env n payload es raw ee v er.
    expr_body_pre ce cx env (Literal (BaseT (BytesT (Dynamic n))) (BytesL payload)) es /\
    eval_expr cx (Literal (BaseT (BytesT (Dynamic n))) (BytesL payload)) es = (INL raw,ee) /\
    read_result cx raw ee = (INL v,er) ==>
    ?sv. evaluate_type (get_tenv cx)
      (lowered_value_type ce (Literal (BaseT (BytesT (Dynamic n))) (BytesL payload))) = SOME sv /\
      value_has_type sv v
Proof
  rpt strip_tac >>
  `literal_alloc_ok (BytesL payload)` by
    gvs[expr_body_pre_def, alloc_limits_expr_def] >>
  gvs[Once evaluate_def, return_def, read_result_def,
      lowered_value_type_def, evaluate_literal_def, evaluate_type_def,
      value_has_type_def, literal_alloc_ok_def, type_slot_size_def,
      word_size_def] >>
  simp[dimword_def] >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `LENGTH payload + 31` strip_assume_tac) >>
  `(LENGTH payload + 31) MOD 32 < 32` by simp[] >>
  decide_tac
QED
