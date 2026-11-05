Theory bodyPtrBytestringBuiltinsCounterexample
Ancestors
  bodyPtrBytestringBuiltinsZeroTrace bodyPtrPreds vyperTypeSystem

Theorem zero_probe_source_result:
  bind (eval_expr cx
    (Builtin (BaseT (StringT 78)) (Uint2Str 78)
      [Literal (BaseT (UintT 256)) (IntL 0)])) (read_result cx) es =
  (INL (StringV "0"), es)
Proof
  EVAL_TAC
QED

Theorem zero_probe_source_typed:
  well_typed_expr env
    (Builtin (BaseT (StringT 78)) (Uint2Str 78)
      [Literal (BaseT (UintT 256)) (IntL 0)])
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM boolTheory.ETA_THM))) >>
  qexists_tac `256` >> simp[]
QED

Theorem zero_probe_lower_value:
  lower_value compile_expr cenv ty
    (Builtin (BaseT (StringT 78)) (Uint2Str 78)
      [Literal (BaseT (UintT 256)) (IntL 0)])
    (zero_probe_compile_state with
      <|cs_next_var := 0; cs_next_id := 0; cs_current_insts := []|>) =
  (Var "%3", u2s_end zero_probe_compile_state (Lit 0w) (Var "%0") 78)
Proof
  EVAL_TAC >> simp[]
QED
