Theory runtimeSymSrcDataExtCallArgs
Ancestors
  symbolicSourceCompilerExprFrame
  runtimeSymSrcDataFrame exprLowering

fun apply_symbolic_frame theorem =
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data` (Q.GEN `R` theorem)))

Theorem runtime_data_frame_ext_call_args:
  (!e ty. MEM e es ==> runtime_data_frame (cfn cenv ty e)) /\
  (!copy vv. runtime_data_frame (compile_snapshot_vv cenv copy vv)) ==>
  runtime_data_frame (compile_ext_call_args cfn cenv kw_es tys es)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_ext_call_args >> simp[]
QED
