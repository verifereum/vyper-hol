Theory runtimeSymSrcDataExtCallArgs
Ancestors
  runtimeSymSrcDataFrame exprLowering

Theorem runtime_data_frame_ext_call_args:
  (!e ty. MEM e es ==> runtime_data_frame (cfn cenv ty e)) /\
  (!copy vv. runtime_data_frame (compile_snapshot_vv cenv copy vv)) ==>
  runtime_data_frame (compile_ext_call_args cfn cenv kw_es tys es)
Proof
  qid_spec_tac `tys` >> Induct_on `es` >>
  simp[compile_ext_call_args_def] >>
  gen_tac >> Cases_on `tys` >> simp[compile_ext_call_args_def] >>
  strip_tac >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac
       >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED
