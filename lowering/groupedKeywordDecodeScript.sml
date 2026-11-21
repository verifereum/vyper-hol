(* The positional and supplied keyword parts share the calldata head. *)
Theory groupedKeywordDecode
Ancestors vyperCalldata list arithmetic

Theorem calldata_decode_args_split:
  !pos kw vals cd off.
    calldata_decode_args cd (pos ++ kw) off = SOME vals ==>
    calldata_decode_args cd pos off = SOME (TAKE (LENGTH pos) vals) /\
    calldata_decode_args cd kw (off + SUM (MAP tv_abi_size pos)) =
      SOME (DROP (LENGTH pos) vals)
Proof
  Induct >- simp[calldata_decode_args_def] >>
  rpt gen_tac >> simp[Once calldata_decode_args_def, LET_THM] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  simp[Once calldata_decode_args_def, LET_THM, ADD_ASSOC]
QED
