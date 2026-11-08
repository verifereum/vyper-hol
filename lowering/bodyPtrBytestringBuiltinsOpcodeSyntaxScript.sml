Theory bodyPtrBytestringBuiltinsOpcodeSyntax
Ancestors bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState exprLowering

Theorem no_extcode_compile_literal:
  !ce et ty lit s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_expr ce et (Literal ty lit) s))
Proof
  rpt strip_tac >> once_rewrite_tac[compile_expr_raw_def] >>
  simp[compile_expr_body_def, no_extcode_literal_vv]
QED

Theorem no_extcode_compile_name:
  !ce et ty id s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_expr ce et (Name ty id) s))
Proof
  rpt strip_tac >> once_rewrite_tac[compile_expr_raw_def] >>
  simp[compile_expr_body_def, no_extcode_name_vv]
QED

Theorem no_extcode_lower_literal:
  !ce et ty lit s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (lower_value compile_expr ce et (Literal ty lit) s))
Proof
  rpt strip_tac >> irule no_extcode_lower_value >>
  simp[no_extcode_compile_literal]
QED

Theorem no_extcode_lower_name:
  !ce et ty id s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (lower_value compile_expr ce et (Name ty id) s))
Proof
  rpt strip_tac >> irule no_extcode_lower_value >>
  simp[no_extcode_compile_name]
QED
