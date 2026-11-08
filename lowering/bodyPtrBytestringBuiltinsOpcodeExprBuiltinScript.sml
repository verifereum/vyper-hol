Theory bodyPtrBytestringBuiltinsOpcodeExprBuiltin
Ancestors bodyPtrBytestringBuiltinsOpcodeScalars
          bodyPtrBytestringBuiltinsOpcodeState
          exprSimHypsDefs exprLowering vyperAST

Theorem no_extcode_expr_builtin_names[local]:
  !bi args. names_builtin bi args ==>
    !cfn bfn tfn ce rt ty s. compiler_no_extcode s ==>
    compiler_no_extcode
      (SND (compile_expr_body cfn bfn tfn ce ty (Builtin rt bi args) s))
Proof
  recInduct names_builtin_ind >>
  simp[names_builtin_def, compile_expr_body_def, expr_type_def,
       no_extcode_addmod_names, no_extcode_mulmod_names,
       no_extcode_powmod256_names]
QED

Theorem no_extcode_expr_builtin:
  !bi args cfn bfn tfn ce rt ty s.
    compiler_no_extcode s /\
    compiler_no_extcode (SND (bfn ce rt ty bi args s)) ==>
    compiler_no_extcode
      (SND (compile_expr_body cfn bfn tfn ce ty (Builtin rt bi args) s))
Proof
  rpt gen_tac >> Cases_on `names_builtin bi args` >>
  simp[no_extcode_expr_builtin_names, compile_expr_body_builtin_dispatch]
QED
