(* The compiler's positional snapshot schedule for the wrapped encoder. *)
Theory entryCreateAbiEncodeTuple
Ancestors
  createSizeCreateLayoutCode createSizeConcreteSnapshots createSizeOperandCode
  exprSimAbiEncodeRuntimeInputs abiEncodeArgsCase exprSimHypsDefs
  bodyFullAbiEncodeTupleFull exprLowering vyperTypeSystem vyperAST list

Theorem abi_encode_args_ctor_schedule:
  !args. compile_abi_encode_args cfn ce args = compile_create_ctor_args cfn ce args
Proof
  rw[compile_abi_encode_args_def] >> Induct_on `args` >>
  simp[compile_ext_call_args_def, compile_create_ctor_args_def]
QED

Theorem abi_encode_args_entry_cut_code:
  create_cut_code {} sa (SND (compile_abi_encode_args compile_expr ce args sa))
Proof
  simp[abi_encode_args_ctor_schedule] >> irule create_ctor_args_cut >>
  simp[create_operand_cut_code, create_vv_snapshot_cut_code]
QED

Theorem abi_encode_tuple_nonempty_args:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es ==>
  1 <= LENGTH args
Proof
  Cases_on `args` >> simp[] >> strip_tac >>
  `well_typed_expr env (TypeBuiltin ann (AbiEncode ensure mid) target [])`
    by fs[expr_body_pre_def] >>
  pop_assum mp_tac >>
  simp[Once well_typed_expr_def, well_typed_type_builtin_args_def]
QED
