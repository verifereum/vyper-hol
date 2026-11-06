Theory exprSimAbiDecodeRealizeFunctionBoundary
Ancestors
  exprSimAbiDecodeRealizeFunction exprSimAbiDecodeRealizeStraight
  exprSimAbiDecodeRealizeIds fragExec compileEnv vyperCompiler venomWf
  venomInst list

Theorem abi_decode_realize_function_has_code:
  fn_has_code (initial_compile_state entry) (abi_decode_realize_final ce k entry)
    (abi_decode_realize_function ce k entry)
Proof
  simp[fn_has_code_def, emitted_blocks_def,
       abi_decode_realize_function_def, abi_decode_realize_final_single_block,
       initial_compile_state_def, mk_raw_function_def, lookup_block_def, FIND_thm]
QED

Theorem abi_decode_realize_function_ids:
  fn_inst_ids_distinct (abi_decode_realize_function ce k entry)
Proof
  mp_tac abi_decode_realize_final_ids >>
  simp[fn_inst_ids_distinct_def, abi_decode_realize_function_def,
       abi_decode_realize_final_single_block, mk_raw_function_def,
       exprSimAbiDecodeRealizeFootprintTheory.abi_decode_realize_code_def]
QED
