(* The zero-hi calldata bytes decoder cannot execute a dynamic allocation. *)
Theory calldataBytesSentinelShape
Ancestors
  abiEncoder compileEnv emitHelper exprLoweringProps venomInst list rich_list

Theorem calldata_bytes_sentinel_non_dalloca:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring n) st = ((),st') ==>
  EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts st st')
Proof
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
       compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED
