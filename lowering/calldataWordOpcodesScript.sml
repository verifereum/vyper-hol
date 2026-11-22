(* Opcode restrictions for the primitive calldata decoder with zero base. *)
Theory calldataWordOpcodes
Ancestors
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper venomInst list rich_list

Theorem calldata_word_checked_opcodes:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES /\
             i.inst_opcode <> DALLOCA)
    (emitted_insts st st')
Proof
  Cases_on `clamp` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
       compile_abi_decode_range_check_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED
