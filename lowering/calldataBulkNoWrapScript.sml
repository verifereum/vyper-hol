(* The zero-base, unbounded bulk calldata decoder emits no dynamic allocation. *)
Theory calldataBulkNoWrap
Ancestors
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper venomInst
  list rich_list

Theorem calldata_bulk_non_dalloca:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei ==>
  EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts st st')
Proof
  strip_tac >>
  gvs[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
      compile_abi_decode_range_check_def] >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def]
QED
