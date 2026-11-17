(* The only gas instruction in either generated SHA suffix. *)
Theory bodyFullHashShaLayout
Ancestors
  bodyFullHashShaGas
  builtinHashing context emitHelper compileEnv exprLoweringProps
  venomInst list rich_list arithmetic
  exprSimHash gasExplicitSites gasShadowState gasShadowUnit
  gasShadowUnitObservations pred_set

Theorem sha_fixed_gas_layout:
  compile_sha256_bytesm value m sa = (op,sb) ==>
  ?prefix gv code.
    emitted_insts sa sb = prefix ++ mk_inst (sa.cs_next_id+3) GAS [] [gv]::code /\
    EVERY (\i. MEM i.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD]) prefix /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) code
Proof
  strip_tac >>
  qexistsl_tac [`TAKE 3 (emitted_insts sa sb)`,
    `STRING #"%" (toString (sa.cs_next_var+2))`, `DROP 4 (emitted_insts sa sb)`] >>
  qpat_x_assum `compile_sha256_bytesm value m sa = _` mp_tac >>
  simp[compile_sha256_bytesm_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, DROP_LENGTH_APPEND,
    APPEND_ASSOC, mk_inst_def, is_terminator_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem sha_bytes_gas_layout:
  compile_sha256_bytes value sa = (op,sb) ==>
  ?prefix gv code.
    emitted_insts sa sb = prefix ++ mk_inst (sa.cs_next_id+3) GAS [] [gv]::code /\
    EVERY (\i. MEM i.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD]) prefix /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) code
Proof
  strip_tac >>
  qexistsl_tac [`TAKE 3 (emitted_insts sa sb)`,
    `STRING #"%" (toString (sa.cs_next_var+3))`, `DROP 4 (emitted_insts sa sb)`] >>
  qpat_x_assum `compile_sha256_bytes value sa = _` mp_tac >>
  simp[compile_sha256_bytes_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, DROP_LENGTH_APPEND,
    APPEND_ASSOC, mk_inst_def, is_terminator_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED

