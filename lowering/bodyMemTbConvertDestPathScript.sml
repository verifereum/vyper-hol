(* Checked counted bridge for the allocating convert suffix. *)
Theory bodyMemTbConvertDestPath
Ancestors bodyAllocMemory fragGasSeqMem fragGasPathMem fragExec
  exprLoweringProps loweringSlice compileEnv rich_list

Theorem convert_alloc_header_counted_probe:
  compile_alloc_buffer n sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; value] sm = ((),sb) /\
  fn_has_code sa sb func /\ ~block_is_terminated sa /\
  stmt_state_rel ctx func cenv cx es s /\ fresh_vars_wrt sa s /\
  32 <= n /\ n < dimword (:256) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t ==>
  gas_path_mem ctx func s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS)
       (emitted_insts sa sm ++ emitted_insts sm sb)))
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
     gvs[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
         compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
         compileEnvTheory.comp_return_def, compileEnvTheory.fresh_id_def,
         compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def,
         cs_extends_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all compile_alloc_buffer_body_header_mem_ok >> strip_tac >>
  drule_all compile_alloc_buffer_body_header_slice >> strip_tac >>
  drule run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then
    [`emitted_insts sa sm ++ emitted_insts sm sb`, `t`, `ctx`, `func`, `bb`] mp_tac) >>
  simp[IS_PREFIX_APPEND]
QED
