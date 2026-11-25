(* Static code geometry for the raw_call preparation intervals. *)
Theory entryCreateRawCallPrepCode
Ancestors
  createSizeCutCode bodyFullRawCallCalldataCopy dallocaCalldata
  exprSimAbiGasBridge abiEncoderProps exprLoweringProps fragExec context
  builtinSystem emitHelper compileEnv venomInst list rich_list arithmetic

Theorem raw_call_header_code:
  emit_op MLOAD [data] sm = (len,sc) /\
  emit_op ADD [data; Lit 32w] sc = (data_ptr,sb) ==>
  create_cut_code {} sm sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code sm sb) /\
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_next_id = sm.cs_next_id + 2 /\
  len = Var ("%" ++ toString sm.cs_next_var) /\
  data_ptr = Var ("%" ++ toString (sm.cs_next_var + 1)) /\
  emitted_insts sm sb =
    [mk_inst sm.cs_next_id MLOAD [data] ["%" ++ toString sm.cs_next_var];
     mk_inst (sm.cs_next_id + 1) ADD [data;Lit 32w]
       ["%" ++ toString (sm.cs_next_var + 1)]]
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
  gvs[] >> conj_tac
  >- (simp[create_cut_code_def, frag_code_def, emitted_blocks_def,
           emitted_insts_def, DROP_APPEND1,
           frag_ids_def] >>
      conj_tac
      >- (irule cs_extends_same_block >> simp[] >>
          pure_once_rewrite_tac [GSYM listTheory.APPEND_ASSOC] >>
          rewrite_tac[IS_PREFIX_APPEND3]) >>
      rpt strip_tac >> gvs[mk_inst_def, create_cut_targets_def]) >>
  simp[frag_code_def, emitted_blocks_def, emitted_insts_def,
       DROP_APPEND1, mk_inst_def]
QED

Theorem raw_call_optional_gas_code:
  (case go of SOME g => (g,sm) | NONE => emit_op GAS [] sm) = (gas,sb) ==>
  create_cut_code {} sm sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code sm sb) /\
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_next_id = sm.cs_next_id + (if go = NONE then 1 else 0) /\
  emitted_insts sm sb =
    (if go = NONE then [mk_inst sm.cs_next_id GAS []
      ["%" ++ toString sm.cs_next_var]] else [])
Proof
  Cases_on `go` >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
  gvs[create_cut_code_def, frag_code_def, emitted_blocks_def, emitted_insts_def,
      cs_extends_same_block, cs_extends_refl, DROP_LENGTH_APPEND,
      frag_ids_def, mk_inst_def, create_cut_targets_def]
QED

Theorem raw_call_outbuf_code:
  compile_raw_call_outbuf cap sm = ((valop,ptrop),sb) ==>
  create_cut_code {} sm sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code sm sb) /\
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_next_id = sm.cs_next_id + (if cap = 0 then 1 else 2) /\
  emitted_insts sm sb =
    mk_inst sm.cs_next_id ALLOCA
      [Lit (n2w (if cap = 0 then 0 else ((cap + 31) DIV 32) * 32 + 32))]
      ["%" ++ toString sm.cs_next_var] ::
    (if cap = 0 then [] else
       [mk_inst (sm.cs_next_id + 1) ADD [valop; Lit 32w]
          ["%" ++ toString (sm.cs_next_var + 1)]])
Proof
  Cases_on `cap = 0` >>
  simp[compile_raw_call_outbuf_def, compile_alloc_buffer_def,
       emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
  gvs[] >>
  (conj_tac
   >- (simp[create_cut_code_def, frag_code_def, emitted_blocks_def,
            emitted_insts_def, DROP_APPEND1, frag_ids_def] >>
       conj_tac
       >- (irule cs_extends_same_block >> simp[] >>
           pure_once_rewrite_tac [GSYM listTheory.APPEND_ASSOC] >>
           rewrite_tac[IS_PREFIX_APPEND3]) >>
       rpt strip_tac >> gvs[mk_inst_def, create_cut_targets_def]) >>
   simp[frag_code_def, emitted_blocks_def, emitted_insts_def,
        DROP_APPEND1, mk_inst_def])
QED

Theorem raw_call_calldata_copy_code:
  compile_msg_data_to_memory sm = ((dp,dl),sb) ==>
  create_cut_code {} sm sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code sm sb) /\
  sm.cs_current_bb = sb.cs_current_bb /\
  sm.cs_next_var + 2 = sb.cs_next_var /\
  sm.cs_next_id + 3 = sb.cs_next_id /\
  emitted_insts sm sb =
    [mk_inst sm.cs_next_id CALLDATASIZE [] ["%" ++ toString sm.cs_next_var];
     mk_inst (sm.cs_next_id + 1) DALLOCA
       [Var ("%" ++ toString sm.cs_next_var)]
       ["%" ++ toString (sm.cs_next_var + 1)];
     mk_inst (sm.cs_next_id + 2) CALLDATACOPY
       [Var ("%" ++ toString (sm.cs_next_var + 1)); Lit 0w;
        Var ("%" ++ toString sm.cs_next_var)] []]
Proof
  strip_tac >>
  `sb.cs_blocks = sm.cs_blocks` by
    (qpat_x_assum `compile_msg_data_to_memory _ = _` mp_tac >>
     simp[compile_msg_data_to_memory_def, compile_alloc_dynamic_def,
          emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[]) >>
  drule calldata_memory_placement >> strip_tac >>
  drule calldata_memory_insts >> strip_tac >>
  `cs_extends sm sb` by (irule cs_extends_same_block >> simp[]) >>
  qpat_x_assum `sm.cs_next_id + 3 = _` (assume_tac o SYM) >>
  simp[create_cut_code_def, frag_code_def, emitted_blocks_def, frag_ids_def] >>
  rpt strip_tac >> gvs[mk_inst_def, create_cut_targets_def]
QED
