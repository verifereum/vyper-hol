(* Static instruction inventory of the unwrapped singleton ABI-word suffix. *)
Theory entryCreateAbiWordInventory
Ancestors
  abiBuiltinEncodeCode abiEncoderProps builtinAbi context compileEnv emitHelper
  createSizeCutCode exprSimAbiGasBridge exprLoweringProps fragExec venomInst
  words list rich_list arithmetic

Theorem abi_encode_word_pack_inventory:
  lower_abi_encode meth 32
    (\dst. comp_ignore_bind (emit_void MSTORE [dst;op]) (comp_return (Lit 32w)))
    sm = (out,sb) ==>
  sb.cs_blocks = sm.cs_blocks /\
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  cs_extends sm sb /\
  sm.cs_next_id < sb.cs_next_id /\
  sm.cs_next_var <= sb.cs_next_var /\
  LENGTH sm.cs_current_insts < LENGTH sb.cs_current_insts /\
  emitted_insts sm sb <> [] /\
  create_cut_code {} sm sb /\
  EVERY (\i. i.inst_id IN frag_ids sm sb /\
             ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ i.inst_opcode <> CREATE /\
             i.inst_opcode <> CREATE2) (emitted_insts sm sb)
Proof
  Cases_on `meth` >>
  simp[lower_abi_encode_phases, abi_builtin_encode_setup_def,
       abi_builtin_encode_method_id_def, abi_builtin_encode_finish_def,
       compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[create_cut_code_def, frag_code_def, emitted_blocks_def,
       emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, cs_extends_same_block,
       frag_ids_def, mk_inst_def, is_terminator_def, create_cut_targets_def] >>
  rpt strip_tac >> gvs[]
QED
