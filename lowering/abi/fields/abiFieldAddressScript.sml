(* TOP-LEVEL: replay the exact source-address ADD used for every aggregate
   field. It preserves memory and every operand except its own SSA output. *)
Theory abiFieldAddress
Ancestors
  abiComplexCode abiMemoryFrame abiStaticLoopCode ssaOperandFrame
  compileEnv exprLoweringProps emitHelperProps fragExec fragBlockPath instIdxIndep
  venomState venomExecSemantics venomInst list rich_list words arithmetic

Definition abi_field_address_state_def:
  abi_field_address_state cs source_offset src_addr ss =
    (update_var (compiler_var_name cs.cs_next_var 0) (src_addr + n2w source_offset) ss)
      with vs_inst_idx := LENGTH cs.cs_current_insts + 1
End

Theorem abi_field_address_state_frame:
  !cs source_offset src_addr ss.
    (abi_field_address_state cs source_offset src_addr ss).vs_current_bb = ss.vs_current_bb /\
    (abi_field_address_state cs source_offset src_addr ss).vs_inst_idx = LENGTH cs.cs_current_insts + 1 /\
    (abi_field_address_state cs source_offset src_addr ss).vs_halted = ss.vs_halted /\
    (abi_field_address_state cs source_offset src_addr ss).vs_memory = ss.vs_memory /\
    abi_memory_frame [] ss (abi_field_address_state cs source_offset src_addr ss)
Proof
  simp[abi_field_address_state_def, update_var_def, abi_memory_frame_def, read_memory_def]
QED

Theorem abi_field_address_state_operand:
  !cs source_offset src_addr ss arg_op.
    arg_op <> Var (compiler_var_name cs.cs_next_var 0) ==>
    eval_operand arg_op (abi_field_address_state cs source_offset src_addr ss) = eval_operand arg_op ss
Proof
  simp[abi_field_address_state_def, eval_op_inst_idx, eval_operand_update_var_avoids]
QED

Theorem abi_field_address_memory:
  !cs source_offset src_addr ss offset byte_count.
    read_memory offset byte_count (abi_field_address_state cs source_offset src_addr ss) =
      read_memory offset byte_count ss /\
    mload offset (abi_field_address_state cs source_offset src_addr ss) = mload offset ss
Proof
  simp[read_memory_def, mload_def, abi_field_address_state_frame]
QED

Theorem abi_field_address_state_value:
  !cs source_offset src_addr ss.
    eval_operand (Var (compiler_var_name cs.cs_next_var 0))
      (abi_field_address_state cs source_offset src_addr ss) = SOME (src_addr + n2w source_offset)
Proof
  simp[abi_field_address_state_def, eval_op_inst_idx, eval_operand_update_var]
QED

Theorem abi_field_address_path:
  !ctx func src source_offset cs ss src_addr.
    fn_has_code cs (abi_complex_field_cut src source_offset cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand src ss = SOME src_addr ==>
    fragment_path ctx func ss (abi_field_address_state cs source_offset src_addr ss)
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst cs.cs_next_id ADD [src; Lit (n2w source_offset)]
    [compiler_var_name cs.cs_next_var 0]) ss =
    OK (update_var (compiler_var_name cs.cs_next_var 0) (src_addr + n2w source_offset) ss)` by
    (irule step_ADD >> simp[eval_operand_lit]) >>
  `run_inst_seq [mk_inst cs.cs_next_id ADD [src; Lit (n2w source_offset)]
    [compiler_var_name cs.cs_next_var 0]] ss =
    OK (update_var (compiler_var_name cs.cs_next_var 0) (src_addr + n2w source_offset) ss)` by
    simp[run_inst_seq_def] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `abi_complex_field_cut src source_offset cs`, `ss`,
    `update_var (compiler_var_name cs.cs_next_var 0) (src_addr + n2w source_offset) ss`]
    fragment_path_emitted) >>
  impl_tac
  >- (asm_simp_tac (srw_ss()) [abi_complex_field_cut_def, emitted_insts_def, same_blocks_def,
        DROP_LENGTH_APPEND] >> simp[mk_inst_def, is_terminator_def]) >>
  simp[abi_field_address_state_def, abi_complex_field_cut_def]
QED
