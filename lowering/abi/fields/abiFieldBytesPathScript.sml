(* TOP-LEVEL: the actual dynamic bytestring child appends its encoding to
   arbitrary completed fields, preserving both their heads and their tails. *)
Theory abiFieldBytesPath
Ancestors
  abiAllocatorState
  abiStateFrame
  abiChildBytesPath abiFieldCompose abiFieldMemory abiFieldLayoutDefs abiMemoryFrame
  abiBytestringCorrect abiStaticLoopCode contractABI compileEnv
  venomState list pair words arithmetic
Libs wordsLib

Theorem abi_field_word_address:
  !(addr:bytes32) offset.
    w2n addr + offset < dimword(:256) ==> w2n (addr + n2w offset) = w2n addr + offset
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `addr` >> fs[word_add_n2w]
QED

Theorem compile_abi_bytes_field_extend:
  !ctx func dst src cap dyn_ptr cs op cs' ss dst_addr dyn_addr src_addr bs fields tail_offset.
    compile_abi_encode_child dst src (AbiBytestring cap) T (abi_field_head_size fields) dyn_ptr cs = (op,cs') /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand dyn_ptr ss = SOME dyn_addr /\
    EVERY (\name. src <> Var name /\ dst <> Var name /\ dyn_ptr <> Var name)
      (compiler_var_names cs.cs_next_var 13) /\
    bytestring_abi_pre (dst_addr + mload (w2n dyn_addr) ss) src_addr bs ss /\
    regions_disjoint (w2n (dst_addr + n2w (abi_field_head_size fields))) 32 (w2n dyn_addr) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss))
      (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))
      (w2n (dst_addr + n2w (abi_field_head_size fields))) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss))
      (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) (w2n dyn_addr) 32 /\
    abi_fields_layout fields (w2n dst_addr) 0 tail_offset ss /\
    mload (w2n dyn_addr) ss = n2w (tail_offset + abi_field_tail_size fields) /\
    w2n dst_addr + abi_field_head_size fields < dimword(:256) /\
    w2n dst_addr + tail_offset + abi_field_tail_size fields < dimword(:256) /\
    EVERY (\(offset,byte_count).
      abi_window_separated (w2n dst_addr) (abi_field_head_size fields) offset byte_count /\
      abi_window_separated (w2n dst_addr + tail_offset) (abi_field_tail_size fields) offset byte_count)
      [(w2n (dst_addr + mload (w2n dyn_addr) ss), LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)));
       (w2n (dst_addr + n2w (abi_field_head_size fields)),32);(w2n dyn_addr,32)] ==>
    ?out.
      fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      eval_operand op out = SOME (n2w (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))) /\
      eval_operand dyn_ptr out = SOME dyn_addr /\
      mload (w2n dyn_addr) out = n2w (tail_offset + abi_field_tail_size fields) +
        n2w (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) /\
      abi_fields_layout (fields ++ [(T,enc (Bytes NONE) (contractABI$BytesV bs))]) (w2n dst_addr) 0 tail_offset out /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 13) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_memory_frame
        [(w2n (dst_addr + mload (w2n dyn_addr) ss), LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)));
         (w2n (dst_addr + n2w (abi_field_head_size fields)),32);(w2n dyn_addr,32)] ss out /\ abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `cap`, `dyn_ptr`, `abi_field_head_size fields`,
    `cs`, `op`, `cs'`, `ss`, `dst_addr`, `dyn_addr`, `src_addr`, `bs`] compile_abi_child_bytes_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `w2n (dst_addr + n2w (abi_field_head_size fields)) = w2n dst_addr + abi_field_head_size fields` by
    (irule abi_field_word_address >> first_assum MATCH_ACCEPT_TAC) >>
  `w2n (dst_addr + mload (w2n dyn_addr) ss) = w2n dst_addr + (tail_offset + abi_field_tail_size fields)` by
    (asm_simp_tac bool_ss [] >> irule abi_field_word_address >> decide_tac) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >>
  mp_tac (Q.SPECL [`fields`, `enc (Bytes NONE) (contractABI$BytesV bs)`, `w2n (dst_addr:bytes32)`,
    `0`, `tail_offset`,
    `[(w2n (dst_addr + mload (w2n (dyn_addr:bytes32)) ss), LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)));
      (w2n (dst_addr + n2w (abi_field_head_size fields):bytes32),32);(w2n (dyn_addr:bytes32),32)]`,
    `ss`, `out`] abi_fields_layout_dynamic_extend) >>
  impl_tac >- fs[EVERY_CONJ] >> DISCH_TAC >>
  qexists_tac `out` >> asm_simp_tac (srw_ss()) []
QED
