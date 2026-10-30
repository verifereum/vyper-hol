(* TOP-LEVEL: the actual bytestring encoder executes after the dynamic-child
   prefix, retaining the saved parent head/offset and counter operand. *)
Theory abiChildBytesExec
Ancestors
  abiAllocatorState
  abiStateFrameOps abiStateFrame abiChildBytesStart abiChildBytesReady abiChildPrefix abiChildCode abiChildMemoryFrame abiMemoryFrame
  abiBytestringCorrect abiBytestringCode abiBytestringExec abiBytestringMemory
  abiStaticLoopCode contractABI instIdxIndep compileEnv
  venomState venomExecSemantics list words arithmetic

Theorem bytestring_copy_state_halted[simp]:
  !dst_addr src_addr ss.
    (bytestring_copy_state dst_addr src_addr ss).vs_halted = ss.vs_halted
Proof
  simp_tac (pure_ss ++ boolSimps.BOOL_ss ++ rewrites
    [venom_state_accfupds, combinTheory.K_THM, LET_THM])
    [bytestring_copy_state_def, mcopy_def, mstore_def, write_memory_with_expansion_def]
QED

Theorem abi_child_bytes_execution:
  !ctx func dst src dyn_ptr head_offset cap cs child_len mid ss dst_addr dyn_addr src_addr bs.
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 2)) src (AbiBytestring cap)
      (abi_child_prefix_cut dst dyn_ptr head_offset cs) = (child_len,mid) /\
    fn_has_code (abi_child_prefix_cut dst dyn_ptr head_offset cs) mid func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ~ss.vs_halted /\
    eval_operand src ss = SOME src_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    EVERY (\name. src <> Var name /\ dyn_ptr <> Var name) (compiler_var_names cs.cs_next_var 12) /\
    bytestring_abi_pre (dst_addr + mload (w2n dyn_addr) ss) src_addr bs ss ==>
    ?out.
      fragment_path ctx func
        ((abi_child_prefix_state cs.cs_next_var head_offset dst_addr dyn_addr ss) with
          vs_inst_idx := LENGTH (abi_child_prefix_cut dst dyn_ptr head_offset cs).cs_current_insts) out /\
      out.vs_current_bb = mid.cs_current_bb /\ out.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~out.vs_halted /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 0)) out = SOME (dst_addr + n2w head_offset) /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 1)) out = SOME (mload (w2n dyn_addr) ss) /\
      eval_operand dyn_ptr out = SOME dyn_addr /\
      eval_operand child_len out = SOME (n2w (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))) /\
      read_memory (w2n (dst_addr + mload (w2n dyn_addr) ss))
        (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) out = enc (Bytes NONE) (contractABI$BytesV bs) /\
      mid.cs_next_var = cs.cs_next_var + 11 /\ dyn_ptr <> Var (compiler_var_name mid.cs_next_var 0) /\
      abi_memory_frame [(w2n (dst_addr + mload (w2n dyn_addr) ss),
        LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))] ss out /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 12) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\ abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`dst`, `src`, `dyn_ptr`, `head_offset`, `cs`, `ss`, `dst_addr`, `dyn_addr`, `src_addr`, `bs`]
    abi_child_bytes_start_ready) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM, EVERY_CONJ]) >>
  drule compile_abi_bytestring_code >> strip_tac >>
  `mid.cs_next_var = cs.cs_next_var + 11` by fs[abi_child_prefix_cut_def] >>
  qabbrev_tac `addressed = (abi_child_prefix_state cs.cs_next_var head_offset dst_addr dyn_addr ss) with
    vs_inst_idx := LENGTH (abi_child_prefix_cut dst dyn_ptr head_offset cs).cs_current_insts` >>
  mp_tac (Q.SPECL [`ctx`, `func`, `Var (compiler_var_name cs.cs_next_var 2)`, `src`, `cap`,
    `abi_child_prefix_cut dst dyn_ptr head_offset cs`, `child_len`, `mid`, `addressed`,
    `dst_addr + mload (w2n (dyn_addr:bytes32)) ss`, `src_addr`, `bs`] compile_abi_bytestring_correct_path) >>
  impl_tac >- fs[Abbr`addressed`, abi_child_prefix_cut_def, abi_child_prefix_frame, EVERY_CONJ] >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `abi_state_frame ss out` by
    (qpat_x_assum `out with vs_vars := _ = _` (mp_tac o AP_TERM ``abi_state_context``) >>
     simp[Abbr`addressed`, abi_state_frame_def]) >>
  `abi_allocator_state out = abi_allocator_state ss` by
    (qpat_assum `out with vs_vars := _ = _` (mp_tac o AP_TERM ``abi_allocator_state``) >>
     simp[Abbr`addressed`]) >>
  `~out.vs_halted` by
    (qpat_x_assum `out with vs_vars := _ = _` (mp_tac o AP_TERM ``\st:venom_state. st.vs_halted``) >>
     asm_simp_tac (srw_ss()) [Abbr`addressed`, abi_child_prefix_frame]) >>
  `eval_operand (Var (compiler_var_name cs.cs_next_var 0)) out = SOME (dst_addr + n2w head_offset)` by
    (qpat_x_assum `!arg_op. EVERY _ _ ==> _`
       (qspec_then `Var (compiler_var_name cs.cs_next_var 0)` mp_tac) >>
     asm_simp_tac (srw_ss()) [Abbr`addressed`]) >>
  `eval_operand (Var (compiler_var_name cs.cs_next_var 1)) out = SOME (mload (w2n dyn_addr) ss)` by
    (qpat_x_assum `!arg_op. EVERY _ _ ==> _`
       (qspec_then `Var (compiler_var_name cs.cs_next_var 1)` mp_tac) >>
     asm_simp_tac (srw_ss()) [Abbr`addressed`]) >>
  `eval_operand dyn_ptr out = SOME dyn_addr` by
    (qpat_x_assum `!arg_op. EVERY _ _ ==> _` (qspec_then `dyn_ptr` mp_tac) >>
     asm_simp_tac (srw_ss()) [Abbr`addressed`]) >>
  mp_tac (Q.SPECL [`dst_addr + mload (w2n (dyn_addr:bytes32)) ss`, `bs`, `cs.cs_next_var`,
    `head_offset`, `dst_addr`, `dyn_addr`, `ss`,
    `LENGTH (abi_child_prefix_cut dst dyn_ptr head_offset cs).cs_current_insts`, `out`]
    abi_child_bytes_read_memory_frame) >> impl_tac
  >- (qpat_x_assum `!offset read_len. _` mp_tac >>
      simp[Abbr`addressed`, abi_child_prefix_read_memory]) >> DISCH_TAC >>
  qexists_tac `out` >> asm_simp_tac (srw_ss()) [Abbr`addressed`] >>
  qx_gen_tac `arg_op` >> DISCH_TAC >>
  mp_tac (Q.SPECL [`arg_op`, `cs.cs_next_var`] abi_child_bytes_input_names) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `head_offset`, `dst_addr`, `dyn_addr`, `ss`, `arg_op`]
    abi_child_prefix_operand_frame) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  qpat_x_assum `!arg_op. EVERY _ _ ==> _` (qspec_then `arg_op` mp_tac) >>
  asm_simp_tac (srw_ss()) [abi_child_prefix_cut_def, eval_op_inst_idx]
QED
