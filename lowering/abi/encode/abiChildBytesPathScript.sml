(* TOP-LEVEL: the actual dynamic bytestring child compiler, including its
   head-offset store and tail-counter update, has a closed execution proof. *)
Theory abiChildBytesPath
Ancestors
  abiAllocatorState
  abiStateFrame abiChildRun abiChildBytesExec abiChildBytesReady abiChildStructure abiChildCode
  abiBytestringCorrect abiBytestringCode abiStaticLoopCode contractABI
  abiMemoryFrame compileEnv fragExec fragBlockPath venomState list words arithmetic

Theorem compile_abi_child_bytes_path:
  !ctx func dst src cap dyn_ptr head_offset cs op cs' ss dst_addr dyn_addr src_addr bs.
    compile_abi_encode_child dst src (AbiBytestring cap) T head_offset dyn_ptr cs = (op,cs') /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand dyn_ptr ss = SOME dyn_addr /\
    EVERY (\name. src <> Var name /\ dst <> Var name /\ dyn_ptr <> Var name)
      (compiler_var_names cs.cs_next_var 13) /\
    bytestring_abi_pre (dst_addr + mload (w2n dyn_addr) ss) src_addr bs ss /\
    regions_disjoint (w2n (dst_addr + n2w head_offset)) 32 (w2n dyn_addr) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss))
      (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) (w2n (dst_addr + n2w head_offset)) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss))
      (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) (w2n dyn_addr) 32 ==>
    ?out.
      fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      eval_operand op out = SOME (n2w (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))) /\
      mload (w2n (dst_addr + n2w head_offset)) out = mload (w2n dyn_addr) ss /\
      mload (w2n dyn_addr) out = mload (w2n dyn_addr) ss +
        n2w (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) /\
      eval_operand dyn_ptr out = SOME dyn_addr /\
      abi_memory_frame
        [(w2n (dst_addr + mload (w2n dyn_addr) ss), LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)));
         (w2n (dst_addr + n2w head_offset),32);(w2n dyn_addr,32)] ss out /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 13) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\
      read_memory (w2n (dst_addr + mload (w2n dyn_addr) ss))
        (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) out = enc (Bytes NONE) (contractABI$BytesV bs) /\
      abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_abi_encode_child _ _ _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [compile_abi_child_dynamic_cuts]) >>
  disch_then (qx_choose_then `mid` strip_assume_tac) >>
  qpat_x_assum `cs' = abi_child_suffix_cut _ _ _ _ _` SUBST_ALL_TAC >>
  qpat_assum `EVERY _ (compiler_var_names _ 13)`
    (strip_assume_tac o SIMP_RULE bool_ss [EVERY_CONJ]) >>
  mp_tac (Q.SPECL [`dst`, `cs.cs_next_var`] abi_child_bytes_input_names) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  mp_tac (Q.SPECL [`dyn_ptr`, `cs.cs_next_var`] abi_child_bytes_input_names) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  drule_all abi_child_dynamic_contains >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `dyn_ptr`, `head_offset`, `cap`, `cs`, `op`, `mid`, `ss`,
    `dst_addr`, `dyn_addr`, `src_addr`, `bs`] abi_child_bytes_execution) >>
  impl_tac >- asm_simp_tac (srw_ss()) [EVERY_CONJ] >>
  disch_then (qx_choose_then `child_out` strip_assume_tac) >>
  `op <> Var (compiler_var_name mid.cs_next_var 0)` by
    (drule compile_abi_bytestring_code >>
     asm_simp_tac (srw_ss()) [abi_child_prefix_cut_def, compiler_var_names_EL, compiler_var_name_def]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `AbiBytestring cap`, `dyn_ptr`, `head_offset`, `cs`,
    `op`, `mid`, `ss`, `dst_addr`, `dyn_addr`, `child_out`, `enc (Bytes NONE) (contractABI$BytesV bs)`]
    abi_child_dynamic_path) >>
  impl_tac >- asm_simp_tac (srw_ss()) [EVERY_CONJ] >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `eval_operand op out = SOME (n2w (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))))` by
    (qpat_x_assum `!arg_op. arg_op <> Var _ ==> _` (qspec_then `op` mp_tac) >> simp[]) >>
  `!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 13) ==>
    eval_operand arg_op out = eval_operand arg_op ss` by
    (qx_gen_tac `arg_op` >> DISCH_TAC >>
     mp_tac (Q.SPECL [`arg_op`, `cs.cs_next_var`] abi_child_bytes_input_names) >>
     impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
     qpat_assum `!arg_op. arg_op <> Var _ ==> _` (qspec_then `arg_op` mp_tac) >>
     qpat_assum `!arg_op. EVERY _ _ ==> _` (qspec_then `arg_op` mp_tac) >> simp[]) >>
  `eval_operand dyn_ptr out = SOME dyn_addr` by
    (qpat_assum `!arg_op. EVERY _ _ ==> eval_operand arg_op out = _` (qspec_then `dyn_ptr` mp_tac) >>
     simp[EVERY_CONJ]) >>
  mp_tac (Q.SPECL
    [`[(w2n (dst_addr + mload (w2n (dyn_addr:bytes32)) ss),
        LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))]`,
     `[(w2n (dst_addr + n2w head_offset:bytes32),32);(w2n (dyn_addr:bytes32),32)]`,
     `ss`, `child_out`, `out`] abi_memory_frame_trans) >>
  impl_tac >- (conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp_tac list_ss [] >> DISCH_TAC >>
  qexists_tac `out` >> asm_simp_tac (srw_ss()) [abi_child_suffix_cut_def, abi_child_suffix_insts_def]
QED
