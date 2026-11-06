(* TOP-LEVEL: execute the actual traversal's source ADD and bytestring child
   from arbitrary source offsets. The remaining compiler action is exposed
   with completed head/tail bytes and all old operand values preserved. *)
Theory abiBytesFieldStep
Ancestors
  abiAllocatorState
  abiStateFrame abiStateFrameOps
  abiBytesFieldPre abiFieldBytesPath abiFieldAddress abiFieldReady abiFieldsStructure
  abiComplexCode abiFieldMemory abiFieldLayoutDefs abiMemoryFrame abiStaticLoopCode
  abiBytestringCorrect contractABI compileEnv fragExec fragBlockPath venomState list pair words arithmetic

Theorem compile_abi_bytes_field_step:
  !ctx func dst src cap dyn_ptr mem_size rest source_offset cs ret cs' ss dst_addr dyn_addr root_addr bs fields tail_offset.
    compile_abi_encode_complex_elems dst src ((AbiBytestring cap,32,mem_size,T)::rest)
      source_offset (abi_field_head_size fields) dyn_ptr cs = (ret,cs') /\ fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\
    eval_operand dyn_ptr ss = SOME dyn_addr /\
    EVERY (\name. src <> Var name /\ dst <> Var name /\ dyn_ptr <> Var name)
      (compiler_var_names cs.cs_next_var 13) /\
    abi_bytes_field_pre fields tail_offset dst_addr dyn_addr (root_addr + n2w source_offset) bs ss ==>
    ?mid out.
      compile_abi_encode_complex_elems dst src rest (source_offset + mem_size)
        (abi_field_head_size fields + 32) dyn_ptr mid = (ret,cs') /\ fn_has_code mid cs' func /\
      cs.cs_next_var + 1 <= mid.cs_next_var /\
      fragment_path ctx func ss out /\
      out.vs_current_bb = mid.cs_current_bb /\ out.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~out.vs_halted /\
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
  qpat_x_assum `compile_abi_encode_complex_elems _ _ (_::_) _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [compile_abi_fields_cons_cuts]) >>
  disch_then (qx_choose_then `child_result` (qx_choose_then `mid` strip_assume_tac)) >>
  drule_all abi_fields_cons_contains >> strip_tac >>
  `cs.cs_next_var + 1 <= mid.cs_next_var` by
    (drule_all compile_abi_child_next_var >> simp[abi_complex_field_cut_def]) >>
  mp_tac (Q.SPECL [`dst`, `dyn_ptr`, `cs`, `source_offset`, `root_addr`, `ss`, `dst_addr`, `dyn_addr`, `12`]
    abi_field_address_inputs) >> impl_tac >- fs[EVERY_CONJ] >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [LET_THM, EVERY_CONJ]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `src`, `source_offset`, `cs`, `ss`, `root_addr`] abi_field_address_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qabbrev_tac `addressed = abi_field_address_state cs source_offset root_addr ss` >>
  `abi_bytes_field_pre fields tail_offset dst_addr dyn_addr (root_addr + n2w source_offset) bs addressed` by
    simp[Abbr`addressed`, abi_bytes_field_pre_address] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `Var (compiler_var_name cs.cs_next_var 0)`, `cap`, `dyn_ptr`,
    `abi_complex_field_cut src source_offset cs`, `child_result`, `mid`, `addressed`,
    `dst_addr`, `dyn_addr`, `root_addr + n2w source_offset`, `bs`, `fields`, `tail_offset`]
    compile_abi_bytes_field_extend) >>
  impl_tac >- fs[abi_bytes_field_pre_def, bytestring_abi_pre_def, Abbr`addressed`, abi_complex_field_cut_def,
    abi_field_address_state_frame, abi_field_address_memory, EVERY_CONJ] >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `abi_state_frame ss out` by
    (irule abi_state_frame_trans >> qexists_tac `addressed` >> simp[Abbr`addressed`, abi_state_frame_def]) >>
  `!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 13) ==>
      eval_operand arg_op out = eval_operand arg_op ss` by
    (qx_gen_tac `arg_op` >> DISCH_TAC >>
     mp_tac (Q.SPECL [`arg_op`, `cs.cs_next_var`, `12`] abi_field_input_names) >>
     impl_tac >- simp[] >> strip_tac >>
     qpat_x_assum `!arg_op. EVERY _ _ ==> _` (qspec_then `arg_op` mp_tac) >>
     fs[Abbr`addressed`, abi_complex_field_cut_def, abi_field_address_state_operand]) >>
  mp_tac (Q.SPECL [`[]`,
    `[(w2n (dst_addr + mload (w2n (dyn_addr:bytes32)) ss), LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)));
      (w2n (dst_addr + n2w (abi_field_head_size fields):bytes32),32);(w2n (dyn_addr:bytes32),32)]`,
    `ss`, `addressed`, `out`] abi_memory_frame_trans) >>
  impl_tac >- fs[Abbr`addressed`, abi_field_address_state_frame, abi_field_address_memory] >>
  simp_tac list_ss [] >> DISCH_TAC >>
  `fragment_path ctx func ss out` by
    (irule fragment_path_trans >> qexists_tac `addressed` >> fs[Abbr`addressed`]) >>
  `abi_allocator_state out = abi_allocator_state ss` by
    (qpat_assum `abi_allocator_state out = abi_allocator_state addressed` mp_tac >> simp[Abbr`addressed`]) >>
  qexistsl_tac [`mid`, `out`] >> fs[]
QED
