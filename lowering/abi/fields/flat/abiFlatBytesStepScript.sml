(* TOP-LEVEL: a concrete bytes/string field advances an arbitrary traversal
   with complete head/tail bytes and all remaining source observations intact. *)
Theory abiFlatBytesStep
Ancestors
  abiAllocatorState
  abiStateFrame
  abiFlatFieldsDefs abiFlatSourcesFrame abiFlatGeometry abiBytesFieldStep abiBytesFieldReady
  abiFieldOperands abiFieldMemory abiFieldLayoutDefs abiMemoryFrame abiMemoryFrameCover
  abiStaticLoopCode contractABI compileEnv fragExec fragBlockPath venomState list pair words arithmetic

Theorem compile_abi_flat_bytes_step:
  !ctx func dst src dyn_ptr cap mem_size bs rest source_offset fields tail_offset capacity
      cs ret cs' ss dst_addr dyn_addr root_addr.
    compile_abi_encode_complex_elems dst src (MAP abi_flat_entry (AbiFlatBytes cap mem_size bs::rest))
      source_offset (abi_field_head_size fields) dyn_ptr cs = (ret,cs') /\ fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    abi_operand_before cs.cs_next_var src /\ abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var dyn_ptr /\
    abi_flat_state fields (AbiFlatBytes cap mem_size bs::rest) tail_offset dst_addr dyn_addr
      root_addr source_offset capacity ss ==>
    ?mid out.
      compile_abi_encode_complex_elems dst src (MAP abi_flat_entry rest) (source_offset + mem_size)
        (abi_field_head_size (fields ++ [(T,enc (Bytes NONE) (contractABI$BytesV bs))])) dyn_ptr mid = (ret,cs') /\
      fn_has_code mid cs' func /\ cs.cs_next_var <= mid.cs_next_var /\ fragment_path ctx func ss out /\
      out.vs_current_bb = mid.cs_current_bb /\ out.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~out.vs_halted /\
      eval_operand dst out = SOME dst_addr /\ eval_operand src out = SOME root_addr /\ eval_operand dyn_ptr out = SOME dyn_addr /\
      abi_flat_state (fields ++ [(T,enc (Bytes NONE) (contractABI$BytesV bs))]) rest tail_offset dst_addr dyn_addr
        root_addr (source_offset + mem_size) capacity out /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_memory_frame [(w2n dst_addr,capacity);(w2n dyn_addr,32)] ss out /\ abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_flat_state _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_flat_state_def, abi_flat_sources_def]) >>
  `abi_bytes_field_geometry fields tail_offset dst_addr dyn_addr bs` by
    (drule_all abi_flat_bytes_geometry >> simp[]) >>
  `abi_bytes_field_pre fields tail_offset dst_addr dyn_addr (root_addr + n2w source_offset) bs ss` by
    (irule abi_bytes_field_ready >> fs[abi_flat_source_def]) >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `cs.cs_next_var`, `src`, `dst`, `dyn_ptr`, `14`]
    abi_field_operands_names) >> impl_tac >- simp[] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `cap`, `dyn_ptr`, `mem_size`, `MAP abi_flat_entry rest`,
    `source_offset`, `cs`, `ret`, `cs'`, `ss`, `dst_addr`, `dyn_addr`, `root_addr`, `bs`, `fields`, `tail_offset`]
    compile_abi_bytes_field_step) >> impl_tac >- fs[abi_flat_entry_def] >>
  disch_then (qx_choose_then `mid` (qx_choose_then `out` strip_assume_tac)) >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `cs.cs_next_var`, `14`, `ss`, `out`]
    abi_operand_before_frame) >> impl_tac >- simp[] >> DISCH_TAC >>
  `abi_writes_cover [(w2n dst_addr,capacity);(w2n dyn_addr,32)]
      [(w2n (dst_addr + n2w (tail_offset + abi_field_tail_size fields)),LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)));
       (w2n (dst_addr + n2w (abi_field_head_size fields)),32);(w2n dyn_addr,32)]` by
    (drule_all abi_flat_bytes_cover >> simp[]) >>
  `abi_memory_frame [(w2n dst_addr,capacity);(w2n dyn_addr,32)] ss out` by
    (irule abi_memory_frame_cover >>
     qexists_tac `[(w2n (dst_addr + n2w (tail_offset + abi_field_tail_size fields):bytes32),
       LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)));
       (w2n (dst_addr + n2w (abi_field_head_size fields):bytes32),32);(w2n (dyn_addr:bytes32),32)]` >> gvs[]) >>
  `abi_flat_geometry (fields ++ [(T,enc (Bytes NONE) (contractABI$BytesV bs))]) rest
      tail_offset dst_addr dyn_addr capacity` by
    (drule abi_flat_geometry_advance >> simp[abi_flat_output_def]) >>
  drule_all abi_flat_sources_frame >> DISCH_TAC >>
  `cs.cs_next_var <= mid.cs_next_var` by decide_tac >>
  qexistsl_tac [`mid`, `out`] >>
  gvs[abi_flat_state_def, abi_flat_mem_size_def, abi_flat_output_def, abi_field_head_size_append,
    abi_field_head_size_def, abi_field_tail_size_append, abi_field_tail_def, word_add_n2w] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >> PURE_REWRITE_TAC [ADD_ASSOC] >> asm_simp_tac bool_ss []
QED
