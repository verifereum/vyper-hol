(* TOP-LEVEL: the empty static child still executes the actual destination
   ADD, returns zero bytes, and preserves every memory read. *)
Theory abiStaticChildEmpty
Ancestors
  abiAllocatorState
  abiStateFrameOps abiStateFrame abiStaticChildCode abiFieldAddress abiFieldReady abiMemoryFrame
  abiComplexCode abiEncoder abiStaticLoopCode abiBytestringCode
  compileEnv emitHelperProps fragExec fragBlockPath venomState list words arithmetic

Theorem compile_abi_child_empty_path:
  !ctx func dst src head_offset dyn_ptr cs op cs' ss dst_addr.
    compile_abi_encode_child dst src (AbiComplex []) F head_offset dyn_ptr cs = (op,cs') /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ eval_operand dst ss = SOME dst_addr ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ eval_operand op out = SOME 0w /\
      read_memory (w2n (dst_addr + n2w head_offset)) 0 out = [] /\
      abi_memory_frame [(w2n (dst_addr + n2w head_offset),0)] ss out /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 1) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\ abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_abi_encode_child _ _ _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [compile_abi_child_static_cuts]) >>
  simp_tac bool_ss [Once compile_abi_encode_child_def, comp_return_def] >> strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `head_offset`, `cs`, `ss`, `dst_addr`] abi_field_address_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qexists_tac `abi_field_address_state cs head_offset dst_addr ss` >>
  asm_simp_tac (srw_ss()) [abi_complex_field_cut_def, abi_field_address_state_frame,
    eval_operand_lit, abi_memory_frame_def, read_memory_def, abi_state_frame_def] >>
  qx_gen_tac `arg_op` >> DISCH_TAC >>
  mp_tac (Q.SPECL [`arg_op`, `cs.cs_next_var`, `0`] abi_field_input_names) >>
  impl_tac >- simp[] >> strip_tac >> simp[abi_field_address_state_operand]
QED
