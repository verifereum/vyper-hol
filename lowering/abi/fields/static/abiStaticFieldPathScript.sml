(* TOP-LEVEL: an actual word/copy child appends a static field while keeping
   completed heads, accumulated tails, root operands and the tail counter. *)
Theory abiStaticFieldPath
Ancestors
  abiAllocatorState
  abiStateFrame
  abiStaticChildPath abiStaticFieldMemory abiFieldCompose abiFieldMemory abiFieldLayoutDefs abiMemoryFrame
  abiStaticLoopCode compileEnv fragExec fragBlockPath venomState list pair words arithmetic

Theorem compile_abi_static_field_extend:
  !ctx func dst src info payload dyn_ptr cs op cs' ss dst_addr src_addr dyn_addr fields tail_offset.
    ((info = AbiPrimWord /\ LENGTH payload = 32) \/ info = AbiCopy (LENGTH payload) \/
      (info = AbiComplex [] /\ LENGTH payload = 0)) /\
    compile_abi_encode_child dst src info F (abi_field_head_size fields) dyn_ptr cs = (op,cs') /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand dyn_ptr ss = SOME dyn_addr /\ src <> Var (compiler_var_name cs.cs_next_var 0) /\
    EVERY (\name. dst <> Var name /\ dyn_ptr <> Var name)
      (compiler_var_names cs.cs_next_var (if info = AbiPrimWord then 2 else 1)) /\
    LENGTH payload < dimword(:256) /\ read_memory (w2n src_addr) (LENGTH payload) ss = payload /\
    abi_fields_layout fields (w2n dst_addr) 0 tail_offset ss /\
    (LENGTH payload = 0 \/ w2n dst_addr + abi_field_head_size fields < dimword(:256)) /\
    abi_window_separated (w2n dst_addr + tail_offset) (abi_field_tail_size fields)
      (w2n (dst_addr + n2w (abi_field_head_size fields))) (LENGTH payload) /\
    abi_window_separated (w2n dyn_addr) 32
      (w2n (dst_addr + n2w (abi_field_head_size fields))) (LENGTH payload) ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      eval_operand op out = SOME (n2w (LENGTH payload)) /\
      eval_operand dst out = SOME dst_addr /\ eval_operand dyn_ptr out = SOME dyn_addr /\
      mload (w2n dyn_addr) out = mload (w2n dyn_addr) ss /\
      abi_fields_layout (fields ++ [(F,payload)]) (w2n dst_addr) 0 tail_offset out /\
      abi_memory_frame [(w2n (dst_addr + n2w (abi_field_head_size fields)),LENGTH payload)] ss out /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var (if info = AbiPrimWord then 2 else 1)) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\ abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `info`, `payload`, `abi_field_head_size fields`,
    `dyn_ptr`, `cs`, `op`, `cs'`, `ss`, `dst_addr`, `src_addr`] compile_abi_child_static_bytes_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qpat_assum `EVERY _ (compiler_var_names _ _)` (strip_assume_tac o SIMP_RULE bool_ss [EVERY_CONJ]) >>
  `eval_operand dst out = SOME dst_addr` by
    (qpat_assum `!arg_op. EVERY _ _ ==> _` (qspec_then `dst` mp_tac) >> simp[]) >>
  `eval_operand dyn_ptr out = SOME dyn_addr` by
    (qpat_assum `!arg_op. EVERY _ _ ==> _` (qspec_then `dyn_ptr` mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`dst_addr`, `fields`, `LENGTH (payload:word8 list)`] abi_static_field_head_separation) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  `read_memory (w2n dst_addr + abi_field_head_size fields) (LENGTH payload) out = payload` by
    (irule abi_static_field_read >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  mp_tac (Q.SPECL
    [`[(w2n (dst_addr + n2w (abi_field_head_size fields):bytes32),LENGTH (payload:word8 list))]`,
     `ss`, `out`, `w2n (dyn_addr:bytes32)`] abi_memory_frame_mload) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`fields`, `payload`, `w2n (dst_addr:bytes32)`, `0`, `tail_offset`,
    `[(w2n (dst_addr + n2w (abi_field_head_size fields):bytes32),LENGTH (payload:word8 list))]`, `ss`, `out`]
    abi_fields_layout_static_extend) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> DISCH_TAC >>
  qexists_tac `out` >> asm_simp_tac bool_ss []
QED
