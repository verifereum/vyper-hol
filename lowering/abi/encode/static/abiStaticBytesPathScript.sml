(* TOP-LEVEL: real word and fixed-size ABI encoders copy their source bytes
   and expose a complete memory frame. These summaries do not require a
   type-specific source theorem or initially undefined SSA temporaries. *)
Theory abiStaticBytesPath
Ancestors
  abiAllocatorState
  abiStateFrame abiMemoryFrame abiEncoderPathProps abiStaticLoopCode memoryReadProps memoryValueAbiExec
  abiEncoder compileEnv exprLoweringProps emitHelperProps instIdxIndep ssaOperandFrame
  venomState venomExecSemantics venomMemProps list words arithmetic
Libs wordsLib

Theorem compile_abi_copy_bytes_path:
  !ctx func dst src payload cs op cs' ss dst_addr src_addr.
    compile_abi_encode_to_buf dst src (AbiCopy (LENGTH payload)) cs = (op,cs') /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    LENGTH payload < dimword(:256) /\ read_memory (w2n src_addr) (LENGTH payload) ss = payload /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ eval_operand op out = SOME (n2w (LENGTH payload)) /\
      read_memory (w2n dst_addr) (LENGTH payload) out = payload /\
      abi_memory_frame [(w2n dst_addr,LENGTH payload)] ss out /\
      (!arg_op. eval_operand arg_op out = eval_operand arg_op ss) /\ abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_abi_copy_path >> strip_tac >>
  drule_all compile_abi_copy_execution >> strip_tac >>
  qexists_tac `(mcopy (w2n (dst_addr:bytes32)) (w2n (src_addr:bytes32)) (LENGTH (payload:word8 list)) ss)
    with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  fs[same_blocks_def, read_memory_inst_idx, read_memory_mcopy_self,
    eval_op_inst_idx, eval_operand_mcopy_eq, abi_memory_frame_inst_idx, abi_memory_frame_mcopy, abi_state_frame_def]
QED

Theorem compile_abi_word_bytes_path:
  !ctx func dst src payload cs op cs' ss dst_addr src_addr.
    compile_abi_encode_to_buf dst src AbiPrimWord cs = (op,cs') /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    dst <> Var (compiler_var_name cs.cs_next_var 0) /\
    LENGTH payload = 32 /\ read_memory (w2n src_addr) 32 ss = payload /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ eval_operand op out = SOME (n2w (LENGTH payload)) /\
      read_memory (w2n dst_addr) (LENGTH payload) out = payload /\
      abi_memory_frame [(w2n dst_addr,LENGTH payload)] ss out /\
      (!arg_op. arg_op <> Var (compiler_var_name cs.cs_next_var 0) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\ abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >>
  `compile_abi_encode_static dst src cs = (op,cs')` by fs[Once compile_abi_encode_child_def] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `cs`, `op`, `cs'`, `ss`, `src_addr`, `dst_addr`]
    compile_abi_encode_static_path) >> impl_tac >- fs[compiler_var_name_def] >> DISCH_TAC >>
  drule compile_abi_encode_static_code >> strip_tac >>
  qexists_tac `(mstore (w2n (dst_addr:bytes32)) (mload (w2n (src_addr:bytes32)) ss)
    (update_var (compiler_var_name cs.cs_next_var 0) (mload (w2n (src_addr:bytes32)) ss) ss))
      with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  fs[same_blocks_def, read_memory_inst_idx, read_memory_word,
    mload_mstore_same, eval_op_inst_idx, eval_operand_mstore_eq,
    eval_operand_update_var_avoids, eval_operand_lit, compiler_var_name_def,
    abi_memory_frame_inst_idx, mstore_update_var, mload_update_var,
    abi_memory_frame_update_var, abi_memory_frame_mstore, abi_state_frame_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed word/copy ABI byte execution frames: " ^ name)
  end) (DB.thms "abiStaticBytesPath")
