(* TOP-LEVEL: native word/copy execution from the recursive source relation.
   The common result records real CFG execution, bytes, scratch-aware memory
   frames and preservation of operands reserved before compilation. *)
Theory abiMemoryLeafRun
Ancestors
  abiMemoryEncodingCases abiStaticBytesPath abiFieldOperands
  abiStateFrame abiAllocatorState abiMemoryFrame memoryValueAbiArray
  memoryReadProps valueEncodingProofs abiEncoder context compileEnv fragExec fragBlockPath
  venomState list words arithmetic

Definition abi_encoding_result_def:
  abi_encoding_result ctx func cs cs' ret dst_addr payload scratch before after <=>
    fragment_path ctx func before after /\
    after.vs_current_bb = cs'.cs_current_bb /\
    after.vs_inst_idx = LENGTH cs'.cs_current_insts /\
    eval_operand ret after = SOME (n2w (LENGTH payload)) /\
    read_memory (w2n dst_addr) (LENGTH payload) after = payload /\
    abi_memory_frame ((w2n dst_addr,LENGTH payload)::scratch) before after /\
    (!arg_op. abi_operand_before cs.cs_next_var arg_op ==>
      eval_operand arg_op after = eval_operand arg_op before) /\
    abi_state_frame before after
End

Theorem compile_abi_memory_word:
  !ctx func dst src span payload cs ret cs' ss dst_addr src_addr.
    compile_abi_encode_to_buf dst src AbiPrimWord cs = (ret,cs') /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    abi_operand_before cs.cs_next_var dst /\
    abi_memory_encoding AbiPrimWord (w2n src_addr) span ss.vs_memory payload ==>
    ?out. abi_encoding_result ctx func cs cs' ret dst_addr payload [] ss out /\
      abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH payload = 32 /\ read_memory (w2n (src_addr:bytes32)) 32 ss = payload` by
    fs[abi_memory_word_cases, read_memory_eq_mem_bytes_at, mem_bytes_at_word] >>
  `dst <> Var (compiler_var_name cs.cs_next_var 0)` by
    fs[abi_operand_before_def] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `payload`, `cs`, `ret`, `cs'`,
    `ss`, `dst_addr`, `src_addr`] compile_abi_word_bytes_path) >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  qexists_tac `out` >> simp[abi_encoding_result_def] >>
  rpt strip_tac >> first_x_assum irule >> fs[abi_operand_before_def]
QED

Theorem compile_abi_memory_copy:
  !ctx func dst src n span payload cs ret cs' ss dst_addr src_addr.
    compile_abi_encode_to_buf dst src (AbiCopy n) cs = (ret,cs') /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    span < dimword (:256) /\
    abi_memory_encoding (AbiCopy n) (w2n src_addr) span ss.vs_memory payload ==>
    ?out. abi_encoding_result ctx func cs cs' ret dst_addr payload [] ss out /\
      abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH payload = n /\ read_memory (w2n (src_addr:bytes32)) n ss = payload` by
    fs[abi_memory_copy_cases, read_memory_eq_mem_bytes_at, LENGTH_mem_bytes_at_proof] >>
  `LENGTH payload < dimword (:256)` by
    (fs[abi_memory_copy_cases] >> decide_tac) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `payload`, `cs`, `ret`, `cs'`,
    `ss`, `dst_addr`, `src_addr`] compile_abi_copy_bytes_path) >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  qexists_tac `out` >> simp[abi_encoding_result_def]
QED

Theorem compile_abi_memory_empty:
  !ctx func dst src span payload cs ret cs' ss dst_addr src_addr.
    compile_abi_encode_to_buf dst src (AbiComplex []) cs = (ret,cs') /\
    ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    abi_memory_encoding (AbiComplex []) (w2n src_addr) span ss.vs_memory payload ==>
    ?out. abi_encoding_result ctx func cs cs' ret dst_addr payload [] ss out /\
      abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >>
  gvs[Once compile_abi_encode_child_def, comp_return_def, abi_memory_empty_cases] >>
  qexists_tac `ss` >>
  simp[abi_encoding_result_def, eval_operand_def, read_memory_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive ABI native leaf execution: " ^ name)
  end) (DB.thms "abiMemoryLeafRun")
