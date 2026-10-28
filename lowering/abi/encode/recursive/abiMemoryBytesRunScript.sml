(* TOP-LEVEL: derive bytestring execution from the recursive source relation
   and separated source/output windows. No child execution premise is used. *)
Theory abiMemoryBytesRun
Ancestors
  abiMemoryLeafRun abiMemoryEncodingCases abiBytestringCorrect abiBytestringMemory abiChildMemoryFrame
  abiStateFrameOps abiStateFrame abiAllocatorState abiMemoryFrame abiFieldOperands
  memoryReadProps valueEncodingProofs compileEnv fragExec fragBlockPath
  venomState contractABI list words arithmetic

Theorem abi_memory_bytes_pre:
  !cap src_addr span payload dst_addr ss.
    abi_memory_encoding (AbiBytestring cap) (w2n src_addr) span ss.vs_memory payload /\
    w2n dst_addr + LENGTH payload < dimword (:256) /\
    abi_window_separated (w2n src_addr) span (w2n dst_addr) (LENGTH payload) ==>
    ?bs. payload = enc (Bytes NONE) (contractABI$BytesV bs) /\
      bytestring_abi_pre dst_addr src_addr bs ss
Proof
  rpt gen_tac >> strip_tac >>
  gvs[abi_memory_bytes_cases] >>
  rename1 `mem_bytes_at (w2n src_addr + 32) (LENGTH bs) ss.vs_memory = bs` >> qexists_tac `bs` >>
  simp[bytestring_abi_pre_def, read_memory_eq_mem_bytes_at,
    GSYM mem_word_at_eq_mload_proof] >>
  fs[bytestring_encoded_size, abi_window_separated_def,
    compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem abi_bytestring_read_frame = abi_bytestring_read_memory_frame;

Theorem compile_abi_memory_bytes:
  !ctx func dst src cap span payload cs ret cs' ss dst_addr src_addr.
    compile_abi_encode_to_buf dst src (AbiBytestring cap) cs = (ret,cs') /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    abi_memory_encoding (AbiBytestring cap) (w2n src_addr) span ss.vs_memory payload /\
    w2n dst_addr + LENGTH payload < dimword (:256) /\
    abi_window_separated (w2n src_addr) span (w2n dst_addr) (LENGTH payload) ==>
    ?out. abi_encoding_result ctx func cs cs' ret dst_addr payload [] ss out /\
      abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_memory_bytes_pre >>
  disch_then (qx_choose_then `bs` strip_assume_tac) >> gvs[] >>
  `EVERY (\name. src <> Var name /\ dst <> Var name)
      (compiler_var_names cs.cs_next_var 8)` by
    (simp[EVERY_CONJ] >> conj_tac >> irule abi_operand_before_names >>
     qexists_tac `cs.cs_next_var` >> simp[]) >>
  drule_all compile_abi_bytestring_correct_path >>
  disch_then (qspec_then `ctx` (qx_choose_then `out` strip_assume_tac)) >>
  `abi_state_frame ss out` by
    (qspecl_then [`dst_addr`, `src_addr`, `ss`, `out`, `LENGTH cs'.cs_current_insts`]
       mp_tac abi_state_frame_bytestring_image >> simp[]) >>
  `abi_allocator_state out = abi_allocator_state ss` by
    (qpat_x_assum `out with vs_vars := _ = _`
       (mp_tac o AP_TERM ``abi_allocator_state``) >> simp[]) >>
  drule_all abi_bytestring_read_frame >> DISCH_TAC >>
  qexists_tac `out` >> simp[abi_encoding_result_def] >>
  qspecl_then [`cs.cs_next_var`, `cs.cs_next_var`, `8`, `ss`, `out`]
    mp_tac abi_operand_before_frame >> fs[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive ABI native bytestring execution: " ^ name)
  end) (DB.thms "abiMemoryBytesRun")
