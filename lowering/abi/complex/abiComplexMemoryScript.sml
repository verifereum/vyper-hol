(* TOP-LEVEL: aggregate counter setup preserves disjoint source bytestrings.
   A single complete source window suffices to retain the bytestring
   encoder's length, payload and physical separation precondition. *)
Theory abiComplexMemory
Ancestors
  loweringStateRelDefs abiComplexEntry abiStaticLoopEntry abiStaticLoopCode abiBytestringCorrect
  memoryReadProps ssaOperandFrame compileEnv venomState venomExecSemantics
  finite_map list words arithmetic

Theorem bytestring_abi_pre_read_frame:
  !dst_addr src_addr bs before after.
    read_memory (w2n src_addr) (32 + LENGTH bs) after =
      read_memory (w2n src_addr) (32 + LENGTH bs) before ==>
    (bytestring_abi_pre dst_addr src_addr bs after = bytestring_abi_pre dst_addr src_addr bs before)
Proof
  rpt gen_tac >> DISCH_TAC >>
  `read_memory (w2n src_addr) 32 after = read_memory (w2n src_addr) 32 before` by
    (mp_tac (Q.SPECL [`w2n (src_addr:bytes32)`, `32 + LENGTH (bs:word8 list)`, `0`, `32`, `after`]
       read_memory_subwindow) >>
     mp_tac (Q.SPECL [`w2n (src_addr:bytes32)`, `32 + LENGTH (bs:word8 list)`, `0`, `32`, `before`]
       read_memory_subwindow) >> simp[]) >>
  `read_memory (w2n src_addr + 32) (LENGTH bs) after =
    read_memory (w2n src_addr + 32) (LENGTH bs) before` by
    (mp_tac (Q.SPECL [`w2n (src_addr:bytes32)`, `32 + LENGTH (bs:word8 list)`, `32`, `LENGTH (bs:word8 list)`, `after`]
       read_memory_subwindow) >>
     mp_tac (Q.SPECL [`w2n (src_addr:bytes32)`, `32 + LENGTH (bs:word8 list)`, `32`, `LENGTH (bs:word8 list)`, `before`]
       read_memory_subwindow) >> simp[]) >>
  simp[bytestring_abi_pre_def, mload_read_memory]
QED

Theorem abi_static_loop_alloc_frame_memory[simp]:
  !id ss. (abi_static_loop_alloc_frame id ss).vs_memory = ss.vs_memory
Proof
  rpt gen_tac >> Cases_on `FLOOKUP ss.vs_allocas id = NONE` >> simp[abi_static_loop_alloc_frame_def]
QED

Theorem abi_complex_prefix_read_frame:
  !id var_base head_size ss offset read_len.
    regions_disjoint offset read_len (w2n (abi_static_loop_counter_addr id ss)) 32 ==>
    read_memory offset read_len (abi_complex_prefix_state id var_base head_size ss) =
      read_memory offset read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >> fs[regions_disjoint_def] >>
  simp_tac bool_ss [abi_complex_prefix_state_def] >>
  `read_memory offset read_len
    (mstore (w2n (abi_static_loop_counter_addr id ss)) (n2w head_size)
      (update_var (compiler_var_name var_base 0) (abi_static_loop_counter_addr id ss)
        (abi_static_loop_alloc_frame id ss))) =
    read_memory offset read_len
      (update_var (compiler_var_name var_base 0) (abi_static_loop_counter_addr id ss)
        (abi_static_loop_alloc_frame id ss))` by
    (irule read_memory_mstore_disjoint >> simp[]) >>
  asm_simp_tac (srw_ss()) [read_memory_def, update_var_def]
QED

Theorem abi_complex_prefix_bytes_pre:
  !id var_base head_size dst_addr src_addr bs ss.
    bytestring_abi_pre dst_addr src_addr bs ss /\
    regions_disjoint (w2n src_addr) (32 + LENGTH bs) (w2n (abi_static_loop_counter_addr id ss)) 32 ==>
    bytestring_abi_pre dst_addr src_addr bs (abi_complex_prefix_state id var_base head_size ss)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`id`, `var_base`, `head_size`, `ss`, `w2n (src_addr:bytes32)`, `32 + LENGTH (bs:word8 list)`]
    abi_complex_prefix_read_frame) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  mp_tac (Q.SPECL [`dst_addr`, `src_addr`, `bs`, `ss`, `abi_complex_prefix_state id var_base head_size ss`]
    bytestring_abi_pre_read_frame) >> simp[]
QED
