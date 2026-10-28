(* TOP-LEVEL: static child encoding is a byte copy. Each iteration preserves
   disjoint source windows and writes the selected element, including a
   zero-size element. These facts supply the memory part of the loop invariant. *)
Theory abiStaticLoopMemory
Ancestors
  abiStaticLoopBody abiStaticLoopRun memoryReadProps mmCopyEquiv
  venomState venomExecSemantics list words arithmetic

Theorem abi_static_loop_child_address:
  !addr i stride.
    w2n (addr:bytes32) + 32 + i * stride < dimword(:256) ==>
    w2n (addr + 32w + n2w i * n2w stride) = w2n addr + 32 + i * stride
Proof
  rpt gen_tac >> Cases_on `addr` >>
  simp[word_add_n2w, word_mul_n2w] >> strip_tac >> simp[]
QED

Theorem abi_static_loop_child_window:
  !offset i n stride.
    0 < stride /\ i < n /\ offset + 32 + n * stride <= dimword(:256) ==>
    offset + 32 + i * stride < dimword(:256) /\
    offset + 32 + i * stride + stride <= offset + 32 + n * stride
Proof
  rpt gen_tac >> strip_tac >>
  `i * stride < n * stride` by simp[LT_MULT_RCANCEL] >>
  `(i + 1) * stride <= n * stride` by simp[LE_MULT_RCANCEL] >>
  qpat_x_assum `(i + 1) * stride <= n * stride`
    (mp_tac o PURE_REWRITE_RULE [RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >>
  strip_tac >> decide_tac
QED

Theorem static_info_memory_copy:
  !info copied_count dst_addr src_addr ss.
    ((info = AbiPrimWord /\ copied_count = 32) \/ info = AbiCopy copied_count) /\
    copied_count < dimword(:256) ==>
    static_info_memory info dst_addr src_addr ss =
      mcopy (w2n dst_addr) (w2n src_addr) copied_count ss
Proof
  rpt gen_tac >> strip_tac >>
  gvs[static_info_memory_def, mload_mstore_eq_mcopy_state]
QED

Theorem static_info_memory_read_frame:
  !info copied_count dst_addr src_addr ss offset read_len.
    ((info = AbiPrimWord /\ copied_count = 32) \/ info = AbiCopy copied_count) /\
    copied_count < dimword(:256) /\
    (copied_count = 0 \/ offset + read_len <= w2n dst_addr \/
      w2n dst_addr + copied_count <= offset) ==>
    read_memory offset read_len (static_info_memory info dst_addr src_addr ss) =
      read_memory offset read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`info`, `copied_count`, `dst_addr`, `src_addr`, `ss`]
    static_info_memory_copy) >> impl_tac >- fs[] >> DISCH_THEN SUBST1_TAC >>
  irule read_memory_mcopy_frame >> fs[]
QED

Theorem static_info_memory_read_self:
  !info copied_count dst_addr src_addr ss.
    ((info = AbiPrimWord /\ copied_count = 32) \/ info = AbiCopy copied_count) /\
    copied_count < dimword(:256) ==>
    read_memory (w2n dst_addr) copied_count (static_info_memory info dst_addr src_addr ss) =
      read_memory (w2n src_addr) copied_count ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`info`, `copied_count`, `dst_addr`, `src_addr`, `ss`]
    static_info_memory_copy) >> impl_tac >- fs[] >> DISCH_THEN SUBST1_TAC >>
  simp[read_memory_mcopy_self]
QED

Theorem abi_static_loop_body_read_frame:
  !info copied_count dst_addr src_addr abi_sz mem_sz counter_addr ss offset read_len.
    ((info = AbiPrimWord /\ copied_count = 32) \/ info = AbiCopy copied_count) /\
    copied_count < dimword(:256) /\
    (copied_count = 0 \/
      offset + read_len <= w2n (dst_addr + 32w + mload (w2n counter_addr) ss * n2w abi_sz) \/
      w2n (dst_addr + 32w + mload (w2n counter_addr) ss * n2w abi_sz) + copied_count <= offset) /\
    (offset + read_len <= w2n counter_addr \/ w2n counter_addr + 32 <= offset) ==>
    read_memory offset read_len
      (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss) =
      read_memory offset read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp_tac bool_ss [abi_static_loop_body_memory_def, LET_THM] >>
  irule EQ_TRANS >>
  qexists_tac `read_memory offset read_len
    (static_info_memory info
      (dst_addr + 32w + mload (w2n counter_addr) ss * n2w abi_sz)
      (src_addr + 32w + mload (w2n counter_addr) ss * n2w mem_sz) ss)` >>
  conj_tac >- (irule read_memory_mstore_disjoint >> fs[]) >>
  irule static_info_memory_read_frame >> qexists_tac `copied_count` >> fs[]
QED

Theorem abi_static_loop_body_read_self:
  !info copied_count dst_addr src_addr abi_sz mem_sz counter_addr ss.
    ((info = AbiPrimWord /\ copied_count = 32) \/ info = AbiCopy copied_count) /\
    copied_count < dimword(:256) /\
    (w2n (dst_addr + 32w + mload (w2n counter_addr) ss * n2w abi_sz) + copied_count <= w2n counter_addr \/
      w2n counter_addr + 32 <= w2n (dst_addr + 32w + mload (w2n counter_addr) ss * n2w abi_sz)) ==>
    read_memory (w2n (dst_addr + 32w + mload (w2n counter_addr) ss * n2w abi_sz)) copied_count
      (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss) =
    read_memory (w2n (src_addr + 32w + mload (w2n counter_addr) ss * n2w mem_sz)) copied_count ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp_tac bool_ss [abi_static_loop_body_memory_def, LET_THM] >>
  irule EQ_TRANS >>
  qexists_tac `read_memory (w2n (dst_addr + 32w + mload (w2n counter_addr) ss * n2w abi_sz)) copied_count
    (static_info_memory info
      (dst_addr + 32w + mload (w2n counter_addr) ss * n2w abi_sz)
      (src_addr + 32w + mload (w2n counter_addr) ss * n2w mem_sz) ss)` >>
  conj_tac >- (irule read_memory_mstore_disjoint >> fs[]) >>
  irule static_info_memory_read_self >> fs[]
QED

Theorem abi_static_loop_effect_read_frame:
  !info copied_count dst_addr src_addr abi_sz mem_sz counter_addr labels ss offset read_len.
    ((info = AbiPrimWord /\ copied_count = 32) \/ info = AbiCopy copied_count) /\
    copied_count < dimword(:256) /\
    (copied_count = 0 \/
      offset + read_len <= w2n (dst_addr + 32w + mload (w2n counter_addr) ss * n2w abi_sz) \/
      w2n (dst_addr + 32w + mload (w2n counter_addr) ss * n2w abi_sz) + copied_count <= offset) /\
    (offset + read_len <= w2n counter_addr \/ w2n counter_addr + 32 <= offset) ==>
    read_memory offset read_len
      (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels ss) =
      read_memory offset read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp_tac (srw_ss()) [abi_static_loop_effect_def, memory_reads_jump_to] >>
  irule abi_static_loop_body_read_frame >> conj_tac >- fs[] >>
  qexists_tac `copied_count` >> fs[]
QED

Theorem abi_static_loop_effects_counter:
  !n info dst_addr src_addr abi_sz mem_sz counter_addr labels ss.
    mload (w2n counter_addr)
      (FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels) n ss) =
      mload (w2n counter_addr) ss + n2w n
Proof
  Induct_on `n` >>
  simp[FUNPOW_SUC, abi_static_loop_effect_def, memory_reads_jump_to,
    abi_static_loop_body_memory_counter, n2w_SUC, WORD_ADD_ASSOC, WORD_ADD_0]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI static-loop memory theorem: " ^ name)
  end) (DB.thms "abiStaticLoopMemory")
