(* The memory-only bytes tail writes just a snapshot prefix and padding. *)
Theory abiDecoderBytesMemory
Ancestors
  abiDecoderBytesPhases abiDecoderContract valueEncodingProps valueEncoding valueEncodingDefs
  venomState venomExecSemantics words list rich_list

Theorem abi_decode_bytes_store_copy_prefix:
  q + 32 <= cap /\ (a + 32 + c <= d \/ d + cap <= a) ==>
  mem_bytes_at d (32+c) (mcopy d a (32+c) (mstore (d+q) 0w s)).vs_memory =
  mem_bytes_at a (32+c) s.vs_memory
Proof
  strip_tac >> rewrite_tac[mcopy_mem_bytes_at_same] >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem abi_decode_bytes_store_copy_frame:
  c <= q /\ q + 32 <= cap ==>
  abi_decode_frame d cap s (mcopy d a (32+c) (mstore (d+q) 0w s))
Proof
  strip_tac >> simp[abi_decode_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      `p + k <= d \/ d + (32+c) <= p` by decide_tac >>
      `p + k <= d+q \/ d+q+32 <= p` by decide_tac >>
      dep_rewrite.DEP_REWRITE_TAC [mcopy_mem_bytes_at_disjoint, mstore_mem_bytes_at_disjoint] >>
      decide_tac) >>
  simp_tac (srw_ss()) [mcopy_def, write_memory_with_expansion_def, mstore_def, LET_THM]
QED

Theorem abi_decode_bytes_store_copy_padding:
  c <= q /\ q <= c+32 ==>
  mem_bytes_at (d+32+c) (q-c)
    (mcopy d a (32+c) (mstore (d+q) 0w s)).vs_memory = REPLICATE (q-c) 0w
Proof
  strip_tac >>
  `d + (32+c) <= d+32+c` by decide_tac >>
  asm_simp_tac bool_ss [mcopy_mem_bytes_at_disjoint] >>
  `word_to_bytes (0w:bytes32) T = REPLICATE 32 (0w:word8)` by (simp[byteTheory.word_to_bytes_def] >> EVAL_TAC >> simp[ZERO_SHIFT, w2w_0]) >>
  `mem_bytes_at (d+q) 32 (mstore (d+q) 0w s).vs_memory =
   mem_bytes_at 0 32 (REPLICATE 32 (0w:word8))` by
    simp[mem_bytes_at_mstore_same, mem_bytes_at_def, GSYM REPLICATE_APPEND, REPLICATE_GENLIST, TAKE_GENLIST] >>
  drule mem_bytes_at_translated_window >>
  disch_then (qspecl_then [`32+c-q`, `q-c`] mp_tac) >>
  `32+c-q + (q-c) <= 32 /\ d+q+(32+c-q) = d+32+c` by decide_tac >>
  simp[mem_bytes_at_def, DROP_REPLICATE, REPLICATE_GENLIST, TAKE_GENLIST,
       TAKE_APPEND1]
QED

(* Empty, aligned and unaligned padding windows are included explicitly. *)
Theorem abi_decode_bytes_store_copy_padding_edges:
  MEM c [0;1;32;33] ==>
  mem_bytes_at (d+32+c) (32*((c+31) DIV 32)-c)
    (mcopy d a (32+c) (mstore (d+32*((c+31) DIV 32)) 0w s)).vs_memory =
  REPLICATE (32*((c+31) DIV 32)-c) 0w
Proof
  strip_tac >> irule abi_decode_bytes_store_copy_padding >> gvs[listTheory.MEM]
QED
