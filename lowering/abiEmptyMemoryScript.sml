(* Zeroing a buffer establishes actual bytes, including omitted array defaults. *)
Theory abiEmptyMemory
Ancestors
  abiEncoderInput abiEncoderMemory abiDecoderFrameCompose abiDecoderContract
  abiDecoderArrayHeader valueEncoding valueEncodingProps venomState
  words list rich_list arithmetic

Theorem abi_empty_prefix_extend:
  mem_bytes_at p m s.vs_memory = REPLICATE m 0w /\
  mem_bytes_at (p+m) n t.vs_memory = REPLICATE n 0w /\
  abi_decode_frame (p+m) n s t ==>
  mem_bytes_at p (m+n) t.vs_memory = REPLICATE (m+n) 0w
Proof
  strip_tac >>
  `mem_bytes_at p m t.vs_memory = REPLICATE m 0w` by
    (qpat_x_assum `abi_decode_frame _ _ _ _`
      (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     disch_then (qspecl_then [`p`, `m`] mp_tac) >> simp[]) >>
  simp[Once abi_encoder_mem_split, REPLICATE_APPEND]
QED

Theorem abi_empty_store_prefix:
  mem_bytes_at p (32*n) s.vs_memory = REPLICATE (32*n) 0w ==>
  mem_bytes_at p (32*SUC n) (mstore (p+32*n) 0w s).vs_memory =
    REPLICATE (32*SUC n) 0w
Proof
  strip_tac >>
  `mem_bytes_at p (32*n) (mstore (p+32*n) 0w s).vs_memory =
    REPLICATE (32*n) 0w` by
    (mp_tac (Q.SPECL [`p`, `32*n`, `p+32*n`, `0w:bytes32`, `s`]
      mstore_mem_bytes_at_disjoint) >> simp[]) >>
  `32*SUC n = 32*n+32` by decide_tac >>
  asm_rewrite_tac[] >>
  simp_tac bool_ss [Once abi_encoder_mem_split] >>
  asm_simp_tac (srw_ss()) [abi_encoder_zero_word, REPLICATE_APPEND]
QED

Theorem abi_empty_store_frame:
  abi_decode_frame p (32*n) initial s ==>
  abi_decode_frame p (32*SUC n) initial (mstore (p+32*n) 0w s)
Proof
  strip_tac >> `32*SUC n = 32*n+32` by decide_tac >>
  asm_rewrite_tac[] >>
  irule abi_decode_frame_adjacent >> qexists_tac `s` >>
  simp[abi_decode_mstore_frame]
QED

Theorem abi_empty_zero_copy_input:
  has_type at av /\ ~is_dynamic at /\ static_length at = sz /\
  enc at av = REPLICATE sz 0w /\
  mem_bytes_at p sz mem = REPLICATE sz 0w /\ sz <= cap ==>
  abi_encoder_input (AbiCopy sz) at av p cap mem
Proof
  simp[abiEncoderInputTheory.abi_encoder_input_copy_iff]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_EMPTY_MEMORY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI empty memory not kernel closed: " ^ n)
  end) (DB.thms "abiEmptyMemory");

