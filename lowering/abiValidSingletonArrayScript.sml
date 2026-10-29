(* Dynamic singleton validity exposes the actual head offset and child window. *)
Theory abiValidSingletonArray
Ancestors
  abiCanonicalLoad abiCanonicalArrayLoad abiDecoderContract vyperABI contractABI
  venomState words list rich_list arithmetic

Theorem abi_dynamic_singleton_value:
  is_dynamic at ==>
  dec (Tuple [at]) bs = ListV [dec at (DROP (abi_head_word bs) bs)]
Proof
  strip_tac >> asm_simp_tac bool_ss [Once dec_def, LET_THM] >>
  asm_simp_tac bool_ss [Once dec_def, LET_THM, GSYM abi_head_word_def] >>
  simp[Once dec_def]
QED

Theorem abi_valid_singleton_dynamic_decode:
  is_dynamic at /\ valid_enc (Tuple [at]) bs /\ dec (Tuple [at]) bs = ListV [av] ==>
  32 <= LENGTH bs /\ valid_enc at (DROP (abi_head_word bs) bs) /\
  dec at (DROP (abi_head_word bs) bs) = av /\
  word_of_bytes T (0w:256 word) (TAKE 32 bs) = n2w (abi_head_word bs)
Proof
  strip_tac >>
  gvs[Once valid_enc_def, Once dec_def, abi_head_word_def, LET_THM] >>
  gvs[Once valid_enc_def, Once dec_def, abi_head_word_def, LET_THM] >>
  gvs[Once valid_enc_def, Once dec_def, abi_head_word_def, LET_THM]
QED

Theorem abi_valid_singleton_array_decode:
  valid_enc (Tuple [Array NONE elem]) bs /\ dec (Tuple [Array NONE elem]) bs = ListV [av] ==>
  32 <= LENGTH bs /\ abi_head_word bs + 32 <= LENGTH bs /\
  valid_enc (Array NONE elem) (DROP (abi_head_word bs) bs) /\
  dec (Array NONE elem) (DROP (abi_head_word bs) bs) = av /\
  word_of_bytes T (0w:256 word) (TAKE 32 bs) = n2w (abi_head_word bs)
Proof
  strip_tac >>
  `is_dynamic (Array NONE elem)` by simp[] >>
  drule_all abi_valid_singleton_dynamic_decode >> strip_tac >>
  `32 <= LENGTH (DROP (abi_head_word bs) bs)` by fs[Once valid_enc_def] >>
  asm_simp_tac bool_ss [] >> fs[LENGTH_DROP] >> decide_tac
QED

Theorem abi_valid_singleton_array_load:
  valid_enc (Tuple [Array NONE elem]) bs /\ dec (Tuple [Array NONE elem]) bs = ListV [av] /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  abi_decode_load opc (n2w sb:bytes32) s = n2w (abi_head_word bs) /\
  sb + abi_head_word bs < dimword (:256) /\
  mem_bytes_at (sb + abi_head_word bs) (LENGTH (DROP (abi_head_word bs) bs))
    (abi_decode_source opc s) = DROP (abi_head_word bs) bs
Proof
  strip_tac >> drule_all abi_valid_singleton_array_decode >> strip_tac >>
  `sb < dimword (:256)` by decide_tac >>
  `mem_bytes_at sb 32 (abi_decode_source opc s) = TAKE 32 bs` by
    (qspecl_then [`sb`, `0`, `32`, `LENGTH bs`, `abi_decode_source opc s`]
      mp_tac mem_bytes_at_window >> simp[]) >>
  asm_simp_tac bool_ss [abi_decode_load_bytes] >> conj_tac
  >- decide_tac >>
  mp_tac (Q.INST [`off` |-> `abi_head_word bs`,
    `n` |-> `LENGTH (DROP (abi_head_word bs) bs)`] abi_decode_source_window) >>
  simp[LENGTH_DROP]
QED
