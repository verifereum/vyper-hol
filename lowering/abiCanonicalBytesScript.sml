(* Dynamic ABI bytes already use Vyper's length-prefixed memory layout. *)
Theory abiCanonicalBytes
Ancestors
  venomMemProps
  abiDecoderTypedContract abiCanonicalHeadSize abiStaticAggregateProps valueEncoding
  valueEncodingProps contractABI words byte arithmetic list rich_list

Theorem canonical_bytes_encoding:
  enc (Bytes NONE) (contractABI$BytesV bs) =
    word_to_bytes (n2w (LENGTH bs) : 256 word) T ++
    bs ++ REPLICATE (contractABI$ceil32 (LENGTH bs) - LENGTH bs) 0w
Proof
  simp[Once enc_def, enc_number_def]
QED

Theorem canonical_bytes_source_head:
  mem_bytes_at sb (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) mem =
    enc (Bytes NONE) (contractABI$BytesV bs) ==>
  mem_bytes_at sb 32 mem = word_to_bytes (n2w (LENGTH bs) : 256 word) T
Proof
  pure_rewrite_tac[canonical_bytes_encoding, GSYM APPEND_ASSOC] >> strip_tac >>
  qspecl_then [`sb`, `[]`, `word_to_bytes (n2w (LENGTH bs) : 256 word) T`,
    `bs ++ REPLICATE (contractABI$ceil32 (LENGTH bs) - LENGTH bs) 0w`, `mem`]
    mp_tac abi_decoder_source_subwindow >> gvs[]
QED

Theorem canonical_bytes_source_payload:
  mem_bytes_at sb (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) mem =
    enc (Bytes NONE) (contractABI$BytesV bs) ==>
  mem_bytes_at (sb + 32) (LENGTH bs) mem = bs
Proof
  pure_rewrite_tac[canonical_bytes_encoding, GSYM APPEND_ASSOC] >> strip_tac >>
  qspecl_then [`sb`, `word_to_bytes (n2w (LENGTH bs) : 256 word) T`, `bs`,
    `REPLICATE (contractABI$ceil32 (LENGTH bs) - LENGTH bs) 0w`, `mem`]
    mp_tac abi_decoder_source_subwindow >> gvs[]
QED

Theorem canonical_bytes_source_layout:
  mem_bytes_at sb (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) mem =
    enc (Bytes NONE) (contractABI$BytesV bs) ==>
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) sb mem
Proof
  strip_tac >> drule canonical_bytes_source_head >> strip_tac >>
  drule canonical_bytes_source_payload >> strip_tac >>
  simp[val_in_memory_def, mem_word_at_bytes, word_of_bytes_word_to_bytes,
       dividesTheory.divides_def]
QED

Theorem canonical_bytes_count_load:
  mem_bytes_at sb (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))
    (abi_decode_source opc s) = enc (Bytes NONE) (contractABI$BytesV bs) /\
  sb < dimword (:256) ==>
  abi_decode_load opc (n2w sb : 256 word) s = n2w (LENGTH bs)
Proof
  strip_tac >> drule canonical_bytes_source_head >> strip_tac >>
  asm_simp_tac bool_ss [abi_decode_load_bytes] >> asm_rewrite_tac[] >>
  irule word_of_bytes_word_to_bytes >> simp[dividesTheory.divides_def]
QED

Theorem canonical_bytes_copied_layout:
  mem_bytes_at sb (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) source =
    enc (Bytes NONE) (contractABI$BytesV bs) /\
  val_wf (BaseTV (BytesT (Dynamic n))) (BytesV bs) /\
  type_memory_size (BaseTV (BytesT (Dynamic n))) <= cap /\
  mem_bytes_at sb cap source = mem_bytes_at d cap mem ==>
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) d mem
Proof
  strip_tac >> irule val_in_memory_relocate >>
  asm_simp_tac bool_ss [] >>
  qexistsl_tac [`source`, `cap`, `sb`] >> asm_simp_tac bool_ss [] >>
  irule canonical_bytes_source_layout >> first_assum ACCEPT_TAC
QED
