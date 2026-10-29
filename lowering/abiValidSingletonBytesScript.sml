(* Valid singleton Bytes/String tuples can use arbitrary in-range offsets.
   TOP-LEVEL: child validity, decoded payload and physical source windows. *)
Theory abiValidSingletonBytes
Ancestors
  abiValidBytes abiCanonicalLoad abiCanonicalArrayLoad abiDecoderContract
  vyperABI contractABI venomState words list rich_list arithmetic

Theorem abi_valid_singleton_bytes_decode:
  (at = Bytes NONE \/ at = String) /\ valid_enc (Tuple [at]) bs /\
  dec (Tuple [at]) bs = ListV [contractABI$BytesV payload] ==>
  32 <= LENGTH bs /\ abi_head_word bs + 32 <= LENGTH bs /\
  valid_enc at (DROP (abi_head_word bs) bs) /\
  dec at (DROP (abi_head_word bs) bs) = contractABI$BytesV payload /\
  word_of_bytes T (0w:256 word) (TAKE 32 bs) = n2w (abi_head_word bs)
Proof
  strip_tac >> gvs[valid_enc_def, dec_def, dec_number_def, dest_NumV_def,
    abi_head_word_def, is_dynamic_def, LET_THM, LENGTH_DROP] >> decide_tac
QED

Theorem abi_valid_singleton_bytes_load:
  (at = Bytes NONE \/ at = String) /\ valid_enc (Tuple [at]) bs /\
  dec (Tuple [at]) bs = ListV [contractABI$BytesV payload] /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  abi_decode_load opc (n2w sb:bytes32) s = n2w (abi_head_word bs) /\
  sb + abi_head_word bs < dimword (:256) /\
  mem_bytes_at (sb + abi_head_word bs) (LENGTH (DROP (abi_head_word bs) bs))
    (abi_decode_source opc s) = DROP (abi_head_word bs) bs
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_valid_singleton_bytes_decode >> strip_tac >>
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
