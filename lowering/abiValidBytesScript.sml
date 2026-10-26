(* Valid Bytes/String windows, including noncanonical padding and trailing data.
   TOP-LEVEL: decode facts, source layout and the actual source count load. *)
Theory abiValidBytes
Ancestors
  abiCanonicalLoad abiDecoderContract abiStaticPrimitiveProps valueEncoding valueEncodingProps
  contractABI words list rich_list arithmetic

Theorem abi_valid_bytes_decode:
  (at = Bytes NONE \/ at = String) /\ valid_enc at bs /\
  dec at bs = contractABI$BytesV payload ==>
  32 <= LENGTH bs /\ 32 + LENGTH payload <= LENGTH bs /\
  TAKE (LENGTH payload) (DROP 32 bs) = payload /\
  word_of_bytes T (0w:256 word) (TAKE 32 bs) = n2w (LENGTH payload)
Proof
  strip_tac >> gvs[valid_enc_def, dec_def, dec_number_def, dest_NumV_def,
    LET_THM, LENGTH_TAKE_EQ, LENGTH_DROP, MIN_DEF] >>
  rpt conj_tac >> TRY (decide_tac) >> simp[]
QED

Theorem abi_valid_bytes_source_layout:
  (at = Bytes NONE \/ at = String) /\ valid_enc at bs /\
  dec at bs = contractABI$BytesV payload /\
  mem_bytes_at sb (LENGTH bs) mem = bs ==>
  val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) sb mem
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_valid_bytes_decode >> strip_tac >>
  `mem_bytes_at sb 32 mem = TAKE 32 bs` by
    (qspecl_then [`sb`, `0`, `32`, `LENGTH bs`, `mem`]
      mp_tac mem_bytes_at_window >> simp[]) >>
  `mem_bytes_at (sb + 32) (LENGTH payload) mem = payload` by
    (qspecl_then [`sb`, `32`, `LENGTH payload`, `LENGTH bs`, `mem`]
      mp_tac mem_bytes_at_window >> simp[]) >>
  simp[val_in_memory_def, mem_word_at_bytes]
QED

Theorem abi_valid_bytes_count_load:
  (at = Bytes NONE \/ at = String) /\ valid_enc at bs /\
  dec at bs = contractABI$BytesV payload /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb < dimword (:256) ==>
  abi_decode_load opc (n2w sb : 256 word) s = n2w (LENGTH payload)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_valid_bytes_decode >> strip_tac >>
  `mem_bytes_at sb 32 (abi_decode_source opc s) = TAKE 32 bs` by
    (qspecl_then [`sb`, `0`, `32`, `LENGTH bs`, `abi_decode_source opc s`]
      mp_tac mem_bytes_at_window >> simp[]) >>
  asm_simp_tac bool_ss [abi_decode_load_bytes]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_BYTES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid bytes not kernel closed: " ^ n)
  end) (DB.thms "abiValidBytes");
