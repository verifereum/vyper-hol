(* TOP-LEVEL: abi_dynamic_bytes_prefix.
   The live length word and bytestring payload in source memory match the
   unpadded prefix of the semantic ABI encoding. *)
Theory abiBytesValueEncoding
Ancestors
  abiValueEncoding valueEncoding valueEncodingProps contractABI
  venomMemProps list rich_list words byte divides

Theorem abi_dynamic_bytes_memory:
  val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV bs) off mem /\
  off + 32 + LENGTH bs ≤ LENGTH mem ⇒
  mem_bytes_at off (32 + LENGTH bs) mem =
    word_to_bytes (n2w (LENGTH bs) : bytes32) T ++ bs
Proof
  rpt strip_tac >>
  `mem_bytes_at off 32 mem =
     word_to_bytes (n2w (LENGTH bs) : bytes32) T` by
    (fs[Once val_in_memory_def, mem_word_at_def, mem_bytes_at_def] >>
     qpat_x_assum `word_of_bytes _ _ _ = _` (SUBST_ALL_TAC o SYM) >>
     irule (GSYM word_bytes_roundtrip) >>
     simp[divides_def]) >>
  `mem_bytes_at (off + 32) (LENGTH bs) mem = bs` by
    fs[Once val_in_memory_def] >>
  mp_tac (Q.SPECL [`off`,`32`,`LENGTH (bs:byte list)`,`mem`]
    mem_bytes_at_split) >>
  impl_tac >- decide_tac >> simp[]
QED

Theorem abi_dynamic_bytes_prefix:
  val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV bs) off mem /\
  off + 32 + LENGTH bs ≤ LENGTH mem ⇒
  mem_bytes_at off (32 + LENGTH bs) mem =
    TAKE (32 + LENGTH bs) (enc (Bytes NONE) (contractABI$BytesV bs))
Proof
  strip_tac >> drule_all abi_dynamic_bytes_memory >>
  simp[Once enc_def, enc_number_def, TAKE_APPEND,
       byteTheory.LENGTH_word_to_bytes, le_ceil32]
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "abiBytesValueEncoding");
