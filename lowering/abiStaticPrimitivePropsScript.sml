(* Slice-local reverse representation boundaries for static ABI chunks. *)
Theory abiStaticPrimitiveProps
Ancestors
  abiStaticLayoutProps valueEncoding vyperABI vyperTyping compileEnv
  contractABI byte integer_word bitstring venomMemProofs

Theorem mem_word_at_bytes:
  mem_word_at off mem = word_of_bytes T (0w:bytes32) (mem_bytes_at off 32 mem)
Proof
  simp[mem_word_at_def, mem_bytes_at_def]
QED

Theorem abi_static_primitive_layout:
  is_word_type (BaseT bt) /\
  value_has_type (BaseTV bt) v /\
  vyper_to_abi_base bt v = SOME av /\
  mem_bytes_at off 32 mem = enc (vyper_base_to_abi_type bt) av ==>
  val_in_memory (BaseTV bt) v off mem
Proof
  Cases_on `bt` >> Cases_on `v` >>
  simp[is_word_type_def, vyper_to_abi_base_def] >>
  rw[] >> gvs[value_has_type_def, val_in_memory_def,
    mem_word_at_bytes, enc_def, enc_number_def, val_to_w256_def,
    typed_val_to_w256_def, word_of_bytes_word_to_bytes,
    dividesTheory.divides_def]
  >- (simp[i2w_def] >> Cases_on `i = 0` >> gvs[] >>
      `~(i < 0)` by intLib.COOPER_TAC >> simp[])
  >- (Cases_on `b` >> gvs[is_word_type_def, vyper_base_to_abi_type_def,
       enc_def, value_has_type_def, listTheory.PAD_RIGHT,
       listTheory.TAKE_LENGTH_TOO_LONG, rich_listTheory.REPLICATE_GENLIST,
       word_of_bytes_be_def])
  >> simp[GSYM wordsTheory.w2w_def]
  >> dep_rewrite.DEP_REWRITE_TAC[w2w_word_of_bytes_be_pad_left_proof]
  >> CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV)
  >> simp[dividesTheory.divides_def]
QED

Theorem abi_static_flag_layout:
  mem_bytes_at off 32 mem = enc (Uint 256) (NumV k) ==>
  val_in_memory (FlagTV m) (FlagV k) off mem
Proof
  simp[val_in_memory_def, mem_word_at_bytes, enc_def, enc_number_def,
       val_to_w256_def] >> strip_tac >> simp[] >>
  irule word_of_bytes_word_to_bytes >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
  simp[dividesTheory.divides_def]
QED

Theorem abi_compatible_base_layout:
  static_layout_compatible cenv tenv (BaseT bt) tv /\
  value_has_type tv v /\
  vyper_to_abi tenv (BaseT bt) v = SOME av /\
  mem_bytes_at off 32 mem = enc (vyper_to_abi_type tenv (BaseT bt)) av ==>
  val_in_memory tv v off mem
Proof
  simp[static_layout_base_iff] >>
  metis_tac[abi_static_primitive_layout]
QED

Theorem abi_compatible_flag_layout:
  mem_bytes_at off 32 mem = enc (vyper_to_abi_type tenv (FlagT nsid)) (NumV k) ==>
  val_in_memory (FlagTV m) (FlagV k) off mem
Proof
  simp[abi_static_flag_layout]
QED

Theorem mem_bytes_at_bounded:
  off + n <= LENGTH mem ==>
  mem_bytes_at off n mem = TAKE n (DROP off mem)
Proof
  simp[mem_bytes_at_def, rich_listTheory.TAKE_APPEND, listTheory.LENGTH_DROP]
QED

Theorem mem_bytes_at_child_slice:
  off + (LENGTH pre + LENGTH child + LENGTH post) <= LENGTH mem /\
  mem_bytes_at off (LENGTH pre + LENGTH child + LENGTH post) mem =
    pre ++ child ++ post ==>
  mem_bytes_at (off + LENGTH pre) (LENGTH child) mem = child
Proof
  rpt strip_tac >>
  `off + LENGTH pre + LENGTH child <= LENGTH mem` by decide_tac >>
  gvs[mem_bytes_at_bounded] >>
  qpat_x_assum `TAKE _ _ = _` (mp_tac o AP_TERM ``\bs:byte list. TAKE (LENGTH (child:byte list)) (DROP (LENGTH (pre:byte list)) bs)``) >>
  simp[listTheory.DROP_TAKE, rich_listTheory.TAKE_TAKE,
       rich_listTheory.DROP_DROP, listTheory.DROP_APPEND,
       rich_listTheory.TAKE_APPEND, arithmeticTheory.MIN_DEF]
QED

Theorem abi_compatible_flag_value_layout:
  value_has_type (FlagTV m) v /\
  vyper_to_abi tenv (FlagT nsid) v = SOME av /\
  mem_bytes_at off 32 mem = enc (vyper_to_abi_type tenv (FlagT nsid)) av ==>
  val_in_memory (FlagTV m) v off mem
Proof
  Cases_on `v` >> simp[value_has_type_def] >>
  rpt strip_tac >> gvs[] >> irule abi_static_flag_layout >> simp[]
QED

(* Assert proof integrity even when imported theories were restored from cache. *)
val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_STATIC_PRIMITIVE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI static primitive not kernel closed: " ^ n)
  end) (DB.thms "abiStaticPrimitiveProps");
