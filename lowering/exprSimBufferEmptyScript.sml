(*
 * Default values in zeroed memory (#636)
 *
 * empty(T) of a non-word type is a zeroed buffer.  The default value of a
 * type is in memory where its bytes are all zero, or, for a bytestring or
 * dynamic array, where its length word is zero.  Nothing here assumes
 * ALLOCA zeroes memory.
 *
 * TOP-LEVEL:
 *   default_memory_header — a zero length word holds the default Bytes[n],
 *     String[n] or dynamic array
 *   default_memory_zero_bytes — type_memory_size tv zero bytes hold
 *     default_value tv
 *   mem_word_at_zero_range, mem_bytes_at_zero_extend — zero ranges
 *
 * Helpers: default_memory_zero_words.
 *)
Theory exprSimBufferEmpty
Ancestors
  valueEncodingProofs valueEncodingProps valueEncoding vyperValue builtinSimple
  list rich_list
Libs
  wordsLib

Theorem default_memory_header:
  (!n off mem. mem_word_at off mem = 0w ==>
    val_in_memory (BaseTV (BytesT (Dynamic n)))
      (default_value (BaseTV (BytesT (Dynamic n)))) off mem) /\
  (!n off mem. mem_word_at off mem = 0w ==>
    val_in_memory (BaseTV (StringT n))
      (default_value (BaseTV (StringT n))) off mem) /\
  (!tv n off mem. mem_word_at off mem = 0w ==>
    val_in_memory (ArrayTV tv (Dynamic n))
      (default_value (ArrayTV tv (Dynamic n))) off mem)
Proof
  simp[default_value_def, val_in_memory_def, mem_bytes_at_def]
QED

Theorem default_memory_zero_words:
  (!tv off mem.
    (!i. i + 32 <= type_memory_size tv ==> mem_word_at (off + i) mem = 0w) ==>
    val_in_memory tv (default_value tv) off mem) /\
  (!tvs off mem.
    (!i. i + 32 <= type_memory_size_list tvs ==> mem_word_at (off + i) mem = 0w) ==>
    tuple_in_memory (MAP default_value tvs) tvs off mem) /\
  (!fields off mem.
    (!i. i + 32 <= type_memory_size_fields fields ==> mem_word_at (off + i) mem = 0w) ==>
    fields_in_memory (MAP (\(id,t). (id, default_value t)) fields) fields off mem)
Proof
  ho_match_mp_tac type_memory_size_ind >>
  simp[default_value_def, default_value_tuple_MAP, default_value_struct_MAP,
       type_memory_size_def, val_in_memory_def, mem_bytes_at_def,
       val_to_w256_def, typed_val_to_w256_def, integer_wordTheory.i2w_def,
       word_of_bytes_be_pad_right, byteTheory.word_of_bytes_be_def,
       word_of_bytes_replicate_zero] >>
  rpt conj_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >- (rpt strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >- (rpt strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >- (rpt strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >- (rpt strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >- (rpt strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >- (rpt strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >- (rpt strip_tac >> first_x_assum (qspec_then `0` mp_tac) >>
      simp[] >> EVAL_TAC)
  >- (rpt strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >- (rpt strip_tac >> first_x_assum irule >> rpt strip_tac >>
      `i * type_memory_size tv + type_memory_size tv <= n * type_memory_size tv` by
        (`SUC i * type_memory_size tv <= n * type_memory_size tv` by
           (irule arithmeticTheory.LESS_MONO_MULT >> simp[]) >>
         qpat_x_assum `SUC i * _ <= _` mp_tac >>
         simp_tac pure_ss [arithmeticTheory.MULT] >> decide_tac) >>
      first_x_assum (qspec_then `i * type_memory_size tv + i'` mp_tac) >>
      (impl_tac >- decide_tac) >>
      `i * type_memory_size tv + i' + off = i' + (off + i * type_memory_size tv)`
        by decide_tac >> asm_rewrite_tac[])
  >- (rpt strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >> rpt strip_tac >> first_x_assum irule >> rpt strip_tac >>
  first_x_assum (qspec_then `type_memory_size tv + i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  `type_memory_size tv + i + off = i + (off + type_memory_size tv)`
    by decide_tac >> asm_rewrite_tac[]
QED

Theorem mem_word_at_zero_range:
  !b len mem i.
    mem_bytes_at b len mem = REPLICATE len 0w /\ i + 32 <= len ==>
    mem_word_at (b+i) mem = 0w
Proof
  rpt strip_tac >>
  `mem_bytes_at b len mem = mem_bytes_at b len []` by
    simp[mem_bytes_at_def] >>
  drule mem_bytes_at_agree_window >> strip_tac >>
  first_x_assum (qspec_then `b+i` mp_tac) >>
  simp[mem_word_at_def, TAKE_LENGTH_ID_rwt, word_of_bytes_replicate_zero]
QED

Theorem default_memory_zero_bytes:
  !tv off mem.
    mem_bytes_at off (type_memory_size tv) mem =
      REPLICATE (type_memory_size tv) 0w ==>
    val_in_memory tv (default_value tv) off mem
Proof
  rpt strip_tac >> irule (cj 1 default_memory_zero_words) >>
  rpt strip_tac >> irule mem_word_at_zero_range >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem mem_bytes_at_zero_extend:
  !b k s.
    mem_bytes_at b k s.vs_memory = REPLICATE k 0w ==>
    mem_bytes_at b (k+32) (mstore (b+k) 0w s).vs_memory =
      REPLICATE (k+32) 0w
Proof
  rpt strip_tac >> rewrite_tac[mem_bytes_at_split_padded] >>
  `mem_bytes_at b k (mstore (b+k) 0w s).vs_memory = mem_bytes_at b k s.vs_memory`
    by (irule mstore_mem_bytes_at_disjoint_proof >> simp[]) >>
  `word_to_bytes (0w:bytes32) T = REPLICATE 32 (0w:word8)` by EVAL_TAC >>
  simp[mem_bytes_at_mstore_same, REPLICATE_APPEND]
QED
