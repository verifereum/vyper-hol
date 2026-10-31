Theory abiCanonicalHeadSize
Ancestors
  venomMemProps abiCanonicalWindows abiDecodeRanges contractABI list rich_list arithmetic byte
  abiDecoderContract valueEncodingProps valueEncodingProofs valueEncoding words venomState

(* Canonical array data and member windows, for fixed and dynamic arrays. *)
Theorem canonical_array_tuple:
  enc (Array bound ty) (ListV vs) =
    (if bound = NONE then enc_number (Uint 256) (NumV (LENGTH vs)) else []) ++
    enc (Tuple (REPLICATE (LENGTH vs) ty)) (ListV vs)
Proof
  Cases_on `bound` >>
  simp[Once enc_def, enc_tuple_parts, abi_tuple_heads_def, abi_tuple_tails_def]
QED

Theorem canonical_array_drop_count:
  DROP (if bound = NONE then 32 else 0)
    (enc (Array bound ty) (ListV vs)) =
  enc (Tuple (REPLICATE (LENGTH vs) ty)) (ListV vs)
Proof
  pure_rewrite_tac[canonical_array_tuple] >> Cases_on `bound` >>
  simp[enc_number_def, LENGTH_word_to_bytes, DROP_APPEND]
QED

Theorem canonical_array_member_head_window:
  has_type (Array bound ty) (ListV (pre ++ v::post)) ==>
  TAKE (abi_member_head_size ty)
    (DROP ((if bound = NONE then 32 else 0) +
           LENGTH pre * abi_member_head_size ty)
      (enc (Array bound ty) (ListV (pre ++ v::post)))) =
    (if is_dynamic ty then enc_number (Uint 256)
       (NumV (LENGTH (pre ++ v::post) * abi_member_head_size ty +
               SUM (MAP (abi_member_tail_size ty) pre)))
     else enc ty v)
Proof
  strip_tac >>
  `has_types (REPLICATE (LENGTH (pre ++ v::post)) ty) (pre ++ v::post)` by
    (irule have_type_replicate >> gvs[has_type_def]) >>
  ONCE_REWRITE_TAC[ADD_COMM] >>
  pure_rewrite_tac[GSYM DROP_DROP_T, canonical_array_drop_count] >>
  qspecl_then [`REPLICATE (LENGTH pre) ty`, `ty`,
    `REPLICATE (LENGTH post) ty`, `pre`, `v`, `post`] mp_tac
    (Q.GENL [`pre`, `ty`, `post`, `pvs`, `v`, `rest`]
      canonical_member_head_window) >>
  simp_tac bool_ss [LENGTH_REPLICATE, GSYM REPLICATE, REPLICATE_APPEND,
    LENGTH_APPEND, LENGTH, uniform_member_sizes, head_lengths_acc,
    MAP_APPEND, SUM_APPEND, MAP, SUM] >>
  simp[uniform_member_sizes, LEFT_ADD_DISTRIB, MULT_CLAUSES] >>
  gvs[LENGTH_APPEND, DROP_DROP_T]
QED

Theorem canonical_array_member_tail_window:
  has_type (Array bound ty) (ListV (pre ++ v::post)) /\ is_dynamic ty ==>
  TAKE (LENGTH (enc ty v))
    (DROP ((if bound = NONE then 32 else 0) +
           LENGTH (pre ++ v::post) * abi_member_head_size ty +
           SUM (MAP (abi_member_tail_size ty) pre))
      (enc (Array bound ty) (ListV (pre ++ v::post)))) = enc ty v
Proof
  strip_tac >>
  `has_types (REPLICATE (LENGTH (pre ++ v::post)) ty) (pre ++ v::post)` by
    (irule have_type_replicate >> gvs[has_type_def]) >>
  pure_rewrite_tac[GSYM ADD_ASSOC] >> ONCE_REWRITE_TAC[ADD_COMM] >>
  pure_rewrite_tac[GSYM DROP_DROP_T, canonical_array_drop_count] >>
  qspecl_then [`REPLICATE (LENGTH pre) ty`, `ty`,
    `REPLICATE (LENGTH post) ty`, `pre`, `v`, `post`] mp_tac
    (Q.GENL [`pre`, `ty`, `post`, `pvs`, `v`, `rest`]
      canonical_member_tail_window) >>
  simp_tac bool_ss [LENGTH_REPLICATE, GSYM REPLICATE, REPLICATE_APPEND,
    LENGTH_APPEND, LENGTH, uniform_member_sizes, head_lengths_acc,
    MAP_APPEND, SUM_APPEND, MAP, SUM] >>
  simp[uniform_member_sizes, LEFT_ADD_DISTRIB, MULT_CLAUSES] >>
  gvs[LENGTH_APPEND, DROP_DROP_T]
QED

(* Canonical byte windows lifted to the actual decoder source loads. *)
Theorem mem_bytes_at_window:
  !sb off n len mem.
  off + n <= len ==>
  TAKE n (DROP off (mem_bytes_at sb len mem)) =
    mem_bytes_at (sb + off) n mem
Proof
  rpt strip_tac >>
  `n <= len - off` by decide_tac >>
  irule LIST_EQ >> simp[LENGTH_TAKE_EQ, LENGTH_DROP, MIN_ALT] >>
  rpt strip_tac >> rename1 `i < n` >>
  `off + i < len` by decide_tac >>
  simp[EL_TAKE, EL_DROP, EL_mem_bytes_at] >>
  pure_rewrite_tac[ADD_ASSOC] >> REFL_TAC
QED

Theorem abi_decode_load_bytes:
  p < dimword (:'a) ==>
  abi_decode_load opc (n2w p : 'a word) s =
    word_of_bytes T (0w:256 word) (mem_bytes_at p 32 (abi_decode_source opc s))
Proof
  strip_tac >> Cases_on `opc = MLOAD` >>
  simp[abi_decode_load_def, abi_decode_source_def, mload_def,
       mem_bytes_at_def, w2n_n2w]
QED

Theorem canonical_member_offset_word:
  has_types (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty ==>
  word_of_bytes T (0w:256 word)
    (TAKE 32 (DROP (SUM (MAP abi_member_head_size pre))
      (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest))))) =
    n2w (head_lengths (pre ++ ty::post) 0 +
         SUM (MAP2 abi_member_tail_size pre pvs))
Proof
  strip_tac >> drule_all canonical_member_head_window >>
  asm_simp_tac bool_ss [LET_THM, abi_member_head_size_def, enc_number_def] >>
  strip_tac >> asm_rewrite_tac[] >> irule word_of_bytes_word_to_bytes >>
  simp[dividesTheory.divides_def]
QED

Theorem abi_decode_load_window:
  off + 32 <= len /\ sb + off < dimword (:'a) ==>
  abi_decode_load opc (n2w (sb + off) : 'a word) s =
    word_of_bytes T (0w:256 word)
      (TAKE 32 (DROP off (mem_bytes_at sb len (abi_decode_source opc s))))
Proof
  strip_tac >> asm_simp_tac bool_ss [abi_decode_load_bytes] >>
  AP_TERM_TAC >> irule EQ_SYM >> irule mem_bytes_at_window >>
  first_assum ACCEPT_TAC
QED

Theorem canonical_member_offset_load:
  has_types (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty /\
  mem_bytes_at sb (LENGTH (enc (Tuple (pre ++ ty::post))
    (ListV (pvs ++ v::rest)))) (abi_decode_source opc s) =
      enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)) /\
  sb + LENGTH (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest))) <
    dimword (:256) ==>
  abi_decode_load opc
    (n2w (sb + SUM (MAP abi_member_head_size pre)) : 256 word) s =
  n2w (head_lengths (pre ++ ty::post) 0 +
       SUM (MAP2 abi_member_tail_size pre pvs))
Proof
  strip_tac >> drule_all canonical_member_ranges >>
  asm_simp_tac bool_ss [LET_THM, abi_member_head_size_def] >> strip_tac >>
  `sb + SUM (MAP abi_member_head_size pre) < dimword (:256)` by decide_tac >>
  irule EQ_TRANS >>
  qexists_tac `word_of_bytes T (0w:256 word)
    (TAKE 32 (DROP (SUM (MAP abi_member_head_size pre))
      (mem_bytes_at sb (LENGTH (enc (Tuple (pre ++ ty::post))
        (ListV (pvs ++ v::rest)))) (abi_decode_source opc s))))` >>
  conj_tac
  >- (irule abi_decode_load_window >> simp[]) >>
  asm_rewrite_tac[] >> irule canonical_member_offset_word >> simp[]
QED

(* Actual source loads and child byte windows for canonical ABI arrays. *)
Theorem abi_decode_source_window:
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  off + n <= LENGTH bs ==>
  mem_bytes_at (sb + off) n (abi_decode_source opc s) = TAKE n (DROP off bs)
Proof
  strip_tac >> irule EQ_TRANS >>
  qexists_tac `TAKE n (DROP off
    (mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s)))` >>
  conj_tac >- (irule EQ_SYM >> irule mem_bytes_at_window >> simp[]) >>
  asm_rewrite_tac[]
QED

Theorem canonical_dynamic_array_count_load:
  mem_bytes_at sb (LENGTH (enc (Array NONE ty) (ListV vs)))
    (abi_decode_source opc s) = enc (Array NONE ty) (ListV vs) /\
  sb + LENGTH (enc (Array NONE ty) (ListV vs)) < dimword (:256) ==>
  abi_decode_load opc (n2w sb : 256 word) s = n2w (LENGTH vs)
Proof
  strip_tac >>
  `32 <= LENGTH (enc (Array NONE ty) (ListV vs))` by
    (pure_rewrite_tac[canonical_array_tuple] >>
     simp[enc_number_def, LENGTH_word_to_bytes]) >>
  `sb < dimword (:256)` by decide_tac >>
  `mem_bytes_at (sb + 0) 32 (abi_decode_source opc s) =
    TAKE 32 (DROP 0 (enc (Array NONE ty) (ListV vs)))` by
    (irule abi_decode_source_window >> asm_simp_tac bool_ss [ADD_CLAUSES]) >>
  `mem_bytes_at sb 32 (abi_decode_source opc s) =
    word_to_bytes (n2w (LENGTH vs) : 256 word) T` by
    (qpat_x_assum `mem_bytes_at (sb + 0) _ _ = _` mp_tac >>
     pure_rewrite_tac[canonical_array_tuple] >>
     simp[enc_number_def, LENGTH_word_to_bytes, TAKE_APPEND]) >>
  asm_simp_tac bool_ss [abi_decode_load_bytes] >>
  asm_rewrite_tac[] >> irule word_of_bytes_word_to_bytes >>
  simp[dividesTheory.divides_def]
QED

Theorem canonical_array_offset_load:
  has_type (Array bound ty) (ListV (pre ++ v::post)) /\ is_dynamic ty /\
  mem_bytes_at sb (LENGTH (enc (Array bound ty) (ListV (pre ++ v::post))))
    (abi_decode_source opc s) = enc (Array bound ty) (ListV (pre ++ v::post)) /\
  sb + LENGTH (enc (Array bound ty) (ListV (pre ++ v::post))) < dimword (:256) ==>
  abi_decode_load opc
    (n2w (sb + ((if bound = NONE then 32 else 0) +
                LENGTH pre * abi_member_head_size ty)) : 256 word) s =
  n2w (LENGTH (pre ++ v::post) * abi_member_head_size ty +
       SUM (MAP (abi_member_tail_size ty) pre))
Proof
  strip_tac >> drule canonical_array_member_ranges >>
  asm_simp_tac bool_ss [LET_THM, abi_member_head_size_def] >> strip_tac >>
  `sb + ((if bound = NONE then 32 else 0) +
         LENGTH pre * 32) < dimword (:256)` by
    (Cases_on `bound = NONE` >> gvs[abi_member_head_size_def] >> decide_tac) >>
  irule EQ_TRANS >>
  qexists_tac `word_of_bytes T (0w:256 word)
    (TAKE 32 (DROP ((if bound = NONE then 32 else 0) +
                    LENGTH pre * abi_member_head_size ty)
      (mem_bytes_at sb (LENGTH (enc (Array bound ty) (ListV (pre ++ v::post))))
        (abi_decode_source opc s))))` >>
  conj_tac
  >- (qpat_assum `is_dynamic ty` (fn dyn =>
        simp_tac bool_ss [abi_member_head_size_def, dyn]) >>
      irule abi_decode_load_window >>
      asm_simp_tac bool_ss [abi_member_head_size_def]) >>
  asm_rewrite_tac[] >> drule canonical_array_member_head_window >>
  asm_simp_tac bool_ss [abi_member_head_size_def] >> strip_tac >>
  asm_rewrite_tac[enc_number_def] >>
  irule word_of_bytes_word_to_bytes >> simp[dividesTheory.divides_def]
QED

Theorem canonical_array_dynamic_child_source:
  has_type (Array bound ty) (ListV (pre ++ v::post)) /\ is_dynamic ty /\
  mem_bytes_at sb (LENGTH (enc (Array bound ty) (ListV (pre ++ v::post))))
    (abi_decode_source opc s) = enc (Array bound ty) (ListV (pre ++ v::post)) ==>
  mem_bytes_at
    (sb + ((if bound = NONE then 32 else 0) +
           LENGTH (pre ++ v::post) * abi_member_head_size ty +
           SUM (MAP (abi_member_tail_size ty) pre)))
    (LENGTH (enc ty v)) (abi_decode_source opc s) = enc ty v
Proof
  strip_tac >> drule canonical_array_member_ranges >>
  asm_simp_tac bool_ss [LET_THM] >> strip_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >>
  irule EQ_TRANS >>
  qexists_tac `TAKE (LENGTH (enc ty v))
    (DROP ((if bound = NONE then 32 else 0) +
           LENGTH (pre ++ v::post) * abi_member_head_size ty +
           SUM (MAP (abi_member_tail_size ty) pre))
      (enc (Array bound ty) (ListV (pre ++ v::post))))` >>
  conj_tac >- (irule abi_decode_source_window >> asm_simp_tac bool_ss []) >>
  irule canonical_array_member_tail_window >> simp[]
QED

Theorem canonical_array_member_type:
  has_type (Array bound ty) (ListV (pre ++ v::post)) ==> has_type ty v
Proof
  strip_tac >>
  `LIST_REL has_type (REPLICATE (LENGTH (pre ++ v::post)) ty) (pre ++ v::post)` by
    gvs[has_type_def, has_types_LIST_REL] >>
  `MEM v (pre ++ v::post)` by simp[] >>
  drule_all LIST_REL_MEM_IMP_R >> simp[]
QED

Theorem canonical_array_static_child_source:
  has_type (Array bound ty) (ListV (pre ++ v::post)) /\ ~is_dynamic ty /\
  mem_bytes_at sb (LENGTH (enc (Array bound ty) (ListV (pre ++ v::post))))
    (abi_decode_source opc s) = enc (Array bound ty) (ListV (pre ++ v::post)) ==>
  mem_bytes_at
    (sb + ((if bound = NONE then 32 else 0) + LENGTH pre * abi_member_head_size ty))
    (LENGTH (enc ty v)) (abi_decode_source opc s) = enc ty v
Proof
  strip_tac >> drule canonical_array_member_ranges >>
  asm_simp_tac bool_ss [LET_THM] >> strip_tac >>
  `has_type ty v` by (drule canonical_array_member_type >> simp[]) >>
  `LENGTH (enc ty v) = abi_member_head_size ty` by
    (simp[abi_member_head_size_def] >>
     irule (cj 1 enc_has_static_length) >> simp[]) >>
  irule EQ_TRANS >>
  qexists_tac `TAKE (abi_member_head_size ty)
    (DROP ((if bound = NONE then 32 else 0) + LENGTH pre * abi_member_head_size ty)
      (enc (Array bound ty) (ListV (pre ++ v::post))))` >>
  conj_tac >- (asm_rewrite_tac[] >> irule abi_decode_source_window >>
               asm_simp_tac bool_ss []) >>
  drule canonical_array_member_head_window >> asm_simp_tac bool_ss []
QED

(* Minimum canonical dynamic heads; a zero-length fixed array is explicit. *)
Theorem canonical_dynamic_head_sum:
  !ts. any_dynamic ts ==> 32 <= SUM (MAP abi_member_head_size ts)
Proof
  Induct >> simp[is_dynamic_def] >> qx_gen_tac `head` >>
  Cases_on `is_dynamic head` >> simp[abi_member_head_size_def] >>
  strip_tac >> first_x_assum drule >> decide_tac
QED

Theorem canonical_dynamic_tuple_head_min:
  has_type (Tuple ts) av /\ any_dynamic ts ==>
  32 <= LENGTH (enc (Tuple ts) av)
Proof
  Cases_on `av` >> simp_tac bool_ss [has_type_def] >> strip_tac >>
  drule canonical_tuple_length >> strip_tac >>
  drule canonical_dynamic_head_sum >> strip_tac >> decide_tac
QED

Theorem canonical_dynamic_array_list_head_min[local]:
  has_type (Array bound ty) (ListV vs) /\
  is_dynamic (Array bound ty) /\ bound <> SOME 0 ==>
  32 <= LENGTH (enc (Array bound ty) (ListV vs))
Proof
  strip_tac >> drule canonical_array_length >> strip_tac >>
  Cases_on `bound` >>
  gvs[is_dynamic_def, abi_member_head_size_def, Excl "enc_def"] >>
  `0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >> decide_tac
QED

Theorem canonical_dynamic_array_head_min:
  has_type (Array bound ty) av /\
  is_dynamic (Array bound ty) /\ bound <> SOME 0 ==>
  32 <= LENGTH (enc (Array bound ty) av)
Proof
  Cases_on `av` >> simp_tac bool_ss [has_type_def] >> rpt strip_tac >>
  irule canonical_dynamic_array_list_head_min >> simp[has_type_def]
QED

Theorem canonical_dynamic_encoding_head_min:
  has_type aty av /\ is_dynamic aty /\
  (!elem. aty <> Array (SOME 0) elem) ==>
  32 <= LENGTH (enc aty av)
Proof
  Cases_on `aty` >> simp_tac bool_ss [is_dynamic_def] >|
  [rename1 `has_type (Bytes bound) av` >>
   Cases_on `bound` >> Cases_on `av` >>
   simp[has_type_def, is_dynamic_def, enc_def, enc_number_def, LENGTH_word_to_bytes],
   Cases_on `av` >>
   simp[has_type_def, enc_def, enc_number_def, LENGTH_word_to_bytes],
   rename1 `has_type (Array bound elem) av` >> rpt strip_tac >>
   `bound <> SOME 0` by
     (strip_tac >> qpat_x_assum `!child. _` (qspec_then `elem` mp_tac) >> simp[]) >>
   irule canonical_dynamic_array_head_min >> asm_simp_tac bool_ss [is_dynamic_def],
   rpt strip_tac >> irule canonical_dynamic_tuple_head_min >> asm_simp_tac bool_ss []]
QED
