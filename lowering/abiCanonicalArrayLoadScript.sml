(* Actual source loads and child byte windows for canonical ABI arrays. *)
Theory abiCanonicalArrayLoad
Ancestors
  venomMemProps
  abiCanonicalArrays abiCanonicalLoad abiCanonicalWindows abiDecoderContract
  abiDecodeRanges contractABI valueEncoding list rich_list arithmetic byte words

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
