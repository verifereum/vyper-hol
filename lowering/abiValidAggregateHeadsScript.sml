(* Readable source heads follow from validity, without canonical offsets. *)
Theory abiValidAggregateHeads
Ancestors
  abiValidMembers abiCanonicalHeadSize abiDecodeRanges vyperABI contractABI
  words list rich_list option arithmetic

Theorem abi_decode_array_members:
  !cnt at base hds acc.
  dec_array cnt (if is_dynamic at then NONE else SOME (static_length at)) at base hds acc =
    dec_tuple (REPLICATE cnt at) base hds acc
Proof
  Induct >- simp[Once dec_def] >> rpt gen_tac >> Cases_on `is_dynamic at` >>
  asm_simp_tac bool_ss [REPLICATE] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [dec_def])) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [dec_def])) >>
  first_x_assum (qspec_then `at` mp_tac) >> asm_simp_tac bool_ss [LET_THM] >>
  strip_tac >> asm_simp_tac bool_ss []
QED

Theorem abi_valid_array_heads:
  valid_enc_array cnt (if is_dynamic at then NONE else SOME (static_length at)) at base hds ==>
  cnt * abi_member_head_size at <= LENGTH hds /\
  has_types (REPLICATE cnt at) (abi_decode_members (REPLICATE cnt at) base hds)
Proof
  strip_tac >>
  `valid_enc_tuple (REPLICATE cnt at) base hds` by fs[valid_enc_tuple_REPLICATE] >>
  drule abi_valid_members_view >>
  simp[map_replicate, SUM_REPLICATE, Excl "dec_def", Excl "valid_enc_def"]
QED

Theorem abi_valid_dynamic_array_view:
  valid_enc (Array NONE at) bs ==>
  32 <= LENGTH bs /\
  valid_enc_tuple (REPLICATE (abi_head_word bs) at) (DROP 32 bs) (DROP 32 bs) /\
  dec (Array NONE at) bs = ListV
    (abi_decode_members (REPLICATE (abi_head_word bs) at) (DROP 32 bs) (DROP 32 bs)) /\
  abi_head_word bs * abi_member_head_size at <= LENGTH (DROP 32 bs) /\
  has_types (REPLICATE (abi_head_word bs) at)
    (abi_decode_members (REPLICATE (abi_head_word bs) at) (DROP 32 bs) (DROP 32 bs))
Proof
  simp_tac bool_ss [Once valid_enc_def, LET_THM, GSYM abi_head_word_def] >> strip_tac >>
  drule abi_valid_array_heads >> strip_tac >>
  asm_simp_tac (srw_ss()) [valid_enc_tuple_REPLICATE, Once dec_def, LET_THM,
    GSYM abi_head_word_def, abi_decode_array_members, abi_decode_members_value,
    Excl "dec_def", Excl "valid_enc_def"]
QED

Theorem abi_valid_dynamic_array_head_min:
  valid_enc (Array bound at) bs /\ is_dynamic (Array bound at) /\ bound <> SOME 0 ==>
  32 <= LENGTH bs
Proof
  Cases_on `bound` >- simp[Once valid_enc_def] >>
  simp_tac bool_ss [Once valid_enc_def, is_dynamic_def, IS_NONE_DEF, SOME_11, LET_THM] >> strip_tac >>
  drule abi_valid_array_heads >> strip_tac >>
  qpat_x_assum `_ * abi_member_head_size at <= _` mp_tac >>
  asm_simp_tac bool_ss [abi_member_head_size_def] >> strip_tac >> decide_tac
QED

Theorem abi_valid_dynamic_head_min:
  valid_enc at bs /\ is_dynamic at /\ (!elem. at <> Array (SOME 0) elem) ==>
  32 <= LENGTH bs
Proof
  Cases_on `at` >> simp_tac bool_ss [is_dynamic_def] >|
  [rename1 `valid_enc (Bytes bound) bs` >> Cases_on `bound` >> simp[Once valid_enc_def],
   simp[Once valid_enc_def],
   rename1 `valid_enc (Array bound elem) bs` >> rpt strip_tac >>
   `bound <> SOME 0` by
     (strip_tac >> qpat_x_assum `!child. _` (qspec_then `elem` mp_tac) >> simp[]) >>
   irule abi_valid_dynamic_array_head_min >> qexistsl_tac [`elem`, `bound`] >>
   asm_simp_tac bool_ss [is_dynamic_def],
   rename1 `valid_enc (Tuple ats) bs` >>
   rpt strip_tac >> `valid_enc_tuple ats bs bs` by fs[Once valid_enc_def] >>
   drule abi_valid_members_view >> strip_tac >>
   drule canonical_dynamic_head_sum >> strip_tac >> decide_tac]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_AGGREGATE_HEADS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid aggregate heads not kernel closed: " ^ n)
  end) (DB.thms "abiValidAggregateHeads");
