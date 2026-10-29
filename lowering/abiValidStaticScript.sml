Theory abiValidStatic
Ancestors
  contractABI venomMemProofs vfmTypes byte words integer_word list rich_list arithmetic
  abiCanonicalArrays vyperABI

(* ===== Scalar ===== *)

(* Valid static scalar encodings agree with their canonical readable prefix. *)

Definition abi_static_prefix_def:
  abi_static_prefix at <=>
    !bs. valid_enc at bs /\ static_length at <= LENGTH bs ==>
      enc at (dec at bs) = TAKE (static_length at) bs
End

Theorem abi_static_prefix_numbers:
  (!n. abi_static_prefix (Uint n)) /\ (!n. abi_static_prefix (Int n)) /\
  abi_static_prefix Address /\ abi_static_prefix Bool /\
  (!n m. abi_static_prefix (Fixed n m)) /\ (!n m. abi_static_prefix (Ufixed n m))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[abi_static_prefix_def] >> rpt strip_tac >>
  irule word_bytes_roundtrip_proof >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
  simp[LENGTH_TAKE_EQ, dividesTheory.divides_def]
QED

Theorem abi_zero_bytes_replicate:
  !bs:word8 list. EVERY ((=) 0w) bs ==> bs = REPLICATE (LENGTH bs) 0w
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem abi_valid_fixed_bytes_prefix:
  valid_enc (Bytes (SOME n)) bs /\ 32 <= LENGTH bs ==>
  enc (Bytes (SOME n)) (dec (Bytes (SOME n)) bs) = TAKE 32 bs
Proof
  simp_tac bool_ss [valid_enc_def, valid_bytes_bound_def] >> strip_tac >>
  drule abi_zero_bytes_replicate >>
  simp[LENGTH_DROP, LENGTH_TAKE_EQ] >> strip_tac >>
  `TAKE n bs ++ DROP n (TAKE 32 bs) = TAKE 32 bs` by
    (qspecl_then [`n`, `TAKE 32 bs`] mp_tac TAKE_DROP >>
     asm_simp_tac bool_ss [TAKE_TAKE, MIN_DEF]) >>
  gvs[Once enc_def, Once dec_def, TAKE_TAKE_MIN, MIN_DEF]
QED

Theorem abi_static_prefix_fixed_bytes:
  !n. abi_static_prefix (Bytes (SOME n))
Proof
  simp[abi_static_prefix_def, abi_valid_fixed_bytes_prefix]
QED

(* ===== Members ===== *)

(* Static member-list decoding reconstructs the canonical readable head prefix. *)

Theorem abi_valid_static_members:
  !ts. EVERY (\at. ~is_dynamic at /\ abi_static_prefix at) ts ==>
  !base hds acc. valid_enc_tuple ts base hds ==>
  ?vs. dec_tuple ts base hds acc = ListV (REVERSE acc ++ vs) /\
    LENGTH vs = LENGTH ts /\ has_types ts vs /\
    FLAT (MAP2 enc ts vs) = TAKE (static_length (Tuple ts)) hds /\
    static_length (Tuple ts) <= LENGTH hds
Proof
  Induct
  >- simp[dec_def, valid_enc_def] >>
  qx_gen_tac `at` >> simp_tac bool_ss [EVERY_DEF] >> strip_tac >>
  MAP_EVERY qx_gen_tac [`input`, `hds`, `acc`] >> strip_tac >>
  qpat_x_assum `valid_enc_tuple _ _ _` mp_tac >>
  asm_simp_tac bool_ss [Once valid_enc_def, LET_THM] >> strip_tac >>
  `has_type at (dec at (TAKE (static_length at) hds))` by
    (irule (cj 1 dec_has_type) >> first_assum ACCEPT_TAC) >>
  `enc at (dec at (TAKE (static_length at) hds)) = TAKE (static_length at) hds` by
    (qpat_x_assum `abi_static_prefix at` mp_tac >>
     simp_tac bool_ss [abi_static_prefix_def] >>
     disch_then (qspec_then `TAKE (static_length at) hds` mp_tac) >>
     asm_simp_tac (srw_ss()) [LENGTH_TAKE_EQ, TAKE_TAKE, MIN_DEF]) >>
  qpat_x_assum `EVERY _ ts ==> _` drule >>
  disch_then (qspecl_then [`input`, `DROP (static_length at) hds`,
    `dec at (TAKE (static_length at) hds)::acc`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qexists_tac `dec at (TAKE (static_length at) hds)::vs` >>
  asm_simp_tac (srw_ss()) [Once dec_def, has_type_def, TAKE_SUM, APPEND_ASSOC] >>
  fs[LENGTH_DROP] >> decide_tac
QED

(* ===== Aggregate ===== *)

(* Static ABI arrays and tuples reconstruct canonical prefixes recursively. *)

Theorem abi_static_array_decode_tuple:
  !n at base hds acc. ~is_dynamic at ==>
  dec_array n (SOME (static_length at)) at base hds acc =
    dec_tuple (REPLICATE n at) base hds acc
Proof
  Induct >> simp[dec_def]
QED

Theorem abi_static_prefix_tuple:
  EVERY (\at. ~is_dynamic at /\ abi_static_prefix at) ts ==>
  abi_static_prefix (Tuple ts)
Proof
  strip_tac >> simp_tac bool_ss [abi_static_prefix_def] >> rpt strip_tac >>
  `~any_dynamic ts` by
    (fs[EVERY_MEM, any_dynamic_EXISTS, EXISTS_MEM] >> metis_tac[]) >>
  `valid_enc_tuple ts bs bs` by fs[Once valid_enc_def] >>
  drule_all abi_valid_static_members >> disch_then (qspec_then `[]` strip_assume_tac) >>
  drule_all enc_tuple_static >> strip_tac >>
  `dec (Tuple ts) bs = ListV vs` by asm_simp_tac (srw_ss()) [Once dec_def] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_static_prefix_array:
  ~is_dynamic at /\ abi_static_prefix at ==>
  abi_static_prefix (Array (SOME n) at)
Proof
  strip_tac >> simp_tac bool_ss [abi_static_prefix_def] >> rpt strip_tac >>
  `EVERY (\ty. ~is_dynamic ty /\ abi_static_prefix ty) (REPLICATE n at)` by simp[] >>
  `valid_enc_tuple (REPLICATE n at) bs bs` by
    fs[valid_enc_tuple_REPLICATE, Once valid_enc_def] >>
  drule_all abi_valid_static_members >> disch_then (qspec_then `[]` strip_assume_tac) >>
  `~any_dynamic (REPLICATE n at)` by simp[any_dynamic_EXISTS] >>
  drule_all enc_tuple_static >> strip_tac >>
  `dec (Array (SOME n) at) bs = ListV vs` by
    asm_simp_tac (srw_ss()) [Once dec_def, LET_THM, abi_static_array_decode_tuple] >>
  `enc (Array (SOME n) at) (ListV vs) = enc (Tuple (REPLICATE n at)) (ListV vs)` by
    (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [enc_def])) >>
     CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [enc_def])) >>
     asm_simp_tac bool_ss [LET_THM, LENGTH_REPLICATE]) >>
  asm_simp_tac bool_ss [static_length_def, static_length_Tuple_SUM, map_replicate,
    SUM_REPLICATE]
QED

Theorem abi_static_prefix_bytes_bound:
  !bound. ~is_dynamic (Bytes bound) ==> abi_static_prefix (Bytes bound)
Proof
  Cases >> simp[is_dynamic_def, abi_static_prefix_fixed_bytes]
QED

Theorem abi_static_prefix_array_bound:
  !bound at. (~is_dynamic at ==> abi_static_prefix at) ==>
    ~is_dynamic (Array bound at) ==> abi_static_prefix (Array bound at)
Proof
  Cases >> simp[is_dynamic_def, abi_static_prefix_array]
QED

Theorem abi_static_prefix_tuple_members:
  (!at. MEM at ts ==> ~is_dynamic at ==> abi_static_prefix at) ==>
  ~is_dynamic (Tuple ts) ==> abi_static_prefix (Tuple ts)
Proof
  rpt strip_tac >> irule abi_static_prefix_tuple >>
  fs[is_dynamic_def, any_dynamic_EXISTS, EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

Theorem abi_static_prefix_static_mutual:
  (!at. ~is_dynamic at ==> abi_static_prefix at) /\
  (!ts. EVERY (\at. ~is_dynamic at ==> abi_static_prefix at) ts)
Proof
  ho_match_mp_tac (legacyInduction.mutual_ind_from_ops abi_type_induction) >>
  simp[is_dynamic_def, abi_static_prefix_numbers, abi_static_prefix_bytes_bound,
    abi_static_prefix_array_bound, abi_static_prefix_tuple_members, EVERY_MEM]
QED

Theorem abi_static_prefix_static = CONJUNCT1 abi_static_prefix_static_mutual;

(* ===== Array ===== *)

(* Dynamic arrays of static ABI elements consume a canonical prefix; trailing
   input bytes need not be part of that canonical encoding. *)

Theorem abi_valid_static_array_values:
  !at cnt (raw_bytes:word8 list).
  ~is_dynamic at /\ valid_enc_array cnt (SOME (static_length at)) at raw_bytes raw_bytes ==>
  ?vs. dec_array cnt (SOME (static_length at)) at raw_bytes raw_bytes [] = ListV vs /\
    LENGTH vs = cnt /\
    enc (Tuple (REPLICATE cnt at)) (ListV vs) = TAKE (cnt * static_length at) raw_bytes /\
    cnt * static_length at <= LENGTH raw_bytes
Proof
  rpt gen_tac >> strip_tac >> drule abi_static_prefix_static >> strip_tac >>
  `EVERY (\ty. ~is_dynamic ty /\ abi_static_prefix ty) (REPLICATE cnt at)` by simp[] >>
  `valid_enc_tuple (REPLICATE cnt at) raw_bytes raw_bytes` by fs[valid_enc_tuple_REPLICATE] >>
  drule_all abi_valid_static_members >> disch_then (qspec_then `[]` strip_assume_tac) >>
  `~any_dynamic (REPLICATE cnt at)` by simp[any_dynamic_EXISTS] >>
  drule_all enc_tuple_static >> strip_tac >>
  qexists_tac `vs` >>
  gvs[abi_static_array_decode_tuple, LENGTH_REPLICATE, static_length_Tuple_SUM,
    map_replicate, SUM_REPLICATE, Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"]
QED

Theorem abi_valid_array_count_bytes:
  32 <= LENGTH bs ==>
  word_to_bytes (n2w (abi_head_word bs):256 word) T = TAKE 32 bs
Proof
  strip_tac >> simp[abi_head_word_def] >> irule word_bytes_roundtrip_proof >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
  simp[LENGTH_TAKE_EQ, dividesTheory.divides_def]
QED

Theorem abi_valid_static_array_prefix:
  ~is_dynamic at /\ valid_enc (Array NONE at) bs ==>
  LENGTH (enc (Array NONE at) (dec (Array NONE at) bs)) <= LENGTH bs /\
  TAKE (LENGTH (enc (Array NONE at) (dec (Array NONE at) bs))) bs =
    enc (Array NONE at) (dec (Array NONE at) bs)
Proof
  strip_tac >>
  `32 <= LENGTH bs /\
   valid_enc_array (abi_head_word bs) (SOME (static_length at)) at (DROP 32 bs) (DROP 32 bs)` by
    (fs[Once valid_enc_def, abi_head_word_def, LET_THM] >>
     gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"]) >>
  drule_all abi_valid_static_array_values >> strip_tac >>
  drule abi_valid_array_count_bytes >> strip_tac >>
  `dec (Array NONE at) bs = ListV vs` by
    asm_simp_tac bool_ss [Once dec_def, LET_THM, GSYM abi_head_word_def] >>
  `32 + abi_head_word bs * static_length at <= LENGTH bs` by (fs[LENGTH_DROP] >> decide_tac) >>
  `enc (Array NONE at) (dec (Array NONE at) bs) =
    TAKE (32 + abi_head_word bs * static_length at) bs` by
    asm_simp_tac bool_ss [canonical_array_tuple, enc_number_def, TAKE_SUM] >>
  asm_simp_tac (srw_ss()) [LENGTH_TAKE_EQ, TAKE_TAKE_MIN]
QED
