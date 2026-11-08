(* Source-window projections for allocation-backed successful decoding. *)
Theory abiValidAllocatedSource
Ancestors
  abiMalformedBoundedParents abiValidMembers abiDecoderCoherence
  vyperABI contractABI list rich_list arithmetic abiDecodeRanges
  abiDecoderOffset abiDecoderOffsetHead abiDecoderDynamic abiValidAggregateHeads
  abiMalformedConstructorContract abiEncoder compileEnv

Theorem abi_valid_static_array_trim[local]:
  !n at origin other hds k acc.
    ~is_dynamic at /\ n * static_length at <= k ==>
    (vyper_decode_valid_enc_array n (SOME (static_length at)) at origin (TAKE k hds) <=>
     vyper_decode_valid_enc_array n (SOME (static_length at)) at other hds) /\
    dec_array n (SOME (static_length at)) at origin (TAKE k hds) acc =
    dec_array n (SOME (static_length at)) at other hds acc
Proof
  Induct >- simp[vyper_decode_valid_enc_def] >>
  rpt gen_tac >> simp_tac bool_ss [MULT_CLAUSES] >> strip_tac >>
  `static_length at <= k` by decide_tac >>
  first_x_assum (qspecl_then [`at`, `origin`, `other`,
    `DROP (static_length at) hds`, `k - static_length at`,
    `dec at (TAKE (static_length at) hds)::acc`] mp_tac) >>
  simp[] >> strip_tac >>
  `MIN (static_length at) k = static_length at` by simp[MIN_DEF] >>
  simp[vyper_decode_valid_enc_def, dec_def,
    TAKE_TAKE_MIN, DROP_TAKE, LENGTH_TAKE_EQ] >>
  Cases_on `k <= LENGTH hds` >> simp[MIN_DEF] >> decide_tac
QED

(* The unconditional dec equality proposed for static windows needs a
   validity or byte-width premise: the ABI datatype itself permits bytes33. *)
Theorem abi_valid_static_window_width_probe[local]:
  ~is_dynamic (Bytes (SOME 33)) /\
  static_length (Bytes (SOME 33)) <= LENGTH (REPLICATE 33 (0w:word8)) /\
  dec (Bytes (SOME 33))
    (TAKE (static_length (Bytes (SOME 33))) (REPLICATE 33 (0w:word8))) <>
  dec (Bytes (SOME 33)) (REPLICATE 33 (0w:word8))
Proof
  EVAL_TAC
QED

Theorem abi_valid_static_window:
  ~is_dynamic at /\ static_length at <= k ==>
  (vyper_decode_valid_enc at (TAKE k bs) <=> vyper_decode_valid_enc at bs)
Proof
  Cases_on `at` >> simp[] >>
  simp[vyper_decode_valid_enc_def, TAKE_TAKE_MIN, LENGTH_TAKE_EQ] >>
  rpt strip_tac
  >~ [`vyper_decode_valid_enc_tuple ats _ _`] >-
     (qspec_then `ats` mp_tac abi_malformed_static_members_trim >>
      disch_then (qspecl_then [`TAKE k bs`, `bs`, `bs`, `k`] mp_tac) >>
      simp[GSYM static_length_Tuple_SUM])
  >~ [`vyper_decode_valid_enc (Array bound elem) _`] >-
     (Cases_on `bound` >> gvs[] >>
      qspec_then `x` mp_tac abi_valid_static_array_trim >>
      disch_then (qspecl_then [`elem`, `TAKE k bs`, `bs`, `bs`, `k`, `[]`] mp_tac) >>
      simp[vyper_decode_valid_enc_def])
  >~ [`vyper_decode_valid_enc (Bytes bound) _`] >-
     (Cases_on `bound` >> gvs[] >>
      simp[vyper_decode_valid_enc_def, valid_bytes_bound_def,
        TAKE_TAKE_MIN, MIN_EQ_LE, LENGTH_TAKE_EQ] >>
      Cases_on `k <= LENGTH bs` >> simp[] >>
      eq_tac >> strip_tac >> simp[])
  >> simp[MIN_EQ_LE] >> Cases_on `k <= LENGTH bs` >> simp[]
QED

Theorem abi_valid_static_decode_window:
  ~is_dynamic at /\ static_length at <= k /\
  vyper_decode_valid_enc at (TAKE k bs) ==>
  dec at (TAKE k bs) = dec at bs
Proof
  Cases_on `at` >> simp[] >> rpt strip_tac
  >~ [`dec_tuple ats _ _ [] = _`] >-
     (qspec_then `ats` mp_tac abi_malformed_static_members_trim >>
      disch_then (qspecl_then [`TAKE k bs`, `bs`, `bs`, `k`] mp_tac) >>
      simp[GSYM static_length_Tuple_SUM, abi_decode_members_value])
  >~ [`dec (Array bound elem) _ = _`] >-
     (Cases_on `bound` >> gvs[] >>
      qspec_then `x` mp_tac abi_valid_static_array_trim >>
      disch_then (qspecl_then [`elem`, `TAKE k bs`, `bs`, `bs`, `k`, `[]`] mp_tac) >>
      simp[Once dec_def])
  >> simp[TAKE_TAKE_MIN, MIN_EQ_LE] >>
  Cases_on `o'` >> gvs[] >>
  gvs[vyper_decode_valid_enc_def, valid_bytes_bound_def] >>
  simp[TAKE_TAKE_MIN, MIN_EQ_LE]
QED

Theorem abi_valid_source_cons_values:
  abi_to_vyper_list env (ty::tys)
    (abi_decode_members (MAP (vyper_to_abi_type env) (ty::tys)) raw_bytes hds) = SOME vs ==>
  ?v rest. vs = v::rest /\
    abi_to_vyper env ty
      (dec (vyper_to_abi_type env ty)
        (abi_decode_member_bytes (vyper_to_abi_type env ty) raw_bytes hds)) = SOME v /\
    abi_to_vyper_list env tys
      (abi_decode_members (MAP (vyper_to_abi_type env) tys) raw_bytes
        (DROP (abi_member_head_size (vyper_to_abi_type env ty)) hds)) = SOME rest
Proof
  simp_tac bool_ss [MAP, abi_decode_members_def, Once abi_to_vyper_def] >>
  simp[AllCaseEqs()] >> metis_tac[]
QED

Theorem abi_valid_source_static_member:
  ~is_dynamic at /\ LENGTH xs = L /\
  p + ao + abi_member_head_size at <= L /\
  vyper_decode_valid_enc at (abi_decode_member_bytes at (DROP p xs) (DROP (p+ao) xs)) ==>
  p+ao <= L /\ p+ao+static_length at <= L /\
  vyper_decode_valid_enc at (DROP (p+ao) xs) /\
  dec at (abi_decode_member_bytes at (DROP p xs) (DROP (p+ao) xs)) =
    dec at (DROP (p+ao) xs)
Proof
  simp_tac bool_ss [abi_decode_member_bytes_def, abi_member_head_size_def] >>
  strip_tac >> simp[] >>
  `vyper_decode_valid_enc at (DROP (p+ao) xs)` by
    metis_tac[abi_valid_static_window, LESS_EQ_REFL] >>
  gvs[abi_valid_static_decode_window]
QED

Theorem abi_valid_source_member_position:
  abi_decoder_coherent ce env sf ty tv /\ LENGTH xs = L /\
  p + ao + abi_member_head_size (vyper_to_abi_type env ty) <= L /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP p xs) (DROP (p+ao) xs)) /\
  q = p + (if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
            then abi_head_word (DROP (p+ao) xs) else ao) ==>
  q <= L /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP q xs) /\
  (is_dynamic (vyper_to_abi_type env ty) \/
    q + static_length (vyper_to_abi_type env ty) <= L) /\
  dec (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP p xs) (DROP (p+ao) xs)) =
  dec (vyper_to_abi_type env ty) (DROP q xs)
Proof
  strip_tac >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (gvs[abi_decoder_empty_dynamic_translation, vyper_to_abi_type_def,
        dec_info_needs_offset_def] >>
      simp[abi_decode_member_bytes_def, vyper_decode_valid_enc_def] >>
      cheat) >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
     is_dynamic (vyper_to_abi_type env ty)` by
    metis_tac[abi_decoder_nonempty_offset] >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (drule_all abi_decoder_nonempty_readable_head >> strip_tac >>
      gvs[abi_decode_member_bytes_def, DROP_DROP_T] >>
      drule_all abi_valid_dynamic_head_min >>
      simp[LENGTH_DROP] >> decide_tac) >>
  drule_all abi_valid_source_static_member >> gvs[]
QED
