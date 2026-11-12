Theory extcallDecoderArraySemantics
Ancestors
  abiDecoderValidArraySetupInputs abiDecoderValidContract abiValidMembers
  abiValidMember abiDecoderTypedContract abiCanonicalHeadSize abiDecodeRanges
  abiDecoderArraySlice vyperTypeABI vyperABI contractABI list rich_list arithmetic
  vyperABIValid abiValidAggregateHeads abiDecoderCoherence abiDecoderContract vyperValue

Theorem array_member_full_suffix[local]:
  (!at bs. ~is_dynamic at /\ static_length at <= LENGTH bs ==>
    (vyper_decode_valid_enc at (TAKE (static_length at) bs) <=>
     vyper_decode_valid_enc at bs)) /\
  (!at bs. ~is_dynamic at /\ static_length at <= LENGTH bs /\
    vyper_decode_valid_enc at bs ==>
    dec at (TAKE (static_length at) bs) = dec at bs) /\
  vyper_decode_valid_enc at (abi_decode_member_bytes at bs (DROP ao bs)) /\
  abi_member_head_size at <= LENGTH (abi_decode_member_bytes at bs (DROP ao bs)) ==>
  vyper_decode_valid_enc at (DROP (abi_decode_member_offset at bs ao) bs) /\
  (is_dynamic at \/ static_length at <= LENGTH (DROP (abi_decode_member_offset at bs ao) bs)) /\
  dec at (abi_decode_member_bytes at bs (DROP ao bs)) =
    dec at (DROP (abi_decode_member_offset at bs ao) bs)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_dynamic at`
  >- gvs[abi_decode_member_bytes_def, abi_decode_member_offset_def] >>
  gvs[abi_decode_member_bytes_def, abi_decode_member_offset_def,
      abi_member_head_size_def, LENGTH_TAKE] >>
  `static_length at <= LENGTH (DROP ao bs)` by (gvs[LENGTH_TAKE_EQ, LENGTH_DROP] >> decide_tac) >>
  `vyper_decode_valid_enc at (DROP ao bs)` by metis_tac[] >>
  gvs[]
QED

Theorem decoder_array_indexed_good:
  let at = vyper_to_abi_type env ty;
      ao = j * abi_member_head_size at;
      off = 32 + abi_decode_member_offset at (DROP 32 bs) ao;
      xs = DROP off bs in
  (!at bs. ~is_dynamic at /\ static_length at <= LENGTH bs ==>
    (vyper_decode_valid_enc at (TAKE (static_length at) bs) <=>
     vyper_decode_valid_enc at bs)) /\
  (!at bs. ~is_dynamic at /\ static_length at <= LENGTH bs /\
    vyper_decode_valid_enc at bs ==>
    dec at (TAKE (static_length at) bs) = dec at bs) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE at) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE at) bs /\ j < LENGTH vs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc s) = bs /\
  B + sb + LENGTH bs < dimword (:256) /\ sb + LENGTH bs <= H ==>
  sb + off <= H /\ vyper_decode_valid_enc at xs /\
  (is_dynamic at \/ static_length at <= LENGTH xs) /\
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (dec at xs) (EL j vs)
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_dynarray_values >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_array_metadata_child >> strip_tac >>
  `j < abi_head_word bs` by metis_tac[] >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_valid_array_child_window) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all array_member_full_suffix >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EL j (abi_decode_members (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty))
      (DROP 32 bs) (DROP 32 bs)) =
    dec (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP 32 bs)
        (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) (DROP 32 bs)))`
    by (irule abi_decode_array_member_EL >> simp[]) >>
  gvs[DROP_DROP_T] >> decide_tac
QED

Theorem array_discovered_values[local]:
  !vs hds.
  LENGTH vs * abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH hds /\
  (!j. j < LENGTH vs ==>
    vyper_decode_valid_enc (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty) raw
        (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) hds)) /\
    abi_to_vyper env ty (dec (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty) raw
        (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) hds))) = SOME (EL j vs)) ==>
  vyper_decode_valid_enc_tuple (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty)) raw hds /\
  abi_to_vyper_list env (REPLICATE (LENGTH vs) ty)
    (abi_decode_members (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty)) raw hds) = SOME vs
Proof
  Induct >- simp[vyper_decode_valid_enc_def, abi_decode_members_def] >>
  rpt gen_tac >> strip_tac >>
  first_assum (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >> strip_tac >>
  `LENGTH vs * abi_member_head_size (vyper_to_abi_type env ty) <=
     LENGTH (DROP (abi_member_head_size (vyper_to_abi_type env ty)) hds)` by
    (gvs[LENGTH_DROP, MULT_CLAUSES] >> decide_tac) >>
  `!j. j < LENGTH vs ==>
    vyper_decode_valid_enc (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty) raw
        (DROP (j * abi_member_head_size (vyper_to_abi_type env ty))
          (DROP (abi_member_head_size (vyper_to_abi_type env ty)) hds))) /\
    abi_to_vyper env ty (dec (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty) raw
        (DROP (j * abi_member_head_size (vyper_to_abi_type env ty))
          (DROP (abi_member_head_size (vyper_to_abi_type env ty)) hds)))) = SOME (EL j vs)` by
    (rpt strip_tac >> first_x_assum (qspec_then `SUC j` mp_tac) >>
     simp[DROP_DROP_T, MULT_CLAUSES, ADD_COMM]) >>
  first_x_assum drule_all >> strip_tac >>
  `abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH hds` by
    (gvs[MULT_CLAUSES] >> decide_tac) >>
  simp_tac (srw_ss()) [abi_decode_members_def] >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
  gvs[Once vyper_decode_valid_enc_def, abi_member_head_size_def,
      abi_decode_member_bytes_def, abi_head_word_def, LET_THM]
QED

Theorem decoder_array_completed_prefix:
  let at = vyper_to_abi_type env ty;
      payload = DROP 32 bs in
  (!at bs. ~is_dynamic at /\ static_length at <= LENGTH bs ==>
    (vyper_decode_valid_enc at (TAKE (static_length at) bs) <=>
     vyper_decode_valid_enc at bs)) /\
  (!at bs. ~is_dynamic at /\ static_length at <= LENGTH bs /\
    vyper_decode_valid_enc at bs ==>
    dec at (TAKE (static_length at) bs) = dec at bs) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  32 <= LENGTH bs /\ abi_head_word bs = LENGTH vs /\ LENGTH vs <= maxn /\
  LENGTH vs < dimword (:256) /\ LENGTH vs * abi_member_head_size at <= LENGTH payload /\
  (!j. j < LENGTH vs ==>
    let off = abi_decode_member_offset at payload (j * abi_member_head_size at);
        xs = DROP (32 + off) bs in
    vyper_decode_valid_enc at xs /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (dec at xs) (EL j vs)) ==>
  vyper_decode_valid_enc (Array NONE at) bs /\
  (is_dynamic (Array NONE at) \/ static_length (Array NONE at) <= LENGTH bs) /\
  abi_to_vyper env (ArrayT ty (Dynamic maxn)) (dec (Array NONE at) bs) =
    SOME (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs))
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!j. j < LENGTH vs ==>
    vyper_decode_valid_enc (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP 32 bs)
        (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) (DROP 32 bs))) /\
    abi_to_vyper env ty (dec (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP 32 bs)
        (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) (DROP 32 bs)))) = SOME (EL j vs)` by
    (rpt strip_tac >> first_assum drule >> simp_tac bool_ss [LET_THM] >> strip_tac >>
     `j * abi_member_head_size (vyper_to_abi_type env ty) +
       abi_member_head_size (vyper_to_abi_type env ty) <=
       LENGTH vs * abi_member_head_size (vyper_to_abi_type env ty)` by
       (irule abi_decoder_array_cell_capacity >> simp[]) >>
     Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     gvs[abi_decode_member_bytes_def, abi_decode_member_offset_def, DROP_DROP_T,
         abi_decoder_metadata_def, abi_member_head_size_def] >>
     `static_length (vyper_to_abi_type env ty) <=
       LENGTH (DROP (j * static_length (vyper_to_abi_type env ty)) (DROP 32 bs))` by
       (simp[LENGTH_DROP] >> decide_tac) >>
     metis_tac[]) >>
  drule_all array_discovered_values >> strip_tac >>
  `vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs` by
    (asm_simp_tac bool_ss [Once vyper_decode_valid_enc_def, LET_THM,
       GSYM abi_head_word_def, GSYM vyper_decode_valid_enc_tuple_REPLICATE] >>
     simp[dec_number_def]) >>
  drule abi_valid_dynamic_array_view >> strip_tac >>
  drule abi_decoder_coherent_header >> strip_tac >>
  gvs[abi_decoder_header_def] >>
  `evaluate_type env ty = SOME tv` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  `abi_to_vyper env (ArrayT ty (Dynamic maxn))
     (dec (Array NONE (vyper_to_abi_type env ty)) bs) = SOME (ArrayV (DynArrayV vs))` by
    simp[Once abi_to_vyper_def, compatible_bound_def, make_array_value_def] >>
  simp[is_dynamic_def, compatible_bound_def, make_array_value_def] >>
  irule (cj 1 abi_to_vyper_well_typed) >> metis_tac[]
QED
