Theory extcallDecoderMemberSemantics
Ancestors
  abiValidMember abiValidMembers abiDecoderMembers
  abiDecoderCoherence abiDecoderTypedContract abiDecodeRanges abiCanonicalHeadSize
  abiDecoderValidContract vyperTypeABI vyperABI vyperABIValid contractABI
  list rich_list arithmetic

(* The same member boundary applies under the descended maps of a struct;
   ce is unchanged, and env and sf are independently quantified. *)
Theorem decoder_member_head_good:
  let at = vyper_to_abi_type env ty;
      pre = MAP (vyper_to_abi_type env) pretys;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      xs = DROP off bs in
  (!at bs. ~is_dynamic at /\ static_length at <= LENGTH bs ==>
    (vyper_decode_valid_enc at (TAKE (static_length at) bs) <=>
     vyper_decode_valid_enc at bs)) /\
  (!at bs. ~is_dynamic at /\ static_length at <= LENGTH bs /\
    vyper_decode_valid_enc at bs ==>
    dec at (TAKE (static_length at) bs) = dec at bs) /\
  LIST_REL (abi_decoder_coherent ce env sf)
    (pretys ++ ty::tys) (pretvs ++ tv::tvs) /\
  LENGTH pretys = LENGTH pretvs /\ LENGTH pretys = LENGTH prevs /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) bs bs /\
  abi_to_vyper_list env (pretys ++ ty::tys)
    (abi_decode_members (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) bs bs) =
    SOME (prevs ++ v::vs) /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc s) = bs /\
  B + sb + LENGTH bs < dimword (:256) /\ sb + LENGTH bs <= H ==>
  sb + off <= H /\ vyper_decode_valid_enc at xs /\
  (is_dynamic at \/ static_length at <= LENGTH xs) /\
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (dec at xs) v
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_valid_members_metadata >>
  simp_tac (srw_ss()) [MAP_APPEND, abi_decode_members_append,
    abi_decode_members_def, abi_decoder_members_append, abi_decoder_members_def] >>
  strip_tac >>
  qpat_x_assum `abi_decoder_members _ _ _ _ _ _ _` mp_tac >>
  simp[abi_decoder_members_append, abi_decode_members_length,
       abi_decoder_members_def] >> strip_tac >>
  `vyper_decode_valid_enc_tuple
     (MAP (vyper_to_abi_type env) pretys ++ vyper_to_abi_type env ty ::
       MAP (vyper_to_abi_type env) tys) bs bs` by gvs[MAP_APPEND] >>
  drule_all (SIMP_RULE (srw_ss()) [LET_THM, ADD_ASSOC] abi_valid_member_window) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule (SIMP_RULE bool_ss [LET_THM] abi_valid_member_head) >> strip_tac >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (gvs[abi_decode_member_bytes_def, abi_decode_member_offset_def] >> decide_tac) >>
  `static_length (vyper_to_abi_type env ty) <=
    LENGTH (DROP (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) bs)` by
    (gvs[abi_member_head_size_def, LENGTH_DROP] >> decide_tac) >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (DROP (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) bs)` by
    metis_tac[abi_decode_member_bytes_def] >>
  gvs[abi_decode_member_bytes_def, abi_decode_member_offset_def] >> decide_tac
QED

(* A completed, discovered list: no validity of an undecoded suffix is assumed. *)
Theorem decoder_members_completed_prefix:
  (!at bs. ~is_dynamic at /\ static_length at <= LENGTH bs ==>
    (vyper_decode_valid_enc at (TAKE (static_length at) bs) <=>
     vyper_decode_valid_enc at bs)) /\
  (!at bs. ~is_dynamic at /\ static_length at <= LENGTH bs /\
    vyper_decode_valid_enc at bs ==>
    dec at (TAKE (static_length at) bs) = dec at bs) ==>
  !tys vs hds.
  LENGTH tys = LENGTH vs /\
  SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <= LENGTH hds /\
  (!j. j < LENGTH tys ==>
    let at = vyper_to_abi_type env (EL j tys);
        tail = DROP (SUM (MAP abi_member_head_size
          (MAP (vyper_to_abi_type env) (TAKE j tys)))) hds;
        xs = if is_dynamic at then DROP (abi_head_word tail) raw else tail in
    vyper_decode_valid_enc at xs /\
    abi_to_vyper env (EL j tys) (dec at xs) = SOME (EL j vs)) ==>
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) raw hds /\
  abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) raw hds) = SOME vs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Induct >- simp[vyper_decode_valid_enc_def, abi_decode_members_def] >>
  rpt gen_tac >> Cases_on `vs` >> simp_tac (srw_ss()) [] >> strip_tac >>
  first_assum (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  `SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <=
    LENGTH (DROP (abi_member_head_size (vyper_to_abi_type env h)) hds)` by
    (gvs[LENGTH_DROP] >> decide_tac) >>
  `!j. j < LENGTH tys ==>
    let at = vyper_to_abi_type env (EL j tys);
        tail = DROP (SUM (MAP abi_member_head_size
          (MAP (vyper_to_abi_type env) (TAKE j tys))))
          (DROP (abi_member_head_size (vyper_to_abi_type env h)) hds);
        xs = if is_dynamic at then DROP (abi_head_word tail) raw else tail in
    vyper_decode_valid_enc at xs /\
    abi_to_vyper env (EL j tys) (dec at xs) = SOME (EL j t)` by
    (rpt strip_tac >> first_x_assum (qspec_then `SUC j` mp_tac) >>
     simp_tac (srw_ss()) [DROP_DROP_T, ADD_COMM, LET_THM] >>
     disch_then irule >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  `abi_member_head_size (vyper_to_abi_type env h) <= LENGTH hds` by
    (gvs[] >> decide_tac) >>
  Cases_on `is_dynamic (vyper_to_abi_type env h)`
  >- gvs[Once vyper_decode_valid_enc_def, abi_decode_members_def,
         abi_decode_member_bytes_def, abi_member_head_size_def, abi_head_word_def, LET_THM] >>
  gvs[abi_decode_member_bytes_def, abi_member_head_size_def] >>
  `static_length (vyper_to_abi_type env h) <= LENGTH hds` by decide_tac >>
  `vyper_decode_valid_enc (vyper_to_abi_type env h)
    (TAKE (static_length (vyper_to_abi_type env h)) hds)` by metis_tac[] >>
  `dec (vyper_to_abi_type env h) (TAKE (static_length (vyper_to_abi_type env h)) hds) =
    dec (vyper_to_abi_type env h) hds` by metis_tac[] >>
  gvs[Once vyper_decode_valid_enc_def, abi_decode_members_def,
      abi_decode_member_bytes_def, abi_member_head_size_def, abi_head_word_def, LET_THM]
QED

Theorem members_tuple_head_window[local]:
  !ats. is_dynamic (Tuple ats) \/
    static_length (Tuple ats) <= SUM (MAP abi_member_head_size ats)
Proof
  Induct >> simp[is_dynamic_def, static_length_def,
    abi_member_head_size_def] >> rpt strip_tac >>
  Cases_on `is_dynamic h` >> gvs[]
QED

Theorem decoder_tuple_completion:
  abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs) /\
  LENGTH tys < dimword (:256) /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) = SOME vs ==>
  vyper_decode_valid_enc (vyper_to_abi_type env (TupleT tys)) bs /\
  (is_dynamic (vyper_to_abi_type env (TupleT tys)) \/
    static_length (vyper_to_abi_type env (TupleT tys)) <= LENGTH bs) /\
  abi_to_vyper env (TupleT tys) (dec (vyper_to_abi_type env (TupleT tys)) bs) =
    SOME (ArrayV (TupleV vs)) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs))
Proof
  strip_tac >>
  `vyper_decode_valid_enc (vyper_to_abi_type env (TupleT tys)) bs` by
    simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
         Once vyper_decode_valid_enc_def] >>
  drule abi_valid_members_view >> strip_tac >>
  qspec_then `MAP (vyper_to_abi_type env) tys` strip_assume_tac members_tuple_head_window >>
  `is_dynamic (vyper_to_abi_type env (TupleT tys)) \/
    static_length (vyper_to_abi_type env (TupleT tys)) <= LENGTH bs` by
    (gvs[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP] >> decide_tac) >>
  `dec (vyper_to_abi_type env (TupleT tys)) bs =
    ListV (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs)` by
    simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
         Once dec_def, abi_decode_members_value] >>
  `abi_to_vyper env (TupleT tys) (dec (vyper_to_abi_type env (TupleT tys)) bs) =
    SOME (ArrayV (TupleV vs))` by simp[Once abi_to_vyper_def] >>
  drule abi_decoder_coherent_header >> strip_tac >>
  simp[] >> irule (cj 1 abi_to_vyper_well_typed) >>
  qexistsl_tac [`dec (vyper_to_abi_type env (TupleT tys)) bs`, `env`, `TupleT tys`] >>
  fs[abi_decoder_header_def]
QED

Theorem decoder_struct_completion:
  abi_decoder_coherent ce env sf (StructT nsid) tv /\
  FLOOKUP env nsid = SOME (StructArgs args) /\ LENGTH args < dimword (:256) /\
  vyper_decode_valid_enc_tuple
    (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) bs bs /\
  abi_to_vyper_list (env \\ nsid) (MAP SND args)
    (abi_decode_members (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) bs bs) = SOME vs ==>
  vyper_decode_valid_enc (vyper_to_abi_type env (StructT nsid)) bs /\
  (is_dynamic (vyper_to_abi_type env (StructT nsid)) \/
    static_length (vyper_to_abi_type env (StructT nsid)) <= LENGTH bs) /\
  abi_to_vyper env (StructT nsid) (dec (vyper_to_abi_type env (StructT nsid)) bs) =
    SOME (StructV (ZIP (MAP FST args,vs))) /\
  value_has_type tv (StructV (ZIP (MAP FST args,vs)))
Proof
  strip_tac >>
  `vyper_decode_valid_enc (vyper_to_abi_type env (StructT nsid)) bs` by
    simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
         Once vyper_decode_valid_enc_def] >>
  drule abi_valid_members_view >> strip_tac >>
  qspec_then `MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)`
    strip_assume_tac members_tuple_head_window >>
  `is_dynamic (vyper_to_abi_type env (StructT nsid)) \/
    static_length (vyper_to_abi_type env (StructT nsid)) <= LENGTH bs` by
    (gvs[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP] >> decide_tac) >>
  `dec (vyper_to_abi_type env (StructT nsid)) bs =
    ListV (abi_decode_members
      (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) bs bs)` by
    simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
         Once dec_def, abi_decode_members_value] >>
  `abi_to_vyper env (StructT nsid) (dec (vyper_to_abi_type env (StructT nsid)) bs) =
    SOME (StructV (ZIP (MAP FST args,vs)))` by simp[Once abi_to_vyper_def] >>
  drule abi_decoder_coherent_header >> strip_tac >>
  simp[] >> irule (cj 1 abi_to_vyper_well_typed) >>
  qexistsl_tac [`dec (vyper_to_abi_type env (StructT nsid)) bs`, `env`, `StructT nsid`] >>
  fs[abi_decoder_header_def] >>
  simp[vyper_to_abi_types_MAP, abi_decode_members_value, Once abi_to_vyper_def]
QED
