Theory abiDecodePtrRejectSource
Ancestors
  abiValidMembers supportedTypes vyperABI contractABI vyperABIValid vyperValue
  list rich_list arithmetic abiDecodeRanges abiDecoderMembers

Theorem abi_decode_first_conversion_failure:
  !tys raw hds.
    abi_to_vyper_list env tys
      (abi_decode_members (MAP (vyper_to_abi_type env) tys) raw hds) = NONE ==>
    ?pre ty post pvs.
      tys = pre ++ ty::post /\
      abi_to_vyper_list env pre
        (abi_decode_members (MAP (vyper_to_abi_type env) pre) raw hds) = SOME pvs /\
      abi_to_vyper env ty
        (dec (vyper_to_abi_type env ty)
          (abi_decode_member_bytes (vyper_to_abi_type env ty) raw
            (DROP (SUM (MAP abi_member_head_size
              (MAP (vyper_to_abi_type env) pre))) hds))) = NONE
Proof
  Induct >- simp[abi_decode_members_def] >>
  qx_gen_tac `ty` >> rpt gen_tac >>
  simp_tac bool_ss [MAP, abi_decode_members_def, Once abi_to_vyper_def] >>
  Cases_on `abi_to_vyper env ty
    (dec (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty) raw hds))`
  >- (strip_tac >> qexistsl_tac [`[]`, `ty`, `tys`, `[]`] >>
      simp[abi_decode_members_def]) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  gvs[AllCaseEqs(), Excl "dec_def"] >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`ty::pre`, `ty'`, `post`, `x::pvs`] >>
  asm_simp_tac bool_ss [MAP, SUM, APPEND, abi_decode_members_def,
    Once abi_to_vyper_def, DROP_DROP_T, ADD_COMM] >>
  full_simp_tac bool_ss [DROP_DROP_T, ADD_COMM] >>
  simp_tac (srw_ss()) []
QED

Theorem abi_decode_scalar_conversion_failure:
  supported_scalar_type ty /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty) raw /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty) raw) = NONE ==>
  ?n ws.
    (ty = BaseT (StringT n) \/ ty = BaseT (BytesT (Dynamic n))) /\
    dec (vyper_to_abi_type env ty) raw = contractABI$BytesV ws /\
    n < LENGTH ws
Proof
  strip_tac >> drule vyper_decode_dec_has_type >> strip_tac >>
  qmatch_asmsub_abbrev_tac `abi_to_vyper env ty av` >>
  qpat_x_assum `vyper_decode_valid_enc _ _` kall_tac >>
  Cases_on `ty` >>
  gvs[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def, Excl "dec_def"] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[supported_word_type_def, supported_string_type_def, Excl "dec_def"] >>
  Cases_on `av` >>
  gvs[check_IntV_def, compatible_bound_def,
      contractABITheory.has_type_def, AllCaseEqs(), Excl "dec_def"] >>
  TRY (Cases_on `b` >>
    gvs[supported_word_type_def, supported_string_type_def,
        compatible_bound_def, valid_length_def, Excl "dec_def"] >> NO_TAC) >>
  gvs[within_int_bound_def, int_bits_bound_def, supported_int_width_def,
      Excl "dec_def", AllCaseEqs()] >>
  intLib.COOPER_TAC
QED

Theorem abi_decode_first_static_invalid_member:
  !ats raw hds.
    EVERY (\at. ~is_dynamic at) ats /\
    SUM (MAP abi_member_head_size ats) <= LENGTH hds /\
    ~vyper_decode_valid_enc_tuple ats raw hds ==>
    ?pre at post.
      ats = pre ++ at::post /\
      vyper_decode_valid_enc_tuple pre raw hds /\
      ~vyper_decode_valid_enc at
        (abi_decode_member_bytes at raw
          (DROP (SUM (MAP abi_member_head_size pre)) hds))
Proof
  Induct >- simp[Once vyper_decode_valid_enc_def] >>
  qx_gen_tac `at` >> rpt gen_tac >> strip_tac >>
  `~is_dynamic at /\ EVERY (\at. ~is_dynamic at) ats` by fs[] >>
  `static_length at <= LENGTH hds /\
   SUM (MAP abi_member_head_size ats) <= LENGTH (DROP (abi_member_head_size at) hds)` by
    (fs[abi_member_head_size_def] >> decide_tac) >>
  Cases_on `vyper_decode_valid_enc at (abi_decode_member_bytes at raw hds)`
  >- ( `~vyper_decode_valid_enc_tuple ats raw (DROP (abi_member_head_size at) hds)` by
         (fs[Once vyper_decode_valid_enc_def, abi_decode_member_bytes_def,
             abi_member_head_size_def] >> gvs[]) >>
       first_x_assum drule_all >> strip_tac >>
       qexistsl_tac [`at::pre`, `at'`, `post`] >>
       asm_simp_tac bool_ss [APPEND, MAP, SUM, DROP_DROP_T, ADD_COMM] >>
       full_simp_tac bool_ss [DROP_DROP_T, ADD_COMM] >>
       simp[Once vyper_decode_valid_enc_def, abi_decode_member_bytes_def,
            abi_member_head_size_def, Excl "dec_def"] >>
       gvs[abi_decode_member_bytes_def, abi_member_head_size_def,
           Excl "vyper_decode_valid_enc_def", Excl "dec_def"]) >>
  qexistsl_tac [`[]`, `at`, `ats`] >>
  simp[Once vyper_decode_valid_enc_def, Excl "dec_def"]
QED

Theorem abi_decode_static_tuple_invalid:
  EVERY (\ty. ~is_dynamic (vyper_to_abi_type env ty)) tys /\
  LENGTH tys < dimword(:256) /\
  LENGTH bs <= vyper_abi_size_bound env (TupleT tys) /\
  ~vyper_valid_enc env (TupleT tys) bs ==>
  LENGTH bs < SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) \/
  ?pre at post.
    MAP (vyper_to_abi_type env) tys = pre ++ at::post /\
    vyper_decode_valid_enc_tuple pre bs bs /\
    ~vyper_decode_valid_enc at
      (abi_decode_member_bytes at bs (DROP (SUM (MAP abi_member_head_size pre)) bs))
Proof
  strip_tac >>
  `EVERY (\at. ~is_dynamic at) (MAP (vyper_to_abi_type env) tys)` by
    fs[EVERY_MAP] >>
  `SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) =
   static_length (Tuple (MAP (vyper_to_abi_type env) tys))` by
    (simp[static_length_Tuple_SUM] >> AP_TERM_TAC >> irule MAP_CONG >>
     fs[abi_member_head_size_def, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `LENGTH bs < SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys))`
  >- simp[] >>
  disj2_tac >> irule abi_decode_first_static_invalid_member >>
  simp[] >>
  gvs[vyper_valid_enc_def, vyper_strict_enc_def, vyper_to_abi_types_MAP,
      Once vyper_decode_valid_enc_def, Excl "vyper_decode_valid_enc_def"]
QED
