(* Arbitrary-byte source and layout boundaries for the static bulk branch. *)
Theory exprSimAbiDecodeArrayBulk
Ancestors
  valueEncodingDefs
  abiDecoderScalarOutcome abiDecoderLayout abiValidStatic abiDecoderMembers
  abiDecoderPrimitiveSource abiDecoderClamp exprLowering abiEncoder
  vyperABI contractABI valueEncoding valueEncodingProps vyperTypeSystem
  abiDecoderCoherence compileEnv vyperValue valueEncodingTyping
  vyperABIValid vyperTypeABI abiCanonicalHeadSize
  finite_map arithmetic rich_list list vyperArith integer_word words exprSimConvert

Theorem abi_decoder_unclamped_word_window:
  abi_decoder_coherent ce env sf ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord NoClamp /\
  32 <= LENGTH (bs:byte list) /\
  mem_word_at d mem = word_of_bytes T (0w:bytes32) (TAKE 32 bs) ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty) (TAKE 32 bs) /\
  ?v. abi_to_vyper env ty
        (dec (vyper_to_abi_type env ty) (TAKE 32 bs)) = SOME v /\
      val_in_memory tv v d mem
Proof
  strip_tac >>
  `LENGTH (TAKE 32 bs) = 32` by simp[LENGTH_TAKE_EQ] >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty) (TAKE 32 bs) /\
   ?v. abi_to_vyper env ty
     (dec (vyper_to_abi_type env ty) (TAKE 32 bs)) = SOME v` by
    (drule_all abi_decoder_primitive_source_acceptance >>
     simp[abi_decoder_clamp_valid_def]) >>
  simp[] >>
  irule abi_decoder_primitive_memory_intro >> metis_tac[]
QED

Theorem abi_decode_static_window_width:
  abi_decoder_coherent ce env sf ty tv /\
  ~is_abi_dynamic ce.ce_struct_fields ty ==>
  static_length (vyper_to_abi_type env ty) = type_memory_bytes ce ty
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> metis_tac[]
QED

Theorem abi_decode_coherent_memory_positive:
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty ==>
  0 < type_memory_bytes ce ty
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `0 < type_slot_size tv` by metis_tac[assignable_type_slot_size_pos] >>
  metis_tac[type_memory_size_pos]
QED

Theorem abi_decode_fixed_bulk_shape:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed n)) atv /\
  assignable_type env (ArrayT ty (Fixed n)) /\
  type_memory_bytes ce (ArrayT ty (Fixed n)) < dimword (:256) ==>
  n < dimword (:256) /\
  (0 < n ==> type_memory_bytes ce ty <=
      type_memory_bytes ce (ArrayT ty (Fixed n)))
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [abi_decoder_coherent_array_iff] >> strip_tac >> gvs[] >>
  `assignable_type env ty` by fs[assignable_type_def] >>
  `0 < type_memory_bytes ce ty` by
    (irule abi_decode_coherent_memory_positive >> metis_tac[]) >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  fs[abi_decoder_header_def, type_memory_size_def] >>
  `n <= n * type_memory_bytes ce ty` by simp[] >>
  conj_tac >- decide_tac >> strip_tac >>
  `type_memory_bytes ce ty <= n * type_memory_bytes ce ty` by simp[] >>
  decide_tac
QED

Theorem abi_decode_member_list_shape:
  !tys tvs. LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
    EVERY (assignable_type env) tys ==>
    LENGTH tys <= type_memory_size_list tvs /\
    (!ty. MEM ty tys ==> type_memory_bytes ce ty <= type_memory_size_list tvs)
Proof
  Induct >- (Cases >> simp[type_memory_size_def]) >>
  qx_gen_tac `ty` >> Cases_on `tvs` >>
  simp_tac (srw_ss()) [LIST_REL_def, EVERY_DEF] >> strip_tac >>
  `0 < type_memory_bytes ce ty` by
    (irule abi_decode_coherent_memory_positive >> metis_tac[]) >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `LENGTH tys <= type_memory_size_list t /\
   (!ty. MEM ty tys ==> type_memory_bytes ce ty <= type_memory_size_list t)`
    by metis_tac[] >>
  simp[type_memory_size_def] >> gen_tac >> strip_tac
  >- (asm_rewrite_tac[] >> decide_tac) >>
  qpat_x_assum `!ty. MEM ty tys ==> _` drule >> decide_tac
QED

Theorem abi_decode_tuple_bulk_shape:
  abi_decoder_coherent ce env sf (TupleT tys) atv /\
  assignable_type env (TupleT tys) /\
  type_memory_bytes ce (TupleT tys) < dimword (:256) ==>
  LENGTH tys < dimword (:256) /\
  (!ty. MEM ty tys ==> type_memory_bytes ce ty <= type_memory_bytes ce (TupleT tys))
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [abi_decoder_coherent_tuple_iff] >> strip_tac >> gvs[] >>
  `EVERY (assignable_type env) tys` by
    (qpat_x_assum `assignable_type env (TupleT tys)` mp_tac >>
     simp_tac bool_ss [Once assignable_type_def] >> metis_tac[]) >>
  drule_all abi_decode_member_list_shape >> strip_tac >>
  fs[abi_decoder_header_def, type_memory_size_def] >>
  metis_tac[]
QED

Theorem abi_decode_struct_bulk_shape:
  abi_decoder_coherent ce env sf (StructT nsid) atv /\
  assignable_type env (StructT nsid) /\
  FLOOKUP env nsid = SOME (StructArgs args) /\
  type_memory_bytes ce (StructT nsid) < dimword (:256) ==>
  LENGTH args < dimword (:256) /\
  (!ty. MEM ty (MAP SND args) ==>
     type_memory_bytes ce ty <= type_memory_bytes ce (StructT nsid))
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [abi_decoder_coherent_struct_iff] >> strip_tac >>
  qpat_x_assum `MAP _ fields = _` kall_tac >> gvs[] >>
  `EVERY (assignable_type (env \\ nsid)) (MAP SND args)` by
    (qpat_x_assum `assignable_type env (StructT nsid)` mp_tac >>
     asm_simp_tac (srw_ss()) [Once assignable_type_def, EVERY_MAP,
       combinTheory.o_DEF]) >>
  drule_all abi_decode_member_list_shape >> strip_tac >>
  `LENGTH (MAP FST args) = LENGTH tvs` by fs[LIST_REL_EL_EQN] >>
  fs[abi_decoder_header_def, type_memory_size_def, type_memory_size_fields_zip] >>
  metis_tac[]
QED

Theorem abi_decoder_unclamped_word_source:
  abi_decoder_coherent ce env sf ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord NoClamp /\
  32 <= LENGTH (bs:byte list) ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty) (TAKE 32 bs) /\
  ?v. abi_to_vyper env ty
        (dec (vyper_to_abi_type env ty) (TAKE 32 bs)) = SOME v
Proof
  strip_tac >>
  `LENGTH (TAKE 32 bs) = 32` by simp[LENGTH_TAKE_EQ] >>
  drule_all abi_decoder_primitive_source_acceptance >>
  simp[abi_decoder_clamp_valid_def]
QED

Theorem abi_decode_static_source_members:
  !tys. EVERY (\ty. ~is_dynamic (vyper_to_abi_type env ty) /\
    !bs:byte list. static_length (vyper_to_abi_type env ty) <= LENGTH bs ==>
      vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
      ?v. abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v) tys ==>
  !base hds acc. SUM (MAP (static_length o vyper_to_abi_type env) tys) <= LENGTH hds ==>
    vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) base hds /\
    ?avs vs. dec_tuple (MAP (vyper_to_abi_type env) tys) base hds acc =
        ListV (REVERSE acc ++ avs) /\
      LENGTH avs = LENGTH tys /\ abi_to_vyper_list env tys avs = SOME vs
Proof
  Induct >- simp[vyper_decode_valid_enc_def, dec_def] >>
  qx_gen_tac `ty` >> simp_tac bool_ss [EVERY_DEF] >> strip_tac >>
  map_every qx_gen_tac [`input`, `hds`, `acc`] >> strip_tac >>
  fs[MAP, SUM] >>
  `static_length (vyper_to_abi_type env ty) <= LENGTH hds` by decide_tac >>
  qpat_x_assum `!bs. _` (qspec_then `TAKE (static_length (vyper_to_abi_type env ty)) hds` mp_tac) >>
  simp[LENGTH_TAKE_EQ] >> strip_tac >>
  qpat_x_assum `!base hds acc. _` (qspecl_then [`input`, `DROP (static_length (vyper_to_abi_type env ty)) hds`,
    `dec (vyper_to_abi_type env ty) (TAKE (static_length (vyper_to_abi_type env ty)) hds)::acc`] mp_tac) >>
  impl_tac >- (simp[LENGTH_DROP] >> decide_tac) >> strip_tac >>
  simp[Once vyper_decode_valid_enc_def, Once dec_def]
QED

Theorem abi_decode_static_source_replicate:
  !n at input hds. vyper_decode_valid_enc_array n
    (if is_dynamic at then NONE else SOME (static_length at)) at input hds =
    vyper_decode_valid_enc_tuple (REPLICATE n at) input hds
Proof
  Induct >> simp[vyper_decode_valid_enc_def] >> gen_tac >>
  first_x_assum (qspec_then `at` assume_tac) >>
  Cases_on `is_dynamic at` >> gvs[vyper_decode_valid_enc_def]
QED

Theorem abi_decode_members_unclamped:
  !xs. ~dec_infos_need_clamp xs <=>
    EVERY (\x. ~dec_info_needs_clamp (FST x)) xs
Proof
  Induct >- simp[dec_info_needs_clamp_def] >>
  PairCases >> simp[dec_info_needs_clamp_def]
QED

Theorem abi_decoder_static_source_acceptance:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  !bs:byte list. assignable_type env ty /\ abi_decode_bytes_widths env ty /\
    ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
    ~is_abi_dynamic ce.ce_struct_fields ty /\
    type_memory_bytes ce ty < dimword (:256) /\
    type_memory_bytes ce ty <= LENGTH bs ==>
    vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
    ?v. abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v
Proof
  ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac
  >- suspend "base"
  >- suspend "flag"
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume abi_decoder_static_source_acceptance[base]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >> Cases_on `bt` >>
      gvs[type_to_abi_dec_info_def, type_to_abi_clamp_def,
        dec_info_needs_clamp_def, COND_RAND, COND_RATOR,
        needs_clamp_def, AllCaseEqs()] >>
      fs[type_memory_bytes_def] >>
      simp[vyper_decode_valid_enc_def, check_IntV_def,
        within_int_bound_ineq, dec_number_def, has_type_def,
        valid_int_bound_def]
      >- (mp_tac (Q.ISPEC `word_of_bytes T (0w:bytes32) (TAKE 32 bs)` w2n_lt) >>
          simp[dimword_def])
      >- (mp_tac (Q.ISPEC `word_of_bytes T (0w:bytes32) (TAKE 32 bs)` w2i_le) >>
          mp_tac (Q.ISPEC `word_of_bytes T (0w:bytes32) (TAKE 32 bs)` w2i_ge) >>
          simp[INT_MIN_def, INT_MAX_def, abi_decoder_signed_bound_source,
            within_int_bound_ineq] >> intLib.ARITH_TAC) >>
      Cases_on `b` >>
      gvs[type_to_abi_dec_info_def, type_to_abi_clamp_def,
        dec_info_needs_clamp_def, COND_RAND, COND_RATOR, needs_clamp_def] >>
      fs[type_memory_bytes_def] >>
      simp[vyper_decode_valid_enc_def, valid_bytes_bound_def,
        compatible_bound_def, LENGTH_TAKE_EQ, DROP_LENGTH_TOO_LONG]
QED

Resume abi_decoder_static_source_acceptance[flag]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      gvs[type_to_abi_dec_info_def, dec_info_needs_clamp_def,
        COND_RAND, COND_RATOR, needs_clamp_def] >>
      fs[type_memory_bytes_def] >>
      simp[vyper_decode_valid_enc_def, dec_number_def, has_type_def,
        valid_int_bound_def] >>
      mp_tac (Q.ISPEC `word_of_bytes T (0w:bytes32) (TAKE 32 bs)` w2n_lt) >>
      simp[dimword_def]
QED

Resume abi_decoder_static_source_acceptance[array]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      Cases_on `bound` >>
      gvs[is_abi_dynamic_def, type_to_abi_dec_info_def,
        dec_info_needs_clamp_def, abi_decode_bytes_widths_def] >>
      `abi_decoder_coherent ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))` by
        metis_tac[abi_decoder_coherent_rules] >>
      drule_all abi_decode_fixed_bulk_shape >> strip_tac >>
      drule abi_decoder_coherent_header >>
      simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
      `assignable_type env ty` by fs[assignable_type_def] >>
      fs[abi_decode_members_unclamped, EVERY_GENLIST, is_abi_dynamic_def] >>
      `EVERY (\ty. ~is_dynamic (vyper_to_abi_type env ty) /\
        !xs:byte list. static_length (vyper_to_abi_type env ty) <= LENGTH xs ==>
          vyper_decode_valid_enc (vyper_to_abi_type env ty) xs /\
          ?v. abi_to_vyper env ty (dec (vyper_to_abi_type env ty) xs) = SOME v)
        (REPLICATE n ty)` by
        (Cases_on `n = 0` >- simp[] >> simp[] >>
         gen_tac >> strip_tac >>
         `0 < n` by decide_tac >>
         `type_memory_bytes ce ty < dimword (:256)` by metis_tac[LESS_EQ_LESS_TRANS] >>
         `static_length (vyper_to_abi_type env ty) = type_memory_bytes ce ty` by
           (irule abi_decode_static_window_width >> metis_tac[]) >>
         first_x_assum irule >> simp[] >> metis_tac[]) >>
      drule abi_decode_static_source_members >>
      disch_then (qspecl_then [`bs`, `bs`, `[]`] mp_tac) >>
      simp[map_replicate, SUM_REPLICATE] >> strip_tac >>
      simp[Once vyper_decode_valid_enc_def, abi_decode_static_source_replicate,
        abi_static_array_decode_tuple, abi_to_vyper_def, compatible_bound_def] >>
      qpat_x_assum `abi_decoder_coherent ce env sf ty tv`
        (strip_assume_tac o MATCH_MP abi_decoder_coherent_header) >>
      qspecl_then [`n`, `vyper_to_abi_type env ty`, `bs`, `bs`] mp_tac abi_decode_static_source_replicate >>
      gvs[abi_decoder_header_def]
QED

Resume abi_decoder_static_source_acceptance[tuple]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      `LIST_REL (abi_decoder_coherent ce env sf) tys tvs` by
        (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
      `abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs)` by
        metis_tac[abi_decoder_coherent_rules] >>
      drule_all abi_decode_tuple_bulk_shape >> strip_tac >>
      fs[type_to_abi_dec_info_def, dec_info_needs_clamp_def,
        abi_decode_members_unclamped, EVERY_MAP, combinTheory.o_DEF,
        is_abi_dynamic_def, abi_decode_bytes_widths_def] >>
      `EVERY (assignable_type env) tys` by
        (qpat_x_assum `assignable_type env (TupleT tys)` mp_tac >>
         simp_tac bool_ss [Once assignable_type_def] >> metis_tac[]) >>
      `EVERY (\ty. ~is_dynamic (vyper_to_abi_type env ty) /\
        !xs:byte list. static_length (vyper_to_abi_type env ty) <= LENGTH xs ==>
          vyper_decode_valid_enc (vyper_to_abi_type env ty) xs /\
          ?v. abi_to_vyper env ty (dec (vyper_to_abi_type env ty) xs) = SOME v) tys` by
        (fs[EVERY_EL, LIST_REL_EL_EQN] >> gen_tac >> strip_tac >>
         qpat_x_assum `!n. n < LENGTH tvs ==> _` drule >> strip_tac >>
         `abi_decoder_header ce env (EL n tys) (EL n tvs)` by
           metis_tac[abi_decoder_coherent_header] >>
         `type_memory_bytes ce (EL n tys) < dimword (:256)` by
           metis_tac[MEM_EL, LESS_EQ_LESS_TRANS] >>
         fs[abi_decoder_header_def]) >>
      `SUM (MAP (static_length o vyper_to_abi_type env) tys) =
        type_memory_bytes ce (TupleT tys)` by
        (fs[abi_decoder_header_def, vyper_to_abi_types_MAP,
          is_abi_dynamic_def, is_dynamic_def, any_dynamic_EXISTS,
          EVERY_MEM, EXISTS_MEM, static_length_Tuple_SUM, MAP_MAP_o,
          combinTheory.o_DEF] >> metis_tac[]) >>
      drule abi_decode_static_source_members >>
      disch_then (qspecl_then [`bs`, `bs`, `[]`] mp_tac) >>
      simp[] >> strip_tac >>
      simp[vyper_to_abi_types_MAP, Once vyper_decode_valid_enc_def]
QED

Resume abi_decoder_static_source_acceptance[struct]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
     (MAP SND args) tvs` by (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `abi_decoder_coherent ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))` by
    (irule (cj 5 abi_decoder_coherent_rules) >> metis_tac[]) >>
  drule_all abi_decode_struct_bulk_shape >> strip_tac >>
  `EVERY (assignable_type (env \\ nsid)) (MAP SND args)` by
    (qpat_x_assum `assignable_type env (StructT nsid)` mp_tac >>
     asm_simp_tac (srw_ss()) [Once assignable_type_def, EVERY_MAP, combinTheory.o_DEF]) >>
  fs[Once type_to_abi_dec_info_def, dec_info_needs_clamp_def,
    abi_decode_members_unclamped, EVERY_MAP, combinTheory.o_DEF] >>
  gs[] >>
  qpat_x_assum `~dec_info_needs_clamp (DecComplex _ _)`
    (mp_tac o PURE_REWRITE_RULE [dec_info_needs_clamp_def,
      abi_decode_members_unclamped, EVERY_MAP]) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  `EVERY (\ty. ~dec_info_needs_clamp
      (type_to_abi_dec_info (sf \\ nsid_to_string nsid) ce ty)) (MAP SND args)` by
    (qpat_x_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
     fs[dec_info_needs_clamp_def, abi_decode_members_unclamped,
       EVERY_MAP, combinTheory.o_DEF, EVERY_MEM] >>
     rpt strip_tac >> pairarg_tac >> gvs[] >>
     qpat_x_assum `!x. MEM x fields ==> ~_`
       (qspec_then `(name,ty,sz)` mp_tac) >> simp[]) >>
  qpat_x_assum `MAP _ fields = args` kall_tac >>
  fs[abi_decode_bytes_widths_def] >>
  gs[combinTheory.o_DEF] >>
  `EVERY (\ty. ~is_dynamic (vyper_to_abi_type (env \\ nsid) ty)) (MAP SND args)` by
    (gs[abi_decoder_header_def, vyper_to_abi_types_MAP,
      is_dynamic_def, any_dynamic_EXISTS, EVERY_MEM, EXISTS_MEM,
      MEM_MAP] >> metis_tac[]) >>
  `EVERY (\ty. ~is_dynamic (vyper_to_abi_type (env \\ nsid) ty) /\
    !xs:byte list. static_length (vyper_to_abi_type (env \\ nsid) ty) <= LENGTH xs ==>
      vyper_decode_valid_enc (vyper_to_abi_type (env \\ nsid) ty) xs /\
      ?v. abi_to_vyper (env \\ nsid) ty (dec (vyper_to_abi_type (env \\ nsid) ty) xs) = SOME v)
    (MAP SND args)` by
    (fs[EVERY_MAP, combinTheory.o_DEF, EVERY_EL, LIST_REL_EL_EQN] >>
     gs[EL_MAP] >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!n. n < LENGTH tvs ==> _` drule >> strip_tac >>
     `abi_decoder_header ce (env \\ nsid) (SND (EL n args)) (EL n tvs)` by
       metis_tac[abi_decoder_coherent_header] >>
     `type_memory_bytes ce (SND (EL n args)) < dimword (:256)` by
       metis_tac[MEM_EL, MEM_MAP, LESS_EQ_LESS_TRANS] >>
     fs[abi_decoder_header_def]) >>
  `SUM (MAP (static_length o vyper_to_abi_type (env \\ nsid)) (MAP SND args)) =
    type_memory_bytes ce (StructT nsid)` by
    (gs[abi_decoder_header_def, vyper_to_abi_types_MAP,
      static_length_Tuple_SUM, MAP_MAP_o, combinTheory.o_DEF] >> metis_tac[]) >>
  drule abi_decode_static_source_members >>
  disch_then (qspecl_then [`bs`, `bs`, `[]`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[vyper_to_abi_types_MAP, Once vyper_decode_valid_enc_def,
    abi_to_vyper_def]
QED

Finalise abi_decoder_static_source_acceptance

Theorem abi_decoder_static_source_acceptance_take:
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty /\
  abi_decode_bytes_widths env ty /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  type_memory_bytes ce ty < dimword (:256) /\
  type_memory_bytes ce ty <= LENGTH (bs:byte list) ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty) (TAKE (type_memory_bytes ce ty) bs) /\
  ?v. abi_to_vyper env ty
    (dec (vyper_to_abi_type env ty) (TAKE (type_memory_bytes ce ty) bs)) = SOME v
Proof
  strip_tac >> drule abi_decoder_static_source_acceptance >>
  disch_then irule >> simp[LENGTH_TAKE_EQ]
QED

Theorem abi_decoder_static_memory_window:
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty /\
  abi_decode_bytes_widths env ty /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  type_memory_bytes ce ty < dimword (:256) /\
  type_memory_bytes ce ty <= LENGTH (bs:byte list) /\
  mem_bytes_at d (type_memory_bytes ce ty) mem = TAKE (type_memory_bytes ce ty) bs ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
  ?v. abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v /\
      val_in_memory tv v d mem
Proof
  strip_tac >> drule_all abi_decoder_static_source_acceptance >> strip_tac >>
  simp[] >>
  `abi_decoder_header ce env ty tv` by metis_tac[abi_decoder_coherent_header] >>
  `~is_dynamic (vyper_to_abi_type env ty)` by fs[abi_decoder_header_def] >>
  `static_length (vyper_to_abi_type env ty) = type_memory_bytes ce ty` by
    (irule abi_decode_static_window_width >> metis_tac[]) >>
  `valid_enc (vyper_to_abi_type env ty) bs` by
    metis_tac[vyper_decode_valid_enc_static] >>
  `enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs) =
    TAKE (type_memory_bytes ce ty) bs` by
    (drule abi_static_prefix_static >> simp[abi_static_prefix_def]) >>
  `value_has_type tv v` by
    metis_tac[abi_to_vyper_well_typed, abi_decoder_header_def] >>
  `has_type (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs)` by
    metis_tac[vyper_decode_dec_has_type] >>
  irule abi_decoder_descended_bulk_layout >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem abi_decoder_static_memory_body:
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty /\
  abi_decode_bytes_widths env ty /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  type_memory_bytes ce ty < dimword (:256) ==>
  !n raw dst acc base. n * type_memory_bytes ce ty <= LENGTH (raw:byte list) /\
    mem_bytes_at dst (n * type_memory_bytes ce ty) mem =
      TAKE (n * type_memory_bytes ce ty) raw ==>
    vyper_decode_valid_enc_array n (SOME (type_memory_bytes ce ty))
      (vyper_to_abi_type env ty) base raw /\
    ?avs vs. dec_tuple (REPLICATE n (vyper_to_abi_type env ty)) base raw acc =
      ListV (REVERSE acc ++ avs) /\
      LENGTH avs = n /\ LENGTH vs = n /\
      abi_to_vyper_list env (REPLICATE n ty) avs = SOME vs /\
      elems_in_memory vs dst tv mem
Proof
  strip_tac >>
  `static_length (vyper_to_abi_type env ty) = type_memory_bytes ce ty` by
    (irule abi_decode_static_window_width >> metis_tac[]) >>
  `~is_dynamic (vyper_to_abi_type env ty)` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  Induct >- simp[vyper_decode_valid_enc_def, dec_def, abi_to_vyper_def,
    val_in_memory_def] >>
  map_every qx_gen_tac [`raw`, `dst`, `acc`, `input`] >> strip_tac >>
  `type_memory_bytes ce ty <= LENGTH raw` by
    (fs[MULT_CLAUSES] >> decide_tac) >>
  `mem_bytes_at dst (type_memory_bytes ce ty) mem = TAKE (type_memory_bytes ce ty) raw` by
    (qspecl_then [`dst`, `0`, `type_memory_bytes ce ty`,
      `SUC n * type_memory_bytes ce ty`, `mem`] mp_tac mem_bytes_at_window >>
     simp[MULT_CLAUSES, TAKE_TAKE_MIN] >>
     `MIN (type_memory_bytes ce ty) (n * type_memory_bytes ce ty + type_memory_bytes ce ty) =
       type_memory_bytes ce ty` by
       (Cases_on `n = 0` >> Cases_on `type_memory_bytes ce ty = 0` >>
        simp[MIN_DEF]) >>
     simp[]) >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty) (TAKE (type_memory_bytes ce ty) raw) /\
   ?v. abi_to_vyper env ty
     (dec (vyper_to_abi_type env ty) (TAKE (type_memory_bytes ce ty) raw)) = SOME v /\
     val_in_memory tv v dst mem` by
    (irule abi_decoder_static_memory_window >> simp[LENGTH_TAKE_EQ, TAKE_TAKE_MIN] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `n * type_memory_bytes ce ty <= LENGTH (DROP (type_memory_bytes ce ty) raw)` by
    (simp[LENGTH_DROP] >> fs[MULT_CLAUSES] >> decide_tac) >>
  `mem_bytes_at (dst + type_memory_bytes ce ty) (n * type_memory_bytes ce ty) mem =
    TAKE (n * type_memory_bytes ce ty) (DROP (type_memory_bytes ce ty) raw)` by
    (qspecl_then [`dst`, `type_memory_bytes ce ty`, `n * type_memory_bytes ce ty`,
      `SUC n * type_memory_bytes ce ty`, `mem`] mp_tac mem_bytes_at_window >>
     simp[MULT_CLAUSES, DROP_TAKE, TAKE_TAKE_MIN]) >>
  first_x_assum (qspecl_then [`DROP (type_memory_bytes ce ty) raw`,
    `dst + type_memory_bytes ce ty`,
    `dec (vyper_to_abi_type env ty) (TAKE (type_memory_bytes ce ty) raw)::acc`, `input`] mp_tac) >>
  simp[] >> strip_tac >>
  conj_tac >- simp[Once vyper_decode_valid_enc_def] >>
  qexistsl [`dec (vyper_to_abi_type env ty) (TAKE (type_memory_bytes ce ty) raw)::avs`, `v::vs`] >>
  simp[Once dec_def, abi_to_vyper_def, val_in_memory_def]
QED

Theorem abi_decoder_static_dynarray_memory:
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty /\
  abi_decode_bytes_widths env ty /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  type_memory_bytes ce ty < dimword (:256) /\
  32 <= LENGTH (bs:byte list) /\ n = abi_head_word bs /\ n <= maxn /\
  n * type_memory_bytes ce ty <= LENGTH (DROP 32 bs) /\
  mem_bytes_at (dst + 32) (n * type_memory_bytes ce ty) mem =
    TAKE (n * type_memory_bytes ce ty) (DROP 32 bs) /\
  mem_word_at dst mem = n2w n ==>
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
  ?v. abi_to_vyper env (ArrayT ty (Dynamic maxn))
        (dec (Array NONE (vyper_to_abi_type env ty)) bs) = SOME v /\
      val_in_memory (ArrayTV tv (Dynamic maxn)) v dst mem
Proof
  strip_tac >> drule_all abi_decoder_static_memory_body >>
  disch_then (qspecl_then [`[]`, `DROP 32 bs`] mp_tac) >>
  simp[] >> strip_tac >>
  `static_length (vyper_to_abi_type env ty) = type_memory_bytes ce ty` by
    (irule abi_decode_static_window_width >> metis_tac[]) >>
  `~is_dynamic (vyper_to_abi_type env ty)` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  conj_tac
  >- (simp[Once vyper_decode_valid_enc_def] >>
      fs[abi_head_word_def, dec_number_def, w2n_lt]) >>
  `dec (Array NONE (vyper_to_abi_type env ty)) bs = ListV avs` by
    (simp[Once dec_def, GSYM abi_head_word_def] >>
     qpat_x_assum `static_length _ = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[abi_static_array_decode_tuple]) >>
  asm_rewrite_tac[] >>
  simp[Once abi_to_vyper_def, compatible_bound_def, val_in_memory_def,
    Excl "dec_def"] >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  gs[compatible_bound_def, make_array_value_def, val_in_memory_def]
QED
