(* Source-side cut only: member offsets are natural numbers relative to b. *)
Theory abiMalformedAggregateFirstBadChild
Ancestors
  abiMalformedMemberReflection abiValidAllocatedSource abiMalformedBoundedParents
  abiValidAggregateHeads abiDecodeRanges abiDecoderCoherence abiVyperAdmissible
  abiMalformedMembers abiValidMembers vyperABI contractABI compileEnv
  valueEncodingTyping valueEncoding vyperTypeSystem vyperValue vyperABIValid
  abiMalformedBoundedContract abiDecoderMembers words list rich_list arithmetic While

val abi_view = ``\a q. if is_dynamic a then DROP q (xs:word8 list)
                         else TAKE (static_length a) (DROP q xs)``;
val abi_ok = ``\e t z. vyper_decode_valid_enc (vyper_to_abi_type e t) z /\
                       abi_vyper_admissible e t (dec (vyper_to_abi_type e t) z)``;
val members_ok = ``\e ts b ao.
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type e) ts) (DROP b xs) (DROP (b+ao) xs) /\
  abi_vyper_admissible_list e ts
    (abi_decode_members (MAP (vyper_to_abi_type e) ts) (DROP b xs) (DROP (b+ao) xs))``;
val head_prefix = ``\e ts j. SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type e) (TAKE j ts)))``;
val slot_ok = ``\e b ao t. let a = vyper_to_abi_type e t; hds = DROP (b+ao) xs in
  b+ao+abi_member_head_size a <= LENGTH xs /\
  (^abi_ok) e t (abi_decode_member_bytes a (DROP b xs) hds)``;

Theorem member_raw_prefix_reconstruct[local]:
  !ts ao. (!j. j < LENGTH ts ==>
    (^slot_ok) e b (ao+(^head_prefix) e ts j) (EL j ts)) ==>
    (^members_ok) e ts b ao
Proof
  simp_tac bool_ss [LET_THM] >> Induct
  >- simp[vyper_decode_valid_enc_def, abi_decode_members_def, abi_vyper_admissible_list_nil] >>
  rpt gen_tac >> disch_then (mk_asm "slots") >>
  asm "slots" (qspec_then `0` mp_tac) >>
  simp_tac bool_ss [TAKE, EL, HD, LENGTH, MAP, SUM, ADD_0, prim_recTheory.LESS_0] >> strip_tac >>
  last_x_assum (qspec_then `ao+abi_member_head_size (vyper_to_abi_type e h)` mp_tac) >>
  (impl_tac >-
    (rpt strip_tac >> asm "slots" (qspec_then `SUC j` mp_tac) >>
     asm_simp_tac bool_ss [ADD_ASSOC, TAKE, EL, TL, LENGTH, LESS_MONO_EQ, MAP, SUM])) >>
  strip_tac >>
  MATCH_MP_TAC (GEN_ALL (REWRITE_RULE [MAP] abi_malformed_members_reflect_cons)) >>
  qexists_tac `LENGTH xs` >> asm_simp_tac bool_ss [] >>
  strip_tac >> fs[abi_member_head_size_def] >>
  simp[dec_number_def, is_num_value_def, LENGTH_DROP] >> decide_tac
QED

val member_position = ``\ce (f:string |-> (string # type # num) list) b ao t. b +
  (if dec_info_needs_offset (type_to_abi_dec_info f ce t)
   then abi_head_word (DROP (b+ao) xs) else ao)``;
val member_meta = ``\ce e f par v0 ts j. let t = EL j ts in
  abi_decode_bytes_widths e t /\
  (?u. abi_decoder_coherent ce e f t u /\ type_memory_size u = type_memory_bytes ce t) /\
  abi_size_bound f t < dimword (:256) /\
  v0 + SUM (MAP (type_memory_bytes ce) (TAKE j ts)) + type_memory_bytes ce t <=
    type_memory_bytes ce par``;
val member_good = ``\ce e f b ao t.
  let a = vyper_to_abi_type e t;
      q = (^member_position) ce f b ao t;
      raw = abi_decode_member_bytes (vyper_to_abi_type e t) (DROP b xs) (DROP (b+ao) xs)
  in (^slot_ok) e b ao t /\ q <= LENGTH xs /\
     (is_dynamic a \/ q + static_length a <= LENGTH xs) /\
     vyper_decode_valid_enc a (DROP q xs) /\ dec a raw = dec a (DROP q xs) /\
     (?v. abi_to_vyper e t (dec a (DROP q xs)) = SOME v)``;
val member_bad = ``\ce e f b ao t.
  let a = vyper_to_abi_type e t;
      end_h = b + ao + abi_member_head_size (vyper_to_abi_type e t);
      q = (^member_position) ce f b ao t;
      raw = abi_decode_member_bytes (vyper_to_abi_type e t) (DROP b xs) (DROP (b+ao) xs)
  in LENGTH xs < end_h \/
     (end_h <= LENGTH xs /\ ~(^abi_ok) e t raw /\ ~(^abi_ok) e t ((^abi_view) a q) /\
      (dimword (:256) <= q \/ (LENGTH xs < q /\ q < dimword (:256)) \/ q <= LENGTH xs))``;
val member_scan = ``\ce e f par b v0 ts.
  LENGTH ts < dimword (:256) /\ ?i. i < LENGTH ts /\
  (!j. j < i ==> (^member_meta) ce e f par v0 ts j /\
     (^member_good) ce e f b ((^head_prefix) e ts j) (EL j ts)) /\
  (^member_meta) ce e f par v0 ts i /\
  (^member_bad) ce e f b ((^head_prefix) e ts i) (EL i ts)``;
val member_table = ``\ce e f par b v0 ts.
  0 < LENGTH ts /\ LENGTH ts < dimword (:256) /\
  (LENGTH xs < b + (^head_prefix) e ts (LENGTH ts) \/
   (b + (^head_prefix) e ts (LENGTH ts) <= LENGTH xs /\
    (^member_scan) ce e f par b v0 ts))``;

Theorem source_readable_member_good[local]:
  abi_decoder_coherent ce e f t tv /\ (^slot_ok) e b ao t ==>
  (^member_good) ce e f b ao t
Proof
  BETA_TAC >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `q = b + (if dec_info_needs_offset (type_to_abi_dec_info f ce t)
                      then abi_head_word (DROP (b+ao) xs) else ao)` >>
  `q = b + (if dec_info_needs_offset (type_to_abi_dec_info f ce t)
            then abi_head_word (DROP (b+ao) xs) else ao)` by simp[Abbr `q`] >>
  `LENGTH xs = LENGTH xs` by simp[] >>
  drule_all abi_valid_source_member_position >> strip_tac >>
  qpat_x_assum `q = _` kall_tac >>
  asm_simp_tac bool_ss [] >> irule abi_vyper_admissible_convert >>
  metis_tac[]
QED

Theorem source_failed_slot_bad[local]:
  abi_decoder_coherent ce e f t tv /\ ~(^slot_ok) e b ao t ==>
  (^member_bad) ce e f b ao t
Proof
  BETA_TAC >> simp_tac bool_ss [LET_THM] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "bad")) >>
  Cases_on `b+ao+abi_member_head_size (vyper_to_abi_type e t) <= LENGTH xs`
  >- (disj2_tac >> asm_simp_tac bool_ss [] >>
      qabbrev_tac `q = b + (if dec_info_needs_offset (type_to_abi_dec_info f ce t)
                          then abi_head_word (DROP (b+ao) xs) else ao)` >>
      conj_tac >- (asm "bad" mp_tac >> asm_simp_tac bool_ss []) >>
      reverse conj_tac >- decide_tac >>
      spose_not_then strip_assume_tac >>
      `LENGTH xs = LENGTH xs` by simp[] >>
      `q = b + (if dec_info_needs_offset (type_to_abi_dec_info f ce t)
                then abi_head_word (DROP (b+ao) xs) else ao)` by simp[Abbr `q`] >>
      drule_all abi_malformed_member_reflection >> strip_tac >>
      asm "bad" mp_tac >> asm_simp_tac bool_ss []) >>
  disj1_tac >> decide_tac
QED

Theorem member_prefix_least_failure[local]:
  LENGTH ts < dimword (:256) /\ (!j. j < LENGTH ts ==> (^member_meta) ce e f par v0 ts j) /\
  ~(^members_ok) e ts b 0 ==>
  (^member_scan) ce e f par b v0 ts
Proof
  BETA_TAC >> simp_tac bool_ss [LET_THM, ADD_CLAUSES] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 (mk_asm "meta") assume_tac)) >>
  asm_simp_tac bool_ss [] >>
  `?j. j < LENGTH ts /\ ~(^slot_ok) e b ((^head_prefix) e ts j) (EL j ts)` by
    (BETA_TAC >> simp_tac bool_ss [LET_THM] >> spose_not_then assume_tac >>
     qspecl_then [`ts`,`0`] mp_tac member_raw_prefix_reconstruct >>
     gvs[LET_THM]) >>
  qspec_then `\j. j < LENGTH ts /\ ~(^slot_ok) e b ((^head_prefix) e ts j) (EL j ts)`
    mp_tac arithmeticTheory.WOP >>
  BETA_TAC >> simp_tac bool_ss [LET_THM] >>
  (impl_tac >- (qexists_tac `j` >> pop_assum mp_tac >>
                asm_simp_tac bool_ss [LET_THM])) >>
  disch_then (qx_choose_then `i` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 assume_tac (mk_asm "failed")) (mk_asm "before"))) >>
  qexists_tac `i` >> asm_simp_tac bool_ss [] >>
  conj_tac
  >- (qx_gen_tac `k` >> disch_tac >> `k < LENGTH ts` by decide_tac >>
      asm "meta" (qspec_then `k` mp_tac) >> asm_simp_tac bool_ss [] >> strip_tac >>
      `(^member_good) ce e f b ((^head_prefix) e ts k) (EL k ts)` by
        (irule source_readable_member_good >>
         conj_tac >- (qexists_tac `u` >> simp[]) >>
         BETA_TAC >> asm_simp_tac bool_ss [LET_THM] >>
         asm "before" (qspec_then `k` mp_tac) >> asm_simp_tac bool_ss []) >>
      pop_assum (STRIP_ASSUME_TAC o SIMP_RULE bool_ss [LET_THM]) >>
      asm_simp_tac bool_ss [] >> rpt conj_tac >> metis_tac[]) >>
  asm "meta" (qspec_then `i` mp_tac) >> asm_simp_tac bool_ss [] >> strip_tac >>
  `(^member_bad) ce e f b ((^head_prefix) e ts i) (EL i ts)` by
    (irule source_failed_slot_bad >> reverse conj_tac >- (qexists_tac `u` >> simp[]) >>
     BETA_TAC >> asm "failed" (fn th => asm_simp_tac bool_ss [LET_THM, th])) >>
  pop_assum (fn th => asm_simp_tac bool_ss [SIMP_RULE bool_ss [LET_THM] th]) >>
  qexists_tac `u` >> asm_rewrite_tac[]
QED

Theorem malformed_members_table[local]:
  LENGTH ts < dimword (:256) /\
  (!j. j < LENGTH ts ==> (^member_meta) ce e f par v0 ts j) /\
  ~(^members_ok) e ts b 0 ==>
  (^member_table) ce e f par b v0 ts
Proof
  disch_tac >>
  `(^member_scan) ce e f par b v0 ts` by (MATCH_MP_TAC member_prefix_least_failure >> first_assum ACCEPT_TAC) >>
  pop_assum (mp_tac o SIMP_RULE bool_ss [LET_THM]) >>
  BETA_TAC >> simp_tac bool_ss [LET_THM] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (fn th => assume_tac th >> strip_assume_tac th)) >>
  `0 < LENGTH ts` by decide_tac >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem source_list_member_metadata[local]:
  LIST_REL (abi_decoder_coherent ce e f) ts tvs /\
  EVERY (abi_decode_bytes_widths e) ts /\ EVERY (\t. abi_size_bound f t < dimword (:256)) ts /\
  v0 + SUM (MAP (type_memory_bytes ce) ts) <= type_memory_bytes ce par /\
  j < LENGTH ts ==>
  (^member_meta) ce e f par v0 ts j
Proof
  BETA_TAC >> simp_tac bool_ss [LET_THM, LIST_REL_EL_EQN, EVERY_EL] >> strip_tac >>
  `abi_decoder_coherent ce e f (EL j ts) (EL j tvs)` by simp[] >>
  drule abi_decoder_coherent_header >> simp[abi_decoder_header_def] >> strip_tac >>
  `SUM (MAP (type_memory_bytes ce) (TAKE (j+1) ts)) =
   SUM (MAP (type_memory_bytes ce) (TAKE j ts)) + type_memory_bytes ce (EL j ts)` by
    simp[TAKE_EL_SNOC, MAP_SNOC, SUM_SNOC] >>
  `SUM (MAP (type_memory_bytes ce) (TAKE (j+1) ts)) <=
   SUM (MAP (type_memory_bytes ce) ts)` by
    (`SUM (MAP (type_memory_bytes ce) ts) =
      SUM (MAP (type_memory_bytes ce) (TAKE (j+1) ts)) +
      SUM (MAP (type_memory_bytes ce) (DROP (j+1) ts))` by
       (rewrite_tac[GSYM SUM_APPEND, GSYM MAP_APPEND, TAKE_DROP]) >> decide_tac) >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (qexists_tac `EL j tvs` >> simp[]) >>
  decide_tac
QED

Theorem source_member_memory_sum[local]:
  !ts tvs. LIST_REL (abi_decoder_coherent ce e f) ts tvs ==>
    SUM (MAP (type_memory_bytes ce) ts) = type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> simp[type_memory_size_def] >>
  rpt strip_tac >> drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]
QED

(* Tuple and struct both use the same ABI tuple view, including its static trim. *)
Theorem source_tuple_view_members[local]:
  (^members_ok) e ts b 0 /\ LENGTH ts < dimword (:256) ==>
  vyper_decode_valid_enc (Tuple (MAP (vyper_to_abi_type e) ts)) ((^abi_view) (Tuple (MAP
    (vyper_to_abi_type e) ts)) b) /\
     abi_vyper_admissible_list e ts (abi_decode_members (MAP (vyper_to_abi_type e) ts) ((^abi_view)
       (Tuple (MAP (vyper_to_abi_type e) ts)) b) ((^abi_view) (Tuple (MAP (vyper_to_abi_type e) ts))
       b))
Proof
  BETA_TAC >> simp_tac bool_ss [LET_THM, ADD_CLAUSES, is_dynamic_def] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `Tuple ats` >> Cases_on `any_dynamic ats`
  >- simp[Abbr `ats`, Once vyper_decode_valid_enc_def] >>
  qspec_then `ats` mp_tac abi_malformed_static_members_trim >>
  disch_then (qspecl_then
    [`TAKE (static_length (Tuple ats)) (DROP b xs)`, `DROP b xs`,
     `DROP b xs`, `static_length (Tuple ats)`] mp_tac) >>
  simp[static_length_Tuple_SUM] >> strip_tac >>
  simp[Once vyper_decode_valid_enc_def, Abbr `ats`]
QED

Theorem source_fixed_view_members[local]:
  (^members_ok) e (REPLICATE n t) b 0 /\ n < dimword (:256) /\
  evaluate_type e t = SOME tv ==>
  (^abi_ok) e (ArrayT t (Fixed n))
    ((^abi_view) (vyper_to_abi_type e (ArrayT t (Fixed n))) b)
Proof
  BETA_TAC >> simp_tac bool_ss [LET_THM, ADD_CLAUSES, vyper_to_abi_type_def,
    is_dynamic_def, optionTheory.IS_NONE_DEF, map_replicate] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `Array (SOME n) at` >>
  Cases_on `is_dynamic at`
  >- (simp_tac bool_ss [Once vyper_decode_valid_enc_def, dec_def, LET_THM,
           GSYM vyper_decode_valid_enc_tuple_REPLICATE,
           abi_decode_array_members, abi_decode_members_value] >>
      simp[Abbr `at`, abi_vyper_admissible_array_iff, compatible_bound_def, map_replicate]) >>
  qspec_then `REPLICATE n at` mp_tac abi_malformed_static_members_trim >>
  disch_then (qspecl_then
    [`TAKE (n * static_length at) (DROP b xs)`, `DROP b xs`,
     `DROP b xs`, `n * static_length at`] mp_tac) >>
  simp[map_replicate, SUM_REPLICATE, any_dynamic_EXISTS] >> strip_tac >>
  simp_tac bool_ss [Once vyper_decode_valid_enc_def, dec_def, LET_THM, static_length_def,
    GSYM vyper_decode_valid_enc_tuple_REPLICATE, abi_decode_array_members, abi_decode_members_value] >>
  qspecl_then [`n`, `at`] mp_tac abi_decode_array_members >>
  gvs[Abbr `at`, abi_decode_members_value, abi_vyper_admissible_array_iff,
      compatible_bound_def, map_replicate]
QED

Theorem malformed_source_tuple_table[local]:
  abi_decoder_coherent ce env sf (TupleT ts) tv /\
  abi_decode_bytes_widths env (TupleT ts) /\
  abi_size_bound sf (TupleT ts) < dimword (:256) /\
  (?av. has_type (vyper_to_abi_type env (TupleT ts)) av) /\
  ~(^abi_ok) env (TupleT ts) ((^abi_view) (vyper_to_abi_type env (TupleT ts)) p) ==>
  (^member_table) ce env sf (TupleT ts) p 0 ts
Proof
  strip_tac >> qpat_x_assum `abi_decoder_coherent _ _ _ (TupleT _) _`
    (strip_assume_tac o REWRITE_RULE [abi_decoder_coherent_tuple_iff]) >>
  `LENGTH ts < dimword (:256)` by
    (Cases_on `av` >> fs[has_type_def] >> drule has_types_length >> simp[vyper_to_abi_types_MAP]) >>
  drule_all abi_malformed_tuple_capacity >> strip_tac >>
  `SUM (MAP (type_memory_bytes ce) ts) = type_memory_bytes ce (TupleT ts)` by
    (drule source_member_memory_sum >> gvs[abi_decoder_header_def, type_memory_size_def]) >>
  MATCH_MP_TAC malformed_members_table >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> MATCH_MP_TAC source_list_member_metadata >>
      fs[abi_decode_bytes_widths_def]) >>
  disch_tac >> drule source_tuple_view_members >> simp[] >>
  qpat_x_assum `~_` mp_tac >>
  simp[LET_THM, vyper_to_abi_types_MAP, abi_decode_members_value] >>
  metis_tac[abiVyperAdmissibleTheory.tuple]
QED

Theorem malformed_source_struct_table[local]:
  abi_decoder_coherent ce env sf (StructT id) tv /\
  abi_decode_bytes_widths env (StructT id) /\
  abi_size_bound sf (StructT id) < dimword (:256) /\
  (?av. has_type (vyper_to_abi_type env (StructT id)) av) /\
  ~(^abi_ok) env (StructT id) ((^abi_view) (vyper_to_abi_type env (StructT id)) p) ==>
  ?args. FLOOKUP env id = SOME (StructArgs args) /\
    (^member_table) ce (env \\ id) (sf \\ nsid_to_string id) (StructT id) p 0 (MAP SND args)
Proof
  strip_tac >> qpat_x_assum `abi_decoder_coherent _ _ _ (StructT _) _`
    (strip_assume_tac o REWRITE_RULE [abi_decoder_coherent_struct_iff]) >>
  `LENGTH args < dimword (:256)` by
    (Cases_on `av` >> fs[has_type_def] >> drule has_types_length >> simp[vyper_to_abi_types_MAP]) >>
  drule_all abi_malformed_struct_capacity >> strip_tac >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `SUM (MAP (type_memory_bytes ce) (MAP SND args)) = type_memory_bytes ce (StructT id)` by
    (drule source_member_memory_sum >>
     gvs[abi_decoder_header_def, type_memory_size_def, type_memory_size_fields_zip]) >>
  qexists_tac `args` >> asm_rewrite_tac[] >> MATCH_MP_TAC malformed_members_table >>
  asm_simp_tac bool_ss [LENGTH_MAP] >> conj_tac
  >- (rpt strip_tac >> simp_tac bool_ss [LET_THM] >>
      MATCH_MP_TAC (SIMP_RULE bool_ss [LET_THM] source_list_member_metadata) >>
      fs[abi_decode_bytes_widths_def, EVERY_MAP, combinTheory.o_DEF]) >>
  pure_once_rewrite_tac [GSYM DE_MORGAN_THM] >>
  disch_then (strip_assume_tac o REWRITE_RULE [ADD_CLAUSES]) >>
  drule (SIMP_RULE bool_ss [ADD_CLAUSES] source_tuple_view_members) >> simp[] >>
  qpat_x_assum `~_` mp_tac >>
  simp[LET_THM, vyper_to_abi_types_MAP, abi_decode_members_value] >>
  metis_tac[abiVyperAdmissibleTheory.struct_case]
QED

Theorem malformed_source_fixed_table[local]:
  abi_decoder_coherent ce env sf (ArrayT t (Fixed n)) tv /\
  abi_decode_bytes_widths env (ArrayT t (Fixed n)) /\
  abi_size_bound sf (ArrayT t (Fixed n)) < dimword (:256) /\
  (?av. has_type (vyper_to_abi_type env (ArrayT t (Fixed n))) av) /\
  ~(^abi_ok) env (ArrayT t (Fixed n))
    ((^abi_view) (vyper_to_abi_type env (ArrayT t (Fixed n))) p) ==>
  (^member_table) ce env sf (ArrayT t (Fixed n)) p 0 (REPLICATE n t)
Proof
  strip_tac >> qpat_x_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _`
    (strip_assume_tac o REWRITE_RULE [abi_decoder_coherent_array_iff]) >>
  `n < dimword (:256)` by (Cases_on `av` >> fs[has_type_def, valid_length_def]) >>
  drule_all_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) abi_malformed_array_capacity >>
  rename1 `abi_decoder_coherent ce env sf t etv` >>
  `evaluate_type env t = SOME etv /\
   n * type_memory_bytes ce t = type_memory_bytes ce (ArrayT t (Fixed n))` by
    (drule abi_decoder_coherent_header >>
     simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
     gvs[abi_decoder_header_def, type_memory_size_def]) >>
  MATCH_MP_TAC malformed_members_table >> conj_tac >- simp[] >> conj_tac
  >- (rpt strip_tac >> MATCH_MP_TAC (GEN_ALL source_list_member_metadata) >>
      qexists_tac `REPLICATE n etv` >>
      gs[LIST_REL_REPLICATE_same, abi_decode_bytes_widths_def, map_replicate, SUM_REPLICATE]) >>
  qpat_x_assum `~_` mp_tac >>
  metis_tac[source_fixed_view_members]
QED

Theorem source_dynamic_view_members[local]:
  (^members_ok) e (REPLICATE n t) (b+32) 0 /\
  b+32 <= LENGTH xs /\ is_num_value (dec_number (Uint 256) (TAKE 32 (DROP b xs))) /\
  n = abi_head_word (DROP b xs) /\ n <= cap /\ n < dimword (:256) /\
  evaluate_type e t = SOME tv ==>
  (^abi_ok) e (ArrayT t (Dynamic cap))
    ((^abi_view) (vyper_to_abi_type e (ArrayT t (Dynamic cap))) b)
Proof
  BETA_TAC >> simp_tac bool_ss [LET_THM, ADD_CLAUSES] >> strip_tac >>
  `32 <= LENGTH (DROP b xs)` by (simp[LENGTH_DROP] >> decide_tac) >>
  `DROP 32 (DROP b xs) = DROP (b+32) xs` by simp[DROP_DROP_T, ADD_COMM] >>
  simp_tac bool_ss [vyper_to_abi_type_def, is_dynamic_def, optionTheory.IS_NONE_DEF] >>
  conj_asm1_tac
  >- (asm_simp_tac bool_ss [Once vyper_decode_valid_enc_def, LET_THM,
                           GSYM abi_head_word_def, GSYM vyper_decode_valid_enc_tuple_REPLICATE] >>
      fs[map_replicate]) >>
  drule_then strip_assume_tac abi_valid_dynamic_array_view >>
  gvs[abi_vyper_admissible_array_iff, compatible_bound_def, map_replicate]
QED

val dynamic_scan = ``\ce e f t cap p.
  let dn = dec_number (Uint 256) (TAKE 32 (DROP p xs));
      n = abi_head_word (DROP p xs)
  in LENGTH xs < p+32 \/
     (p+32 <= LENGTH xs /\ is_num_value dn /\ n < dimword (:256) /\
      (cap < n \/ (n <= cap /\
       (^member_scan) ce e f (ArrayT t (Dynamic cap)) (p+32) 32 (REPLICATE n t))))``;

Theorem malformed_source_dynamic_scan[local]:
  abi_decoder_coherent ce env sf (ArrayT t (Dynamic cap)) tv /\
  abi_decode_bytes_widths env (ArrayT t (Dynamic cap)) /\
  abi_size_bound sf (ArrayT t (Dynamic cap)) < dimword (:256) /\
  ~(^abi_ok) env (ArrayT t (Dynamic cap))
    ((^abi_view) (vyper_to_abi_type env (ArrayT t (Dynamic cap))) p) ==>
  (^dynamic_scan) ce env sf t cap p
Proof
  strip_tac >> qpat_x_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _`
    (strip_assume_tac o REWRITE_RULE [abi_decoder_coherent_array_iff]) >>
  BETA_TAC >> simp_tac bool_ss [LET_THM] >>
  Cases_on `LENGTH xs < p+32` >- asm_rewrite_tac[] >>
  `p+32 <= LENGTH xs` by decide_tac >>
  qabbrev_tac `n = abi_head_word (DROP p xs)` >>
  `is_num_value (dec_number (Uint 256) (TAKE 32 (DROP p xs))) /\ n < dimword (:256)` by
    (simp[Abbr `n`, abi_head_word_def, dec_number_def, is_num_value_def,
          dest_NumV_def, w2n_lt, LENGTH_DROP] >> decide_tac) >>
  asm_rewrite_tac[] >> Cases_on `cap < n` >- asm_rewrite_tac[] >>
  `n <= cap` by decide_tac >> asm_rewrite_tac[] >>
  drule_all_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) abi_malformed_array_capacity >>
  rename1 `abi_decoder_coherent ce env sf t etv` >>
  `evaluate_type env t = SOME etv /\
   32 + cap * type_memory_bytes ce t = type_memory_bytes ce (ArrayT t (Dynamic cap))` by
    (drule abi_decoder_coherent_header >>
     simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
     gvs[abi_decoder_header_def, type_memory_size_def]) >>
  `32 + n * type_memory_bytes ce t <= type_memory_bytes ce (ArrayT t (Dynamic cap))` by
    (qpat_x_assum `_ + _ = type_memory_bytes _ _` (SUBST1_TAC o SYM) >>
     simp[LE_MULT_RCANCEL]) >>
  `(^member_scan) ce env sf (ArrayT t (Dynamic cap)) (p+32) 32 (REPLICATE n t)`
    suffices_by simp_tac bool_ss [LET_THM] >>
  MATCH_MP_TAC member_prefix_least_failure >> conj_tac >- simp[] >> conj_tac
  >- (rpt strip_tac >> MATCH_MP_TAC (GEN_ALL source_list_member_metadata) >>
      qexists_tac `REPLICATE n etv` >>
      gs[LIST_REL_REPLICATE_same, abi_decode_bytes_widths_def, map_replicate, SUM_REPLICATE] >>
      metis_tac[LESS_LESS_EQ_TRANS]) >>
  qpat_x_assum `~(^abi_ok) _ _ _` mp_tac >>
  asm_simp_tac bool_ss [Abbr `n`] >>
  metis_tac[BETA_RULE source_dynamic_view_members]
QED

Theorem malformed_aggregate_first_bad_child:
  !ce env sf par tv xs p.
    abi_decoder_coherent ce env sf par tv /\
    abi_decode_bytes_widths env par /\
    assignable_type env par /\
    type_memory_size tv < dimword (:256) /\
    abi_size_bound sf par < dimword (:256) /\
    (?av. has_type (vyper_to_abi_type env par) av) /\
    p < dimword (:256) /\ LENGTH xs < dimword (:256) /\
    ~(^abi_ok) env par ((^abi_view) (vyper_to_abi_type env par) p) ==>
    case par of
      TupleT ts => (^member_table) ce env sf par p 0 ts
    | StructT id => (?args. FLOOKUP env id = SOME (StructArgs args) /\
        (^member_table) ce (env \\ id) (sf \\ nsid_to_string id) par p 0 (MAP SND args))
    | ArrayT t (Fixed n) => (^member_table) ce env sf par p 0 (REPLICATE n t)
    | ArrayT t (Dynamic cap) => (^dynamic_scan) ce env sf t cap p
    | _ => T
Proof
  rpt strip_tac >> Cases_on `par` >>
  simp_tac bool_ss [TypeBase.case_def_of ``:type``, LET_THM]
  >- (MATCH_MP_TAC (SIMP_RULE bool_ss [LET_THM] malformed_source_tuple_table) >>
      asm_simp_tac bool_ss [] >> metis_tac[])
  >- (rename1 `abi_decoder_coherent _ _ _ (ArrayT _ b) _` >> Cases_on `b` >>
      simp_tac bool_ss [vyperASTTheory.bound_case_def, LET_THM]
      >- (MATCH_MP_TAC (SIMP_RULE bool_ss [LET_THM] malformed_source_fixed_table) >>
          asm_simp_tac bool_ss [] >> metis_tac[]) >>
      MATCH_MP_TAC (SIMP_RULE bool_ss [LET_THM] malformed_source_dynamic_scan) >>
      asm_simp_tac bool_ss [] >> metis_tac[]) >>
  MATCH_MP_TAC (SIMP_RULE bool_ss [LET_THM] malformed_source_struct_table) >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED
