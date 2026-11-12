(* Indexed semantic consumers for arbitrary decoder snapshots. *)
Theory extcallDecoderIndexedMember
Ancestors
  extcallDecoderMemberSemantics extcallDecoderStaticSuffix
  entryCanonicalEmptyWindow abiDecoderOffsetHead abiDecoderOffset abiDecoderContract
  abiDecoderMembers abiValidMembers vyperABIRoundtrip
  abiEncoder abiDecoderCoherence abiDecoderDynamic abiCanonicalHeadSize abiDecodeRanges
  vyperABI contractABI list rich_list arithmetic words

Theorem decoded_member_at[local]:
  !ats j raw hds. j < LENGTH ats ==>
  EL j (abi_decode_members ats raw hds) =
    dec (EL j ats) (abi_decode_member_bytes (EL j ats) raw
      (DROP (SUM (MAP abi_member_head_size (TAKE j ats))) hds))
Proof
  Induct >- simp[] >> Cases_on `j`
  >- simp_tac (srw_ss()) [abi_decode_members_def] >>
  simp_tac (srw_ss()) [abi_decode_members_def, DROP_DROP_T, ADD_COMM] >>
  rpt strip_tac >> first_x_assum drule >>
  disch_then (qspecl_then [`raw`, `DROP (abi_member_head_size h) hds`] mp_tac) >>
  simp_tac (srw_ss()) [DROP_DROP_T, ADD_COMM]
QED

Theorem indexed_member_view[local]:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\ j < LENGTH tys /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) raw raw /\
  abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) raw raw) = SOME ws ==>
  let at = vyper_to_abi_type env (EL j tys);
      ao = SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (TAKE j tys)));
      bytes = abi_decode_member_bytes at raw (DROP ao raw) in
  ao + abi_member_head_size at <= LENGTH raw /\
  vyper_decode_valid_enc at bytes /\
  abi_to_vyper env (EL j tys) (dec at bytes) = SOME (EL j ws) /\
  value_has_type (EL j tvs) (EL j ws) /\
  abi_decoder_coherent ce env sf (EL j tys) (EL j tvs)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `tys = TAKE j tys ++ EL j tys :: DROP (SUC j) tys` by
    metis_tac[TAKE_DROP, DROP_CONS_EL] >>
  `vyper_decode_valid_enc_tuple
    (MAP (vyper_to_abi_type env) (TAKE j tys) ++
      vyper_to_abi_type env (EL j tys) ::
      MAP (vyper_to_abi_type env) (DROP (SUC j) tys)) raw raw` by
    metis_tac[MAP_APPEND, MAP] >>
  qpat_x_assum `tys = _` kall_tac >>
  drule abiValidMemberTheory.abi_valid_member_head >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_valid_members_metadata >>
  disch_then (strip_assume_tac o MATCH_MP abi_decoder_members_relations) >>
  drule abi_to_vyper_list_EL >> strip_tac >>
  `j < LENGTH (MAP (vyper_to_abi_type env) tys)` by
    (pure_rewrite_tac[LENGTH_MAP] >> first_assum ACCEPT_TAC) >>
  drule decoded_member_at >>
  disch_then (qspecl_then [`raw`, `raw`] assume_tac) >>
  fs[LIST_REL_EL_EQN, EL_MAP, GSYM MAP_TAKE] >>
  qpat_x_assum `!i. _ ==> abi_to_vyper _ _ _ = _`
    (qspec_then `j` mp_tac) >>
  asm_simp_tac (srw_ss()) [EL_MAP] >> metis_tac[]
QED

Theorem decoder_indexed_member_suffix:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\ j < LENGTH tys /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) raw raw /\
  abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) raw raw) = SOME ws ==>
  let at = vyper_to_abi_type env (EL j tys);
      ao = SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (TAKE j tys)));
      k = if dec_info_needs_offset (type_to_abi_dec_info sf ce (EL j tys))
          then abi_head_word (DROP ao raw) else ao in
  k <= LENGTH raw /\ vyper_decode_valid_enc at (DROP k raw) /\
  (is_dynamic at \/ static_length at <= LENGTH (DROP k raw)) /\
  abi_to_vyper env (EL j tys) (dec at (DROP k raw)) = SOME (EL j ws) /\
  value_has_type (EL j tvs) (EL j ws)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all indexed_member_view >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  Cases_on `type_to_abi_dec_info sf ce (EL j tys) = DecComplex T []`
  >- suspend "empty" >>
  suspend "nonempty"
QED

Resume decoder_indexed_member_suffix[empty]:
  drule (iffLR abi_decoder_empty_dynamic_translation) >> strip_tac >>
  gvs[vyper_to_abi_type_def, dec_info_needs_offset_def,
    abi_decode_member_bytes_def] >>
  irule entry_fixed_zero_array_suffix_valid
QED

Resume decoder_indexed_member_suffix[nonempty]:
  `is_dynamic (vyper_to_abi_type env (EL j tys)) ==>
    !elem. vyper_to_abi_type env (EL j tys) <> Array (SOME 0) elem` by
    metis_tac[abi_decoder_nonempty_readable_head] >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce (EL j tys)) =
    is_dynamic (vyper_to_abi_type env (EL j tys))` by
    metis_tac[abi_decoder_nonempty_offset] >>
  Cases_on `is_dynamic (vyper_to_abi_type env (EL j tys))`
  >- (gvs[abi_decode_member_bytes_def] >>
      drule_all abiValidAggregateHeadsTheory.abi_valid_dynamic_head_min >>
      simp[LENGTH_DROP]) >>
  `static_length (vyper_to_abi_type env (EL j tys)) <= LENGTH
    (DROP (SUM (MAP abi_member_head_size
      (MAP (vyper_to_abi_type env) (TAKE j tys)))) raw)` by
    (fs[abi_member_head_size_def, LENGTH_DROP] >> decide_tac) >>
  gvs[abi_decode_member_bytes_def, static_decode_valid_suffix, static_dec_suffix,
    abi_member_head_size_def, LENGTH_DROP] >> decide_tac
QED

Finalise decoder_indexed_member_suffix

Theorem decoder_indexed_member_snapshot:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\ j < LENGTH tys /\
  sb <= H /\ H <= P /\ LENGTH snap = P /\ B+P < dimword(:256) /\
  mem_bytes_at B P s.vs_memory = snap /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys)
    (DROP sb (TAKE H snap)) (DROP sb (TAKE H snap)) /\
  abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys)
      (DROP sb (TAKE H snap)) (DROP sb (TAKE H snap))) = SOME ws ==>
  let at = vyper_to_abi_type env (EL j tys);
      ao = SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (TAKE j tys)));
      k = if dec_info_needs_offset (type_to_abi_dec_info sf ce (EL j tys))
          then w2n (abi_decode_load MLOAD (n2w (B+(sb+ao)):bytes32) s) else ao in
  sb+k <= H /\ vyper_decode_valid_enc at (DROP (sb+k) (TAKE H snap)) /\
  (is_dynamic at \/ static_length at <= LENGTH (DROP (sb+k) (TAKE H snap))) /\
  abi_to_vyper env (EL j tys) (dec at (DROP (sb+k) (TAKE H snap))) = SOME (EL j ws) /\
  value_has_type (EL j tvs) (EL j ws)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all decoder_indexed_member_suffix >> simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all indexed_member_view >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `vyper_decode_valid_enc_tuple _ raw raw` >>
  qmatch_goalsub_abbrev_tac `if dec_info_needs_offset di then _ else ao` >>
  Cases_on `dec_info_needs_offset di`
  >- suspend "load" >>
  fs[DROP_DROP_T, Abbr `raw`, Abbr `di`, Abbr `ao`, LENGTH_DROP] >>
  gvs[LENGTH_TAKE, MIN_DEF] >> decide_tac
QED

Resume decoder_indexed_member_snapshot[load]:
  `is_dynamic (vyper_to_abi_type env (EL j tys))` by
    metis_tac[abi_decoder_needs_offset_iff, abi_decoder_coherent_dynamic] >>
  `ao+32 <= LENGTH raw` by fs[Abbr `ao`, abi_member_head_size_def] >>
  `sb+ao+32 <= H /\ B+(sb+ao) < dimword(:256)` by
    (fs[Abbr `raw`, LENGTH_DROP] >> gvs[LENGTH_TAKE, MIN_DEF] >> decide_tac) >>
  `abi_decode_load MLOAD (n2w (B+(sb+ao)):bytes32) s =
    n2w (abi_head_word (DROP ao raw))` by
    (`abi_decode_load MLOAD (n2w (B+(sb+ao)):bytes32) s =
       word_of_bytes T 0w (TAKE 32 (DROP (sb+ao) snap))` by
       (irule EQ_TRANS >>
        qexists_tac `word_of_bytes T (0w:256 word)
          (TAKE 32 (DROP (sb+ao) (mem_bytes_at B P (abi_decode_source MLOAD s))))` >>
        conj_tac >- (irule abi_decode_load_window >> simp[] >> decide_tac) >>
        simp[abi_decode_source_def]) >>
     asm_rewrite_tac[] >> rewrite_tac[GSYM abiValidMemberTheory.abi_head_word_bytes] >>
     AP_TERM_TAC >> simp[Abbr `raw`, DROP_TAKE, TAKE_TAKE_MIN, DROP_DROP_T] >>
     `MIN 32 (H-(ao+sb)) = 32` by (simp[MIN_DEF] >> decide_tac) >>
     asm_rewrite_tac[]) >>
  `abi_head_word (DROP ao raw) < dimword(:256)` by
    (fs[Abbr `raw`, LENGTH_DROP] >> gvs[LENGTH_TAKE, MIN_DEF] >> decide_tac) >>
  fs[Abbr `di`, Abbr `ao`, Abbr `raw`, DROP_DROP_T, w2n_n2w] >>
  gvs[LENGTH_TAKE, LENGTH_DROP, MIN_DEF] >> decide_tac
QED

Finalise decoder_indexed_member_snapshot

(* Observed success is transported to the semantic member suffix, including
   the inline representation of an empty dynamic fixed array. *)
Theorem decoder_member_snapshot_observed:
  abi_decoder_coherent ce env sf ty tv /\
  sb <= H /\ H <= P /\ LENGTH snap = P /\ B+P < dimword(:256) /\
  mem_bytes_at B P s.vs_memory = snap /\
  ao + abi_member_head_size (vyper_to_abi_type env ty) <= H-sb /\
  (let k = if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
           then w2n (abi_decode_load MLOAD (n2w (B+(sb+ao)):bytes32) s) else ao in
   vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP (sb+k) (TAKE H snap)) /\
   (is_dynamic (vyper_to_abi_type env ty) \/ static_length (vyper_to_abi_type env ty)
      <= LENGTH (DROP (sb+k) (TAKE H snap))) /\
   abi_to_vyper env ty (dec (vyper_to_abi_type env ty)
      (DROP (sb+k) (TAKE H snap))) = SOME v) ==>
  let at = vyper_to_abi_type env ty;
      raw = DROP sb (TAKE H snap);
      xs = if is_dynamic at then DROP (abi_head_word (DROP ao raw)) raw else DROP ao raw in
  vyper_decode_valid_enc at xs /\ (is_dynamic at \/ static_length at <= LENGTH xs) /\
  abi_to_vyper env ty (dec at xs) = SOME v
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- suspend "observed_empty" >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty)` by
    metis_tac[abi_decoder_nonempty_offset, abi_decoder_coherent_dynamic] >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- suspend "observed_load" >>
  gvs[DROP_DROP_T]
QED

Resume decoder_member_snapshot_observed[observed_empty]:
  drule (iffLR abi_decoder_empty_dynamic_translation) >> strip_tac >>
  gvs[vyper_to_abi_type_def, dec_info_needs_offset_def] >>
  irule entry_fixed_zero_array_suffix_valid
QED

Resume decoder_member_snapshot_observed[observed_load]:
  `sb+ao+32 <= H /\ B+(sb+ao) < dimword(:256)` by
    (fs[abi_member_head_size_def] >> decide_tac) >>
  `abi_decode_load MLOAD (n2w (B+(sb+ao)):bytes32) s =
    n2w (abi_head_word (DROP ao (DROP sb (TAKE H snap))))` by
    (irule EQ_TRANS >>
     qexists_tac `word_of_bytes T (0w:256 word)
       (TAKE 32 (DROP (sb+ao) (mem_bytes_at B P (abi_decode_source MLOAD s))))` >>
     conj_tac >- (irule abi_decode_load_window >> simp[] >> decide_tac) >>
     simp[abi_decode_source_def] >>
     rewrite_tac[GSYM abiValidMemberTheory.abi_head_word_bytes] >>
     AP_TERM_TAC >> simp[DROP_TAKE, TAKE_TAKE_MIN, DROP_DROP_T] >>
     `MIN 32 (H-(ao+sb)) = 32` by (simp[MIN_DEF] >> decide_tac) >>
     asm_rewrite_tac[]) >>
  gvs[w2n_n2w, abi_head_word_def, DROP_DROP_T]
QED

Finalise decoder_member_snapshot_observed
