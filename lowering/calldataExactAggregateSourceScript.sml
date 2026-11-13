Theory calldataExactAggregateSource
Ancestors
  vyperCalldata vyperCalldataProps vyperValue list rich_list arithmetic

(* The address of a member is computed from the ABI sizes of its prefix,
   not from its in-memory displacement. *)
Theorem calldata_exact_aggregate_source_pack:
  !ts vs ofs.
  cd_decode_list nat cd ts base ofs = SOME vs <=>
  LENGTH vs = LENGTH ts /\
  (!i. i < LENGTH ts ==>
    cd_decode nat cd (EL i ts)
      (cd_member_ptr nat cd (EL i ts) base
        (ofs + SUM (MAP tv_abi_size (TAKE i ts)))) = SOME (EL i vs))
Proof
  Induct >> Cases_on `vs`
  >- simp[cd_decode_def]
  >- simp[cd_decode_def]
  >- (simp[Once cd_decode_def, AllCaseEqs()] >> metis_tac[]) >>
  simp[Once cd_decode_def, AllCaseEqs()] >>
  rpt gen_tac >> qpat_x_assum `!vs ofs. _` kall_tac >> eq_tac
  >- (strip_tac >> conj_tac >- simp[] >>
      qx_gen_tac `i` >> Cases_on `i`
      >- (simp[NoAsms, TAKE] >> first_assum ACCEPT_TAC) >>
      pure_rewrite_tac [TAKE, EL, HD, TL, MAP, SUM, LESS_MONO_EQ] >>
      qpat_x_assum `!i. _` (qspec_then `n` mp_tac) >>
      simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]) >>
  strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  pure_rewrite_tac [TAKE, EL, HD, TL, MAP, SUM, LESS_MONO_EQ] >>
  asm_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]
QED

Theorem calldata_exact_aggregate_source_reject:
  i < LENGTH ts /\
  cd_decode nat cd (EL i ts)
    (cd_member_ptr nat cd (EL i ts) base
      (ofs + SUM (MAP tv_abi_size (TAKE i ts)))) = NONE ==>
  cd_decode_list nat cd ts base ofs = NONE
Proof
  strip_tac >> Cases_on `cd_decode_list nat cd ts base ofs` >> simp[] >>
  drule (iffLR calldata_exact_aggregate_source_pack) >>
  strip_tac >> first_x_assum drule >> simp[]
QED

Theorem calldata_exact_elems_source_list:
  !n i. cd_decode_elems nat cd tv base i n =
    cd_decode_list nat cd (REPLICATE n tv) base (i * tv_abi_size tv)
Proof
  Induct >> simp[Once cd_decode_def, REPLICATE] >> gen_tac >>
  pure_rewrite_tac [Once cd_decode_def] >>
  simp_tac bool_ss [Once cd_decode_def] >>
  simp_tac arith_ss [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_COMM]
QED

Theorem calldata_exact_tuple_source_some:
  LENGTH vs = LENGTH ts /\
  (!i. i < LENGTH ts ==>
    cd_decode nat cd (EL i ts)
      (cd_member_ptr nat cd (EL i ts) base
        (SUM (MAP tv_abi_size (TAKE i ts)))) = SOME (EL i vs)) ==>
  cd_decode nat cd (TupleTV ts) base = SOME (ArrayV (TupleV vs))
Proof
  strip_tac >>
  `cd_decode_list nat cd ts base 0 = SOME vs` by
    simp[calldata_exact_aggregate_source_pack] >>
  simp[Once cd_decode_def]
QED

Theorem calldata_exact_tuple_source_none:
  i < LENGTH ts /\
  cd_decode nat cd (EL i ts)
    (cd_member_ptr nat cd (EL i ts) base
      (SUM (MAP tv_abi_size (TAKE i ts)))) = NONE ==>
  cd_decode nat cd (TupleTV ts) base = NONE
Proof
  strip_tac >>
  `cd_decode_list nat cd ts base 0 = NONE` by
    (irule calldata_exact_aggregate_source_reject >> simp[] >> metis_tac[]) >>
  simp[Once cd_decode_def]
QED

Theorem calldata_exact_struct_source_some:
  LENGTH vs = LENGTH fs /\
  (!i. i < LENGTH fs ==>
    cd_decode nat cd (SND (EL i fs))
      (cd_member_ptr nat cd (SND (EL i fs)) base
        (SUM (MAP tv_abi_size (TAKE i (MAP SND fs))))) = SOME (EL i vs)) ==>
  cd_decode nat cd (StructTV fs) base = SOME (StructV (ZIP (MAP FST fs, vs)))
Proof
  strip_tac >>
  `cd_decode_list nat cd (MAP SND fs) base 0 = SOME vs` by
    simp[calldata_exact_aggregate_source_pack, EL_MAP] >>
  simp[Once cd_decode_def]
QED

Theorem calldata_exact_struct_source_none:
  i < LENGTH fs /\
  cd_decode nat cd (SND (EL i fs))
    (cd_member_ptr nat cd (SND (EL i fs)) base
      (SUM (MAP tv_abi_size (TAKE i (MAP SND fs))))) = NONE ==>
  cd_decode nat cd (StructTV fs) base = NONE
Proof
  strip_tac >>
  `cd_decode_list nat cd (MAP SND fs) base 0 = NONE` by
    (irule calldata_exact_aggregate_source_reject >>
     qexists_tac `i` >> simp[EL_MAP]) >>
  simp[Once cd_decode_def]
QED

Theorem calldata_exact_fixed_source_some:
  LENGTH vs = n /\
  (!i. i < n ==>
    cd_decode nat cd tv (cd_member_ptr nat cd tv base (i * tv_abi_size tv)) = SOME (EL i vs)) ==>
  cd_decode nat cd (ArrayTV tv (Fixed n)) base =
    SOME (ArrayV (make_array_value tv (Fixed n) vs))
Proof
  strip_tac >>
  `cd_decode_list nat cd (REPLICATE n tv) base 0 = SOME vs` by
    (simp[calldata_exact_aggregate_source_pack, EL_REPLICATE] >>
     rpt strip_tac >>
     `TAKE i (REPLICATE n tv) = REPLICATE i tv` by
       simp[REPLICATE_GENLIST, TAKE_GENLIST, MIN_DEF] >>
     simp[map_replicate, SUM_REPLICATE]) >>
  simp[Once cd_decode_def, calldata_exact_elems_source_list]
QED

Theorem calldata_exact_fixed_source_none:
  i < n /\
  cd_decode nat cd tv (cd_member_ptr nat cd tv base (i * tv_abi_size tv)) = NONE ==>
  cd_decode nat cd (ArrayTV tv (Fixed n)) base = NONE
Proof
  strip_tac >>
  `cd_decode_list nat cd (REPLICATE n tv) base 0 = NONE` by
    (irule calldata_exact_aggregate_source_reject >> qexists_tac `i` >>
     `TAKE i (REPLICATE n tv) = REPLICATE i tv` by
       simp[REPLICATE_GENLIST, TAKE_GENLIST, MIN_DEF] >>
     simp[EL_REPLICATE, map_replicate, SUM_REPLICATE]) >>
  simp[Once cd_decode_def, calldata_exact_elems_source_list]
QED
