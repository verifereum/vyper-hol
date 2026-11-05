Theory exprSimAbiDecodeTupleAssembly
Ancestors
  exprSimAbiDecodeMemberExecute exprSimAbiDecodeTupleSource
  exprSimAbiDecodeTupleOutcome abiDecodeRanges abiValidMembers rich_list pred_set
  abiValidDecodedMetadata abiDecoderCoherence abiDecoderLayout
  valueTypingMemoryProps vyperTypeABI vyperABIValid vyperABI
  abiDecoderMembers abiDecoderFixedMemory valueEncodingProps
  vyperValue valueEncoding contractABI list arithmetic

Theorem abi_decode_source_accepts_wf:
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decode_source_accepts env ty view v ==> val_wf tv v
Proof
  simp_tac bool_ss [abi_decode_source_accepts_def] >> strip_tac >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `has_type (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) view)` by
    (irule vyper_decode_dec_has_type >> simp[]) >>
  `value_has_type tv v` by
    (irule (cj 1 abi_to_vyper_well_typed) >>
     qexistsl_tac [`dec (vyper_to_abi_type env ty) view`, `env`, `ty`] >> simp[]) >>
  metis_tac[value_has_type_memory_wf]
QED

Definition abi_tuple_rows_schema_def:
  abi_tuple_rows_schema ce env rows <=>
    EVERY (\(ei,ty,tv,asz,msz).
      abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
      assignable_type env ty /\ abi_decode_bytes_widths env ty /\
      ei = type_to_abi_dec_info ce.ce_struct_fields ce ty /\
      asz = abi_member_head_size (vyper_to_abi_type env ty) /\
      msz = type_memory_bytes ce ty /\ msz = type_memory_size tv /\
      (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem)) rows
End

Definition abi_tuple_rows_accept_def:
  (abi_tuple_rows_accept env bs ao [] vs <=> vs = []) /\
  (abi_tuple_rows_accept env bs ao ((ei,ty,tv,asz,msz)::rows) vs <=>
    ?v tail. vs = v::tail /\
      abi_tuple_row_accepts env bs ao (ei,ty,tv,asz,msz) v /\
      abi_tuple_rows_accept env bs (ao+asz) rows tail)
End

Theorem abi_tuple_rows_values_accept:
  !rows env bs ao vo d vs s.
    abi_tuple_rows_values env bs ao vo d rows vs s ==>
    abi_tuple_rows_accept env bs ao rows vs
Proof
  Induct >- simp[abi_tuple_rows_values_def, abi_tuple_rows_accept_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_rows_values_def, abi_tuple_rows_accept_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_tuple_row_accepts_wf:
  abi_tuple_rows_schema ce env [(ei,ty,tv,asz,msz)] /\
  abi_tuple_row_accepts env bs ao (ei,ty,tv,asz,msz) v ==> val_wf tv v
Proof
  simp_tac (srw_ss()) [abi_tuple_rows_schema_def, abi_tuple_row_accepts_def] >>
  strip_tac >> irule abi_decode_source_accepts_wf >>
  simp[abi_decode_source_accepts_def] >> metis_tac[]
QED

Theorem abi_tuple_rows_accept_length:
  !rows env bs ao vs.
    abi_tuple_rows_accept env bs ao rows vs ==> LENGTH vs = LENGTH rows
Proof
  Induct >- simp[abi_tuple_rows_accept_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_rows_accept_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_tuple_rows_accept_indexed:
  !rows env bs ao vs.
  abi_tuple_rows_accept env bs ao rows vs <=>
    LENGTH vs = LENGTH rows /\
    (!i. i < LENGTH rows ==>
      abi_tuple_row_accepts env bs
        (abi_tuple_row_cursor abi_tuple_row_abi_width rows ao i) (EL i rows) (EL i vs))
Proof
  Induct >- simp[abi_tuple_rows_accept_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> Cases_on `vs`
  >- simp[abi_tuple_rows_accept_def] >>
  simp_tac bool_ss [abi_tuple_rows_accept_def] >>
  asm_simp_tac (srw_ss()) [] >>
  eq_tac
  >- (strip_tac >> conj_tac >- simp[] >>
      gen_tac >> strip_tac >> Cases_on `i` >>
      gvs[abi_tuple_row_abi_width_def]) >>
  strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  asm_simp_tac bool_ss [] >>
  gen_tac >> strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp[abi_tuple_row_abi_width_def]
QED

Theorem abi_tuple_rows_schema_member:
  abi_tuple_rows_schema ce env rows /\ i < LENGTH rows ==>
  abi_tuple_rows_schema ce env [EL i rows]
Proof
  simp[abi_tuple_rows_schema_def, EVERY_EL] >> metis_tac[]
QED

Theorem abi_tuple_rows_accept_values:
  abi_tuple_rows_schema ce env rows /\ abi_tuple_rows_accept env bs ao rows vs /\
  (!i. i < LENGTH rows ==>
    case EL i rows of (ei,ty,tv,asz,msz) =>
      val_in_memory tv (EL i vs)
        (d + abi_tuple_row_cursor abi_tuple_row_mem_width rows vo i) s.vs_memory) ==>
  abi_tuple_rows_values env bs ao vo d rows vs s
Proof
  simp_tac bool_ss [abi_tuple_rows_values_indexed, abi_tuple_rows_accept_indexed] >>
  strip_tac >> asm_simp_tac bool_ss [] >> gen_tac >> strip_tac >>
  `abi_tuple_rows_schema ce env [EL i rows]` by
    metis_tac[abi_tuple_rows_schema_member] >>
  Cases_on `EL i rows` >> PairCases_on `r` >>
  fs[abi_tuple_row_value_def] >>
  conj_tac
  >- (irule abi_tuple_row_accepts_wf >> metis_tac[]) >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[]
QED

Theorem abi_tuple_rows_values_memory:
  !rows env bs ao vo d vs s.
  abi_tuple_rows_schema ce env rows /\
  abi_tuple_rows_values env bs ao vo d rows vs s ==>
  tuple_in_memory vs (MAP (\(ei,ty,tv,asz,msz). tv) rows) (d+vo) s.vs_memory
Proof
  Induct >- simp[abi_tuple_rows_values_def, val_in_memory_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac (srw_ss()) [abi_tuple_rows_schema_def, abi_tuple_rows_values_def,
    abi_tuple_row_value_def] >> strip_tac >> gvs[] >>
  asm_simp_tac (srw_ss()) [val_in_memory_def, LET_THM, GSYM ADD_ASSOC] >>
  first_x_assum irule >>
  asm_simp_tac (srw_ss()) [abi_tuple_rows_schema_def, ADD_ASSOC] >>
  metis_tac[]
QED

Theorem abi_tuple_rows_accept_source:
  !rows env bs ao vs.
  abi_tuple_rows_schema ce env rows /\
  ao + SUM (MAP abi_tuple_row_abi_width rows) <= LENGTH bs ==>
  (abi_tuple_rows_accept env bs ao rows vs <=>
    vyper_decode_valid_enc_tuple
      (MAP (\(ei,ty,tv,asz,msz). vyper_to_abi_type env ty) rows) bs (DROP ao bs) /\
    abi_to_vyper_list env (MAP (\(ei,ty,tv,asz,msz). ty) rows)
      (abi_decode_members
        (MAP (\(ei,ty,tv,asz,msz). vyper_to_abi_type env ty) rows) bs (DROP ao bs)) = SOME vs)
Proof
  Induct
  >- simp[abi_tuple_rows_accept_def, Once vyper_decode_valid_enc_def,
          abi_decode_members_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac (srw_ss()) [abi_tuple_rows_schema_def, abi_tuple_row_abi_width_def] >>
  strip_tac >>
  `ao + abi_member_head_size (vyper_to_abi_type env h1) +
     SUM (MAP abi_tuple_row_abi_width rows) <= LENGTH bs` by fs[] >>
  `abi_member_head_size (vyper_to_abi_type env h1) <= LENGTH (DROP ao bs)` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  first_x_assum (qspecl_then [`env`, `bs`,
    `ao+abi_member_head_size (vyper_to_abi_type env h1)`] mp_tac) >>
  asm_simp_tac (srw_ss()) [abi_tuple_rows_schema_def] >> strip_tac >>
  simp_tac (srw_ss()) [abi_tuple_rows_accept_def, abi_tuple_valid_cons_iff,
    abi_decode_members_def, Once abi_to_vyper_def, abi_tuple_row_accepts_def,
    DROP_DROP_T, AC ADD_ASSOC ADD_COMM, LET_THM, AllCaseEqs()] >>
  qpat_x_assum `_ <= LENGTH (DROP ao bs)`
    (assume_tac o REWRITE_RULE [LENGTH_DROP]) >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED

Theorem abi_tuple_rows_tuple_source:
  abi_tuple_rows_schema ce env rows /\
  tys = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
  SUM (MAP abi_tuple_row_abi_width rows) <= LENGTH bs /\
  LENGTH rows < dimword(:256) ==>
  (abi_decode_source_accepts env (TupleT tys) bs (ArrayV (TupleV vs)) <=>
    abi_tuple_rows_accept env bs 0 rows vs)
Proof
  strip_tac >>
  drule abi_tuple_rows_accept_source >>
  disch_then (qspecl_then [`bs`, `0`, `vs`] mp_tac) >>
  simp_tac (srw_ss()) [abi_decode_source_accepts_def, Once vyper_decode_valid_enc_def,
    Once dec_def, abi_decode_members_value, vyper_to_abi_types_MAP,
    MAP_MAP_o, combinTheory.o_DEF, abi_to_vyper_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, AllCaseEqs()] >>
  `MAP (\x. vyper_to_abi_type env ((\(ei,ty,tv,asz,msz). ty) x)) rows =
    MAP (\(ei,ty,tv,asz,msz). vyper_to_abi_type env ty) rows` by
    (irule MAP_CONG >> simp[pairTheory.FORALL_PROD]) >>
  simp[]
QED

Theorem abi_tuple_rows_tuple_memory:
  abi_tuple_rows_schema ce env rows /\
  abi_tuple_rows_values env bs ao 0 d rows vs s ==>
  val_in_memory (TupleTV (MAP (\(ei,ty,tv,asz,msz). tv) rows))
    (ArrayV (TupleV vs)) d s.vs_memory
Proof
  strip_tac >> drule_all abi_tuple_rows_values_memory >>
  simp[val_in_memory_def]
QED

Theorem abi_tuple_rows_struct_source:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  abi_tuple_rows_schema ce (env \\ nsid) rows /\
  MAP SND args = MAP (\(ei,ty,tv,asz,msz). ty) rows /\
  SUM (MAP abi_tuple_row_abi_width rows) <= LENGTH bs /\
  LENGTH rows < dimword(:256) ==>
  (abi_decode_source_accepts env (StructT nsid) bs (StructV fields) <=>
    ?vs. abi_tuple_rows_accept (env \\ nsid) bs 0 rows vs /\
      fields = ZIP (MAP FST args,vs))
Proof
  strip_tac >>
  drule abi_tuple_rows_accept_source >>
  disch_then (qspecl_then [`bs`, `0`] mp_tac) >>
  asm_simp_tac (srw_ss()) [abi_decode_source_accepts_def, Once vyper_decode_valid_enc_def,
    Once dec_def, abi_decode_members_value, vyper_to_abi_types_MAP,
    MAP_MAP_o, combinTheory.o_DEF, abi_to_vyper_def] >>
  `MAP (\x. vyper_to_abi_type (env \\ nsid) ((\(ei,ty,tv,asz,msz). ty) x)) rows =
    MAP (\(ei,ty,tv,asz,msz). vyper_to_abi_type (env \\ nsid) ty) rows` by
    (irule MAP_CONG >> simp[pairTheory.FORALL_PROD]) >>
  `LENGTH args = LENGTH rows` by metis_tac[LENGTH_MAP] >>
  `MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args) =
    MAP (\(ei,ty,tv,asz,msz). vyper_to_abi_type (env \\ nsid) ty) rows` by
    (asm_simp_tac bool_ss [] >>
     simp[MAP_MAP_o, combinTheory.o_DEF]) >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem abi_tuple_rows_struct_memory:
  !rows names env bs ao vo d vs s.
  abi_tuple_rows_schema ce env rows /\ LENGTH names = LENGTH rows /\
  abi_tuple_rows_values env bs ao vo d rows vs s ==>
  val_in_memory (StructTV (ZIP (names,MAP (\(ei,ty,tv,asz,msz). tv) rows)))
    (StructV (ZIP (names,vs))) (d+vo) s.vs_memory
Proof
  Induct >- simp[abi_tuple_rows_values_def, val_in_memory_def] >>
  gen_tac >> PairCases_on `h` >> Cases_on `names`
  >- simp[] >> rpt gen_tac >>
  simp_tac (srw_ss()) [abi_tuple_rows_schema_def, abi_tuple_rows_values_def,
    abi_tuple_row_value_def] >> strip_tac >> gvs[] >>
  asm_simp_tac (srw_ss()) [val_in_memory_def, LET_THM, GSYM ADD_ASSOC] >>
  rewrite_tac[GSYM val_in_memory_struct] >>
  first_x_assum irule >>
  asm_simp_tac (srw_ss()) [abi_tuple_rows_schema_def, ADD_ASSOC] >>
  metis_tac[]
QED
