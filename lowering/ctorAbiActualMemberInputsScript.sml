Theory ctorAbiActualMemberInputs
Ancestors
  ctorAbiActualMemberBoundary abiDecoderMemberBody abiDecoderMembers
  abiDecoderDynamicLoopSetup abiDecoderContract abiDecoderReentry
  abiDecoderReentryAddress abiDecoderReentryPointer abiDecoderTypedContract
  abiEncoder abiCanonicalHeadSize abiDecodeRanges compileEnv loweringStateRelDefs valueEncoding
  contractABI words list rich_list arithmetic

Theorem ctor_actual_member_child_inputs:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))) <= h /\ h < dimword (:256)) /\
  abi_decoder_address_frame st.cs_next_var initial prepared /\
  abi_decoder_operand_live st.cs_next_var hi /\ st.cs_next_var <= middle.cs_next_var /\
  eval_operand childsrc prepared = SOME (n2w (sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs) (LENGTH pretys))) /\
  eval_operand childdst prepared = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var childdst /\
  D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) <= D+N ==>
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  mem_bytes_at (sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
      (preavs ++ av::avs) (LENGTH pretys)) (LENGTH (enc (vyper_to_abi_type env ty) av))
      prepared.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
    (preavs ++ av::avs) (LENGTH pretys) + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi prepared = SOME (n2w h) /\
    sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
      (preavs ++ av::avs) (LENGTH pretys) + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\
    h < dimword (:256)) /\
  (!x. childsrc = Var x \/ childdst = Var x \/ hi = Var x ==> not_fresh_at middle x) /\
  D <= d + SUM (MAP (type_memory_bytes ce) pretys) /\
  d + SUM (MAP (type_memory_bytes ce) pretys) + type_memory_bytes ce ty <= D+N
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac abi_decoder_members_child_facts >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `DLOAD`, `s` |-> `initial:venom_state`]
    abi_decoder_member_source) >>
  (impl_tac >- gvs[abi_decode_source_def, MAP_APPEND, APPEND_ASSOC, Excl "enc_def"]) >> strip_tac >>
  `abi_decoder_operand_live middle.cs_next_var hi` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `prepared.vs_data_section = initial.vs_data_section` by
    gvs[abi_decoder_address_frame_def] >>
  qpat_x_assum `LENGTH pretys = LENGTH preavs` kall_tac >>
  asm_simp_tac bool_ss [] >> rpt conj_tac
  >- gvs[abi_decode_source_def, Excl "enc_def"]
  >- decide_tac
  >- (Cases_on `hi = Lit 0w` >- asm_simp_tac bool_ss [] >>
      qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
      `eval_operand hi prepared = SOME (n2w h)` by
        (gvs[abi_decoder_address_frame_def] >> metis_tac[]) >>
      qexists `h` >> asm_simp_tac bool_ss [] >> decide_tac)
  >- (rpt strip_tac >> gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
        not_fresh_at_def] >> metis_tac[])
  >- decide_tac >> decide_tac
QED

Theorem ctor_actual_member_inline_guard:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))) <= h /\ h < dimword (:256)) /\
  abi_decoder_address_frame st.cs_next_var initial prepared /\
  abi_decoder_operand_live st.cs_next_var hi ==>
  hi = Lit 0w \/ ?h. eval_operand hi prepared = SOME (n2w h) /\
    sb + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)) <= h /\
    h < dimword (:256)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac abi_decoder_members_child_facts >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  drule canonical_tuple_length >> disch_then assume_tac >>
  `SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)) <=
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs)))` by
    (asm_simp_tac bool_ss [] >> simp[MAP_APPEND, SUM_APPEND, Excl "enc_def"]) >>
  irule abi_decoder_address_frame_guard >>
  qexistsl [`st.cs_next_var`, `initial`] >> asm_simp_tac bool_ss [] >>
  Cases_on `hi = Lit 0w` >- asm_simp_tac bool_ss [] >>
  qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
  qexists `h` >> asm_simp_tac bool_ss [] >> decide_tac
QED
