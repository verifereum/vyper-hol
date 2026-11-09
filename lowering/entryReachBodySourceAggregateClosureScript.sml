(* One member-result adapter for all source aggregate constructors. *)
Theory entryReachBodySourceAggregateClosure
Ancestors
  valueEncodingDefs entryReachBodySourceMemberExecution entryReachBodySourceAggregateInputs
  entryReachBodySourceProducer entryReachBodySourceMemberEntry
  entryReachBodyCanonicalMembers entryReachBodyCanonicalArrayChild
  calldataRecursiveProducers abiDecoderMembers abiDecoderCoherence
  abiDecoderTypedContract abiDecoderMemberInfos valueEncodingProps valueEncoding
  vyperABI vyperTyping vyperValue contractABI exprLowering compileEnv
  abiEncoder abiDecoderFixedInputs abiDecoderFixedMemory list rich_list
  valueEncodingProofs abiCanonicalHeadSize abiDecoderStruct valueEncodingTyping
  abiStaticDynarrayLayout

Theorem source_complex_result[local]:
  (last.cs_current_insts = [] ==> !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  entry_source_members ce env sf tys tvs avs vs /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (!i. i < LENGTH tys ==> entry_source_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ce env sf
    (EL i tys) (EL i tvs) (EL i avs) (EL i vs)
    ctx fn oid root extent ambient b cap site limit_st) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecComplex dyn (abi_decoder_member_infos sf ce tys)) st = ((),last) /\
  canonical_members_frame ctx fn oid root extent ambient b cap site limit_st
    dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) st s /\
  sb+LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) < dimword (:256) /\
  d+SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN ambient /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET ambient /\
  type_memory_size outtv = SUM (MAP (type_memory_bytes ce) tys) /\
  (!d mem. tuple_in_memory vs tvs d mem ==> val_in_memory outtv outv d mem) ==>
  ?t. array_child_result ctx fn oid root extent ambient
    (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
    b cap site limit_st st last d outtv outv s t
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [Once compile_abi_decode_to_buf_def, LET_THM]) >>
  `?t. tuple_in_memory vs tvs d t.vs_memory /\
    canonical_members_frame ctx fn oid root extent ambient b cap site limit_st
      dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) last t /\
    canonical_members_effect ctx fn ambient d (SUM (MAP (type_memory_bytes ce) tys)) st s t /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,SUM (MAP (type_memory_bytes ce) tys))] s t` by
    (irule (entry_source_certified_members_endpoint |> Q.INST
      [`cert` |-> `\z. z.cs_current_insts = [] ==> !bb.
        lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0`] |> SIMP_RULE bool_ss []) >>
     asm_rewrite_tac[] >> conj_tac
     >- metis_tac[calldata_member_tail_empty_exit_phi] >>
     conj_tac
     >- (qexistsl_tac [`avs`,`env`,`sf`] >> asm_rewrite_tac[]) >>
     qexists_tac `SUM (MAP (type_memory_bytes ce) tys)` >> asm_rewrite_tac[]) >>
  qexists_tac `t` >>
  gvs[canonical_members_effect_def, canonical_members_frame_def,
      array_child_result_def, Excl "enc_def"]
QED

Theorem entry_source_tuple_producer:
  abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs) /\
  (!i av v. i < LENGTH tys ==> entry_source_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (EL i tys) (EL i tvs) av v ctx fn oid root extent ambient b cap site limit_st) ==>
  entry_source_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (TupleT tys) (TupleTV tvs) pav pv ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> simp_tac bool_ss [entry_source_certified_child_producer_def] >>
  rpt gen_tac >> strip_tac >> rename1 `fn_has_code st last fn` >>
  drule_all entry_source_tuple_inputs >> strip_tac >> gvs[Excl "enc_def"] >>
  `canonical_members_frame ctx fn oid root extent ambient b cap site limit_st
    dst src sb cell (SUM (MAP (type_memory_bytes ce) tys)) st s` by
    (simp[canonical_members_frame_def] >> gvs[Excl "enc_def"]) >>
  `cell+SUM (MAP (type_memory_bytes ce) tys) < dimword (:256)` by gvs[Excl "enc_def"] >>
  irule source_complex_result >> asm_rewrite_tac[] >>
  qexistsl_tac [`avs`,`ce`,`dst`,`EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`,
    `env`,`sb`,`sf`,`src`,`tvs`,`tys`,`vs`] >>
  simp[val_in_memory_tuple, Excl "enc_def"]
QED

Theorem entry_source_fixed_array_producer:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  (!av v. entry_source_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf ty tv av v ctx fn oid root extent ambient b cap site limit_st) ==>
  entry_source_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) pav pv
      ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> simp_tac bool_ss [entry_source_certified_child_producer_def] >>
  rpt gen_tac >> strip_tac >> rename1 `fn_has_code st last fn` >>
  drule_all entry_source_fixed_inputs >> strip_tac >>
  qpat_x_assum `pav = _` SUBST_ALL_TAC >> qpat_x_assum `pv = _` SUBST_ALL_TAC >>
  `canonical_members_frame ctx fn oid root extent ambient b cap site limit_st
    dst src sb cell (SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))) st s` by
    (simp[canonical_members_frame_def] >> gvs[Excl "enc_def"]) >>
  `cell+SUM (MAP (type_memory_bytes ce) (REPLICATE n ty)) < dimword (:256)` by
    gvs[Excl "enc_def"] >>
  irule source_complex_result >> asm_rewrite_tac[] >>
  qexistsl_tac [`avs`,`ce`,`dst`,`is_abi_dynamic ce.ce_struct_fields ty`,
    `env`,`sb`,`sf`,`src`,`REPLICATE n tv`,`REPLICATE n ty`,`vs`] >>
  fs[EL_REPLICATE, Excl "enc_def"]
QED

Theorem entry_source_struct_producer:
  FLOOKUP env nsid = SOME (StructArgs args) /\ LENGTH tvs = LENGTH args /\
  abi_decoder_coherent ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs))) /\
  (!i av v. i < LENGTH args ==> entry_source_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce (env \\ nsid) (sf \\ nsid_to_string nsid) (EL i (MAP SND args)) (EL i tvs) av v
      ctx fn oid root extent ambient b cap site limit_st) ==>
  entry_source_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs))) pav pv
      ctx fn oid root extent ambient b cap site limit_st
Proof
  strip_tac >> simp_tac bool_ss [entry_source_certified_child_producer_def] >>
  rpt gen_tac >> strip_tac >> rename1 `fn_has_code st last fn` >>
  drule_all entry_source_struct_inputs >> strip_tac >>
  `args' = args` by gvs[] >>
  `tvs' = tvs` by
    (qpat_x_assum `StructTV _ = StructTV _` mp_tac >>
     simp[] >> disch_then (mp_tac o AP_TERM ``MAP SND : (string # type_value) list -> type_value list``) >>
     fs[MAP_ZIP]) >>
  qpat_x_assum `args' = args` SUBST_ALL_TAC >>
  qpat_x_assum `tvs' = tvs` SUBST_ALL_TAC >>
  qpat_x_assum `pav = _` SUBST_ALL_TAC >> qpat_x_assum `pv = _` SUBST_ALL_TAC >>
  `canonical_members_frame ctx fn oid root extent ambient b cap site limit_st
    dst src sb cell (SUM (MAP (type_memory_bytes ce) (MAP SND args))) st s` by
    (simp[canonical_members_frame_def] >> gvs[Excl "enc_def"]) >>
  `cell+SUM (MAP (type_memory_bytes ce) (MAP SND args)) < dimword (:256)` by
    gvs[Excl "enc_def"] >>
  irule source_complex_result >> simp[Excl "enc_def"] >>
  qexistsl_tac [`avs`,`ce`,`dst`,`EXISTS (is_abi_dynamic ce.ce_struct_fields) (MAP SND args)`,
    `env \\ nsid`,`sb`,`sf \\ nsid_to_string nsid`,`src`,`tvs`,`MAP SND args`,`MAP SND vals`] >>
  fs[Excl "enc_def"]
QED
