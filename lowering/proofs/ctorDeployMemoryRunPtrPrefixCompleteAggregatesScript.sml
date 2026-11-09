(* Aggregate closure preserves the complete member endpoint verbatim. *)
Theory ctorDeployMemoryRunPtrPrefixCompleteAggregates
Ancestors
  ctorDeployMemoryRunPtrPrefixCompleteCode
  ctorDeployMemoryRunPtrPrefixRecursive
  abiDecoderFixedInputs abiDecoderFixedMemory abiDecoderMemberInfos
  abiDecoderComplexExecute abiDecoderComplexHead abiDecoderMembers abiCanonicalHeadSize
  compileEnv exprLowering rich_list valueEncoding valueEncodingProps vyperABI vyperTypeABI
  abiDecoderTypedContract abiDecoderContract abiDecoderTupleInputs abiDecoderStruct valueEncodingTyping
  abiStaticDynarrayLayout vyperTyping arithmetic list

val CshiftCode = ``\ty tv.
 !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
  G tn b sz Ddead lo PG.
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
   (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst) initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb.
    lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
 lo <= initial.vs_alloca_next /\ lo <= d ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\
 DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
    val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
                           op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_tuple_complete_code_contract:
  LIST_REL (^CshiftCode) tys tvs ==>
    (^CshiftCode) (TupleT tys) (TupleTV tvs)
Proof
  strip_tac >> drule prefix_members_complete_code >>
  disch_then (mk_asm "members") >>
  qpat_x_assum `LIST_REL _ tys tvs` kall_tac >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_to_vyper env (TupleT tys) av = SOME v` by
    fs[abi_decoder_metadata_def] >>
  drule abi_decoder_tuple_values >> strip_tac >>
  qpat_x_assum `av = ListV _` SUBST_ALL_TAC >>
  qpat_x_assum `v = ArrayV _` SUBST_ALL_TAC >>
  drule_all abi_decoder_tuple_members >> strip_tac >>
  `type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys)` by
    (simp[Once type_memory_bytes_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  `vyper_to_abi_type env (TupleT tys) = Tuple (MAP (vyper_to_abi_type env) tys)` by
    simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
  drule abi_decoder_complex_trace >> strip_tac >>
  qpat_x_assum `abi_decode_complex_head_guard _ _ _ _ = _`
    (SUBST_ALL_TAC o SYM o SIMP_RULE (srw_ss()) [abi_decode_complex_head_guard_def, comp_return_def]) >>
  asm_x "members" (mp_tac o SIMP_RULE bool_ss [MAP, SUM, APPEND, ADD_CLAUSES] o
    Q.INST [`final` |-> `st'`, `pretys` |-> `[]`, `pretvs` |-> `[]`,
      `preavs` |-> `[]`, `prevs` |-> `[]`] o SPEC_ALL o BETA_RULE) >>
  (impl_tac >- (asm_simp_tac bool_ss [Once abi_decoder_members_def] >>
    gvs[Excl "enc_def"] >> metis_tac[])) >>
  strip_tac >> qexistsl_tac [`actual`,`H`,`qt`,`B`] >>
  asm_simp_tac bool_ss [val_in_memory_tuple]
QED

val CshiftCode_desc =
  ``(\env sf. ^CshiftCode) (env \\ nsid) (sf \\ nsid_to_string nsid)``;

Theorem prefix_struct_complete_code_contract:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (^CshiftCode_desc) (MAP SND args) tvs ==>
  (^CshiftCode) (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH tvs = LENGTH args` by (drule LIST_REL_LENGTH >> simp[]) >>
  qpat_x_assum `LIST_REL _ _ _` (assume_tac o BETA_RULE) >>
  drule (Q.INST [`env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`]
    prefix_members_complete_code) >>
  disch_then (mk_asm "members") >>
  qpat_x_assum `LIST_REL _ _ _` kall_tac >>
  BETA_TAC >> rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_to_vyper env (StructT nsid) av = SOME v` by fs[abi_decoder_metadata_def] >>
  drule abi_decoder_struct_values >> strip_tac >>
  qpat_x_assum `av = ListV _` SUBST_ALL_TAC >>
  qpat_x_assum `v = StructV _` SUBST_ALL_TAC >>
  drule_all abi_decoder_struct_members_at >> strip_tac >>
  drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> simp[]) >>
  `type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args))` by
    fs[abi_decoder_metadata_def, Once type_memory_size_def, Excl "enc_def"] >>
  drule_all abi_decoder_struct_field_types >> strip_tac >>
  drule abi_decoder_struct_infos >> strip_tac >>
  `vyper_to_abi_type env (StructT nsid) =
    Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))` by
    simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  drule abi_decoder_complex_trace >> strip_tac >>
  qpat_x_assum `abi_decode_complex_head_guard _ _ _ _ = _`
    (SUBST_ALL_TAC o SYM o SIMP_RULE (srw_ss()) [abi_decode_complex_head_guard_def, comp_return_def]) >>
  asm_x "members" (mp_tac o SIMP_RULE bool_ss [MAP, SUM, APPEND, ADD_CLAUSES] o
    Q.INST [`final` |-> `st'`, `pretys` |-> `[]`, `pretvs` |-> `[]`,
      `preavs` |-> `[]`, `prevs` |-> `[]`,
      `vs` |-> `MAP SND (fields:(string # value) list)`] o SPEC_ALL o BETA_RULE) >>
  (impl_tac >- (asm_simp_tac bool_ss [Once abi_decoder_members_def] >>
    gvs[Excl "enc_def"] >> metis_tac[])) >>
  strip_tac >>
  `!mem. tuple_in_memory (MAP SND fields) tvs d mem ==>
     fields_in_memory fields (ZIP (MAP FST args,tvs)) d mem` by
    (rpt strip_tac >> irule static_fields_memory_zip >>
     fs[abi_decoder_metadata_def, Once value_has_type_def]) >>
  qexistsl_tac [`actual`,`H`,`qt`,`B`] >>
  asm_simp_tac bool_ss [val_in_memory_struct] >>
  metis_tac[]
QED

Theorem prefix_fixed_array_complete_code_contract:
  (^CshiftCode) ty tv ==>
  (^CshiftCode) (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
  strip_tac >>
  `!count. LIST_REL (^CshiftCode) (REPLICATE count ty)
     (REPLICATE count tv)` by
    (gen_tac >> simp_tac bool_ss [LIST_REL_REPLICATE_same] >>
     BETA_TAC >> strip_tac >> first_assum (ACCEPT_TAC o BETA_RULE)) >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_fixed_array_values >> strip_tac >>
  gnvs[Once vyper_to_abi_type_def, canonical_array_tuple, Excl "enc_def"] >>
  qpat_assum `LENGTH vs = LENGTH avs`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]) >> assume_tac th) >>
  `type_memory_bytes ce (ArrayT ty (Fixed (LENGTH vs))) =
     LENGTH vs * type_memory_bytes ce ty` by simp[Once type_memory_bytes_def] >>
  qpat_assum `type_memory_bytes ce (ArrayT ty (Fixed (LENGTH vs))) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `LIST_REL (^CshiftCode) (REPLICATE (LENGTH vs) ty)
     (REPLICATE (LENGTH vs) tv)` by
    (qpat_x_assum `!k. LIST_REL _ _ _`
       (qspec_then `LENGTH vs` mp_tac) >> simp[]) >>
  drule prefix_members_complete_code >> disch_then (mk_asm "members") >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
  drule abi_decoder_complex_trace >> strip_tac >>
  qpat_x_assum `abi_decode_complex_head_guard _ _ _ _ = _`
    (SUBST_ALL_TAC o SYM o SIMP_RULE (srw_ss())
      [abi_decode_complex_head_guard_def, comp_return_def]) >>
  asm_x "members" (mp_tac o SIMP_RULE bool_ss
    [MAP, SUM, APPEND, ADD_CLAUSES, map_replicate, SUM_REPLICATE] o
    Q.INST [`final` |-> `st'`, `pretys` |-> `[]`, `pretvs` |-> `[]`,
      `preavs` |-> `[]`, `prevs` |-> `[]`, `vs'` |-> `vs`] o SPEC_ALL o BETA_RULE) >>
  (impl_tac >- (asm_simp_tac bool_ss [Once abi_decoder_members_def] >>
    gvs[Excl "enc_def"] >> first_assum ACCEPT_TAC)) >>
  strip_tac >> qexistsl_tac [`actual`,`H`,`qt`,`B`] >>
  qpat_x_assum `LENGTH vs = LENGTH avs` (fn th => rewrite_tac[GSYM th]) >>
  asm_simp_tac bool_ss [Once type_memory_bytes_def] >>
  conj_tac >- (irule abi_decoder_fixed_array_memory >> simp[]) >>
  conj_tac >- simp[Once type_memory_bytes_def] >>
  rpt strip_tac >> irule abi_decoder_fixed_array_memory >> simp[]
QED
