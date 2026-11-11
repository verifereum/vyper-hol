(* Entry boundaries for successful allocation-backed member traversal. *)
Theory abiValidAllocatedMemberEntry
Ancestors
  abiValidAllocatedNavigate abiValidAllocatedMembers abiValidAllocatedSource
  abiValidAllocatedMemberSetup
  abiDecoderSequenceReach abiDecoderMemberCode exprSimDefs
  abiDecoderTypedCompose fragExec abiValidAllocatedContract abiMalformedMemberSetup
  exprLoweringProps instIdxIndep
  abiDecoderMemberCons abiDecoderMemberSetup abiDecoderCoherence abiDecoderContract
  abiMalformedRecursiveInterface abiMalformedMembers abiDecoderMemberInfos
  abiEncoder compileEnv loweringStateRelDefs venomState vyperABI contractABI valueEncoding
  words list rich_list arithmetic pred_set abiDecodeRanges abiValidMembers

Theorem abi_valid_allocated_members_head_entry:
  abi_valid_allocated_members_entry ce env sf (ty::tys) (tv::tvs) vs
    ctx func cenv cx es st en base_op hi src dst B L xs p d outsz ao vo dstid live ceiling s /\
  abi_decode_member_setup dst src MLOAD base_op hi
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  compile_abi_decode_complex_elems dst src MLOAD base_op hi
    (abi_decoder_member_infos sf ce tys)
    (ao + abi_embedded_static_size ce.ce_struct_fields ty)
    (vo + type_memory_bytes ce ty) end_st = ((),en) ==>
  ?v rest t. vs = v::rest /\
    abi_to_vyper_list env tys
      (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs)
        (DROP (abi_member_head_size (vyper_to_abi_type env ty)) (DROP (p+ao) xs))) = SOME rest /\
    abi_decode_sim ctx func s t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    abi_valid_allocated_entry ce env sf ty tv v ctx func cenv cx es middle end_st
      base_op hi (FST ops) (SND ops) B L xs
      (p + if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
           then abi_head_word (DROP (p+ao) xs) else ao)
      (d+vo) dstid live ceiling t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s t
Proof
  strip_tac >>
  qhdtm_assum `abi_valid_allocated_members_entry`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_members_entry_def]) >>
  fs[LIST_REL_CONS1] >>
  drule (SIMP_RULE bool_ss [MAP] abi_valid_source_cons_values) >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `LENGTH xs = L` by
    (fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >>
     qpat_x_assum `mem_bytes_at B L s.vs_memory = xs`
       (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `p+ao+abi_member_head_size (vyper_to_abi_type env ty) <= L /\
   vo+type_memory_bytes ce ty <= outsz /\ middle.cs_next_var <= ceiling.cs_next_var` by
    (fs[abi_decoder_header_def, type_memory_size_def] >> decide_tac) >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP p xs) (DROP (p+ao) xs))` by
    (Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     fs[vyper_decode_valid_enc_def, abi_decode_member_bytes_def, abi_head_word_def,
        dec_number_def, dest_NumV_def]) >>
  drule_all abi_valid_allocated_member_navigate >> strip_tac >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `inst_extends st middle` by
    (irule abi_decoder_inst_extends_prefix >> simp[]) >>
  `fn_has_code st middle func` by
    metis_tac[fn_has_code_split] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st middle)` by fs[EVERY_MEM] >>
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `abi_malformed_entry ctx func cenv cx es middle _ _ _ _ _ _ _ _ _ _ q _ _ t` >>
  `q <= L /\ vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP q xs) /\
   (is_dynamic (vyper_to_abi_type env ty) \/ q + static_length (vyper_to_abi_type env ty) <= L) /\
   dec (vyper_to_abi_type env ty)
     (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP p xs) (DROP (p+ao) xs)) =
   dec (vyper_to_abi_type env ty) (DROP q xs)` by
    (irule abi_valid_source_member_position >> simp[Abbr `q`] >> metis_tac[]) >>
  `abi_malformed_scratch_sites middle end_st func SUBSET
   abi_malformed_scratch_sites st en func` by
    (irule abi_malformed_scratch_sites_nested >> decide_tac) >>
  qexistsl_tac [`v`, `rest`, `t'`] >> simp[] >>
  qpat_x_assum `t' = _` SUBST_ALL_TAC >>
  `fn_has_code middle end_st func` by metis_tac[fn_has_code_split] >>
  drule_all abi_valid_allocated_member_setup_frame >>
  disch_then (qspecl_then [`{}`, `0`, `0`] strip_assume_tac) >>
  `ao+p = p+ao` by decide_tac >>
  fs[Abbr `q`] >>
  simp[abi_valid_allocated_entry_def, fresh_vars_wrt_def] >>
  fs[abi_malformed_entry_def, abi_malformed_resource_post_def,
     abi_malformed_allocated_window_def, abi_malformed_destination_def,
     stmt_state_rel_inst_idx, eval_op_inst_idx, fresh_vars_wrt_def,
     SUBSET_DEF] >>
  rpt conj_tac
  >- metis_tac[]
  >- metis_tac[]
  >- (qexistsl_tac [`inst`, `q`] >> simp[]) >>
  metis_tac[]
QED

Theorem abi_valid_allocated_members_tail_entry:
  abi_valid_allocated_members_entry ce env sf (ty::tys) (tv::tvs) (v::rest)
    ctx func cenv cx es st en base_op hi src dst B L xs p d outsz ao vo dstid live ceiling s /\
  abi_decode_member_setup dst src MLOAD base_op hi
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  compile_abi_decode_complex_elems dst src MLOAD base_op hi
    (abi_decoder_member_infos sf ce tys)
    (ao + abi_embedded_static_size ce.ce_struct_fields ty)
    (vo + type_memory_bytes ce ty) end_st = ((),en) /\
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
    (abi_malformed_scratch_sites st en func) dstid s u /\
  abi_valid_allocated_post tv v ctx func cenv cx es middle end_st ceiling dstid
    (d+vo) (type_memory_bytes ce ty) u t ==>
  abi_valid_allocated_members_entry ce env sf tys tvs rest
    ctx func cenv cx es end_st en base_op hi src dst B L xs p d outsz
    (ao + abi_embedded_static_size ce.ce_struct_fields ty)
    (vo + type_memory_bytes ce ty) dstid live ceiling t
Proof
  strip_tac >>
  qhdtm_assum `abi_valid_allocated_members_entry`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_members_entry_def]) >>
  qhdtm_assum `abi_valid_allocated_post`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_post_def]) >>
  fs[LIST_REL_CONS1] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `abi_malformed_scratch_sites middle end_st func SUBSET
   abi_malformed_scratch_sites st en func /\
   abi_malformed_scratch_sites end_st en func SUBSET
   abi_malformed_scratch_sites st en func` by
    (conj_tac >> irule abi_malformed_scratch_sites_nested >> decide_tac) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
    (abi_malformed_scratch_sites st en func) dstid u t` by
    (irule abi_malformed_resource_weaken >>
     qexistsl_tac [`middle.cs_next_var`, `abi_malformed_scratch_sites middle end_st func`] >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
    (abi_malformed_scratch_sites st en func) dstid s t` by
    (irule abi_malformed_resource_trans >> qexists_tac `u` >> simp[]) >>
  `local_ptrs_reserved cenv end_st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
     fs[abi_malformed_entry_def] >> decide_tac) >>
  `abi_malformed_entry ctx func cenv cx es end_st
    (abi_malformed_scratch_sites end_st en func) dstid live
    base_op hi src dst B L xs p d outsz t` by
    (irule abi_malformed_aggregate_reentry >>
     simp[] >> qexistsl_tac [`s`, `abi_malformed_scratch_sites st en func`, `st`] >>
     simp[] >> decide_tac) >>
  drule abi_decoder_coherent_header >> strip_tac >>
  drule (SIMP_RULE bool_ss [MAP] abi_valid_source_cons_values) >> strip_tac >>
  fs[abi_decoder_header_def, type_memory_size_def] >>
  `abi_member_head_size (vyper_to_abi_type env ty) + (ao+p) =
   ao + (p + abi_member_head_size (vyper_to_abi_type env ty))` by decide_tac >>
  fs[DROP_DROP] >>
  simp[abi_valid_allocated_members_entry_def] >>
  `!n. n+(ao+p) = ao+(p+n)` by decide_tac >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
  fs[vyper_decode_valid_enc_def, abi_member_head_size_def,
     abi_decoder_header_def] >>
  gvs[DROP_DROP_T]
QED
