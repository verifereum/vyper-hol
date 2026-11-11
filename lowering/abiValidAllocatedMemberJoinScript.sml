(* Composition of successful allocated member posts. *)
Theory abiValidAllocatedMemberJoin
Ancestors
  abiValidAllocatedMemberEntry abiValidAllocatedMemberSetup
  abiValidAllocatedMembers abiValidAllocatedContract abiValidAllocatedSource
  abiMalformedRecursiveInterface abiMalformedMemberSetup abiDecoderMemberCons
  abiMalformedSiteFrame
  abiDecoderCoherence abiDecoderContract abiDecoderLoop abiDecoderTypedCompose
  compileEnv venomState valueEncoding valueEncodingDefs valueEncodingProofs valueEncodingTyping
  vyperTypeABI exprSimDefs exprLoweringProps words list rich_list arithmetic pred_set

Theorem abi_valid_allocated_members_cons_post:
  abi_valid_allocated_members_entry ce env sf (ty::tys) (tv::tvs) (v::vs)
    ctx func cenv cx es st en base_op hi src dst B L xs p d outsz ao vo dstid live ceiling s /\
  abi_decode_member_setup dst src MLOAD base_op hi
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  compile_abi_decode_complex_elems dst src MLOAD base_op hi
    (abi_decoder_member_infos sf ce tys)
    (ao + abi_embedded_static_size ce.ce_struct_fields ty)
    (vo + type_memory_bytes ce ty) end_st = ((),en) /\
  abi_decode_sim ctx func s u /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
    (abi_malformed_scratch_sites st en func) dstid s u /\
  abi_valid_allocated_post tv v ctx func cenv cx es middle end_st ceiling dstid
    (d+vo) (type_memory_bytes ce ty) u t /\
  abi_valid_allocated_members_post tvs vs ctx func cenv cx es end_st en ceiling dstid
    (d+(vo+type_memory_bytes ce ty)) (type_memory_size_list tvs) t r ==>
  abi_valid_allocated_members_post (tv::tvs) (v::vs) ctx func cenv cx es st en ceiling dstid
    (d+vo) (type_memory_size_list (tv::tvs)) s r
Proof
  strip_tac >>
  qhdtm_assum `abi_valid_allocated_members_entry`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_members_entry_def]) >>
  qhdtm_assum `abi_valid_allocated_post`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_post_def]) >>
  qhdtm_assum `abi_valid_allocated_members_post`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_members_post_def]) >>
  fs[LIST_REL_CONS1] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  drule abi_decoder_coherent_header >> strip_tac >>
  drule (SIMP_RULE bool_ss [MAP] abi_valid_source_cons_values) >> strip_tac >>
  `val_wf tv v` by
    (irule (cj 1 value_has_type_val_wf) >>
     irule (cj 1 abi_to_vyper_well_typed) >>
     fs[abi_decoder_header_def] >> metis_tac[]) >>
  drule_all abi_valid_allocated_members_tail_entry >> strip_tac >>
  `alloca_inv t /\ s.vs_alloca_next <= t.vs_alloca_next /\
   t.vs_alloca_next <= r.vs_alloca_next` by
    fs[abi_malformed_resource_post_def, stmt_state_rel_def] >>
  `abi_malformed_destination func cenv es.scopes dstid (d+vo)
     (type_memory_size tv) t /\
   dstid NOTIN abi_malformed_scratch_sites end_st en func` by
    (fs[abi_valid_allocated_members_entry_def, abi_malformed_entry_def,
        abi_decoder_header_def] >>
     irule abi_malformed_destination_subrange >>
     qexistsl_tac [`d`, `outsz`] >> simp[] >> fs[type_memory_size_def] >> decide_tac) >>
  `mem_bytes_at (d+vo) (type_memory_size tv) r.vs_memory =
   mem_bytes_at (d+vo) (type_memory_size tv) t.vs_memory` by
    (irule abi_valid_allocated_frame_sibling >>
     simp[] >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`d+(vo+type_memory_bytes ce ty)`, `type_memory_size_list tvs`] >>
     fs[abi_decoder_header_def]) >>
  `val_in_memory tv v (d+vo) r.vs_memory` by
    (qpat_assum `val_in_memory tv v (d+vo) t.vs_memory`
       (mp_then Any mp_tac (cj 1 val_in_memory_mem_agree_proof)) >>
     disch_then irule >> simp[]) >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    fs[abi_decoder_header_def] >>
  `abi_decode_sim ctx func s r` by
    metis_tac[abi_decode_sim_trans] >>
  `abi_malformed_scratch_sites middle end_st func SUBSET
     abi_malformed_scratch_sites st en func /\
   abi_malformed_scratch_sites end_st en func SUBSET
     abi_malformed_scratch_sites st en func` by
    (simp[abi_malformed_scratch_sites_def, SUBSET_DEF] >> rpt strip_tac >>
     fs[] >> decide_tac) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
     (abi_malformed_scratch_sites st en func) dstid u t` by
    (irule abi_malformed_resource_weaken >>
     qexistsl_tac [`middle.cs_next_var`, `abi_malformed_scratch_sites middle end_st func`] >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
     (abi_malformed_scratch_sites st en func) dstid t r` by
    (irule abi_malformed_resource_weaken >>
     qexistsl_tac [`end_st.cs_next_var`, `abi_malformed_scratch_sites end_st en func`] >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
     (abi_malformed_scratch_sites st en func) dstid s r` by
    metis_tac[abi_malformed_resource_trans] >>
  `abi_valid_allocated_frame (abi_malformed_scratch_sites st en func)
     (d+vo) (type_memory_size tv+type_memory_size_list tvs) u t` by
    (irule abi_valid_allocated_frame_weaken >>
     qexistsl_tac [`d+vo`, `abi_malformed_scratch_sites middle end_st func`,
       `type_memory_bytes ce ty`] >> simp[]) >>
  `abi_valid_allocated_frame (abi_malformed_scratch_sites st en func)
     (d+vo) (type_memory_size tv+type_memory_size_list tvs) t r` by
    (irule abi_valid_allocated_frame_weaken >>
     qexistsl_tac [`d+(vo+type_memory_bytes ce ty)`, `abi_malformed_scratch_sites end_st en func`,
       `type_memory_size_list tvs`] >> simp[] >> decide_tac) >>
  `abi_valid_allocated_frame (abi_malformed_scratch_sites st en func)
     (d+vo) (type_memory_size tv+type_memory_size_list tvs) s t` by
    (qpat_assum `abi_valid_allocated_frame _ _ (type_memory_size tv + type_memory_size_list tvs) u t` mp_tac >>
     qpat_assum `u.vs_memory = s.vs_memory` mp_tac >>
     qpat_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
     qpat_assum `u.vs_alloca_next = s.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abi_valid_allocated_frame_def, abi_malformed_site_range_def]) >>
  `!id b sz. FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
     FLOOKUP s.vs_allocas id = SOME (b,sz) \/ s.vs_alloca_next <= b` by
    metis_tac[] >>
  `abi_valid_allocated_frame (abi_malformed_scratch_sites st en func)
     (d+vo) (type_memory_size tv+type_memory_size_list tvs) s r` by
    (irule abi_valid_allocated_frame_trans >> qexists_tac `t` >> simp[]) >>
  simp[abi_valid_allocated_members_post_def, val_in_memory_def,
       type_memory_size_def] >>
  conj_tac >- gvs[] >>
  rpt strip_tac >>
  qpat_x_assum `!id b sz. FLOOKUP r.vs_allocas id = _ ==> _` drule >>
  strip_tac >- metis_tac[] >> disj2_tac >> decide_tac
QED
