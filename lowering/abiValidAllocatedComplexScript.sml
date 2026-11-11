(* Successful complex head guard over allocation-backed resources. *)
Theory abiValidAllocatedComplex
Ancestors
  abiValidAllocatedMembers abiValidAllocatedContract abiValidAllocatedMemberFold
  abiDecoderComplexExecute abiDecoderComplexGuard abiDecoderComplexHead
  abiMalformedConstructorContract abiMalformedRecursiveInterface abiMalformedSiteFrame
  abiDecoderSequenceReach abiDecoderReentry abiDecoderReentryPointer
  abiDecoderContract abiDecoderTypedCompose abiDecoderLoop abiDecoderDynamicLoopSetup
  exprLoweringProps exprSimDefs compileEnv venomState venomInst instIdxIndep
  emitHelperProps freshWrites words list arithmetic pred_set
  abiDecoderCoherence abiDecoderMemberInfos abiDecodeRanges abiEncoder vyperABI valueEncoding
  abiMalformedMemberSetup

Theorem abi_valid_allocated_complex_guard:
  abi_decode_complex_head_guard src hi H st = ((),middle) /\
  fn_has_code st middle func /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d n s /\
  p + H <= L /\ middle.cs_next_var <= ceiling.cs_next_var /\
  fresh_vars_wrt ceiling s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. abi_decode_sim ctx func s t /\
    fresh_vars_wrt ceiling t /\ ~t.vs_halted /\
    t.vs_current_bb = middle.cs_current_bb /\
    t.vs_inst_idx = LENGTH middle.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t
Proof
  strip_tac >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  `L < dimword (:256)` by
    (fs[abi_malformed_allocated_window_def] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var hi` by fs[] >>
  drule abi_decoder_complex_guard_reentry >>
  disch_then (qspecl_then [`p`, `ceiling`, `s`] mp_tac) >>
  (impl_tac >- (simp[] >> qexists_tac `L` >> simp[])) >> strip_tac >>
  drule abi_malformed_complex_guard_writes >> strip_tac >>
  drule_all abi_malformed_read_sequence_frame >> strip_tac >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s actual` by
    (irule abi_malformed_read_sequence_resource >>
     simp[] >> qexists_tac `emitted_insts st middle` >> simp[]) >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st middle)` by
    (fs[EVERY_MEM] >> metis_tac[fresh_write_op_simple, abi_decode_source_opcode_def,
                              is_terminator_def]) >>
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  fs[abi_decoder_address_frame_def, fresh_vars_wrt_def,
     abi_malformed_resource_post_def, stmt_state_rel_inst_idx, eval_op_inst_idx] >>
  qpat_x_assum `actual = _` SUBST_ALL_TAC >> simp[]
QED

Theorem abi_valid_allocated_complex_members_entry:
  abi_decode_complex_head_guard src hi H st = ((),middle) /\
  compile_abi_decode_complex_elems dst src MLOAD base_op hi
    (abi_decoder_member_infos sf ce tys) 0 0 middle = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  abi_malformed_entry ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    base_op hi src dst B L xs p d n s /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  type_memory_size_list tvs <= n /\ p + H <= L /\
  p + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <= L /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs) /\
  abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs)) = SOME vs /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. abi_decode_sim ctx func s t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s t /\
    abi_valid_allocated_members_entry ce env sf tys tvs vs ctx func cenv cx es
      middle en base_op hi src dst B L xs p d n 0 0 dstid live ceiling t
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_complex_code >> strip_tac >>
  `middle.cs_next_var <= ceiling.cs_next_var` by decide_tac >>
  drule_all abi_valid_allocated_complex_guard >> strip_tac >>
  `abi_malformed_scratch_sites middle en func SUBSET
   abi_malformed_scratch_sites st en func` by
    (irule abi_malformed_scratch_sites_nested >> decide_tac) >>
  `local_ptrs_reserved cenv middle` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
     fs[abi_malformed_entry_def]) >>
  `EVERY (abi_decoder_operand_live middle.cs_next_var) [base_op;hi;src;dst]` by
    (fs[abi_malformed_entry_def, EVERY_MEM] >> rpt strip_tac >>
     irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_malformed_entry ctx func cenv cx es middle
    (abi_malformed_scratch_sites middle en func) dstid live
    base_op hi src dst B L xs p d n t` by
    (drule_all abi_malformed_aggregate_reentry >> simp[]) >>
  qexists_tac `t` >> simp[abi_valid_allocated_members_entry_def]
QED

Theorem abi_valid_allocated_complex_members_post:
  st.cs_next_var <= middle.cs_next_var /\
  st.cs_next_id <= middle.cs_next_id /\ middle.cs_next_id <= en.cs_next_id /\
  abi_decode_sim ctx func s u /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
    (abi_malformed_scratch_sites st en func) dstid s u /\
  abi_valid_allocated_members_post tvs vs ctx func cenv cx es middle en ceiling dstid
    d n u t ==>
  abi_valid_allocated_members_post tvs vs ctx func cenv cx es st en ceiling dstid
    d n s t
Proof
  strip_tac >>
  qhdtm_assum `abi_valid_allocated_members_post`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_members_post_def]) >>
  `abi_malformed_scratch_sites middle en func SUBSET
   abi_malformed_scratch_sites st en func` by
    (irule abi_malformed_scratch_sites_nested >> decide_tac) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
    (abi_malformed_scratch_sites st en func) dstid u t` by
    (irule abi_malformed_resource_weaken >>
     qexistsl_tac [`middle.cs_next_var`, `abi_malformed_scratch_sites middle en func`] >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
    (abi_malformed_scratch_sites st en func) dstid s t` by
    metis_tac[abi_malformed_resource_trans] >>
  `abi_decode_sim ctx func s t` by metis_tac[abi_decode_sim_trans] >>
  `abi_valid_allocated_frame (abi_malformed_scratch_sites st en func) d n u t` by
    (irule abi_valid_allocated_frame_weaken >>
     qexistsl_tac [`d`, `abi_malformed_scratch_sites middle en func`, `n`] >> simp[]) >>
  `abi_valid_allocated_frame (abi_malformed_scratch_sites st en func) d n s t` by
    (qpat_assum `abi_valid_allocated_frame _ d n u t` mp_tac >>
     qpat_assum `u.vs_memory = s.vs_memory` mp_tac >>
     qpat_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
     qpat_assum `u.vs_alloca_next = s.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abi_valid_allocated_frame_def, abi_malformed_site_range_def]) >>
  simp[abi_valid_allocated_members_post_def] >> metis_tac[]
QED

Theorem abi_valid_allocated_complex_members:
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecComplex dyn (abi_decoder_member_infos sf ce tys)) st = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  abi_malformed_entry ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    base_op hi src dst B L xs p d (type_memory_size_list tvs) s /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  abi_valid_allocated_members_contract ce env sf tys tvs /\ p <= L /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs) /\
  abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs)) = SOME vs /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. abi_valid_allocated_members_post tvs vs ctx func cenv cx es st en ceiling dstid
    d (type_memory_size_list tvs) s t
Proof
  strip_tac >> drule abi_decoder_complex_trace >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_complex_code >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `LENGTH xs = L` by
    (fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >>
     qpat_x_assum `mem_bytes_at B L s.vs_memory = xs`
       (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `p + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <= L` by
    (drule abiValidMembersTheory.abi_valid_members_view >> simp[LENGTH_DROP] >> decide_tac) >>
  `type_memory_size_list tvs <= type_memory_size_list tvs` by simp[] >>
  `p + FOLDR (\(_,asz,_) acc. asz + acc) 0
      (abi_decoder_member_infos sf ce tys) <= L` by simp[] >>
  drule_all abi_valid_allocated_complex_members_entry >> strip_tac >>
  qhdtm_x_assum `abi_valid_allocated_members_contract`
    (mp_tac o PURE_REWRITE_RULE [abi_valid_allocated_members_contract_def]) >>
  disch_then drule >> strip_tac >>
  qexists_tac `t'` >>
  irule abi_valid_allocated_complex_members_post >>
  qexistsl_tac [`middle`, `t`] >> gvs[]
QED
