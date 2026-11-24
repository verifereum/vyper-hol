Theory createCtorEncoderWindowImmMods
Ancestors
  bodyFullPostsMods bodyInvSplit abiEncoderWindowPhase abiEncoderWindowContract
  abiEncoderRegisteredEffect exprSimAbiEncodeExecFrame stateRelProj
  exprSimProps exprLoweringProps loweringStateRelDefs loweringSlice valueEncodingProps
  venomState venomMemDefs finite_map pred_set list pair arithmetic

(* The owner encloses the explicit writes. Old scratch is separated by the
   input immutable frame; fresh scratch is beyond the input frontier. *)
Theorem ctor_immutable_owner_window[local]:
  abi_encoder_registered_effect ids outs s t /\ window_alloca_growth s t /\
  FLOOKUP s.vs_allocas shared = SOME (b,cap) /\
  EVERY (\(p,n). b <= p /\ p+n <= b+cap) outs /\
  q+k <= s.vs_alloca_next /\
  (!aid p n. aid IN shared INSERT ids /\ FLOOKUP s.vs_allocas aid = SOME (p,n) ==>
     loweringStateRelDefs$regions_disjoint q k p n) ==>
  mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory
Proof
  strip_tac >>
  `loweringStateRelDefs$regions_disjoint q k b cap` by metis_tac[IN_INSERT] >>
  irule window_alloca_growth_frame >> asm_rewrite_tac[] >>
  qexistsl_tac [`ids`,`outs`] >> asm_rewrite_tac[] >> reverse conj_tac
  >- (qpat_assum `EVERY _ outs` mp_tac >>
      simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD, venomMemDefsTheory.regions_disjoint_def] >>
      strip_tac >> rpt gen_tac >> disch_tac >> first_x_assum drule >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qx_genl_tac [`scratch_id`,`scratch_base`,`scratch_size`] >> strip_tac >>
  `loweringStateRelDefs$regions_disjoint q k scratch_base scratch_size` by metis_tac[IN_INSERT] >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def, venomMemDefsTheory.regions_disjoint_def] >>
  decide_tac
QED

Theorem ctor_immutable_module_bytes[local]:
  abi_encoder_registered_effect ids outs s t /\ window_alloca_growth s t /\
  t.vs_data_section = s.vs_data_section /\
  FLOOKUP s.vs_allocas shared = SOME (b,cap) /\
  EVERY (\(p,n). b <= p /\ p+n <= b+cap) outs /\
  (!aid. aid IN shared INSERT ids ==>
    ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid) /\
  immutables_rel ce cx.txn.target src ce.ce_is_ctor ee s /\
  immutable_alloca_sep func (ce with ce_module := src) cx ee s ==>
  immutables_rel ce cx.txn.target src ce.ce_is_ctor ee t
Proof
  strip_tac >> reverse (Cases_on `ce.ce_is_ctor`)
  >- (qpat_x_assum `immutables_rel _ _ _ _ _ s` mp_tac >> simp[immutables_rel_def]) >>
  gvs[immutables_rel_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!name tv v off. _ /\ _ ==> immutable_value_admissible _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
  simp[immutable_alloca_sep_def] >> strip_tac >>
  qpat_assum `!name tv v off. _ /\ _ ==> off + type_memory_size tv <= _ /\ _`
    (drule_all_then strip_assume_tac) >>
  rename1 `val_in_memory vt value off t.vs_memory` >>
  `mem_bytes_at off (type_memory_size vt) t.vs_memory =
   mem_bytes_at off (type_memory_size vt) s.vs_memory` by
    (irule ctor_immutable_owner_window >> asm_rewrite_tac[] >>
     qexistsl_tac [`b`,`cap`,`ids`,`outs`,`shared`] >> simp[] >>
     qx_genl_tac [`aid`,`win_base`,`win_size`] >>
     disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     qpat_assum `!aid. _ ==> ?inst. _ /\ _ /\ inst.inst_id = aid`
       (drule_then strip_assume_tac) >>
     qpat_assum `!inst b sz. MEM inst _ /\ inst.inst_opcode = ALLOCA /\ _ ==>
       loweringStateRelDefs$regions_disjoint _ _ b sz` irule >>
     qexists_tac `inst` >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >> irule val_in_memory_mem_agree >>
  conj_tac >- (irule (cj 1 immutable_admissible_val_wf) >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`type_memory_size vt`,`s.vs_memory`] >> simp[]
QED

Theorem ctor_encoder_window_immutable_mods:
  window_phase ctx func st en ids outs s t /\
  abi_encode_exec_frame func s t /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
  local_ptrs_reserved ce front /\ front.cs_next_var <= st.cs_next_var /\
  FLOOKUP s.vs_allocas shared = SOME (b,cap) /\
  EVERY (\(p,n). b <= p /\ p+n <= b+cap) outs /\
  (!aid. aid IN shared INSERT ids ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
  immutable_frame_mods func ce cx ee s ==>
  immutable_frame_mods func ce cx ee t
Proof
  strip_tac >>
  drule_then assume_tac window_phase_effect >>
  drule_then strip_assume_tac window_phase_resources >>
  `!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) ==>
      FLOOKUP s.vs_allocas aid = SOME (p,n) \/ s.vs_alloca_next <= p` by
    (rpt gen_tac >> disch_tac >> Cases_on `FLOOKUP s.vs_allocas aid` >>
     metis_tac[window_alloca_growth_def, abi_encoder_registered_effect_allocated, optionTheory.SOME_11]) >>
  qpat_x_assum `immutable_frame_mods func ce cx ee s`
    (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def, immutables_rel_mods_def,
                                     immutable_alloca_sep_mods_def]) >>
  rewrite_tac[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> irule ctor_immutable_module_bytes >>
      qexistsl_tac [`b`,`cap`,`func`,`ids`,`outs`,`s`,`shared`] >>
      qpat_assum `abi_encode_exec_frame func s t`
        (strip_assume_tac o REWRITE_RULE [abi_encode_exec_frame_def]) >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> irule immutable_alloca_sep_frame >>
  qexistsl_tac [`s`,`ee`] >>
  `s.vs_alloca_next <= t.vs_alloca_next` by fs[window_alloca_growth_def] >>
  `immutable_alloca_sep func (ce with ce_module := src) cx ee s` by metis_tac[] >>
  asm_rewrite_tac[] >> qx_genl_tac [`local_id`,`local_base`,`local_size`] >>
  disch_tac >> disj1_tac >> qexists_tac `local_id` >>
  `local_region ce ee.scopes t local_id local_base local_size` by fs[local_region_def] >>
  `local_ptrs_reserved ce st` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `local_region ce ee.scopes s local_id local_base local_size` by
    (irule local_region_frame >> conj_tac
     >- (qexists_tac `func` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`st`,`ee.scopes`,`t`] >> simp[] >> metis_tac[window_phase_vars]) >>
  fs[local_region_def]
QED
