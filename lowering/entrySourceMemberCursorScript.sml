(* Cursor reconstruction uses the resource endpoint selected by the framed child. *)
Theory entrySourceMemberCursor
Ancestors
  entrySourceMemberChild entryDecoderMemberEndpoint entryDecoderStateFrame
  calldataSourceMemberFold calldataMemberResourceFrame calldataSafeIteration
  abiDecoderMemberCons abiDecoderMemberCode abiDecoderValidMemberCursor
  abiDecoderMemberInfos abiDecoderMembers abiDecoderMemberSetup abiDecoderOffsetHead
  abiDecoderCode abiDecoderCounters abiDecoderAppend abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract abiDecoderReentry abiEncoderInput
  abiEncoder compileEnv emitHelper emitHelperProps fragExec exprLoweringProps
  valueEncodingTyping venomState venomExecSemantics words list rich_list pair arithmetic

Theorem entry_source_member_cursor_step_local_success:
  calldata_source_member_cursor ce env sf ctx fn site limit_st
    xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
    0 0 first final initial ((ei,az,mz)::rest) ao vo a s /\
  xs = abi_decoder_member_infos sf ce tys /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  MAP type_memory_size tvs = MAP (type_memory_bytes ce) tys /\
  LENGTH vs = LENGTH tys /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)];
      compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) ei od) a = ((),next) /\
  fn_has_code a final fn /\
  (a.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  final.cs_next_var <= limit_st.cs_next_var /\
  (oid < first.cs_next_id \/ final.cs_next_id <= oid) /\
  base_addr <= d /\ d + SUM (MAP type_memory_size tvs) <= base_addr+cap /\
  SUM (MAP type_memory_size tvs) <= outsz /\
  d + SUM (MAP type_memory_size tvs) < dimword(:256) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  (!i. i < LENGTH tys ==> entry_member_child_contract ce env sf ctx fn site limit_st
    (EL i tys) (EL i tvs)) /\ fn_inst_ids_distinct fn /\ alloca_history fn s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = next.cs_current_bb /\
    t.vs_inst_idx = LENGTH next.cs_current_insts /\
    calldata_source_member_cursor ce env sf ctx fn site limit_st
      xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
      0 0 first final initial rest (ao+az) (vo+mz) next t /\
    calldata_member_transfers ctx fn s t /\ entry_decoder_obs s t /\ alloca_history fn t /\
    ?scratch. calldata_member_success ctx fn site limit_st a next (d+vo)
      (type_memory_size (EL (LENGTH xs - LENGTH ((ei,az,mz)::rest)) tvs))
      (EL (LENGTH xs - LENGTH ((ei,az,mz)::rest)) tvs)
      (EL (LENGTH xs - LENGTH ((ei,az,mz)::rest)) vs) s t scratch
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `calldata_source_member_cursor`
    (strip_assume_tac o REWRITE_RULE [calldata_source_member_cursor_def]) >>
  `LENGTH xs = LENGTH tys /\ LENGTH tvs = LENGTH tys` by
    (fs[abi_decoder_member_infos_def] >> metis_tac[LIST_REL_LENGTH]) >>
  `LENGTH ((ei,az,mz)::rest) = LENGTH (DROP n xs)` by metis_tac[] >>
  `n < LENGTH tys /\ n = LENGTH xs - LENGTH ((ei,az,mz)::rest)` by
    (qpat_x_assum `LENGTH (_::rest) = _` mp_tac >> simp[LENGTH_DROP] >> decide_tac) >>
  rule_assum_tac (REWRITE_RULE [ADD_CLAUSES]) >>
  drule_all calldata_source_member_layout >> strip_tac >>
  `DROP n tys = EL n tys::DROP (SUC n) tys /\
   DROP n tvs = EL n tvs::DROP (SUC n) tvs /\
   DROP n vs = EL n vs::DROP (SUC n) vs` by
    (qpat_assum `n < LENGTH tys` mp_tac >>
     qpat_assum `n < LENGTH tvs` mp_tac >>
     qpat_assum `LENGTH vs = LENGTH tys` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[DROP_EL_CONS, ADD1]) >>
  qpat_assum `abi_decoder_members _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `DROP n tys = _` (fn th => pure_once_rewrite_tac[th]) >>
  qpat_assum `DROP n tvs = _` (fn th => pure_once_rewrite_tac[th]) >>
  qpat_assum `DROP n vs = _` (fn th => pure_once_rewrite_tac[th]) >>
  disch_then (mp_tac o MATCH_MP abi_decoder_valid_member_cursor) >>
  strip_tac >>
  `val_wf (EL n tvs) (EL n vs)` by metis_tac[value_has_type_val_wf] >>
  qpat_x_assum `DROP n tys = _` kall_tac >>
  qpat_x_assum `DROP n tvs = _` kall_tac >>
  qpat_x_assum `DROP n vs = _` kall_tac >>
  qpat_x_assum `ao = SUM (MAP (\(ei,az,mz). az) _)` kall_tac >>
  qpat_x_assum `vo = SUM (MAP (\(ei,az,mz). mz) _)` kall_tac >>
  suspend "phases_goal"
QED

Resume entry_source_member_cursor_step_local_success[phases_goal]:
  `?ops ready.
    abi_decode_member_setup dst src CALLDATALOAD (Lit 0w)
      (dec_info_needs_offset ei) ao vo a = (ops,ready) /\
    compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) ei ready = ((),next) /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
      rest (ao+az) (vo+mz) next = ((),final) /\
    cs_extends a next /\ cs_extends next final /\ fn_has_code a next fn /\
    a.cs_next_id < ready.cs_next_id /\ ready.cs_next_id <= next.cs_next_id /\
    next.cs_next_id <= final.cs_next_id /\ next.cs_next_var <= final.cs_next_var /\
    (ready.cs_blocks = next.cs_blocks \/
      !bb. lookup_block next.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0)` by suspend "phases" >>
  suspend "child"
QED

Resume entry_source_member_cursor_step_local_success[phases]:
  qpat_assum `(do ep <- _; _ od) a = ((),next)` mp_tac >>
  qpat_assum `compile_abi_decode_complex_elems _ _ _ _ (_::rest) _ _ _ = _` mp_tac >>
  qpat_assum `fn_has_code a final fn` mp_tac >>
  qpat_assum `a.cs_blocks = _ \/ _` mp_tac >>
  qpat_assum `xs = abi_decoder_member_infos _ _ _` mp_tac >>
  qpat_assum `_::rest = DROP n xs` mp_tac >>
  qpat_assum `n < LENGTH tys` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt disch_tac >>
  qpat_assum `(do ep <- _; _ od) a = ((),next)` mp_tac >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_getelemptr_abi src _ ao CALLDATALOAD (Lit 0w) a = (ep,middle)` >>
  rename1 `emit_op ADD _ middle = (dp,ready)` >>
  `abi_decode_member_setup dst src CALLDATALOAD (Lit 0w)
    (dec_info_needs_offset ei) ao vo a = ((ep,dp),ready)` by
    simp[abi_decode_member_setup_def, comp_bind_def, comp_return_def] >>
  `compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
    rest (ao+az) (vo+mz) next = ((),final)` by
    (qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ (_::rest) _ _ _ = _` mp_tac >>
     simp[abi_decode_complex_member_phases, comp_bind_def, comp_ignore_bind_def, ADD_COMM]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decoder_member_cons_code >> simp_tac bool_ss [FST,SND] >>
  disch_then drule_all >> strip_tac >>
  `rest = abi_decoder_member_infos sf ce (DROP (SUC n) tys)` by
    (`rest = DROP (SUC n) xs` by
       (qpat_assum `_::rest = DROP n xs`
          (mp_tac o AP_TERM ``DROP 1 : (abi_dec_info # num # num) list -> (abi_dec_info # num # num) list``) >>
        simp[DROP_DROP_T, ADD1, ADD_COMM]) >>
     simp[abi_decoder_member_infos_def, MAP_DROP]) >>
  qpat_x_assum `rest = abi_decoder_member_infos _ _ _` SUBST_ALL_TAC >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule_all abi_decoder_members_child_phi >> strip_tac >>
  qexistsl_tac [`(ep,dp)`,`ready`] >> fs[ADD_COMM]
QED

Resume entry_source_member_cursor_step_local_success[child]:
  markerLib.RESUME_TAC >>
  `vo + type_memory_size (EL n tvs) <= SUM (MAP type_memory_size tvs)` by
    (qpat_assum `vo = _` (fn th => rewrite_tac[th]) >>
     irule abi_encoder_prefix_sum_bound >> simp[]) >>
  `fresh_vars_wrt limit_st s /\ alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
   calldata_member_own fn first.cs_next_id final.cs_next_id s` by
    (drule calldata_member_resource_endpoint >> simp[]) >>
  `calldata_member_own fn a.cs_next_id next.cs_next_id s` by
    (irule calldata_member_own_nested >>
     qhdtm_assum `calldata_member_own` (irule_at Any) >> fs[ci_mono_def]) >>
  `?t scratch. calldata_member_success ctx fn site limit_st a next (d+vo)
    (type_memory_size (EL n tvs)) (EL n tvs) (EL n vs) s t scratch /\
    entry_decoder_obs s t /\ alloca_history fn t` suffices_by
    (strip_tac >> suspend "advance") >>
  suspend "apply"
QED

Resume entry_source_member_cursor_step_local_success[apply]:
  markerLib.RESUME_TAC >>
  qhdtm_x_assum `calldata_source_member_cursor` kall_tac >>
  qpat_x_assum `(do ep <- _; _ od) a = _` kall_tac >>
  `MAP (vyper_to_abi_type env) tys =
    MAP (vyper_to_abi_type env) (TAKE n tys) ++
    vyper_to_abi_type env (EL n tys)::MAP (vyper_to_abi_type env) (DROP (SUC n) tys)` by
    (`DROP n tys = EL n tys::DROP (SUC n) tys` by
       (qpat_assum `n < LENGTH tys` mp_tac >> rpt (pop_assum kall_tac) >>
        metis_tac[DROP_EL_CONS, ADD1]) >>
     pure_rewrite_tac[GSYM MAP, GSYM MAP_APPEND] >> AP_TERM_TAC >>
     qpat_x_assum `DROP n tys = _` (fn th => pure_rewrite_tac[GSYM th]) >> simp[TAKE_DROP]) >>
  `d+vo+type_memory_size (EL n tvs) < dimword(:256) /\
   next.cs_next_var <= limit_st.cs_next_var /\ base_addr <= d+vo /\
   d+vo+type_memory_size (EL n tvs) <= base_addr+cap /\
   vo+type_memory_bytes ce (EL n tys) <= outsz /\
   (oid < ready.cs_next_id \/ next.cs_next_id <= oid)` by
    (RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [ci_mono_def]) >> decide_tac) >>
  qpat_x_assum `ei = _` SUBST_ALL_TAC >>
  qpat_x_assum `ao = _` SUBST_ALL_TAC >>
  qpat_x_assum `vo = _` kall_tac >>
  qpat_x_assum `type_memory_size (EL n tvs) = _` kall_tac >>
  irule (SIMP_RULE bool_ss [LET_THM] entry_source_member_success) >>
  asm_simp_tac bool_ss [] >>
  qpat_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `FLOOKUP s.vs_allocas oid = _` (irule_at Any) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`env`,`MAP (vyper_to_abi_type env) (DROP (SUC n) tys)`] >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `MAP (vyper_to_abi_type env) tys = _`
    (fn th => pure_rewrite_tac[GSYM th]) >> asm_rewrite_tac[]
QED

Resume entry_source_member_cursor_step_local_success[advance]:
  markerLib.RESUME_TAC >> (
  drule calldata_member_success_observations >> strip_tac >>
  `a.cs_next_var <= ready.cs_next_var` by
    (drule abi_decode_member_setup_counters >> rpt (pop_assum kall_tac) >> simp[]) >>
  `ready.cs_next_var <= next.cs_next_var` by
    (drule abi_decoder_variable_counter >> disch_then ACCEPT_TAC) >>
  `ci_mono a next /\ ci_mono next final` by
    (RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [ci_mono_def]) >>
     rewrite_tac[ci_mono_def] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `LENGTH tys = LENGTH xs /\ LENGTH tvs = LENGTH xs /\ LENGTH vs = LENGTH xs` by simp[] >>
  `?scratch. calldata_member_success ctx fn site limit_st a next (d+vo)
      (type_memory_size (EL (LENGTH xs - LENGTH ((ei,az,mz)::rest)) tvs))
      (EL (LENGTH xs - LENGTH ((ei,az,mz)::rest)) tvs)
      (EL (LENGTH xs - LENGTH ((ei,az,mz)::rest)) vs) s t scratch` by suspend "local_success" >>
  qexists_tac `t` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `scratch''` >> first_assum ACCEPT_TAC) >>
  irule (SIMP_RULE bool_ss [LET_THM] calldata_source_member_cursor_advance) >>
  qhdtm_assum `calldata_source_member_cursor` (irule_at Any) >>
  qexists_tac `scratch'` >>
  qpat_x_assum `n = LENGTH xs - _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_x_assum `xs = _` kall_tac >>
  qpat_x_assum `vo = _` (fn th => assume_tac (SYM th)) >>
  qpat_x_assum `type_memory_size (EL n tvs) = _` kall_tac >>
  qhdtm_x_assum `calldata_source_member_cursor` kall_tac >>
  qhdtm_x_assum `abi_decoder_coherent` kall_tac >>
  qhdtm_x_assum `abi_to_vyper` kall_tac >>
  qhdtm_x_assum `vyper_decode_valid_enc_tuple` kall_tac >>
  qhdtm_x_assum `LIST_REL` kall_tac >>
  rpt (qhdtm_x_assum `abi_decoder_members` kall_tac) >>
  qpat_x_assum `MAP type_memory_size _ = _` kall_tac >>
  qpat_x_assum `ao = _` kall_tac >>
  qpat_x_assum `ei = _` kall_tac >>
  qpat_x_assum `az = _` kall_tac >>
  qpat_x_assum `mz = _` kall_tac >>
  qpat_x_assum `LENGTH (_::rest) = _` kall_tac >>
  qpat_x_assum `LENGTH xs = LENGTH tys` kall_tac >>
  qpat_x_assum `LENGTH tvs = LENGTH tys` kall_tac >>
  qpat_x_assum `LENGTH vs = LENGTH tys` kall_tac >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- decide_tac >>
  conj_tac >- (gns[ci_mono_def] >> decide_tac) >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[] >> decide_tac) >>
  simp[] >> decide_tac)
QED
Resume entry_source_member_cursor_step_local_success[local_success]:
  markerLib.RESUME_TAC >> qexists_tac `scratch'` >>
  qpat_assum `n = LENGTH xs - _` (fn th => pure_rewrite_tac[GSYM th]) >>
  first_assum ACCEPT_TAC
QED
Finalise entry_source_member_cursor_step_local_success

(* Compatibility projection: the cursor and frame share the producer's t. *)
Theorem entry_source_member_cursor_step:
  calldata_source_member_cursor ce env sf ctx fn site limit_st
    xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
    0 0 first final initial ((ei,az,mz)::rest) ao vo a s /\
  xs = abi_decoder_member_infos sf ce tys /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  MAP type_memory_size tvs = MAP (type_memory_bytes ce) tys /\
  LENGTH vs = LENGTH tys /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)];
      compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) ei od) a = ((),next) /\
  fn_has_code a final fn /\
  (a.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  final.cs_next_var <= limit_st.cs_next_var /\
  (oid < first.cs_next_id \/ final.cs_next_id <= oid) /\
  base_addr <= d /\ d + SUM (MAP type_memory_size tvs) <= base_addr+cap /\
  SUM (MAP type_memory_size tvs) <= outsz /\
  d + SUM (MAP type_memory_size tvs) < dimword(:256) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  (!i. i < LENGTH tys ==> entry_member_child_contract ce env sf ctx fn site limit_st
    (EL i tys) (EL i tvs)) /\ fn_inst_ids_distinct fn /\ alloca_history fn s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = next.cs_current_bb /\
    t.vs_inst_idx = LENGTH next.cs_current_insts /\
    calldata_source_member_cursor ce env sf ctx fn site limit_st
      xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
      0 0 first final initial rest (ao+az) (vo+mz) next t /\
    calldata_member_transfers ctx fn s t /\ entry_decoder_obs s t /\ alloca_history fn t
Proof
  disch_then (strip_assume_tac o MATCH_MP entry_source_member_cursor_step_local_success) >>
  qexists_tac `t` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
