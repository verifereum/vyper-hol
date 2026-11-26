(* Both payload routes start at the same linked ABI setup landing. *)
Theory bodyAbiEncodeSetupLandingMods
Ancestors
  bodyAbiEncodeSetupRunMods bodyAbiEncodeSetupFrameMods bodyAbiEncodeSetupBufferMods
  bodyAbiEncodePackedPostMods bodyAbiEncodeStageMods
  bodyFullShadowBodyInv bodyMemoryDefs exprSimWordArgs wordArgsPtr exprSimOperands
  abiBuiltinAllocation emitHelperProps exprSimProps exprBodyPreProps
  vyperStorageFootprint loweringStateRelDefs bodyPtrDefs typedMemoryCopy
  stateRelProj venomMemDefs venomState finite_map pred_set words arithmetic

Theorem setup_world[local]:
  u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
           vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  typed_copy_state_frame allocated (p+32) write_len u pre ==>
  pre.vs_accounts = s.vs_accounts /\ pre.vs_transient = s.vs_transient /\
  pre.vs_call_ctx = s.vs_call_ctx /\ pre.vs_labels = s.vs_labels /\
  pre.vs_immutables = s.vs_immutables /\ pre.vs_data_section = s.vs_data_section
Proof
  simp[typed_copy_state_frame_def] >> strip_tac >>
  qpat_x_assum `_ = s` (SUBST1_TAC o SYM) >>
  qpat_x_assum `_ = u` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem setup_capture_windows[local]:
  alloca_inv s /\
  (!name b n. local_region ce ee.scopes s name b n ==> b+n <= s.vs_alloca_next) /\
  local_ptrs_reserved ce st /\
  (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s) /\
  (!name b n. local_region ce ee.scopes u name b n ==> regions_disjoint p N b n) /\
  (!aid b n. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
     regions_disjoint p N b n) /\
  lo <= p /\ lo <= s.vs_alloca_next /\ 32+write_len <= N ==>
  !b n. ((b = 0 /\ n = lo) \/
         (?name. local_region ce ee.scopes s name b n) \/
         (?aid. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n))) ==>
    (b+n <= p+32 \/ p+32+write_len <= b) /\ b+n <= s.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!name b n. local_region ce ee.scopes u name b n <=>
              local_region ce ee.scopes s name b n` by
    (rpt gen_tac >> match_mp_tac local_region_lookup_cong >>
     rpt strip_tac >> first_x_assum irule >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  ntac 2 gen_tac >> strip_tac
  >- (gvs[] >> decide_tac)
  >- (`regions_disjoint p N b n` by
        (qpat_assum `!name b n. local_region _ _ u name b n ==> _`
           (qspecl_then [`name`,`b`,`n`] mp_tac) >> simp[]) >>
      qpat_assum `!name b n. local_region _ _ s name b n ==> b+n <= _`
        (drule_then assume_tac) >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `regions_disjoint p N b n` by (first_x_assum drule_all >> simp[]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def, alloca_inv_def, alloca_next_valid_def] >>
  qpat_assum `!aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) ==> _ <= _`
    (drule_then assume_tac) >> decide_tac
QED

Theorem abi_encode_setup_landing_mods:
  let e = TypeBuiltin ann (AbiEncode ensure mid) target args;
      single = (LENGTH args = 1 /\ ~ensure);
      tys = MAP (lowered_value_type ce) args;
      maxlen = abi_size_bound ce.ce_struct_fields
        (if single then lowered_value_type ce (HD args) else TupleT tys);
      midw = OPTION_MAP bytes_method_id_word mid;
      k = (case mid of NONE => 0 | SOME _ => 4);
      write_len = (case mid of NONE => 0 | SOME _ => 32);
      N = 32 + 32 * word_size (maxlen+k);
      prefix = abi_encode_method_id_bytes mid
  in
  expr_body_pre_mods mods ce cx env e es /\
  lower_abi_encode midw maxlen (compile_abi_encode_payload ce single svs tys) st = (out,sb) /\
  fn_has_code st sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce st /\
  sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_packed_post_mods mods DF lo d ctx func ce cx env
      args svs sa st es s0 G0 tn0 H (INL vs : value list + 'err) ee G tn s) ==>
  ?buf allocated method_st dp ready len body_end root p u Gu tu pre Gpre tnpre.
    out = Var root /\ buf.buf_operand = Var root /\
    compile_alloc_buffer N st = (buf,allocated) /\
    abi_builtin_encode_method_id midw out allocated = ((),method_st) /\
    emit_op ADD [out;Lit (n2w (32+k))] method_st = (Var dp,ready) /\
    compile_abi_encode_payload ce single svs tys (Var dp) ready = (len,body_end) /\
    abi_builtin_encode_finish out len k body_end = ((),sb) /\
    fn_has_code st allocated func /\ fn_has_code allocated ready func /\
    fn_has_code ready body_end func /\ fn_has_code body_end sb func /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK pre,Gpre,tnpre)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      abi_encode_packed_post_mods mods DF lo d ctx func ce cx env
        args svs sa st es s0 G0 tn0 H (INL vs : value list + 'err) ee G tn s) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee pre /\ immutable_frame_mods func ce cx ee pre /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gpre tnpre pre) /\
    wb_frame ce es ee sa s0 pre /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gpre tnpre /\
    (~EXISTS expr_has_effect args ==> pure_frame ce func es sa s0 pre) /\
    MAP FDOM ee.scopes = MAP FDOM es.scopes /\ return_buf_frame d ce ready pre /\
    alloca_history func pre /\ (ctx_has_dalloca ctx ==> allocas_below_fmp pre) /\
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d st s G tn
      st.cs_next_id p N root dp (32+k) prefix ready pre Gpre tnpre /\
    st.cs_next_var <= allocated.cs_next_var /\ st.cs_next_var <= ready.cs_next_var /\
    st.cs_next_id < ready.cs_next_id /\
    MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w N)] [root]) (fn_insts func) /\
    not_local_ptr ce ee.scopes root /\
    ~pre.vs_halted /\ pre.vs_current_bb = ready.cs_current_bb /\
    pre.vs_inst_idx = LENGTH ready.cs_current_insts /\
    not_fresh_at ready root /\ not_fresh_at ready dp /\
    eval_operand (Var root) pre = SOME (n2w p) /\ ptr_covers Gpre tnpre root pre N /\
    eval_operand (Var dp) pre = SOME (n2w (p+32+k)) /\ ptr_covers Gpre tnpre dp pre (N-(32+k)) /\
    FLOOKUP pre.vs_allocas st.cs_next_id = SOME (p,N) /\ FLOOKUP Gpre root = SOME (p,N) /\
    alloca_inv pre /\ allocas_from lo pre /\
    lo <= p /\ p+N < dimword(:256) /\ p+N <= pre.vs_alloca_next /\
    lo <= s.vs_alloca_next /\ s.vs_alloca_next <= pre.vs_alloca_next /\
    s0.vs_alloca_next <= pre.vs_alloca_next /\ 32+write_len <= N /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP pre.vs_allocas aid = SOME entry) /\
    (!aid b n. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
      regions_disjoint p N b n) /\
    (!name b n. local_region ce ee.scopes u name b n ==> regions_disjoint p N b n) /\
    (!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x s /\
       FLOOKUP Gpre x = FLOOKUP G x /\ op_taint tnpre (Var x) = op_taint tn (Var x)) /\
    typed_copy_state_frame allocated (p+32) write_len u pre /\
    (!b n. b+n <= p+32 \/ p+32+write_len <= b ==>
       mem_bytes_at b n pre.vs_memory = mem_bytes_at b n s.vs_memory) /\
    (!i. i IN tu.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < p+N)) /\
    tnpre.t_mem = tu.t_mem DIFF {i | p+32 <= i /\ i < p+32+write_len} /\
    tnpre.t_stor = tn.t_stor /\ tnpre.t_trans = tn.t_trans /\ tnpre.t_imm = tn.t_imm /\
    pre.vs_accounts = s.vs_accounts /\ pre.vs_transient = s.vs_transient /\
    pre.vs_call_ctx = s.vs_call_ctx /\ pre.vs_labels = s.vs_labels /\
    pre.vs_immutables = s.vs_immutables /\ pre.vs_data_section = s.vs_data_section /\
    LENGTH prefix = k /\ read_memory (p+32) k pre = prefix /\
    (!i. p+32 <= i /\ i < p+32+k ==> i NOTIN tnpre.t_mem)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_then strip_assume_tac abi_encode_stage_static_mods >>
  qmatch_asmsub_abbrev_tac `lower_abi_encode midw maxlen (compile_abi_encode_payload ce single svs tys)` >>
  qabbrev_tac `k = case mid of NONE => 0 | SOME _ => 4` >>
  qabbrev_tac `write_len = case mid of NONE => 0 | SOME _ => 32` >>
  qabbrev_tac `N = 32 + 32 * word_size (maxlen+k)` >>
  qabbrev_tac `prefix = abi_encode_method_id_bytes mid` >>
  suspend "select"
QED

Resume abi_encode_setup_landing_mods[select]:
  `k = (case midw of NONE => 0 | SOME _ => 4) /\
   write_len = (case midw of NONE => 0 | SOME _ => 32) /\
   k <= write_len /\ 32+write_len <= N` by
    (Cases_on `mid` >> fs[Abbr `midw`, Abbr `k`, Abbr `write_len`, Abbr `N`] >>
     qspec_then `maxlen+4` mp_tac le_word_size_mul >> decide_tac) >>
  `N < dimword(:256)` by
    (`2 ** 64 < dimword(:256)` by simp[dimword_def] >> decide_tac) >>
  `N = 32 + 32 * word_size (maxlen+k)` by simp[Abbr `N`] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    (qpat_assum `storage_trace_domain _ _ _`
       (ACCEPT_TAC o REWRITE_RULE[storage_trace_domain_def])) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o REWRITE_RULE[abi_encode_packed_post_mods_def])) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ lo _ _ _ _ _ _ s`
      (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >> asm_rewrite_tac[]) >>
  `prefix = abi_builtin_encode_prefix midw` by
    (qpat_assum `abi_builtin_encode_prefix midw = prefix` (ACCEPT_TAC o SYM)) >>
  drule_all abi_encode_setup_run_effects_mods >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`buf`,`allocated`,`method_st`,`dp`,`ready`,`len`,`body_end`,
      `root`,`p`,`u`,`Gu`,`tu`,`pre`,`Gpre`,`tnpre`] strip_assume_tac)) >>
  suspend "frames"
QED

Resume abi_encode_setup_landing_mods[frames]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
     storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
       (drule_then (strip_assume_tac o REWRITE_RULE[abi_encode_packed_post_mods_def])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry` by
    (qpat_assum `u.vs_allocas = pre.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `st.cs_next_var <= ready.cs_next_var` by decide_tac >>
  `tnpre.t_stor = tu.t_stor /\ tnpre.t_trans = tu.t_trans /\ tnpre.t_imm = tu.t_imm` by
    (rpt conj_tac >>
     metis_tac[]) >>
  `(!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee pre /\ immutable_frame_mods func ce cx ee pre /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gpre tnpre pre) /\
    wb_frame ce es ee sa s0 pre /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gpre tnpre /\
    (~EXISTS expr_has_effect args ==> pure_frame ce func es sa s0 pre) /\
    return_buf_frame d ce ready pre /\ alloca_history func pre /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp pre)` by
    (match_mp_tac (Q.INST [`t` |-> `s`] abi_encode_setup_frame_mods) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "buffer"
QED

Resume abi_encode_setup_landing_mods[buffer]:
  `wb_frame ce ee ee st s s` by simp_tac bool_ss [wb_frame_refl] >>
  `ghost_kept_at lo ce ee st G tn s G tn` by simp_tac bool_ss [ghost_kept_at_refl] >>
  `(!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee pre /\ immutable_frame_mods func ce cx ee pre /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gpre tnpre pre) /\
    wb_frame ce ee ee st s pre /\ ghost_kept_at lo ce ee st G tn s Gpre tnpre /\
    (F ==> pure_frame ce func ee st s pre) /\
    return_buf_frame d ce ready pre /\ alloca_history func pre /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp pre)` by
    (match_mp_tac (Q.INST [`t` |-> `s`] abi_encode_setup_frame_mods) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp_tac bool_ss [LESS_EQ_REFL])) >>
  suspend "assemble"
QED

Resume abi_encode_setup_landing_mods[assemble]:
  drule_all_then strip_assume_tac setup_world >>
  qpat_x_assum `out = Var root` SUBST_ALL_TAC >>
  `not_local_ptr ce ee.scopes root` by
    (irule fresh_not_local_ptr >> qexists `st` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     qpat_assum `emit_op ALLOCA _ _ = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     qpat_assum `buf.buf_operand = Var root` (mp_tac o SYM) >>
     qpat_assum `buf.buf_operand = Var (STRING _ _)` (fn th =>
       simp_tac bool_ss [th, operand_11, not_fresh_at_def, LESS_EQ_REFL] >>
       disch_then SUBST1_TAC >> simp[not_fresh_at_def])) >>
  `!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x u = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `!b n. ((b = 0 /\ n = lo) \/
         (?name. local_region ce ee.scopes s name b n) \/
         (?aid. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n))) ==>
    (b+n <= p+32 \/ p+32+write_len <= b) /\ b+n <= s.vs_alloca_next` by
    (match_mp_tac setup_capture_windows >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (drule_then (ACCEPT_TAC o CONJUNCT2) stmt_state_rel_local_ptrs_alloca) >>
     rpt gen_tac >> disch_tac >> drule_all_then ACCEPT_TAC body_local_region_frontier) >>
  `!i. i < s.vs_alloca_next /\ i IN tnpre.t_mem ==> i IN tn.t_mem` by
    (gen_tac >> disch_then strip_assume_tac >>
     `i IN tu.t_mem` by
       (qpat_assum `i IN tnpre.t_mem` mp_tac >>
        qpat_assum `tnpre.t_mem = _` (fn th => simp_tac bool_ss [th, IN_DIFF])) >>
     qpat_assum `!i. i IN tu.t_mem <=> _` (qspec_then `i` (fn th =>
       qpat_assum `i IN tu.t_mem` (mp_tac o REWRITE_RULE [th]))) >>
     disch_then strip_assume_tac >> (first_assum ACCEPT_TAC ORELSE decide_tac)) >>
  suspend "entry"
QED

Resume abi_encode_setup_landing_mods[entry]:
  `abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d st s G tn
      st.cs_next_id p N root dp (32+k) prefix ready pre Gpre tnpre` by
    (match_mp_tac abi_encode_setup_buffer_mods >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC)
     >- (gen_tac >> disch_tac >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ pre /\ _`
           (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC)
     >- (REWRITE_TAC [ADD_ASSOC] >> first_assum ACCEPT_TAC)
     >- decide_tac
     >- decide_tac
     >- (`p + (32+k) - LENGTH prefix = p+32` by decide_tac >>
         qpat_assum `LENGTH prefix = k` (fn th =>
         qpat_assum `p + (32+k) - LENGTH prefix = p+32` (fn th' =>
           ONCE_REWRITE_TAC [th'] >> REWRITE_TAC [th])) >> first_assum ACCEPT_TAC)
     >- (`p + (32+k) - LENGTH prefix = p+32` by decide_tac >>
         qpat_assum `p + (32+k) - LENGTH prefix = p+32` (fn th =>
           ONCE_REWRITE_TAC [th] >> REWRITE_TAC [ADD_ASSOC]) >> first_assum ACCEPT_TAC)
     >- (rpt gen_tac >> disch_tac >>
         qpat_assum `!b n. _ ==> (_ <= _ \/ _ <= _) /\ b+n <= _`
           (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!b n. _ ==> (_ <= _ \/ _ <= _) /\ b+n <= _`
       (drule_then (CONJUNCTS_THEN2 assume_tac assume_tac)) >> conj_tac
     >- (qpat_assum `!b n. _ \/ _ ==> mem_bytes_at b n pre.vs_memory = _`
           (drule_then ACCEPT_TAC)) >>
     gen_tac >> disch_then strip_assume_tac >>
     `i < s.vs_alloca_next` by decide_tac >>
     qpat_assum `!i. _ /\ i IN tnpre.t_mem ==> i IN tn.t_mem` (drule_all_then ACCEPT_TAC)) >>
  qexistsl_tac [`buf`,`allocated`,`method_st`,`dp`,`ready`,`len`,`body_end`,
    `root`,`p`,`u`,`Gu`,`tu`,`pre`,`Gpre`,`tnpre`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
  decide_tac
QED

Finalise abi_encode_setup_landing_mods
