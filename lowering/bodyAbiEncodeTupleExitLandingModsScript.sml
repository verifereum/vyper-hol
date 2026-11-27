(* Interpret the one reached tuple-loop cut as an ABI finish landing. *)
Theory bodyAbiEncodeTupleExitLandingMods
Ancestors
  bodyAbiEncodePayloadLandingMods bodyAbiTupleBufferResourcesMods bodyAbiTupleBufferStateMods
  abiEncoderRegisteredEffect venomInst stateRelProj
  exprSimAbiEncodeFrameTransfer abiDecodeStaticProps exprSimProps
  exprSimWordArgs wordArgsPtr vyperStorageFootprint memoryReadProps
  exprLoweringProps loweringPosts loweringStateRelDefs freshWrites
  venomMemDefs venomState finite_map pred_set list pair arithmetic words

Theorem tuple_exit_pure[local]:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d st s G tn
    st.cs_next_id p cap root dp off prefix ready pre Gpre tnpre /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d st s G tn
    st.cs_next_id p cap root dp off prefix body_end q Gq tq /\
  abi_tuple_row_effects_mods ce ee func st.cs_next_id p cap off ready.cs_next_id
    ready pre Gpre tnpre body_end q Gq tq /\
  local_ptrs_reserved ce st /\
  (!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x s) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = st.cs_next_id ==>
  pure_frame ce func ee st pre q
Proof
  strip_tac >>
  qpat_x_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pre _ _`
    (strip_assume_tac o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
  qpat_x_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q _ _`
    (strip_assume_tac o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
  qpat_x_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_tuple_row_effects_mods_def]) >>
  rename1 `abi_encoder_registered_effect ids outs pre q` >>
  rewrite_tac [pure_frame_def] >> conj_tac
  >- (map_every qx_gen_tac [`nm`,`b`,`n`] >> disch_tac >>
      `local_region ce ee.scopes pre nm b n <=> local_region ce ee.scopes s nm b n` by
        (irule local_region_lookup_cong >> rpt strip_tac >>
         qpat_assum `!x. not_fresh_at st x ==> lookup_var x pre = _` irule >>
         drule_all_then ACCEPT_TAC exprOperandVarTheory.environment_var_not_fresh) >>
      `local_region ce ee.scopes s nm b n` by
        (qpat_assum `local_region ce ee.scopes pre nm b n <=> _`
           (fn th => ONCE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
      `mem_bytes_at b n q.vs_memory = mem_bytes_at b n s.vs_memory` by
        (qpat_assum `!b n. _ ==> mem_bytes_at b n q.vs_memory = _ /\ _`
           (qspecl_then [`b`,`n`] mp_tac) >> impl_tac
         >- (disj2_tac >> disj1_tac >> qexists_tac `nm` >> first_assum ACCEPT_TAC) >>
         disch_then (ACCEPT_TAC o CONJUNCT1)) >>
      qpat_assum `!b n. _ ==> mem_bytes_at b n pre.vs_memory = _ /\ _`
         (qspecl_then [`b`,`n`] mp_tac) >> impl_tac
      >- (disj2_tac >> disj1_tac >> qexists_tac `nm` >> first_assum ACCEPT_TAC) >>
      disch_then (SUBST1_TAC o CONJUNCT1) >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_tac >> rename1 `mem_bytes_at a n q.vs_memory = _` >>
  `!id b k. id IN ids /\ FLOOKUP q.vs_allocas id = SOME (b,k) ==>
     a+n <= b \/ b+k <= a` by
    (rpt strip_tac >>
     qpat_assum `!aid. aid IN ids ==> _`
       (drule_then (CONJUNCTS_THEN2 assume_tac
         (qx_choosel_then [`scratch`,`x`] strip_assume_tac))) >>
     qpat_assum `!j b k. _ ==> regions_disjoint a n b k`
       (qspecl_then [`scratch`,`b`,`k`] mp_tac) >>
     asm_simp_tac (srw_ss()) [loweringStateRelDefsTheory.regions_disjoint_def] >>
     decide_tac) >>
  `a+n <= p \/ p+cap <= a` by
    (qpat_assum `!j b k. _ ==> regions_disjoint a n b k`
       (qspecl_then [`inst`,`p`,`cap`] mp_tac) >>
     asm_simp_tac (srw_ss()) [loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `EVERY (\(b,k). a+n <= b \/ b+k <= a) outs` by
    (qpat_assum `EVERY _ outs` mp_tac >>
     simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD] >> strip_tac >>
     rpt gen_tac >> disch_tac >> first_x_assum drule >> decide_tac) >>
  irule mem_bytes_at_bytewise >> rpt strip_tac >>
  irule abi_encode_registered_protected_byte >>
  qexistsl_tac [`ids`,`a`,`n`,`outs`] >> asm_rewrite_tac[]
QED

Theorem abi_encode_tuple_exit_landing_mods:
  stmt_state_rel H0 ctx func ce cx es s0 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce st /\
  sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  ann = BaseT (BytesT (Dynamic limit)) /\
  evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs =
    INL (BytesV (abi_encode_method_id_bytes mid ++ bytes)) /\
  LENGTH (abi_encode_method_id_bytes mid ++ bytes) <= limit /\
  32 + LENGTH (abi_encode_method_id_bytes mid ++ bytes) <= cap /\
  prefix = abi_encode_method_id_bytes mid /\ k = LENGTH prefix /\ lo <= p /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  wb_frame ce es ee sa s0 s /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  wb_frame ce es ee sa s0 pre /\
  (~EXISTS expr_has_effect args ==> pure_frame ce func es sa s0 pre) /\
  (!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x s) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = st.cs_next_id /\
  not_local_ptr ce ee.scopes root /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d st s G tn
    st.cs_next_id p cap root dp (32+k) prefix ready pre Gpre tnpre /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d st s G tn
    st.cs_next_id p cap root dp (32+k) prefix body_end q Gq tq /\
  abi_tuple_row_effects_mods ce ee func st.cs_next_id p cap (32+k) ready.cs_next_id
    ready pre Gpre tnpre body_end q Gq tq /\
  eval_operand len q = SOME (n2w (LENGTH bytes)) /\ op_taint tq len = {} /\
  (!x. len = Var x ==> not_fresh_at body_end x) /\
  mem_bytes_at (p+(32+k)) (LENGTH bytes) q.vs_memory = bytes /\
  (!j. p+(32+k) <= j /\ j < p+(32+k)+LENGTH bytes ==> j NOTIN tq.t_mem) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (pre,Gpre,tnpre) [] (OK q,Gq,tq)) ==>
  abi_encode_payload_landing_mods ctx func ce cx st0 DF lo d explicit PG
    ann ensure mid target args vs (es,sa,s0,G0,tn0) ee (pre,Gpre,tnpre)
    (body_end,st.cs_next_id,p,cap,root,len) (bytes,limit,q,Gq,tq)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `pure_frame ce func ee st pre q` by (drule_all_then ACCEPT_TAC tuple_exit_pure) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    (qpat_assum `storage_trace_domain _ _ _` (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
  qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q _ _`
    (mp_then (Pos hd) mp_tac abi_tuple_buffer_resources_mods) >>
  (impl_tac >- (qexists_tac `storage_trace_horizon ee.storage_trace` >> first_assum ACCEPT_TAC)) >>
  disch_then strip_assume_tac >>
  drule_then assume_tac alloca_room_next_lt >>
  qpat_x_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q _ _`
    (strip_assume_tac o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
  qpat_x_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_tuple_row_effects_mods_def]) >>
  suspend "frames"
QED

Resume abi_encode_tuple_exit_landing_mods[frames]:
  `wb_frame ce es ee sa s0 q` by
    (match_mp_tac (Q.INST [`H` |-> `H0`,`s1` |-> `st`,`t` |-> `s`,`es1` |-> `ee`]
        (SPEC_ALL wb_frame_trans)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 Gq tq` by
    (irule ghost_kept_at_trans >>
     qexistsl_tac [`G`,`ee`,`s`,`st`,`tn`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (gen_tac >> gen_tac >> gen_tac >> once_rewrite_tac [EQ_SYM_EQ] >>
         irule wb_frame_local_regions >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- (qexistsl_tac [`ee`,`sa`] >> conj_tac >> first_assum ACCEPT_TAC) >>
         qexistsl_tac [`H0`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC) >>
     qpat_assum `wb_frame ce es ee sa s0 s`
       (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [wb_frame_def])) >>
  `~EXISTS expr_has_effect args ==> pure_frame ce func es sa s0 q` by
    (disch_tac >>
     irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`ee`,`st`,`pre`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qpat_assum `wb_frame ce es ee sa s0 pre`
           (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [wb_frame_def]))
     >- (rpt strip_tac >> drule_all_then ACCEPT_TAC abi_encoder_registered_effect_allocated) >>
     qpat_assum `~EXISTS expr_has_effect args ==> pure_frame ce func es sa s0 pre`
       (drule_then ACCEPT_TAC)) >>
  suspend "finish"
QED

Resume abi_encode_tuple_exit_landing_mods[finish]:
  `local_ptrs_rel func ce ee.scopes q` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ q /\ _`
       (drule_then (strip_assume_tac o CONJUNCT1)) >>
     drule_then (ACCEPT_TAC o CONJUNCT1) stmt_state_rel_local_ptrs_alloca) >>
  `sa.cs_next_var <= body_end.cs_next_var` by decide_tac >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at body_end x` by
    (rpt gen_tac >> disch_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `st` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     first_assum (drule_then ACCEPT_TAC)) >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at body_end x` by
    (rpt gen_tac >> disch_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `st` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     first_assum (drule_then ACCEPT_TAC)) >>
  `s0.vs_alloca_next <= q.vs_alloca_next` by decide_tac >>
  `p+(32+k)-LENGTH prefix = p+32` by decide_tac >>
  `mem_bytes_at (p+32) (LENGTH prefix) q.vs_memory = prefix` by
    (qpat_assum `read_memory _ _ q = prefix`
       (mp_tac o REWRITE_RULE [read_memory_eq_mem_bytes_at]) >>
     qpat_assum `p+(32+k)-LENGTH prefix = p+32` (fn th => simp_tac bool_ss [th])) >>
  `!i. p+32 <= i /\ i < p+32+LENGTH prefix+LENGTH bytes ==> i NOTIN tq.t_mem` by
    (gen_tac >> strip_tac >> Cases_on `i < p+(32+k)`
     >- (qpat_assum `!i. p+(32+k)-LENGTH prefix <= i /\ _ ==> _` irule >> decide_tac) >>
     qpat_assum `!j. p+(32+k) <= j /\ _ ==> _` irule >> decide_tac) >>
  simp_tac bool_ss [abi_encode_payload_landing_mods_def, LET_THM] >>
  qpat_x_assum `prefix = abi_encode_method_id_bytes mid` SUBST_ALL_TAC >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (disch_tac >>
      qpat_assum `ctx_has_dalloca ctx ==> _ /\ _`
        (drule_then (ACCEPT_TAC o CONJUNCT1)))
  >- (rewrite_tac [expr_has_effect_thm] >> first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ q /\ _`
        (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `k = LENGTH _` (SUBST_ALL_TAC o SYM) >>
  rewrite_tac [GSYM ADD_ASSOC] >> first_assum ACCEPT_TAC
QED

Finalise abi_encode_tuple_exit_landing_mods
