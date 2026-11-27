(* Enter the linked ABI fold after the shared ALLOCA, selector MSTORE,
   and payload-address ADD. The cursor ALLOCA belongs to the fold itself. *)
Theory bodyExtPackingEntryMods
Ancestors
  bodyExtPhysicalPrefixMods bodyExtPackingEndpointMods bodyExtPackingFrameMods
  ptrDiscipline fragExec
  bodyFullAbiEncodeOffset bodyPtrMakeArrayEmission bodyFullPathHistory
  abiEncodeValuesCode stateRelProj allocationPtr gasOriginPtrLabels fragFuel
  compileEnv entryDecodeStructure bodyFullHashKeccakFixed exprSimOperands
  decoderGhostFramePtr loweringShapeDefs fragGasOriginPtrLoop
  loweringPosts bodyPtrDefs abiEncoderWindowContract exprLoweringProps
  venomState words finite_map pred_set arithmetic

Theorem ext_packing_entry_mods:
  compile_alloc_buffer n sa = (shared,sb) /\
  emit_void MSTORE [shared.buf_operand;Lit (calldata_method_id bs)] sb = ((),sc) /\
  emit_op ADD [shared.buf_operand;Lit 32w] sc = (dst,sd) /\
  compile_abi_encode_values_to_buf ce dst rows sd = (out,en) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\
  fn_has_code sc sd func /\ fn_has_code sd en func /\ fn_inst_ids_distinct func /\
  LENGTH bs = 4 /\ 32 <= n /\ n < dimword (:256) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func ce cx ee s /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at_mods (DF H) lo ret ce cx ee G tn s /\
       immutable_frame_mods func ce cx ee s) /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?root dp b u Gu tu.
    shared.buf_operand = Var root /\ dst = Var dp /\
    ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret sa s G tn
      sa.cs_next_id b n root dp bs sd u Gu tu /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func) /\
    lo <= b /\ b+n < dimword (:256) /\ b+n <= u.vs_alloca_next /\
    ci_mono sa sd /\ local_ptrs_reserved ce sd /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      op_taint tu (Var x) = op_taint tn (Var x)) /\
    alloca_inv u /\ alloca_room ctx func u /\ allocas_from lo u /\
    lo <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
      u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp) /\
    (!p k. FLOOKUP u.vs_allocas sd.cs_next_id = SOME (p,k) ==> k = 32) /\
    (return_buf_frame ret ce sa s ==> return_buf_frame ret ce sd u) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `es` |-> `ee`, `d` |-> `ret`]
    ext_physical_prefix_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  rename1 `shared.buf_operand = Var root` >>
  rename1 `lookup_var root t = SOME w` >>
  rename1 `ptr_covers gt tt root t n` >>
  `stmt_state_rel H0 ctx func ce cx ee t` by simp[] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (qpat_assum `stmt_state_rel H0 ctx func ce cx ee t`
      (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  `emit_op ADD [Var root;Lit (n2w 32)] sc = (dst,sd)` by
    (qpat_assum `shared.buf_operand = Var root` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `32 + (n-32) <= n /\ w2n w + 32 < dimword (:256)` by decide_tac >>
  drule_all (Q.INST [`off` |-> `32`, `n` |-> `(n:num) - 32`]
    (SPEC_ALL abi_encode_owned_offset_origin)) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  strip_tac >>
  rename1 `dst = Var dp` >>
  rename1 `lookup_var dp u = SOME _` >>
  rename1 `ptr_covers Gu tu dp u (n-32)` >>
  suspend "entry"
QED

Resume ext_packing_entry_mods[entry]:
  `!x. not_fresh_at sc x ==> x <> dp` by
    (drule_all emit_op_fetch_boundary >> strip_tac >> gvs[]) >>
  `!x. not_fresh_at sa x ==> x <> dp` by
    (gen_tac >> disch_tac >> qpat_assum `!x. not_fresh_at sc x ==> x <> dp` irule >>
     irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists `sa` >> fs[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==>
     lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
     op_taint tu (Var x) = op_taint tn (Var x)` by simp[] >>
  `ci_mono sc sd` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sa sd` by (irule ci_mono_trans >> qexists `sc` >> simp[]) >>
  `sa.cs_next_var <= sd.cs_next_var /\ sc.cs_next_var <= sd.cs_next_var` by fs[ci_mono_def] >>
  `sa.cs_next_id < sd.cs_next_id` by
    (drule emit_op_next_id >> fs[ci_mono_def]) >>
  `!H:(bool # bytes32 # type_value) list # num list.
     stmt_state_rel H ctx func ce cx ee t ==> stmt_state_rel H ctx func ce cx ee u` by
    (rpt strip_tac >>
     `not_local_ptr ce ee.scopes dp` by metis_tac[fresh_not_local_ptr] >>
     qpat_assum `u = _` SUBST1_TAC >>
     simp[stmt_state_rel_inst_idx, stmt_state_rel_update_var]) >>
  `u.vs_accounts = t.vs_accounts /\ u.vs_transient = t.vs_transient /\
   u.vs_call_ctx = t.vs_call_ctx /\ u.vs_immutables = t.vs_immutables /\
   u.vs_data_section = t.vs_data_section` by
    (qpat_x_assum `u = _` SUBST1_TAC >> simp[update_var_def]) >>
  qpat_x_assum `u = _` kall_tac >>
  `stmt_state_rel H0 ctx func ce cx ee u` by
    (qpat_assum `!H. stmt_state_rel H ctx func ce cx ee t ==> stmt_state_rel H ctx func ce cx ee u`
       irule >> first_assum ACCEPT_TAC) >>
  `alloca_inv t` by
    (qpat_assum `stmt_state_rel H0 ctx func ce cx ee t`
       (mp_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `alloca_history func u` by
    (qpat_assum `!D. gas_origin_ptr_path _ (t,gt,tt) [] (OK u,Gu,tu)`
       (qspec_then `ARB` assume_tac) >>
     drule_all_then ACCEPT_TAC body_full_path_alloca_history) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by fs[window_alloca_growth_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`gt`,`t`,`tt`] >> simp[]) >>
  qexistsl [`root`,`dp`,`w2n w`,`u`,`Gu`,`tu`] >>
  asm_rewrite_tac[] >>
  conj_tac >- suspend "endpoint" >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists `sc` >> simp[]) >>
  suspend "resources"
QED

Resume ext_packing_entry_mods[endpoint]:
  `!x. not_fresh_at sc x ==>
     lookup_var x u = lookup_var x t /\ FLOOKUP Gu x = FLOOKUP gt x /\
     op_taint tu (Var x) = op_taint tt (Var x)` by simp[] >>
  `ptr_covers Gu tu root u n` by
    (irule ptr_covers_frame >> qexistsl [`gt`,`t`,`tt`] >> simp[]) >>
  `pure_frame ce func ee sc t u` by simp[pure_frame_def] >>
  `window_alloca_growth t u` by
    (simp[window_alloca_growth_def] >> rpt strip_tac >> gvs[]) >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `sa` >> fs[ci_mono_def]) >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `sa` >> fs[ci_mono_def]) >>
  `!D. ghost_inv_at_mods D lo ret ce cx ee gt tt t /\ immutable_frame_mods func ce cx ee t ==>
       ghost_inv_at_mods D lo ret ce cx ee Gu tu u /\ immutable_frame_mods func ce cx ee u` by
    (gen_tac >> strip_tac >> irule (INST_TYPE [Type.alpha |-> ``:256``] ext_packing_frame_mods) >>
     qexistsl [`gt`,`H0`,`ctx`,`sc`,`tt`,`t`] >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func ce cx ee u /\ storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at_mods (DF H) lo ret ce cx ee Gu tu u /\ immutable_frame_mods func ce cx ee u` by
    (qx_gen_tac `h` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     conj_tac >- (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ t ==> _` irule >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!D. ghost_inv_at_mods D _ _ _ _ _ gt tt t /\ _ ==> _`
       (qspec_then `DF h` mp_tac) >>
     impl_tac >- (qpat_assum `!D. ghost_inv_at_mods D _ _ _ _ _ G tn s /\ _ ==> _`
       (qspec_then `DF h` mp_tac) >> simp[]) >>
     simp[]) >>
  `wb_frame ce ee ee sa s u` by
    (qpat_x_assum `wb_frame ce ee ee sa s t` mp_tac >>
     simp[wb_frame_def,locals_kept_def,popped_kept_def]) >>
  `ghost_kept_at lo ce ee sa G tn s Gu tu` by
    (qpat_assum `!ce es origin G0 tn0 s0. ghost_kept_at _ _ _ _ _ _ _ _ _ /\ _ ==> _` irule >>
     simp[] >> metis_tac[]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK u,Gu,tu)`
      (qspec_then `ARB` (mp_tac o MATCH_MP gas_origin_ptr_path_preserves_labels)) >> simp[]) >>
  `window_alloca_growth s u` by
    (qpat_x_assum `window_alloca_growth s t` mp_tac >> simp[window_alloca_growth_def]) >>
  `pure_frame ce func ee sa s u` by
    (qpat_x_assum `pure_frame ce func ee sa s t` mp_tac >> simp[pure_frame_def]) >>
  `not_fresh_at sd root` by
    (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists `sc` >> simp[]) >>
  simp[ext_packing_endpoint_mods_def, read_memory_def] >>
  rpt conj_tac
  >- (qpat_assum `read_memory _ 4 t = bs`
        (ACCEPT_TAC o REWRITE_RULE[venomStateTheory.read_memory_def])) >>
  map_every qx_gen_tac [`p0`,`k0`] >>
  qpat_x_assum `!a k. _ ==> mem_bytes_at a k t.vs_memory = _ /\ _`
    (qspecl_then [`p0`,`k0`] mp_tac) >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume ext_packing_entry_mods[resources]:
  `alloca_inv u` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `alloca_room ctx func u` by (drule stmt_state_rel_alloca_room >> simp[]) >>
  `fmp_room ctx func u` by (drule stmt_state_rel_fmp_room >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `stmt_state_rel H0 ctx func ce cx ee u`
      (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  simp[allocas_from_def] >>
  (conj_tac >- (fs[allocas_from_def])) >>
  (conj_tac >- (strip_tac >> fs[fmp_room_def] >> decide_tac)) >>
  conj_tac >- suspend "cursor" >>
  Cases_on `ret` >> simp[return_buf_frame_def] >>
  PairCases_on `x` >> simp[return_buf_frame_def] >>
  strip_tac >> rename1 `lookup_var x s = SOME wret` >>
  `not_fresh_at sd x` by
    (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  metis_tac[LESS_EQ_TRANS]
QED

Resume ext_packing_entry_mods[cursor]:
  drule_then strip_assume_tac abi_encode_values_to_buf_trace >>
  `ci_mono sd en` by metis_tac[ci_mono_compile_abi_encode_values_to_buf,pairTheory.SND] >>
  `ci_mono sd allocated` by metis_tac[ci_mono_emit_op,pairTheory.SND] >>
  `ci_mono allocated ready` by metis_tac[ci_mono_emit_void,pairTheory.SND] >>
  `ci_mono ready stored` by metis_tac[ci_mono_compile_abi_encode_value_rows,pairTheory.SND] >>
  `ci_mono stored en` by metis_tac[ci_mono_emit_op,pairTheory.SND] >>
  `ci_mono allocated en` by
    (irule ci_mono_trans >> qexists `ready` >> simp[] >>
     irule ci_mono_trans >> qexists `stored` >> simp[]) >>
  `fn_has_code sd allocated func` by
    (mp_tac (Q.SPECL [`sd`,`allocated`,`en`,`func`] fn_has_code_split) >>
     fs[ci_mono_def]) >>
  drule_all_then strip_assume_tac
    (Q.INST [`opc` |-> `ALLOCA`, `sm` |-> `sd`, `s` |-> `u`]
       emit_op_fetch_boundary) >>
  rename1 `cursor = Var cv` >>
  `MEM (mk_inst sd.cs_next_id ALLOCA [Lit 32w] [cv]) (fn_insts func)` by
     (drule_all_then ACCEPT_TAC lookup_block_get_instruction_fn_insts) >>
  rpt gen_tac >> disch_tac >>
  `32 < dimword (:256)` by simp[] >>
  drule_all_then strip_assume_tac
    (Q.INST [`n` |-> `32`, `s` |-> `t`] (SPEC_ALL stmt_state_rel_alloca_site_bound)) >>
  simp[]
QED

Finalise ext_packing_entry_mods
