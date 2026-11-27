(* Restore the caller at the selected INVOKE's merged endpoint. *)
Theory bodySelectedCallerMergeMods
Ancestors
  bodyFullIntCallReturnFrame bodyFullPostsMods bodyFullShadowBodyInv
  intCallStep lowerDloadPtrReturn allocasBelowFmpUpdatesProps allocaHistory
  vyperPlaceWriteSoundness vyperFiniteStoragePreservation allocaSiteResource
  exprBopSimProps valueEncodingDefs loweringStateRelDefs exprLoweringProps
  stateRelProj bodyInvSplit bodyInvCodeProps vyperImmutableMetadataFrame vyperState
  venomMemDefs venomExecSemantics ptrDiscipline bodyPtrDefs compileEnv finite_map
  exprSimProps loweringPosts fnRunFields execMemoryLength list
  gasOutcomeFull gasOutcomeFullMods fragGasOriginPtr vyperStorageFootprint
  bodySelectedReturnSourceSuccessMods bodySelectedReturnFocusMods
  bodySelectedReturnAbortMods bodySelectedInvokeReturnEdgeMods
  bodySelectedResultStoresMods bodySelectedStoredCallerFrameMods
  bodySelectedStoredReturnValueMods bodySelectedCallerSretMods
  bodySelectedNoBufferReturnMods bodySelectedReturnUnwrapMods
  bodyFullIntCallReturnTyping bodyFullIntCallReturnValue exprBodyPreProps
  typedMemoryCopy exprSimHypsDefs bodyIntCallStageCutsMods bodyIntCallStagePacketMods
  bodyPtrMakeArrayPrimitiveInstall emitHelper fragExec
Libs monadsyntax

Theorem caller_local_registered_bound[local]:
  local_ptrs_rel func ce scopes t /\ local_region ce scopes t n b sz ==>
  b + sz <= t.vs_alloca_next
Proof
  simp[local_region_def, local_ptrs_rel_def] >> rpt strip_tac >>
  qpat_x_assum `!n e p sz. _ ==> ?w. _` drule_all >> strip_tac >> gvs[]
QED

Theorem caller_region_below_unit[local]:
  contract_inv mods exps ctx ce cx /\ expr_sim_inv_mods mods ce cx env es /\
  dead_lo_ok_mods H D lo ce cx /\
  immutable_decl_sep_mods ce cx es.scopes t.vs_vars t.vs_allocas t.vs_alloca_next /\
  (local_region ce es.scopes t n b sz \/ FLOOKUP t.vs_allocas aid = SOME (b,sz)) /\
  0 < sz ==> lo <= b
Proof
  strip_tac >> drule contract_inv_cenv_modules >> strip_tac >>
  Cases_on `ce.ce_is_ctor` >> gvs[dead_lo_ok_mods_def] >>
  `b < b + sz` by simp[] >>
  metis_tac[intcall_local_immutable_prefix_disjoint_mods,
            intcall_alloca_immutable_prefix_disjoint_mods, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem caller_linked_sep[local]:
  immutable_frame_mods func ce cx es t ==>
  immutable_decl_sep_mods ce cx es.scopes t.vs_vars t.vs_allocas t.vs_alloca_next
Proof
  simp[immutable_frame_mods_def, immutable_alloca_sep_mods_def,
       immutable_decl_sep_mods_def, immutable_alloca_sep_def]
QED

Theorem caller_region_preserved[local]:
  lo <= b /\ b + sz <= t.vs_alloca_next /\
  (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
     n <= aid /\ aid < m ==> regions_disjoint b sz a cap) /\
  (!b sz. lo <= b /\ b + sz <= t.vs_alloca_next /\
     (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
        n <= aid /\ aid < m ==> regions_disjoint b sz a cap) ==>
     mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  (!i. lo <= i /\ i < t.vs_alloca_next /\ i IN tc.t_mem /\
     (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
        n <= aid /\ aid < m ==> i < a \/ a + cap <= i) ==> i IN tn.t_mem) ==>
  mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory /\
  (!i. b <= i /\ i < b + sz /\ i IN tc.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >> conj_tac
  >- (qpat_x_assum `!b sz. _ ==> mem_bytes_at _ _ _ = _` irule >> simp[] >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >> qpat_x_assum `!i. lo <= i /\ _ ==> _` irule >>
  `lo <= i /\ i < t.vs_alloca_next` by decide_tac >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!aid a cap. _ ==> regions_disjoint _ _ _ _` drule_all >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem caller_local_regions_merge[local]:
  local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t) ==>
  !n b sz. local_region ce scopes u n b sz <=> local_region ce scopes t n b sz
Proof
  simp[local_ptrs_reserved_def, local_region_def] >> metis_tac[]
QED

Theorem caller_source_immutables_case[local]:
  get_source_immutables src (case opt of NONE => [] | SOME imms => imms) =
  (case opt of NONE => FEMPTY | SOME imms => get_source_immutables src imms)
Proof
  Cases_on `opt` >> simp[get_source_immutables_def]
QED

Theorem caller_immutable_sep_merge[local]:
  immutable_alloca_sep func ce cx es t /\
  immutable_metadata_frame es ee /\ ee.scopes = es.scopes /\
  (!n b sz. local_region ce es.scopes u n b sz ==> local_region ce es.scopes t n b sz) /\
  u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next ==>
  immutable_alloca_sep func ce cx ee u
Proof
  simp[immutable_alloca_sep_def, immutable_decl_sep_alt] >> strip_tac >>
  conj_tac >- metis_tac[] >> strip_tac >> rpt strip_tac >>
  `?old. FLOOKUP
     (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,old)` by
    (metis_tac[SIMP_RULE bool_ss [caller_source_immutables_case]
                immutable_metadata_frame_value_lookup]) >> metis_tac[]
QED

Theorem caller_merge_physical[local]:
  stmt_state_rel H ctx func ce cx es t /\ immutable_frame_mods func ce cx es t /\
  state_rel H func ce cx (ee with scopes := []) cs /\
  immutables_rel_mods ce cx.txn.target ce.ce_is_ctor ee cs /\
  immutable_metadata_frame es ee /\ ee.scopes = es.scopes /\
  local_ptrs_reserved ce sa /\ (!x. MEM x outs ==> ~not_fresh_at sa x) /\
  (!n b sz. local_region ce es.scopes t n b sz ==>
     mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  ir.iret_adopt_fmp = NONE /\ LENGTH t.vs_memory <= LENGTH cs.vs_memory /\
  cs.vs_call_ctx = t.vs_call_ctx /\ cs.vs_tx_ctx = t.vs_tx_ctx /\
  cs.vs_block_ctx = t.vs_block_ctx /\ cs.vs_data_section = t.vs_data_section /\
  cs.vs_code = t.vs_code ==>
  stmt_state_rel H ctx func ce cx ee u /\ immutable_frame_mods func ce cx ee u /\
  u.vs_fmp = t.vs_fmp /\ u.vs_initial_fmp = t.vs_initial_fmp /\
  u.vs_current_bb = t.vs_current_bb /\ u.vs_inst_idx = t.vs_inst_idx
Proof
  strip_tac >> drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule intCallFrameTheory.invoke_return_frame >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t` by metis_tac[] >>
  `!n b sz. local_region ce es.scopes u n b sz <=> local_region ce es.scopes t n b sz` by
    (irule caller_local_regions_merge >> qexists_tac `sa` >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  `EVERY (not_local_ptr ce es.scopes) outs` by
    (simp[EVERY_MEM, not_local_ptr_def] >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `local_ptrs_rel func ce es.scopes u` by
    (irule intCallFrameTheory.invoke_return_local_ptrs_rel >>
     goal_assum (drule_at (Pat `bind_outputs _ _ _ = SOME _`)) >>
     simp[] >> metis_tac[]) >>
  `immutable_alloca_sep func ce cx ee u` by
    (irule caller_immutable_sep_merge >>
     qexistsl_tac [`es`,`t`] >> simp[] >> drule return_stmt_immutable_sep >> simp[]) >>
  `immutable_alloca_sep_mods func ce cx ee u` by
    (fs[immutable_frame_mods_def, immutable_alloca_sep_mods_def] >>
     rpt strip_tac >> irule caller_immutable_sep_merge >>
     qexistsl_tac [`es`,`t`] >> simp[] >>
     gvs[local_region_def]) >>
  drule dload_bind_outputs_frame >> strip_tac >>
  `state_rel H func ce cx ee u` by
    (irule exprLoweringPropsTheory.state_rel_frame >>
     conj_tac >- simp[] >> qexistsl_tac [`ee with scopes := []`,`cs`] >>
     drule state_rel_immutables_rel >>
     qpat_assum `u = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[immutables_rel_def, adopt_return_fmp_def, merge_callee_state_def,
          evaluation_state_component_equality]) >>
  conj_tac
  >- (irule stmt_state_rel_allocas_frame >> simp[] >>
      conj_tac
      >- (irule immutable_base_zero_frame >> qexists_tac `t` >>
          conj_tac >- (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
          conj_tac
          >- (qpat_assum `u = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
              simp[adopt_return_fmp_def, merge_callee_state_def]) >>
          drule stmt_state_rel_immutable_base_zero >> simp[]) >>
      qexistsl_tac [`es`,`t`] >>
      qpat_assum `u = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
      simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  simp[immutable_frame_mods_def] >>
  qpat_assum `u = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
  fs[immutables_rel_mods_def, immutables_rel_def, adopt_return_fmp_def,
     merge_callee_state_def] >> first_assum ACCEPT_TAC
QED

Theorem caller_merge_ghost[local]:
  ghost_inv_at_mods D lo d ce cx es G tn t /\
  stmt_state_rel H ctx func ce cx es t /\ ee.scopes = es.scopes /\
  local_ptrs_reserved ce sa /\ (!x. MEM x outs ==> ~not_fresh_at sa x) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  stor_taint_ok_at D tc cs /\
  (!i. i < lo /\ i IN tc.t_mem ==>
     imm_section_dead_mods ce (mem_bytes_at 0 lo cs.vs_memory) i) /\
  (!n b sz. local_region ce es.scopes t n b sz ==>
     mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory /\
     (!i. b <= i /\ i < b + sz /\ i IN tc.t_mem ==> i IN tn.t_mem)) /\
  cs.vs_call_ctx = t.vs_call_ctx ==>
  ghost_inv_at_mods D lo d ce cx ee (DRESTRICT G (COMPL (set outs)))
    (tc with t_var := DRESTRICT tn.t_var (COMPL (set outs))) u
Proof
  strip_tac >> drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule intCallFrameTheory.invoke_return_frame >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> ~MEM x outs` by metis_tac[] >>
  simp[ghost_inv_at_mods_def] >> rpt conj_tac
  >- suspend "local"
  >- suspend "buf"
  >- suspend "pc"
  >- suspend "storage"
  >- suspend "base"
  >> fs[ghost_inv_at_mods_def, allocas_from_def] >> first_assum ACCEPT_TAC
QED
Resume caller_merge_ghost[local]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `~MEM p outs /\ lookup_var p u = lookup_var p t` by metis_tac[] >>
  `ptr_covers G tn p t sz /\
   !w mem. lookup_var p t = SOME w /\
      mem_agree_outside tn.t_mem t.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem` by
    (fs[ghost_inv_at_mods_def] >> metis_tac[]) >>
  conj_tac >- fs[ptr_covers_def, op_taint_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >>
  `local_region ce es.scopes t name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  qpat_x_assum `!n b sz. local_region _ _ _ n b sz ==> _` drule >> strip_tac >>
  `type_memory_size entry.type <= sz /\ val_wf entry.type entry.value` by
    (fs[local_ptrs_rel_def] >>
     qpat_x_assum `!n e p sz. _ ==> ?w. _` drule_all >> strip_tac >> gvs[]) >>
  drule exprSimPropsTheory.val_footprint_le >> strip_tac >>
  irule bodyPtrMakeArrayMemoryFrameTheory.robust_val_in_memory_shrinking_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`tn.t_mem`,`tc.t_mem`,`t.vs_memory`,`cs.vs_memory`,`sz`] >>
  simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED
Resume caller_merge_ghost[buf]:
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME p) _ _ _ _` >> PairCases_on `p` >>
  fs[ghost_inv_at_mods_def, return_buf_ptr_def] >>
  `not_fresh_at sa x /\ ~MEM x outs` by metis_tac[] >>
  simp[ptr_covers_def, op_taint_def, FLOOKUP_DRESTRICT] >>
  gvs[ptr_covers_def, op_taint_def]
QED
Resume caller_merge_ghost[pc]:
  rpt strip_tac >>
  `not_fresh_at sa x /\ ~MEM x outs` by metis_tac[] >>
  fs[ghost_inv_at_mods_def, op_taint_def, FLOOKUP_DRESTRICT]
QED
Resume caller_merge_ghost[storage]:
  drule dload_bind_outputs_frame >> strip_tac >>
  qpat_assum `u = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
  Cases_on `ir.iret_adopt_fmp` >>
  fs[stor_taint_ok_at_def, adopt_return_fmp_def, merge_callee_state_def]
QED
Resume caller_merge_ghost[base]:
  rpt strip_tac >>
  `not_fresh_at sa x` by fs[local_ptrs_reserved_def] >> `~MEM x outs` by simp[] >>
  fs[ghost_inv_at_mods_def, op_taint_def, FLOOKUP_DRESTRICT]
QED
Finalise caller_merge_ghost[local]

(* The same reached exit preserves caller regions outside the staged IDs. *)
Theorem caller_merge_regions[local]:
  contract_inv mods exps ctx ce cx /\ expr_sim_inv_mods mods ce cx env es /\
  stmt_state_rel H ctx func ce cx es t /\ immutable_frame_mods func ce cx es t /\
  dead_lo_ok_mods H D lo ce cx /\
  (!n b sz aid a cap. local_region ce es.scopes t n b sz /\
     FLOOKUP t.vs_allocas aid = SOME (a,cap) /\ front <= aid /\ aid < stop ==>
     regions_disjoint b sz a cap) /\
  (!b sz. lo <= b /\ b + sz <= t.vs_alloca_next /\
     (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
        front <= aid /\ aid < stop ==> regions_disjoint b sz a cap) ==>
     mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  (!i. lo <= i /\ i < t.vs_alloca_next /\ i IN tc.t_mem /\
     (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
        front <= aid /\ aid < stop ==> i < a \/ a + cap <= i) ==> i IN tn.t_mem) ==>
  (!n b sz. local_region ce es.scopes t n b sz ==>
     mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory /\
     (!i. b <= i /\ i < b + sz /\ i IN tc.t_mem ==> i IN tn.t_mem)) /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ aid < front ==>
     mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory /\
     (!i. b <= i /\ i < b + sz /\ i IN tc.t_mem ==> i IN tn.t_mem))
Proof
  strip_tac >> drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule caller_linked_sep >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `sz = 0`
      >- simp[mem_bytes_at_def] >>
      `lo <= b` by
        (irule caller_region_below_unit >>
         goal_assum (drule_at (Pat `contract_inv _ _ _ _ _`)) >>
         goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >>
         goal_assum (drule_at (Pat `dead_lo_ok_mods _ _ _ _ _`)) >> simp[] >>
         qexistsl_tac [`ARB`,`n`,`sz`,`t`] >> simp[]) >>
      `b + sz <= t.vs_alloca_next` by metis_tac[caller_local_registered_bound] >>
      irule caller_region_preserved >>
      simp[] >> qexistsl_tac [`lo`,`stop`,`front`] >> asm_rewrite_tac[] >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `sz = 0` >- simp[mem_bytes_at_def] >>
  `lo <= b` by
    (irule caller_region_below_unit >>
     goal_assum (drule_at (Pat `contract_inv _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `dead_lo_ok_mods _ _ _ _ _`)) >> simp[] >>
     qexistsl_tac [`aid`,`ARB`,`sz`,`t`] >> simp[]) >>
  `b + sz <= t.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  irule caller_region_preserved >>
  simp[] >> qexistsl_tac [`lo`,`stop`,`front`] >> asm_rewrite_tac[] >>
  rpt strip_tac >>
  `aid <> aid'` by decide_tac >>
  fs[alloca_inv_def, allocas_non_overlapping_def,
     loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]
QED

Theorem caller_merge_kept[local]:
  ghost_kept_at lo ce es0 sa G0 tn0 s0 G tn /\
  locals_kept ce es0 es s0 t /\ ee.scopes = es.scopes /\
  local_ptrs_reserved ce sa /\ (!x. MEM x outs ==> ~not_fresh_at sa x) /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
  (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
     (!n a cap. local_region ce es0.scopes s0 n a cap ==>
        b + sz <= a \/ a + cap <= b) ==>
     mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
  (!n b sz. local_region ce es.scopes t n b sz ==>
     mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory /\
     (!i. b <= i /\ i < b + sz /\ i IN tc.t_mem ==> i IN tn.t_mem)) /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id ==>
     mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory /\
     (!i. b <= i /\ i < b + sz /\ i IN tc.t_mem ==> i IN tn.t_mem)) ==>
  locals_kept ce es0 ee s0 u /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
     (!n a cap. local_region ce es0.scopes s0 n a cap ==>
        b + sz <= a \/ a + cap <= b) ==>
     mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
  ghost_kept_at lo ce es0 sa G0 tn0 s0 (DRESTRICT G (COMPL (set outs)))
    (tc with t_var := DRESTRICT tn.t_var (COMPL (set outs)))
Proof
  strip_tac >> drule intCallFrameTheory.invoke_return_frame >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t` by metis_tac[] >>
  `!n b sz. local_region ce es0.scopes s0 n b sz ==> local_region ce es.scopes t n b sz` by
    (rpt gen_tac >> strip_tac >>
     irule exprSimPropsTheory.local_region_frame_fwd >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     qexists_tac `sa` >> fs[locals_kept_def]) >>
  conj_tac >- suspend "local_bytes" >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  fs[ghost_kept_at_def] >> conj_tac
  >- (rpt strip_tac >> `~MEM x outs` by metis_tac[] >>
      fs[op_taint_def, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  conj_tac >- suspend "alloca_taint" >>
  rpt strip_tac >> metis_tac[]
QED

Resume caller_merge_kept[local_bytes]:
  irule exprSimPropsTheory.locals_kept_regions_tail >>
  qexists_tac `t` >> reverse conj_tac
  >- (pure_rewrite_tac[locals_kept_def, popped_kept_def] >>
      qpat_assum `ee.scopes = _` (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `locals_kept _ _ _ _ _`
        (ACCEPT_TAC o PURE_REWRITE_RULE [locals_kept_def, popped_kept_def])) >>
  rpt strip_tac >>
  `local_region ce es.scopes t n b sz` by metis_tac[] >>
  qpat_assum `!n b sz. local_region _ _ t n b sz ==> _` drule >> simp[]
QED
Resume caller_merge_kept[alloca_taint]:
  rpt strip_tac >>
  `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by
    (qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP t.vs_allocas aid = SOME b` drule >> simp[]) >>
  `i IN tn.t_mem` by
    (qpat_assum `!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ _ ==> _`
       drule_all >> strip_tac >> first_x_assum irule >> simp[]) >>
  qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
    drule_all >> simp[]
QED
Finalise caller_merge_kept[local]

(* At the raw INVOKE return, keep the physical fields and caller ghost at
   the very same merged state.  The result-store code, when present, starts
   after this cut. *)
Theorem selected_caller_merge_frame_mods:
  contract_inv mods exps ctx ce cx /\ expr_sim_inv_mods mods ce cx env es /\
  stmt_state_rel H ctx func ce cx es t /\ immutable_frame_mods func ce cx es t /\
  dead_lo_ok_mods H D lo ce cx /\ ghost_inv_at_mods D lo d ce cx es G tn t /\
  es.scopes = prev /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. MEM x outs ==> ~not_fresh_at sa x) /\
  ghost_kept_at lo ce es0 sa G0 tn0 s0 G tn /\ locals_kept ce es0 es s0 t /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
  (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
     (!n a cap. local_region ce es0.scopes s0 n a cap ==>
        b + sz <= a \/ a + cap <= b) ==>
     mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
  (!n b sz aid a cap. local_region ce es.scopes t n b sz /\
     FLOOKUP t.vs_allocas aid = SOME (a,cap) /\ sa.cs_next_id <= aid /\
     aid < sm.cs_next_id ==> regions_disjoint b sz a cap) /\
  state_rel H func ce cx (out with scopes := []) cs /\
  immutables_rel_mods ce cx.txn.target ce.ce_is_ctor out cs /\
  storage_well_formed_on cx out (FST H) /\ immutable_metadata_frame es out /\
  stor_taint_ok_at D tc cs /\
  (!i. i < lo /\ i IN tc.t_mem ==>
     imm_section_dead_mods ce (mem_bytes_at 0 lo cs.vs_memory) i) /\
  (!b sz. lo <= b /\ b + sz <= t.vs_alloca_next /\
     (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
        sa.cs_next_id <= aid /\ aid < sm.cs_next_id ==>
        regions_disjoint b sz a cap) ==>
     mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  (!i. lo <= i /\ i < t.vs_alloca_next /\ i IN tc.t_mem /\
     (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
        sa.cs_next_id <= aid /\ aid < sm.cs_next_id ==> i < a \/ a + cap <= i) ==>
     i IN tn.t_mem) /\
  setup_callee callee argv t = SOME setup /\ run_blocks fuel ctx callee setup = IntRet ir cs /\
  step_inst fuel ctx inst t = OK u /\
  bind_outputs outs ir.iret_values (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  ir.iret_adopt_fmp = NONE ==>
  let ee = out with scopes := prev in
  let J = DRESTRICT G (COMPL (set outs)) in
  let N = tc with t_var := DRESTRICT tn.t_var (COMPL (set outs)) in
  stmt_state_rel H ctx func ce cx ee u /\ immutable_frame_mods func ce cx ee u /\
  storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods D lo d ce cx ee J N u /\
  ghost_kept_at lo ce es0 sa G0 tn0 s0 J N /\ locals_kept ce es0 ee s0 u /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
     (!n a cap. local_region ce es0.scopes s0 n a cap ==>
        b + sz <= a \/ a + cap <= b) ==>
     mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
  u.vs_fmp = t.vs_fmp /\ u.vs_initial_fmp = t.vs_initial_fmp /\
  u.vs_current_bb = t.vs_current_bb /\ u.vs_inst_idx = t.vs_inst_idx /\
  u.vs_alloca_next = t.vs_alloca_next /\ u.vs_memory = cs.vs_memory
Proof
  strip_tac >> simp[] >>
  drule intCallFrameTheory.invoke_return_frame >> strip_tac >>
  `LENGTH t.vs_memory <= LENGTH cs.vs_memory` by
    (drule execMemoryLengthTheory.step_inst_memory_length >> simp[]) >>
  `cs.vs_call_ctx = t.vs_call_ctx /\ cs.vs_tx_ctx = t.vs_tx_ctx /\
   cs.vs_block_ctx = t.vs_block_ctx /\ cs.vs_data_section = t.vs_data_section /\
   cs.vs_code = t.vs_code` by
    (drule fnRunFieldsTheory.run_blocks_intret_fields >>
     drule intCallReturnTheory.run_blocks_intret_data_section >>
     gvs[setup_callee_def, AllCaseEqs()]) >>
  drule_all caller_merge_regions >> strip_tac >>
  `immutable_metadata_frame es (out with scopes := prev)` by
    (fs[immutable_metadata_frame_def] >> metis_tac[]) >>
  `immutables_rel_mods ce cx.txn.target ce.ce_is_ctor (out with scopes := prev) cs` by
    (fs[immutables_rel_mods_def, immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  `(out with scopes := prev).scopes = es.scopes /\
   state_rel H func ce cx ((out with scopes := prev) with scopes := []) cs` by simp[] >>
  `!n b sz. local_region ce es.scopes t n b sz ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!n b sz. local_region _ _ _ n b sz ==> _` drule >> simp[]) >>
  drule_all caller_merge_physical >> strip_tac >>
  drule_all caller_merge_ghost >> strip_tac >>
  drule_all caller_merge_kept >> strip_tac >>
  asm_rewrite_tac[storage_well_formed_on_scopes]
QED

(* The same marks and endpoint serve both the complete and bad-domain arms. *)
Theorem caller_return_endpoint_outcome[local]:
  (!tail. source (es with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail) =
     (res,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 observations /\
  (!H. valid_horizon cx st0 H observations ==>
       valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H observations) /\
  (!H. valid_horizon cx st0 H observations ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) marks (OK z,J,N)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       Q H res (ee with gas_obs := []) J N z) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (es,t,G,tn) Q R
Proof
  strip_tac >> pure_rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
  Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`OK z`,`J`,`N`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      gen_tac >> strip_tac >> simp[] >>
      qpat_assum `!H. valid_horizon _ _ H observations ==> gas_origin_ptr_path _ _ _ _` irule >>
      simp[]) >>
  disj1_tac >> conj_tac
  >- (irule gas_bad_storage_at_endpoint >> qexistsl_tac [`ee`,`res`] >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon observations) observations` by
    fs[storage_trace_domain_def] >>
  qexistsl_tac [`storage_trace_horizon observations`,`func`,`PG`,`J`,`N`,`z`] >>
  conj_tac >- simp[] >>
  irule (cj 1 gas_origin_ptr_focus_rules) >> simp[]
QED

val return_source = ``do lock_if_nr cx nr (is_view_mut mut);
  try (do eval_stmts (cx with stk updated_by CONS (src,name)) ss;
          return NoneV od) handle_function od``;

val return_rest = ``do lock_if_nr cx nr (is_view_mut mut);
    rv <- finally_unless_halt
      (finally (try (do eval_stmts (cx with stk updated_by CONS (src,name)) ss;
                        return NoneV od) handle_function) (pop_function prev))
      (unlock_if_nr cx nr (is_view_mut mut));
    crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
    return (Value crv) od``;

val caller_exit = ``\(H : (bool # 256 word # type_value) list # num list)
  (res : eval_result + exception) out (gt : ((string |-> num # num) # taint)) r.
  expr_exit res r /\ halt_exit H cx out res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

Theorem caller_callee_outcome_cases[local]:
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops) /\
  gas_invoke_entry (ctx,func) t callee entered /\
  (!H. (storage_trace_domain cx st0 es1.storage_trace ==>
        valid_horizon cx st0 H es1.storage_trace) ==>
       ptr_inst_ok (DF H) lo 0 ctx func G tn inst t) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,callee,MAP (op_prov G) ops)
    mods cx st0 (^return_source) (es1,entered,FEMPTY,tn with t_var := FEMPTY)
    (\H res out Gc tc s. F)
    (\H res out gt r. (expr_exit res r /\ halt_exit H cx out res r) \/
       (?v ir cs. res = INL v /\ r = IntRet ir cs /\ P H v out gt ir cs)) /\
  (!marks v ee ir cs Gc tc.
     (!tail. (^return_source)
       (es1 with gas_obs := gas_explicit marks entered.vs_gas_readings ++ tail) =
       (INL v,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,callee,MAP (op_prov G) ops)
         (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir cs,Gc,tc) /\
       P H v (ee with gas_obs := []) (Gc,tc) ir cs) ==>
     gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
       (^return_rest) (es1,t,G,tn) Q (^caller_exit)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (^return_rest) (es1,t,G,tn) Q (^caller_exit)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [gas_outcome_full_mods_def])
  >- suspend "bad_storage"
  >- suspend "completed" >>
  suspend "exempt"
QED

Resume caller_callee_outcome_cases[bad_storage]:
  irule (SIMP_RULE bool_ss [LET_THM] selected_return_focus_mods) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish`,`marks`] >> simp[]
QED

Resume caller_callee_outcome_cases[exempt]:
  irule (SIMP_RULE bool_ss [LET_THM] selected_return_focus_mods) >>
  rpt (goal_assum (drule_at Any)) >> simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  disj2_tac >> qexistsl_tac [`err`,`ee`] >> first_assum ACCEPT_TAC
QED

Resume caller_callee_outcome_cases[completed]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
  Cases_on `res` >- suspend "intret" >> suspend "abort"
QED

Resume caller_callee_outcome_cases[intret]:
  fs[Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  rename1 `r = IntRet ret final` >>
  first_x_assum irule >>
  qexistsl_tac [`G'`,`final`,`ee`,`ret`,`marks`,`tn'`,`x`] >>
  fs[Excl "lock_if_nr_def", Excl "is_view_mut_def"]
QED

Resume caller_callee_outcome_cases[abort]:
  irule selected_return_abort_mods >>
  rpt (goal_assum (drule_at Any)) >> simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  qexistsl_tac [`G'`,`r`,`tn'`] >>
  fs[]
QED
Finalise caller_callee_outcome_cases[local]

(* Fields of the callee's reached IntRet, before restoring caller scopes. *)
val _ = Parse.hide "rc";

val callee_return = ``\(H : (bool # 256 word # type_value) list # num list)
  v ee (gt : ((string |-> num # num) # taint)) ir cs.
    (?out. unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),out) /\
      state_rel H func ce cx (out with scopes := []) cs /\
      immutables_rel_mods ce cx.txn.target ce.ce_is_ctor out cs /\
      storage_well_formed_on cx out (FST H) /\ immutable_metadata_frame es1 out) /\
    LENGTH ir.iret_values = rc /\ ir.iret_adopt_fmp = NONE /\
    intret_vals_match rtv v ir.iret_values /\
    stor_taint_ok_at (DF H) (SND gt) cs /\
    (!i. i < lo /\ i IN (SND gt).t_mem ==>
      imm_section_dead_mods ce (mem_bytes_at 0 lo cs.vs_memory) i) /\
    (!b sz. lo <= b /\ b + sz <= t.vs_alloca_next /\
      (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
        sa.cs_next_id <= aid /\ aid < sm.cs_next_id ==>
        regions_disjoint b sz a cap) ==>
      mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
    (!i. lo <= i /\ i < t.vs_alloca_next /\ i IN (SND gt).t_mem /\
      (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
        sa.cs_next_id <= aid /\ aid < sm.cs_next_id ==> i < a \/ a + cap <= i) ==>
      i IN tn.t_mem) /\
    (rc = 0 /\ 0 < rbs ==> !mem. mem_agree_outside (SND gt).t_mem cs.vs_memory mem ==>
      val_in_memory rtv v (w2n (HD (argv : bytes32 list))) mem)``;

Theorem caller_intret_landing[local]:
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops) /\
  eval_operands ops t = SOME argv /\ gas_invoke_entry (ctx,func) t callee entered /\
  LENGTH inst.inst_outputs = rc /\ alloca_history func t /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==> ptr_inst_ok (DF H) lo 0 ctx func G tn inst t) /\
  gas_admissible (^return_rest) expr_vv_res_ok es1 /\
  (!tail. (^return_source)
    (es1 with gas_obs := gas_explicit marks entered.vs_gas_readings ++ tail) =
    (INL v,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,callee,MAP (op_prov G) ops)
      (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir cs,Gc,tc) /\
    (^callee_return) H v (ee with gas_obs := []) (Gc,tc) ir cs) ==>
  ?out u setup fuel.
    unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) = (INL (),out) /\
    out.gas_obs = [] /\ safe_cast rtv v = SOME v /\
    (!tail. (^return_rest) (es1 with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail) =
      (INL (Value v),(out with scopes := prev) with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H out.storage_trace ==> valid_horizon cx st0 H ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es1.storage_trace) /\
    bind_outputs inst.inst_outputs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
    setup_callee callee argv t = SOME setup /\ run_blocks fuel ctx callee setup = IntRet ir cs /\
    step_inst fuel ctx inst t = OK u /\ ir.iret_adopt_fmp = NONE /\
    let a = u with vs_inst_idx := SUC t.vs_inst_idx in
    let J = DRESTRICT G (COMPL (set inst.inst_outputs)) in
    let N = tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs)) in
    ~a.vs_halted /\ alloca_history func a /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (t,G,tn) marks (OK a,J,N) /\
      state_rel H func ce cx (out with scopes := []) cs /\
      immutables_rel_mods ce cx.txn.target ce.ce_is_ctor out cs /\
      storage_well_formed_on cx out (FST H) /\ immutable_metadata_frame es1 out /\
      (^callee_return) H v (ee with gas_obs := []) (Gc,tc) ir cs
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `out.gas_obs = []` by
    (qpat_assum `unlock_if_nr _ _ _ _ = (INL (),out)`
       (mp_then Any (qspec_then `[]` mp_tac) externalCallSelectedTheory.unlock_if_nr_with_gas_obs) >>
     simp[Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
     disch_then (mp_tac o Q.AP_TERM `\s. s.gas_obs`) >> simp[]) >>
  drule_all selected_return_source_success_mods >>
  disch_then (qspecl_then [`st0`] strip_assume_tac) >>
  drule_then assume_tac fragGasFocusTheory.gas_invoke_entry_readings >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ptr_inst_ok (DF H) lo 0 ctx func G tn inst t /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,callee,MAP (op_prov G) ops)
      (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir cs,Gc,tc)` by fs[] >>
  `LENGTH inst.inst_outputs = LENGTH ir.iret_values` by simp[] >>
  mp_tac (Q.INST [`outs` |-> `inst.inst_outputs`, `observations` |-> `ee.storage_trace`,
                 `H` |-> `storage_trace_horizon ee.storage_trace`] selected_invoke_return_edge_mods) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qexistsl_tac [`out`,`u`,`setup`,`fuel`] >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  conj_tac
  >- fs[vyperStateTheory.evaluation_state_fupdcanon, Excl "lock_if_nr_def",
        Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> gvs[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

val caller_s0_kept = ``\ee z.
  locals_kept ce es0 ee s0 z /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
  (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
     (!n a cap. local_region ce es0.scopes s0 n a cap ==>
        b + sz <= a \/ a + cap <= b) ==>
     mem_bytes_at b sz z.vs_memory = mem_bytes_at b sz s0.vs_memory)``;

val caller_frame = ``\(H : (bool # 256 word # type_value) list # num list) ee J N z.
  stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
  storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee J N z /\
  ghost_kept_at lo ce es0 sa G0 tn0 s0 J N /\ (^caller_s0_kept) ee z``;

Theorem caller_merge_at_return_horizon[local]:
  contract_inv mods exps ctx ce cx /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. MEM x inst.inst_outputs ==> ~not_fresh_at sa x) /\
  (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  expr_sim_inv_mods mods ce cx env (es1 with scopes := prev) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    (^caller_frame) H (es1 with scopes := prev) G tn t) /\
  (!n b sz aid a cap. local_region ce prev t n b sz /\
     FLOOKUP t.vs_allocas aid = SOME (a,cap) /\ sa.cs_next_id <= aid /\
     aid < sm.cs_next_id ==> regions_disjoint b sz a cap) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es1.storage_trace) /\
  valid_horizon cx st0 H ee.storage_trace /\
  state_rel H func ce cx (out with scopes := []) cs /\
  immutables_rel_mods ce cx.txn.target ce.ce_is_ctor out cs /\
  storage_well_formed_on cx out (FST H) /\ immutable_metadata_frame es1 out /\
  (^callee_return) H v (ee with gas_obs := []) (Gc,tc) ir cs /\
  setup_callee callee argv t = SOME setup /\ run_blocks fuel ctx callee setup = IntRet ir cs /\
  step_inst fuel ctx inst t = OK u /\
  bind_outputs inst.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u ==>
  (^caller_frame) H (out with scopes := prev) (DRESTRICT G (COMPL (set inst.inst_outputs)))
    (tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs))) u /\
  u.vs_fmp = t.vs_fmp /\ u.vs_initial_fmp = t.vs_initial_fmp /\
  u.vs_current_bb = t.vs_current_bb /\ u.vs_inst_idx = t.vs_inst_idx /\
  u.vs_alloca_next = t.vs_alloca_next /\ u.vs_memory = cs.vs_memory
Proof
  BETA_TAC >> disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 H es1.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H es1.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `immutable_metadata_frame (es1 with scopes := prev) out` by
    (simp_tac (srw_ss()) [immutable_metadata_frame_def] >>
     qpat_assum `immutable_metadata_frame es1 out`
       (ACCEPT_TAC o PURE_REWRITE_RULE [immutable_metadata_frame_def])) >>
  rule_assum_tac (PURE_REWRITE_RULE [pairTheory.SND]) >>
  mp_tac (Q.INST [`D` |-> `DF H`]
    (Q.ISPEC `(H : (bool # 256 word # type_value) list # num list)`
      (Q.GEN `H` (Q.INST [`es` |-> `es1 with scopes := prev`, `outs` |-> `inst.inst_outputs`]
         selected_caller_merge_frame_mods)))) >>
  simp_tac bool_ss [LET_THM] >>
  (impl_tac >- (rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE (simp[] >> first_assum ACCEPT_TAC)))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

val selected_call_expr = ``Call ann (IntCall (src,name)) es dflt``;

val selected_owned = ``\(H : (bool # 256 word # type_value) list # num list)
  (res : eval_result + exception) ee J N z. ?tv. res = INL tv /\
    vv_post_mods H ctx func ce cx (^selected_call_expr) es0 sa sm s0 ee tv vv z /\
    vv_store_bound cx (post_value_type ce (^selected_call_expr))
      (lowered_value_type ce (^selected_call_expr)) ee tv vv z /\
    z.vs_current_bb = sm.cs_current_bb /\ z.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s0.vs_alloca_next <= z.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d ce cx ee J N z /\
    ptr_vv_ok cx (post_value_type ce (^selected_call_expr)) tv vv ee J N z /\
    (!v. tv = Value v /\ ~is_word_type (post_value_type ce (^selected_call_expr)) /\
       ~is_bytestring_type (post_value_type ce (^selected_call_expr)) ==>
       vv_own ce cx (post_value_type ce (^selected_call_expr)) sa sm ee tv vv z /\
       (!tag p. vv = LocatedValue tag p ==> p.ptr_location = LocMemory)) /\
    (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?v. read_result cx tv ee = (INL v,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type ce (^selected_call_expr)) = SOME rt /\
           eval_operand (vv_operand vv) z = SOME w ==>
           w2n w + type_memory_size rt <= lo /\
           (!mem. mem_agree_outside N.t_mem z.vs_memory mem ==> val_in_memory rt v (w2n w) mem)) /\
    (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce (^selected_call_expr)) ==>
       ptr_buf_ok ce (^selected_call_expr) op J z) /\
    (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok ce (^selected_call_expr) p.ptr_operand J z) /\
    ghost_kept_at lo ce es0 sa G0 tn0 s0 J N``;

Theorem caller_zero_no_buffer[local]:
  expr_sim_inv_mods mods ce cx env es0 /\
  ce.ce_func_return_type (nsid_to_string (src,name)) = ret /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\ value_has_type rtv v /\
  type_widens_to (get_tenv cx) ret ann /\
  (ret = NoneT \/ type_memory_bytes ce ret = 0) /\ vv = StackValue ret (Lit 0w) /\
  (^caller_frame) H ee J N u /\
  u.vs_current_bb = sm.cs_current_bb /\ i = LENGTH sm.cs_current_insts /\
  alloca_history func (u with vs_inst_idx := i) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp (u with vs_inst_idx := i)) /\
  s0.vs_alloca_next <= u.vs_alloca_next ==>
  (^selected_owned) H (INL (Value v)) ee J N (u with vs_inst_idx := i)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `i = LENGTH _` SUBST_ALL_TAC >>
  qexists_tac `Value v` >> simp_tac bool_ss [sumTheory.INL_11, AND_CLAUSES] >>
  drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)
    (INST_TYPE [alpha |-> ``:256``]
      (SIMP_RULE bool_ss [LET_THM] selected_no_buffer_return_post_mods)) >>
  disch_then (qspecl_then [`ann`,`src`,`name`,`es`,`dflt`] (mp_tac o SPEC_ALL)) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  qpat_x_assum `vv = StackValue _ _` SUBST_ALL_TAC >>
  qpat_assum `ce.ce_func_return_type _ = ret` (fn ret_eq =>
    disch_then (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [ret_eq])) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])
QED

Theorem caller_frame_cursor[local]:
  (^caller_frame) H ee J N u ==>
  (^caller_frame) H ee J N (u with vs_inst_idx := i)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `immutable_frame_mods func ce cx ee (u with vs_inst_idx := i)` by
    (let val rules = [immutable_frame_mods_def, immutables_rel_mods_def,
          immutables_rel_def, immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
          local_region_def, venomStateTheory.lookup_var_def]
     in simp_tac (srw_ss()) rules >>
        qpat_assum `immutable_frame_mods _ _ _ _ u`
          (ACCEPT_TAC o SIMP_RULE (srw_ss()) rules)
     end) >>
  `ghost_inv_at_mods (DF H) lo d ce cx ee J N (u with vs_inst_idx := i)` by
    (qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ u` mp_tac >>
     Cases_on `d`
     >- (simp_tac (srw_ss()) [ghost_inv_at_mods_def, return_buf_ptr_def,
           ptr_covers_def, stor_taint_ok_at_def, allocas_from_def, venomStateTheory.lookup_var_def] >>
         strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     PairCases_on `x` >> simp_tac (srw_ss()) [ghost_inv_at_mods_def, return_buf_ptr_def,
       ptr_covers_def, stor_taint_ok_at_def, allocas_from_def, venomStateTheory.lookup_var_def] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rule_assum_tac (PURE_REWRITE_RULE [venomStateTheory.lookup_var_def]) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (simp[stmt_state_rel_inst_idx, venomStateTheory.lookup_var_def] >> first_assum ACCEPT_TAC))
QED

Theorem caller_invoke_path[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (t,G,tn) marks (OK a,J,N) /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,J,N) [] (r,Gr,tr) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) marks (r,Gr,tr)
Proof
  strip_tac >> drule_all (cj 2 gas_origin_ptr_path_rules) >> simp[]
QED

val sret_result_buffer = ``
  vv = LocatedValue ret (base_ptr buf) /\ buf.buf_operand = Var root /\
  eval_operand buf.buf_operand t = SOME (n2w off) /\
  HD argv = (n2w off : bytes32) /\ off < dimword (:256) /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (off,buf.buf_size) /\
  FLOOKUP G root = SOME (off,buf.buf_size) /\ op_taint tn (Var root) = {} /\
  sa.cs_next_id < sm.cs_next_id /\ type_memory_size rtv <= buf.buf_size /\
  w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next``;

val sret_owned = subst [``es0:evaluation_state`` |-> ``es:evaluation_state``,
  ``es:expr list`` |-> ``args:expr list``, ``dflt:expr option`` |-> ``drv:expr option``,
  ``sm:compile_state`` |-> ``sb:compile_state``] selected_owned;
val sret_frame = subst [``es0:evaluation_state`` |-> ``es:evaluation_state``] caller_frame;
val sret_buffer = subst [``sm:compile_state`` |-> ``sb:compile_state``] sret_result_buffer;

Theorem caller_zero_sret[local]:
  rc = 0 /\ 0 < rbs /\ LENGTH outs = rc /\
  ce.ce_func_return_type (nsid_to_string (src,name)) = ret /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\ value_has_type rtv v /\
  type_widens_to (get_tenv cx) ret ann /\ type_memory_bytes ce ret = type_memory_size rtv /\
  ^sret_buffer /\
  (!n b sz. local_region ce ee.scopes t n b sz ==>
     b + sz <= off \/ off + buf.buf_size <= b) /\
  (!mem. mem_agree_outside tc.t_mem cs.vs_memory mem ==>
         val_in_memory rtv v (w2n (HD argv)) mem) /\
  bind_outputs outs ir.iret_values (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  a = u with vs_inst_idx := SUC t.vs_inst_idx /\ J = DRESTRICT G (COMPL (set outs)) /\
  N = tc with t_var := DRESTRICT tn.t_var (COMPL (set outs)) /\
  (^sret_frame) H ee J N a /\
  a.vs_current_bb = sb.cs_current_bb /\ a.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func a /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
  s0.vs_alloca_next <= a.vs_alloca_next ==>
  (^sret_owned) H (INL (Value v)) ee J N a
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qexists_tac `Value v` >> simp_tac bool_ss [sumTheory.INL_11, AND_CLAUSES] >>
  mp_tac (Q.INST [`fid` |-> `(src,name)`, `nreturns` |-> `rc`, `D` |-> `DF H`]
    (INST_TYPE [alpha |-> ``:256``]
      (SIMP_RULE bool_ss [LET_THM] selected_caller_sret_post_mods))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  qpat_x_assum `a = u with vs_inst_idx := _` SUBST_ALL_TAC >>
  qpat_x_assum `J = DRESTRICT _ _` SUBST_ALL_TAC >>
  qpat_x_assum `N = tc with t_var := _` SUBST_ALL_TAC >>
  `SUC t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qpat_assum `(u with vs_inst_idx := _).vs_inst_idx = _`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])) >>
  pop_assum (fn th => rule_assum_tac (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `buf.buf_operand = Var root` (fn th =>
    rule_assum_tac (SIMP_RULE (srw_ss()) [contextTheory.base_ptr_def, th]) >>
    simp_tac (srw_ss()) [contextTheory.base_ptr_def, contextTheory.vv_location_def, th]) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])
QED

Theorem caller_register_owned[local]:
  let e = ^selected_call_expr in
  let pt = post_value_type ce e in
  (^caller_frame) H ee J N z /\
  z.vs_current_bb = sm.cs_current_bb /\ z.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  s0.vs_alloca_next <= z.vs_alloca_next /\
  vv_holds_mods ce cx pt (Value v) vv ee z /\
  vv_at ce cx pt sa sm ee (Value v) vv z /\
  vv_place_ptr_mods ce cx ee z (Value v) vv /\
  vv_own ce cx pt sa sm ee (Value v) vv z /\
  vv_store_bound cx pt (lowered_value_type ce e) ee (Value v) vv z /\
  ptr_vv_ok cx pt (Value v) vv ee J N z /\
  (!tag p. vv = LocatedValue tag p ==> p.ptr_location = LocMemory) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==> ptr_buf_ok ce e p.ptr_operand J z) /\
  (!tag op. vv = StackValue tag op /\ ~is_word_type pt ==> ptr_buf_ok ce e op J z) /\
  vv_location vv <> SOME LocCode ==>
  (^selected_owned) H (INL (Value v)) ee J N z
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexists_tac `Value v` >> simp_tac bool_ss [sumTheory.INL_11, AND_CLAUSES] >>
  conj_tac
  >- (`expr_has_effect (^selected_call_expr)` by
        simp[supportedExprTraverseTheory.expr_has_effect_def,
          supportedExprTraverseTheory.supported_expr_exists_def,
          supportedExprTraverseTheory.expr_effect_root_def] >>
      pop_assum (fn th => simp_tac bool_ss [vv_post_mods_def, th]) >>
      rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
        (disch_tac >> first_assum ACCEPT_TAC))) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]) >>
  disch_tac >>
  qpat_assum `vv_own _ _ _ _ _ _ _ _ _` (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])
QED

(* The result-buffer pin is the allocation made before argument evaluation.
   The only suffix after a register return is the emitted result stores. *)
val register_buffer = ``
  ?buf root off ai st4.
    buf.buf_operand = Var root /\ buf.buf_size = 32 * rc /\
    vv = LocatedValue (ce.ce_func_return_type (nsid_to_string (src,name))) (base_ptr buf) /\
    lookup_var root t = SOME (n2w off) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (off,32 * rc) /\
    FLOOKUP G root = SOME (off,32 * rc) /\ op_taint tn (Var root) = {} /\
    lo <= off /\ off + 32 * rc < dimword (:256) /\
    off + 32 * rc <= t.vs_alloca_next /\ sa.cs_next_id < sm.cs_next_id /\
    MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_id = sa.cs_next_id /\
    store_multi_results (Var root) (MAP Var outs) 0 st4 = ((),sm) /\
    fn_has_code st4 sm func /\
    LENGTH st4.cs_current_insts = SUC t.vs_inst_idx /\ st4.cs_current_bb = t.vs_current_bb /\
    not_fresh_at st4 root /\ ~MEM root outs /\
    (!x. MEM x outs ==> not_fresh_at st4 x) /\ sa.cs_next_var <= st4.cs_next_var``;

Theorem caller_register_landing[local]:
  contract_inv mods exps ctx ce cx /\ ALOOKUP mods src = SOME tops /\
  ALOOKUP ce.ce_modules ce.ce_module = SOME caller_tops /\
  expr_body_pre_mods mods ce cx env (^selected_call_expr) es0 /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\ safe_cast rtv v = SOME v /\
  ce.ce_func_info (nsid_to_string (src,name)) = (rc,rbs,pvs) /\
  ce.ce_func_info (nsid_to_string (src,name)) =
    compute_func_info (\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n))
      ret (type_memory_bytes ce ret) (MAP SND args) /\
  0 < rc /\ LENGTH outs = rc /\ ALL_DISTINCT outs /\
  LENGTH ir.iret_values = rc /\ intret_vals_match rtv v ir.iret_values /\
  ir.iret_adopt_fmp = NONE /\ ~t.vs_halted /\ allocas_from lo t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  bind_outputs outs ir.iret_values (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  (!x. MEM x outs ==> ~not_fresh_at sa x) /\
  local_ptrs_reserved ce sa /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (^register_buffer) /\
  (!n b sz aid off cap. local_region ce ee.scopes t n b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,cap) /\ sa.cs_next_id <= aid /\
    aid < sm.cs_next_id ==> regions_disjoint b sz off cap) ==>
  let a = u with vs_inst_idx := SUC t.vs_inst_idx in
  let J = DRESTRICT G (COMPL (set outs)) in
  let N = tc with t_var := DRESTRICT tn.t_var (COMPL (set outs)) in
  a.vs_current_bb = t.vs_current_bb /\ alloca_history func a /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  (!H. valid_horizon cx st0 H observations ==> (^caller_frame) H ee J N a) ==>
  ?z Gs ts.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,J,N) [] (OK z,Gs,ts)) /\
    (!H. valid_horizon cx st0 H observations ==> (^selected_owned) H (INL (Value v)) ee Gs ts z)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `buf.buf_operand = Var root` >>
  rename1 `lookup_var root t = SOME (n2w off)` >>
  rename1 `store_multi_results (Var root) (MAP Var outs) 0 st4 = ((),sm)` >>
  mp_tac (Q.INST [`nret` |-> `rc`, `aid` |-> `sa.cs_next_id`] selected_result_stores_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st4 sm) _ = OK stored` >>
  rename1 `ts.t_mem = tc.t_mem DIFF _` >>
  rename1 `FLOOKUP Gs _ = FLOOKUP (DRESTRICT G _) _` >>
  qabbrev_tac `a = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  qabbrev_tac `J = DRESTRICT G (COMPL (set outs))` >>
  qabbrev_tac `N = tc with t_var := DRESTRICT tn.t_var (COMPL (set outs))` >>
  qexistsl_tac [`stored with vs_inst_idx := LENGTH sm.cs_current_insts`,`Gs`,`ts`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H observations ==> _`
    (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac intCallFrameTheory.invoke_return_frame >>
  `!n b sz. local_region ce ee.scopes a n b sz <=> local_region ce ee.scopes t n b sz` by
    (`!n b sz. local_region ce ee.scopes u n b sz <=> local_region ce ee.scopes t n b sz` by
       (irule caller_local_regions_merge >> qexists_tac `sa` >> metis_tac[]) >>
     simp_tac (srw_ss()) [Abbr `a`, local_region_def, venomStateTheory.lookup_var_def] >>
     qpat_assum `!n b sz. local_region _ _ u n b sz <=> _`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [local_region_def, venomStateTheory.lookup_var_def])) >>
  `!n b sz. local_region ce ee.scopes a n b sz ==>
     b + sz <= off \/ off + 32 * rc <= b` by
    (rpt strip_tac >>
     `local_region ce ee.scopes t n b sz` by metis_tac[] >>
     qpat_assum `!n b sz aid off cap. _ ==> loweringStateRelDefs$regions_disjoint _ _ _ _`
       (qspecl_then [`n`,`b`,`sz`,`sa.cs_next_id`,`off`,`32 * rc`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  mp_tac (Q.INST [`tops` |-> `caller_tops`, `cap` |-> `32 * rc`,
                  `buf` |-> `Var root`, `ops` |-> `MAP Var outs`, `k` |-> `0`]
      (INST_TYPE [alpha |-> ``:256``] (SIMP_RULE bool_ss [LET_THM] selected_stored_caller_frame_mods))) >>
  (impl_tac >- (rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE
     (simp[Abbr `a`, Abbr `N`] >> NO_TAC) ORELSE
     (qpat_assum `u.vs_allocas = t.vs_allocas` (fn allocas =>
      qpat_assum `u.vs_alloca_next = t.vs_alloca_next` (fn frontier =>
       let val rules = [Abbr `a`, Abbr `N`, allocas, frontier, venomStateTheory.lookup_var_def]
       in simp_tac (srw_ss()) rules >> first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss()) rules)
       end)))))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `z = stored with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `!x. not_fresh_at sa x ==> lookup_var x stored = lookup_var x u` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at st4 x ==> _` drule >>
     simp[] >> metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  `!n b sz. local_region ce ee.scopes z n b sz <=> local_region ce ee.scopes a n b sz` by
    (`!n b sz. local_region ce ee.scopes stored n b sz <=> local_region ce ee.scopes u n b sz` by
       (irule caller_local_regions_merge >> qexists_tac `sa` >> simp[]) >>
     simp_tac (srw_ss()) [Abbr `z`, Abbr `a`, local_region_def, venomStateTheory.lookup_var_def] >>
     qpat_assum `!n b sz. local_region _ _ stored n b sz <=> _`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [local_region_def, venomStateTheory.lookup_var_def])) >>
  `eval_operand (Var root) z = SOME (n2w off)` by
    (qpat_assum `!x. not_fresh_at st4 x ==> _` (qspec_then `root` mp_tac) >>
     simp[Abbr `z`, venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def] >>
     rule_assum_tac (PURE_REWRITE_RULE [venomStateTheory.lookup_var_def]) >> metis_tac[]) >>
  `FLOOKUP Gs root = SOME (off,32 * rc) /\ op_taint ts (Var root) = {}` by
    (qpat_assum `!x. not_fresh_at st4 x ==> _` (qspec_then `root` mp_tac) >>
     qpat_assum `op_taint tn (Var root) = {}` (mp_tac o PURE_REWRITE_RULE [op_taint_def]) >>
     simp[Abbr `J`, Abbr `N`, FLOOKUP_DRESTRICT, op_taint_def]) >>
  `off + buf.buf_size <= stored.vs_alloca_next` by
    (qpat_assum `stored with <|vs_vars := _; vs_memory := _|> = a`
       (mp_tac o Q.AP_TERM `venom_state_vs_alloca_next`) >>
     simp[Abbr `a`]) >>
  `!n b sz. local_region ce ee.scopes z n b sz ==>
     off + buf.buf_size <= b \/ b + sz <= off` by metis_tac[] >>
  `off < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `rbuf` |-> `buf`, `nret` |-> `rc`,
            `ws` |-> `ir.iret_values`, `G` |-> `Gs`, `tn` |-> `ts`, `aid` |-> `sa.cs_next_id`]
    (SIMP_RULE bool_ss [LET_THM] selected_stored_return_value_mods)) >>
  (impl_tac >- (rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE (simp[Abbr `z`] >> NO_TAC) ORELSE
     (simp_tac (srw_ss()) [Abbr `z`] >>
      first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss()) []))))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`J` |-> `Gs`, `N` |-> `ts`]
    (SIMP_RULE bool_ss [LET_THM] (BETA_RULE caller_register_owned))) >>
  qpat_assum `vv = LocatedValue _ _` (fn th => pure_rewrite_tac [th]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[contextTheory.vv_location_def, contextTheory.base_ptr_def]
QED

val caller_stage_frame = ``
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. MEM x inst.inst_outputs ==> ~not_fresh_at sa x) /\
  (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  expr_sim_inv_mods mods ce cx env (es1 with scopes := prev) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    (^caller_frame) H (es1 with scopes := prev) G tn t) /\
  (!n b sz aid off cap. local_region ce prev t n b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,cap) /\ sa.cs_next_id <= aid /\
    aid < sm.cs_next_id ==> regions_disjoint b sz off cap)``;

val reached_return = ``
  (!tail. (^return_source) (es1 with gas_obs := gas_explicit marks entered.vs_gas_readings ++ tail) =
    (INL v,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,callee,MAP (op_prov G) ops)
      (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir cs,Gc,tc) /\
    (^callee_return) H v (ee with gas_obs := []) (Gc,tc) ir cs)``;

val reached_invoke = ``
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops) /\
  eval_operands ops t = SOME argv /\ gas_invoke_entry (ctx,func) t callee entered /\
  LENGTH inst.inst_outputs = rc /\ alloca_history func t /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==> ptr_inst_ok (DF H) lo 0 ctx func G tn inst t)``;

Theorem caller_intret_frame[local]:
  contract_inv mods exps ctx ce cx /\ (^caller_stage_frame) /\ (^reached_invoke) /\
  gas_admissible (^return_rest) expr_vv_res_ok es1 /\ (^reached_return) /\
  s0.vs_alloca_next <= t.vs_alloca_next ==>
  ?out u.
    out.gas_obs = [] /\ safe_cast rtv v = SOME v /\
    (!tail. (^return_rest) (es1 with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail) =
      (INL (Value v),(out with scopes := prev) with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H out.storage_trace ==> valid_horizon cx st0 H ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es1.storage_trace) /\
    bind_outputs inst.inst_outputs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
    ir.iret_adopt_fmp = NONE /\ LENGTH ir.iret_values = rc /\ intret_vals_match rtv v ir.iret_values /\
    (rc = 0 /\ 0 < rbs ==> !mem. mem_agree_outside tc.t_mem cs.vs_memory mem ==>
      val_in_memory rtv v (w2n (HD argv)) mem) /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_alloca_next = t.vs_alloca_next /\
    let a = u with vs_inst_idx := SUC t.vs_inst_idx in
    let J = DRESTRICT G (COMPL (set inst.inst_outputs)) in
    let N = tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs)) in
    ~a.vs_halted /\ alloca_history func a /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (t,G,tn) marks (OK a,J,N) /\
      (^caller_frame) H (out with scopes := prev) J N a)
Proof
  BETA_TAC >> PURE_REWRITE_TAC[LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] (BETA_RULE caller_intret_landing)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `out` (qx_choose_then `u`
    (qx_choose_then `setup` (qx_choose_then `fuel` (map_every assume_tac o CONJUNCTS))))) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    (^caller_frame) H (out with scopes := prev) (DRESTRICT G (COMPL (set inst.inst_outputs)))
      (tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs)))
      (u with vs_inst_idx := SUC t.vs_inst_idx) /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_alloca_next = t.vs_alloca_next` by
    (BETA_TAC >> gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     rule_assum_tac (PURE_REWRITE_RULE [pairTheory.SND]) >>
     `stor_taint_ok_at (DF H) tc cs` by
       (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
          (qspec_then `H` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (map_every assume_tac o CONJUNCTS) >> first_assum ACCEPT_TAC) >>
     mp_tac (PURE_REWRITE_RULE [pairTheory.SND] (BETA_RULE caller_merge_at_return_horizon)) >>
     (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (qexists_tac `out` >> rpt conj_tac >> first_assum ACCEPT_TAC)))) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     mp_tac (Q.INST [`ee` |-> `out with scopes := prev`, `i` |-> `SUC t.vs_inst_idx`,
         `J` |-> `DRESTRICT G (COMPL (set inst.inst_outputs))`,
         `N` |-> `tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs))`]
       (BETA_RULE caller_frame_cursor)) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum (mk_asm "returned_frame") >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [pairTheory.SND]) >>
  asm "returned_frame" (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by simp[] >>
  qexistsl_tac [`out`,`u`] >> BETA_TAC >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  asm "returned_frame" (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

val zero_result_layout = ``
  t.vs_current_bb = sm.cs_current_bb /\ SUC t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (if rbs = 0 then vv = StackValue (ce.ce_func_return_type (nsid_to_string (src,name))) (Lit 0w)
   else ?buf root off. ^sret_result_buffer)``;

val caller_typed = ``
  ce.ce_func_return_type (nsid_to_string (src,name)) = ret /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\ value_has_type rtv v /\
  type_widens_to (get_tenv cx) ret ann``;

val caller_func_info = ``
  ce.ce_func_info (nsid_to_string (src,name)) = (rc,rbs,pvs) /\
  ce.ce_func_info (nsid_to_string (src,name)) =
    compute_func_info (\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n))
      ret (type_memory_bytes ce ret) (MAP SND (args : (string # type) list))``;

Theorem caller_zero_landing[local]:
  rc = 0 /\ (^caller_func_info) /\ (^zero_result_layout) /\ (^caller_typed) /\
  expr_sim_inv_mods mods ce cx env es0 /\ type_memory_bytes ce ret = type_memory_size rtv /\
  LENGTH outs = rc /\
  (!n b sz aid off cap. local_region ce ee.scopes t n b sz /\
     FLOOKUP t.vs_allocas aid = SOME (off,cap) /\ sa.cs_next_id <= aid /\
     aid < sm.cs_next_id ==> regions_disjoint b sz off cap) /\
  (!mem. 0 < rbs /\ mem_agree_outside tc.t_mem cs.vs_memory mem ==>
         val_in_memory rtv v (w2n (HD argv)) mem) /\
  bind_outputs outs ir.iret_values (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  local_ptrs_reserved ce sa /\ (!x. MEM x outs ==> ~not_fresh_at sa x) /\
  u.vs_current_bb = t.vs_current_bb /\ s0.vs_alloca_next <= u.vs_alloca_next ==>
  let a = u with vs_inst_idx := SUC t.vs_inst_idx in
  let J = DRESTRICT G (COMPL (set outs)) in
  let N = tc with t_var := DRESTRICT tn.t_var (COMPL (set outs)) in
  (^caller_frame) H ee J N a /\
  alloca_history func a /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a) ==>
  (^selected_owned) H (INL (Value v)) ee J N a
Proof
  PURE_REWRITE_TAC[LET_THM] >> BETA_TAC >>
  ntac 2 (disch_then (map_every assume_tac o CONJUNCTS)) >>
  Cases_on `rbs = 0`
  >- (`vv = StackValue ret (Lit 0w)` by
        ((qpat_assum `if rbs = 0 then _ else _` mp_tac >> simp[] >> (gvs[]))) >>
      `ret = NoneT \/ type_memory_bytes ce ret = 0` by
        (qpat_assum `ce.ce_func_info _ = (rc,rbs,pvs)` (fn info =>
           qpat_assum `ce.ce_func_info _ = compute_func_info _ _ _ _`
             (mp_tac o PURE_REWRITE_RULE [info])) >>
         Cases_on `ret` >> simp[compute_func_info_def, Excl "type_memory_bytes_def"] >>
         Cases_on `returns_stack_count (\n. MAP (FST o SND)
           (get_struct_fields ce.ce_struct_fields n)) ret` >> simp[]) >>
      mp_tac (Q.INST [`u` |-> `u with vs_inst_idx := SUC t.vs_inst_idx`,
          `i` |-> `SUC t.vs_inst_idx`, `J` |-> `DRESTRICT G (COMPL (set outs))`,
          `N` |-> `tc with t_var := DRESTRICT tn.t_var (COMPL (set outs))`]
         (BETA_RULE caller_zero_no_buffer)) >>
      (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (simp[] >> NO_TAC) ORELSE
        (simp_tac (srw_ss()) [] >> first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss()) []))))) >>
      qpat_assum `SUC t.vs_inst_idx = LENGTH _` (fn cursor =>
        disch_then (fn post =>
          simp_tac (srw_ss()) [cursor] >>
          ACCEPT_TAC (SIMP_RULE (srw_ss()) [cursor] post)))) >>
  qpat_assum `rbs <> 0` (fn nz =>
    qpat_x_assum `if rbs = 0 then _ else _`
      (strip_assume_tac o SIMP_RULE bool_ss [nz])) >>
  `0 < rbs` by decide_tac >>
  rename1 `buf.buf_operand = Var root` >>
  rename1 `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (off,buf.buf_size)` >>
  `!n b sz. local_region ce ee.scopes t n b sz ==>
       b + sz <= off \/ off + buf.buf_size <= b` by
    (rpt strip_tac >>
     qpat_assum `!n b sz aid off cap. _ ==> regions_disjoint _ _ _ _`
       (drule_then (qspecl_then [`sa.cs_next_id`,`off`,`buf.buf_size`] mp_tac)) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!mem. mem_agree_outside tc.t_mem cs.vs_memory mem ==>
       val_in_memory rtv v (w2n (HD argv)) mem` by
    (rpt strip_tac >> first_x_assum (irule o SPEC_ALL) >> asm_rewrite_tac[]) >>
  mp_tac (INST [``args:expr list`` |-> ``es:expr list``,
      ``es:evaluation_state`` |-> ``es0:evaluation_state``,
      ``drv:expr option`` |-> ``dflt:expr option``, ``sb:compile_state`` |-> ``sm:compile_state``]
     (Q.INST [`a` |-> `u with vs_inst_idx := SUC t.vs_inst_idx`,
       `J` |-> `DRESTRICT G (COMPL (set outs))`,
       `N` |-> `tc with t_var := DRESTRICT tn.t_var (COMPL (set outs))`]
       (BETA_RULE caller_zero_sret))) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then ACCEPT_TAC
QED

Theorem caller_completed_normal[local]:
  contract_inv mods exps ctx ce cx /\ (^caller_stage_frame) /\ (^reached_invoke) /\
  gas_admissible (^return_rest) expr_vv_res_ok es1 /\ (^reached_return) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ALOOKUP mods src = SOME tops /\ ALOOKUP ce.ce_modules ce.ce_module = SOME caller_tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  expr_body_pre_mods mods ce cx env (^selected_call_expr) es0 /\ (^caller_func_info) /\
  (rc = 0 ==> (^zero_result_layout)) /\
  (0 < rc ==> ALL_DISTINCT inst.inst_outputs /\ (^register_buffer)) /\
  outs = inst.inst_outputs /\ ~t.vs_halted /\ allocas_from lo t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ fn_inst_ids_distinct func ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (^return_rest) (es1,t,G,tn) (^selected_owned) (^caller_exit)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] (BETA_RULE caller_intret_frame)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `out` (qx_choose_then `u` (map_every assume_tac o CONJUNCTS))) >>
  `((out with scopes := prev) with gas_obs := []) = out with scopes := prev` by
    simp[evaluation_state_component_equality] >>
  `?z J N.
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) marks (OK z,J,N)) /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
       (^selected_owned) H (INL (Value v)) (out with scopes := prev) J N z)` suffices_by
    (BETA_TAC >>
     disch_then (qx_choose_then `z` (qx_choose_then `J` (qx_choose_then `N` strip_assume_tac))) >>
     irule caller_return_endpoint_outcome >> suspend "outcome") >>
  BETA_TAC >> Cases_on `rc = 0` >- suspend "zero" >> suspend "register"
QED

Resume caller_completed_normal[outcome]:
  qexistsl_tac [`J`,`N`,`out with scopes := prev`,`marks`,`ee.storage_trace`,`INL (Value v)`,`z`] >>
  BETA_TAC >> rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (simp[] >> NO_TAC) ORELSE
    (qpat_assum `((out with scopes := prev) with gas_obs := []) = _`
       (fn obs_eq => PURE_REWRITE_TAC [obs_eq]) >>
     gen_tac >> strip_tac >>
     `valid_horizon cx st0 H ee.storage_trace` by fs[] >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> ?tv. _`
       (qspecl_then [`H`] mp_tac) >> simp[]))
QED

Resume caller_completed_normal[zero]:
  `^caller_typed` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `tenv` |-> `env`]
       intcall_return_type_facts_mods) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `type_memory_bytes ce ret = type_memory_size rtv` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ es0`
       (strip_assume_tac o PURE_REWRITE_RULE [expr_sim_inv_mods_def]) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (rpt strip_tac >> qpat_assum `!name fields. _ ==> ALL_DISTINCT _ /\ _`
          (drule_then (ACCEPT_TAC o CONJUNCT2))))) >>
  qpat_assum `rc = 0 ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `outs = inst.inst_outputs` SUBST_ALL_TAC >>
  qexistsl_tac [`u with vs_inst_idx := SUC t.vs_inst_idx`,
    `DRESTRICT G (COMPL (set inst.inst_outputs))`,
    `tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs))`] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS))
  >- (irule caller_invoke_path >>
      qexistsl_tac [`DRESTRICT G (COMPL (set inst.inst_outputs))`,
        `tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs))`,
        `u with vs_inst_idx := SUC t.vs_inst_idx`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule (cj 1 gas_origin_ptr_path_rules) >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`ee` |-> `out with scopes := prev`, `outs` |-> `inst.inst_outputs`]
    (SIMP_RULE bool_ss [LET_THM] (BETA_RULE caller_zero_landing))) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (simp[] >> NO_TAC) ORELSE
    (qpat_assum `!n b sz aid off cap. local_region ce prev t _ _ _ /\ _ ==> _` mp_tac >>
     simp_tac (srw_ss()) [])))) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (qpat_assum `SUC t.vs_inst_idx = LENGTH _` (fn cursor =>
      simp_tac (srw_ss()) [cursor] >>
      first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss()) [cursor])))))) >>
  simp[]
QED

Resume caller_completed_normal[register]:
  `0 < rc` by decide_tac >>
  qpat_assum `0 < rc ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `outs = inst.inst_outputs` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`ee` |-> `out with scopes := prev`, `observations` |-> `ee.storage_trace`,
      `outs` |-> `inst.inst_outputs`]
    (SIMP_RULE bool_ss [LET_THM] (BETA_RULE caller_register_landing))) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (qpat_assum `!n b sz aid off cap. local_region ce prev t _ _ _ /\ _ ==> _` mp_tac >>
     simp_tac (srw_ss()) [])))) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (simp[] >> NO_TAC) ORELSE
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC)))) >>
  disch_then (qx_choose_then `z` (qx_choose_then `Gs` (qx_choose_then `ts` strip_assume_tac))) >>
  qexistsl_tac [`z`,`Gs`,`ts`] >> reverse conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> ?tv. _`
        (drule_then (fn post => simp_tac (srw_ss()) [] >>
          ACCEPT_TAC (SIMP_RULE (srw_ss()) [] post)))) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _ /\ _`
    (drule_then (assume_tac o CONJUNCT1)) >>
  irule caller_invoke_path >>
  qexistsl_tac [`DRESTRICT G (COMPL (set inst.inst_outputs))`,
    `tc with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs))`,
    `u with vs_inst_idx := SUC t.vs_inst_idx`] >>
  conj_tac >- first_assum ACCEPT_TAC >> first_x_assum irule
QED

Finalise caller_completed_normal[local]

Theorem caller_fresh_outputs[local]:
  !n s xs s'. fresh_vars n s = (xs,s') ==>
    ALL_DISTINCT xs /\ LENGTH xs = n /\ s'.cs_current_bb = s.cs_current_bb /\
    s'.cs_current_insts = s.cs_current_insts /\ s'.cs_next_id = s.cs_next_id /\
    s.cs_next_var <= s'.cs_next_var /\
    (!x. MEM x xs ==> ~not_fresh_at s x /\ not_fresh_at s' x)
Proof
  Induct >> simp[fresh_vars_def, comp_return_def, comp_bind_def, fresh_var_def, LET_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  rpt strip_tac >> gvs[not_fresh_at_def] >>
  TRY (qpat_x_assum `!x. MEM x vs ==> _` drule >>
       simp[ASCIInumbersTheory.toString_inj] >> NO_TAC) >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_REFL,
            arithmeticTheory.LESS_EQ_ADD]
QED

Theorem caller_multi_emit[local]:
  emit_multi_op INVOKE (Label lbl :: ops) rc s3 = (results,s4) /\
  fn_has_code s3 s4 func /\ t.vs_current_bb = s3.cs_current_bb /\
  t.vs_inst_idx = LENGTH s3.cs_current_insts /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst ==>
  results = MAP Var inst.inst_outputs /\ ALL_DISTINCT inst.inst_outputs /\
  LENGTH inst.inst_outputs = rc /\ s4.cs_current_bb = t.vs_current_bb /\
  LENGTH s4.cs_current_insts = SUC t.vs_inst_idx /\ s3.cs_next_var <= s4.cs_next_var /\
  (!x. MEM x inst.inst_outputs ==> ~not_fresh_at s3 x /\ not_fresh_at s4 x)
Proof
  strip_tac >>
  qpat_x_assum `emit_multi_op _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac[emit_multi_op_def, comp_bind_def] >>
  Cases_on `fresh_vars rc s3` >> simp_tac (srw_ss()) [] >>
  pure_rewrite_tac[emit_inst_def, comp_bind_def, fresh_id_def, comp_return_def] >>
  simp_tac (srw_ss()) [LET_THM, emit_def, comp_ignore_bind_def, comp_bind_def,
    comp_return_def, fresh_id_def] >>
  strip_tac >>
  drule_then strip_assume_tac caller_fresh_outputs >>
  qpat_x_assum `_ with <|cs_next_id := _; cs_current_insts := _|> = s4`
    (assume_tac o SYM) >>
  `s4.cs_current_insts = s3.cs_current_insts ++ [mk_inst s3.cs_next_id INVOKE (Label lbl::ops) q] /\
   s4.cs_current_bb = s3.cs_current_bb` by simp[] >>
  drule_all_then strip_assume_tac fn_has_code_same_block >>
  qpat_x_assum `!i. i < LENGTH [mk_inst _ INVOKE _ _] ==> _` (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[venomInstTheory.mk_inst_def, not_fresh_at_def]
QED

val prepared_compile = ``
  let key = nsid_to_string (src,name) in
  let ds = omitted_defaults ce key (LENGTH es) in
  let tys = TAKE (LENGTH es + LENGTH ds) (ce.ce_func_param_types key) in
  compile_stage_intcall_args compile_expr ce es pvs tys s2 = (supplied,s2a) /\
  compile_stage_intcall_args compile_expr (cenv_without_defaults ce key)
    ds (DROP (LENGTH es) pvs) (DROP (LENGTH es) tys) s2a = (dfl,s3)``;

val prepared_allocation = ``
  let cap = if 0 < rc then 32 * rc else rbs in
  if cap = 0 then s2 = sa /\ pin = NONE
  else ?buf root b ai. compile_alloc_buffer cap sa = (buf,s2) /\
    buf.buf_operand = Var root /\ buf.buf_size = cap /\ pin = SOME (root,b,cap) /\
    b + cap < dimword (:256) /\ MEM ai (fn_insts func) /\
    ai.inst_opcode = ALLOCA /\ ai.inst_id = sa.cs_next_id /\ ai.inst_outputs = [root]``;

val caller_real_compile = ``compile_expr ce ty (^selected_call_expr) sa = (vv,sm)``;
val caller_shadow_compile = ``
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (^selected_call_expr)) shadow_sa = (vv,shadow_sm) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm``;

val selected_label = ``
  internal_fn_label (ce.ce_func_ids (nsid_to_string (src,name))) (nsid_to_string (src,name))
    (ce.ce_func_param_types (nsid_to_string (src,name))) ce.ce_is_ctor``;

Theorem caller_prepared_emission[local]:
  (^caller_real_compile) /\ (^caller_shadow_compile) /\
  ce.ce_func_info (nsid_to_string (src,name)) = (rc,rbs,pvs) /\
  fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
  (^prepared_compile) /\ (^prepared_allocation) /\
  t.vs_current_bb = s3.cs_current_bb /\ t.vs_inst_idx = LENGTH s3.cs_current_insts ==>
  ?s4 ops bb inst.
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME ((^selected_label),ops) /\
    fn_has_code s3 s4 func /\ fn_has_code s4 sm func /\
    (0 < rc ==> ?buf results.
      compile_alloc_buffer (32 * rc) sa = (buf,s2) /\ ops = supplied ++ dfl /\
      emit_multi_op INVOKE (Label (^selected_label) :: ops) rc s3 = (results,s4) /\
      store_multi_results buf.buf_operand results 0 s4 = ((),sm) /\
      vv = LocatedValue (ce.ce_func_return_type (nsid_to_string (src,name))) (base_ptr buf)) /\
    (rc = 0 ==> s4 = sm /\ ?u. emit_void INVOKE (Label (^selected_label) :: ops) s3 = (u,sm)) /\
    (rc = 0 /\ 0 < rbs ==> ?buf. compile_alloc_buffer rbs sa = (buf,s2) /\
      ops = buf.buf_operand :: (supplied ++ dfl) /\
      vv = LocatedValue (ce.ce_func_return_type (nsid_to_string (src,name))) (base_ptr buf)) /\
    (rc = 0 /\ rbs = 0 ==> ops = supplied ++ dfl /\
      vv = StackValue (ce.ce_func_return_type (nsid_to_string (src,name))) (Lit 0w))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`fallback` |-> `dflt`,`v` |-> `vv`,`sv` |-> `vv`,
       `sb` |-> `sm`,`sha` |-> `shadow_sa`,`shb` |-> `shadow_sm`,
       `fn` |-> `func`,`shfn` |-> `shadow_func`,`flags` |-> `pvs`, `ret_count` |-> `rc`]
      (SIMP_RULE bool_ss [LET_THM] paired_intcall_stage_cuts_mods)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`c2`,`c2a`,`c3`,`sh2`,`sh2a`,`sh3`,`cop`,`cdfl`]
    (strip_assume_tac)) >>
  rename1 `fn_has_code c3 c4 func` >>
  rename1 `decode_invoke _ = SOME (_,aops)` >>
  Cases_on `0 < rc` >- suspend "register" >>
  `rc = 0` by decide_tac >>
  Cases_on `0 < rbs` >- suspend "sret" >>
  `rbs = 0` by decide_tac >> suspend "void"
QED

fun reached_static_emission s4 =
  `c2 = s2` by (first_assum ACCEPT_TAC ORELSE
    (qpat_assum `compile_alloc_buffer _ sa = (_,s2)` (fn th =>
       qpat_assum `compile_alloc_buffer _ sa = (_,c2)` (mp_tac o PURE_REWRITE_RULE [th])) >> simp[]) ORELSE
    simp[]) >>
  qpat_x_assum `c2 = s2` SUBST_ALL_TAC >>
  `cop = supplied /\ c2a = s2a` by
    (qpat_assum `compile_stage_intcall_args compile_expr ce es _ _ s2 = (supplied,s2a)` (fn th =>
       qpat_assum `compile_stage_intcall_args compile_expr ce es _ _ s2 = (cop,c2a)`
         (mp_tac o PURE_REWRITE_RULE [th])) >> simp[]) >>
  qpat_x_assum `c2a = s2a` SUBST_ALL_TAC >>
  `cdfl = dfl /\ c3 = s3` by
    (qpat_assum `compile_stage_intcall_args compile_expr _ _ _ _ s2a = (dfl,s3)` (fn th =>
       qpat_assum `compile_stage_intcall_args compile_expr _ _ _ _ s2a = (cdfl,c3)`
         (mp_tac o PURE_REWRITE_RULE [th])) >> simp[]) >>
  qpat_x_assum `c3 = s3` SUBST_ALL_TAC >>
  qpat_assum `!t. t.vs_current_bb = s3.cs_current_bb /\ _ ==> _`
    (qspec_then `t` mp_tac) >> (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`bb`,`inst`] strip_assume_tac) >>
  qexistsl_tac [s4,`aops`,`bb`,`inst`];

Resume caller_prepared_emission[register]:
  qpat_x_assum `0 < rc ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `if _ then s2 = sa /\ _ else _` mp_tac >>
  simp_tac (srw_ss()) [] >>
  `32 * rc <> 0` by simp[] >> simp[] >> strip_tac >>
  reached_static_emission `c4` >>
  rename1 `store_multi_results _ results 0 c4 = (u,sm)` >> Cases_on `u` >> gvs[]
QED

Resume caller_prepared_emission[sret]:
  qpat_x_assum `rc = 0 /\ 0 < rbs ==> _` (drule_all_then strip_assume_tac) >>
  `rbs <> 0` by decide_tac >>
  qpat_assum `rc = 0` (fn z => qpat_assum `rbs <> 0` (fn nz =>
    qpat_x_assum `if _ then s2 = sa /\ _ else _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [z,nz]))) >>
  `rbuf = buf` by
    (qpat_assum `compile_alloc_buffer rbs sa = (buf,s2)` (fn th =>
       qpat_assum `compile_alloc_buffer rbs sa = (rbuf,c2)`
         (mp_tac o PURE_REWRITE_RULE [th])) >> simp[]) >>
  reached_static_emission `c4` >> simp[]
QED

Resume caller_prepared_emission[void]:
  qpat_x_assum `rc = 0 /\ rbs = 0 ==> _` (drule_all_then strip_assume_tac) >>
  qpat_assum `rc = 0` (fn z => qpat_assum `rbs = 0` (fn zr =>
    qpat_x_assum `if _ then s2 = sa /\ _ else _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [z,zr]))) >>
  reached_static_emission `c4` >> simp[]
QED

Finalise caller_prepared_emission[local]

val prepared_frame = ``intcall_stage_frame_mods (DF,lo,d,ctx,func) ce cx st0
  (sa,es0,s0,G0,tn0) (s3,es1 with scopes := prev,t,G,tn) pin``;
val prepared_ops = ``intcall_stage_ops_mods (lo,func) ce cx sa
  (s3,es1 with scopes := prev,t,G,tn) (pin : (string # num # num) option)
    (supplied ++ dfl,ws,vals,ptys,pflags)``;

Theorem caller_frame_from_packet[local]:
  (^prepared_frame) /\ (?H. valid_horizon cx st0 H es1.storage_trace) ==>
  allocas_from lo t /\ alloca_history func t /\ ~t.vs_halted /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ t.vs_current_bb = s3.cs_current_bb /\
  t.vs_inst_idx = LENGTH s3.cs_current_insts /\
  sa.cs_next_id <= s3.cs_next_id /\ sa.cs_next_var <= s3.cs_next_var /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
     (^caller_frame) H (es1 with scopes := prev) G tn t)
Proof
  BETA_TAC >> simp_tac (srw_ss()) [intcall_stage_frame_mods_def, wb_frame_def] >>
  strip_tac >>
  `allocas_from lo t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [ghost_inv_at_mods_def]) >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `H'` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _` mp_tac >>
     simp[]))
QED

Theorem caller_invoke_ptr_clean[local]:
  EVERY (\op. op_taint tn op = {}) ops /\ decode_invoke inst = SOME (lbl,ops) /\
  inst.inst_opcode = INVOKE /\ allocas_from lo t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
  ptr_inst_ok D lo 0 ctx func G tn inst t
Proof
  strip_tac >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def] >>
  qpat_x_assum `decode_invoke inst = _` mp_tac >>
  simp[venomExecSemanticsTheory.decode_invoke_def, AllCaseEqs()] >> strip_tac >>
  gvs[ptrDisciplineTheory.taint_ok_def, EVERY_MEM, op_taint_def,
      contextCodegenRelTheory.source_memory_read_ranges_def] >>
  gen_tac >> Cases_on `op = Label lbl` >> simp[] >> Cases_on `MEM op ops` >> simp[]
QED

Theorem caller_void_emit[local]:
  emit_void INVOKE (Label lbl :: ops) s3 = (u,sm) /\
  fn_has_code s3 sm func /\ t.vs_current_bb = s3.cs_current_bb /\
  t.vs_inst_idx = LENGTH s3.cs_current_insts /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst ==>
  inst.inst_outputs = [] /\ t.vs_current_bb = sm.cs_current_bb /\
  SUC t.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  Cases_on `u` >> strip_tac >> drule_all_then strip_assume_tac emit_void_fetch_boundary >>
  gvs[venomInstTheory.mk_inst_def]
QED

Theorem caller_sret_size[local]:
  (^caller_func_info) /\ rc = 0 /\ 0 < rbs /\
  expr_body_pre_mods mods ce cx env (^selected_call_expr) es0 /\
  evaluate_type (get_tenv cx) ret = SOME rtv ==>
  type_memory_size rtv = rbs
Proof
  strip_tac >>
  `type_memory_bytes ce ret = rbs` by
    (qpat_assum `ce.ce_func_info _ = (rc,rbs,pvs)` (fn info =>
       qpat_assum `ce.ce_func_info _ = compute_func_info _ _ _ _`
         (mp_tac o PURE_REWRITE_RULE [info])) >>
     Cases_on `ret` >> simp[compute_func_info_def, Excl "type_memory_bytes_def"] >>
     Cases_on `returns_stack_count (\n. MAP (FST o SND)
       (get_struct_fields ce.ce_struct_fields n)) ret` >> simp[]) >>
  qpat_x_assum `type_memory_bytes ce ret = rbs` (pure_rewrite_tac o single o SYM) >>
  sym_tac >> irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
  drule_then (strip_assume_tac o PURE_REWRITE_RULE [expr_sim_inv_mods_def]) expr_body_pre_mods_inv >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (rpt strip_tac >> qpat_assum `!name fields. _ ==> ALL_DISTINCT _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))))
QED

Theorem caller_pin_packet[local]:
  (^prepared_frame) /\ pin = SOME (root,off,cap) ==>
  FLOOKUP G root = SOME (off,cap) /\ op_taint tn (Var root) = {} /\
  lookup_var root t = SOME (n2w off) /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (off,cap) /\
  sa.cs_next_id < s3.cs_next_id /\ lo <= off /\ off+cap <= t.vs_alloca_next /\
  not_fresh_at s3 root
Proof
  simp_tac (srw_ss()) [intcall_stage_frame_mods_def] >> strip_tac >> gvs[]
QED

Theorem caller_ops_packet[local]:
  (^prepared_ops) ==>
  eval_operands (supplied ++ dfl) t = SOME ws /\
  EVERY (\op. op_taint tn op = {}) (supplied ++ dfl)
Proof
  simp_tac (srw_ss()) [intcall_stage_ops_mods_def]
QED

val prepared_fetch = ``
  t.vs_current_bb = s3.cs_current_bb /\ t.vs_inst_idx = LENGTH s3.cs_current_insts /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,ops) /\ inst.inst_opcode = INVOKE``;

Theorem caller_register_layout[local]:
  (^prepared_fetch) /\ (^prepared_frame) /\ (^prepared_ops) /\ (^prepared_allocation) /\
  0 < rc /\ fn_has_code s3 st4 func /\ fn_has_code st4 sm func /\
  ops = supplied ++ dfl /\ outs = inst.inst_outputs /\ sa.cs_next_var <= s3.cs_next_var /\
  compile_alloc_buffer (32 * rc) sa = (rbuf,s2) /\
  emit_multi_op INVOKE (Label lbl :: ops) rc s3 = (results,st4) /\
  store_multi_results rbuf.buf_operand results 0 st4 = ((),sm) /\
  vv = LocatedValue (ce.ce_func_return_type (nsid_to_string (src,name))) (base_ptr rbuf) ==>
  eval_operands ops t = SOME ws /\ EVERY (\op. op_taint tn op = {}) ops /\
  LENGTH outs = rc /\ (!x. MEM x outs ==> ~not_fresh_at sa x) /\
  ALL_DISTINCT outs /\ (^register_buffer)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  drule_then strip_assume_tac caller_ops_packet >>
  drule_all_then strip_assume_tac caller_multi_emit >>
  `32 * rc <> 0` by simp[] >>
  qpat_assum `0 < rc` (fn pos => qpat_assum `32 * rc <> 0` (fn nz =>
    qpat_x_assum `if _ then s2 = sa /\ _ else _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [pos,nz]))) >>
  `rbuf = buf` by
    (qpat_assum `compile_alloc_buffer _ sa = (buf,s2)` (fn eq =>
       qpat_assum `compile_alloc_buffer _ sa = (rbuf,s2)`
         (mp_tac o PURE_REWRITE_RULE [eq])) >> simp[]) >>
  qpat_x_assum `rbuf = buf` SUBST_ALL_TAC >>
  rename1 `buf.buf_operand = Var root` >>
  drule_all_then strip_assume_tac caller_pin_packet >>
  `s3.cs_next_id <= st4.cs_next_id` by
    (qpat_assum `emit_multi_op _ _ _ _ = _` (fn eq =>
       mp_tac (PURE_REWRITE_RULE [eq, pairTheory.SND]
         (Q.SPECL [`INVOKE`,`Label lbl :: ops`,`rc`,`s3`] ci_mono_emit_multi_op))) >>
     simp[ci_mono_def]) >>
  drule_then strip_assume_tac intCallResultTheory.store_multi_results_shape >>
  `sa.cs_next_id < sm.cs_next_id /\ sa.cs_next_var <= st4.cs_next_var` by decide_tac >>
  `not_fresh_at st4 root` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `results = _` SUBST_ALL_TAC >>
  qpat_x_assum `outs = _` SUBST_ALL_TAC >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >-
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qexistsl_tac [`buf`,`root`,`b`,`ai`,`st4`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (simp[] >> NO_TAC) ORELSE metis_tac[])
QED

Theorem caller_sret_layout[local]:
  (^prepared_fetch) /\ (^prepared_frame) /\ (^prepared_ops) /\ (^prepared_allocation) /\
  rc = 0 /\ 0 < rbs /\ fn_has_code s3 sm func /\
  emit_void INVOKE (Label lbl :: ops) s3 = (u,sm) /\ outs = inst.inst_outputs /\
  compile_alloc_buffer rbs sa = (rbuf,s2) /\ ops = rbuf.buf_operand :: (supplied ++ dfl) /\
  vv = LocatedValue (ce.ce_func_return_type (nsid_to_string (src,name))) (base_ptr rbuf) /\
  ce.ce_func_return_type (nsid_to_string (src,name)) = ret /\ type_memory_size rtv = rbs ==>
  ?argv. eval_operands ops t = SOME argv /\ EVERY (\op. op_taint tn op = {}) ops /\
    LENGTH outs = rc /\ (!x. MEM x outs ==> ~not_fresh_at sa x) /\ (^zero_result_layout)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  drule_then strip_assume_tac caller_ops_packet >>
  drule_all_then strip_assume_tac caller_void_emit >>
  `rbs <> 0` by decide_tac >>
  qpat_assum `rc = 0` (fn z => qpat_assum `rbs <> 0` (fn nz =>
    qpat_x_assum `if _ then s2 = sa /\ _ else _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [z,nz]))) >>
  `rbuf = buf` by
    (qpat_assum `compile_alloc_buffer _ sa = (buf,s2)` (fn eq =>
       qpat_assum `compile_alloc_buffer _ sa = (rbuf,s2)`
         (mp_tac o PURE_REWRITE_RULE [eq])) >> simp[]) >>
  qpat_x_assum `rbuf = buf` SUBST_ALL_TAC >>
  rename1 `buf.buf_operand = Var root` >>
  drule_all_then strip_assume_tac caller_pin_packet >>
  `s3.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `emit_void _ _ _ = _` (fn eq =>
       mp_tac (PURE_REWRITE_RULE [eq, pairTheory.SND]
         (Q.SPECL [`INVOKE`,`Label lbl :: ops`,`s3`] ci_mono_emit_void))) >>
     simp[ci_mono_def]) >>
  `sa.cs_next_id < sm.cs_next_id /\ b < dimword (:256)` by decide_tac >>
  qexists_tac `n2w b :: ws` >>
  simp[venomStateTheory.eval_operands_def, venomStateTheory.eval_operand_def,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  qexistsl_tac [`buf`,`root`] >> simp[venomStateTheory.eval_operand_def]
QED

Theorem caller_void_layout[local]:
  (^prepared_fetch) /\ (^prepared_ops) /\ rc = 0 /\ rbs = 0 /\ fn_has_code s3 sm func /\
  emit_void INVOKE (Label lbl :: ops) s3 = (u,sm) /\ outs = inst.inst_outputs /\
  ops = supplied ++ dfl /\
  vv = StackValue (ce.ce_func_return_type (nsid_to_string (src,name))) (Lit 0w) ==>
  eval_operands ops t = SOME ws /\ EVERY (\op. op_taint tn op = {}) ops /\
    LENGTH outs = rc /\ (!x. MEM x outs ==> ~not_fresh_at sa x) /\ (^zero_result_layout)
Proof
  BETA_TAC >> strip_tac >> drule_then strip_assume_tac caller_ops_packet >>
  drule_all_then strip_assume_tac caller_void_emit >> simp[]
QED

(* The decoded words come from the reached packet.  Only a hidden structure
   return operand is added by the INVOKE emission. *)
Theorem caller_prepared_layout[local]:
  (^caller_real_compile) /\ (^caller_shadow_compile) /\ (^caller_func_info) /\
  fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
  (^prepared_compile) /\ (^prepared_allocation) /\ (^prepared_frame) /\ (^prepared_ops) /\
  t.vs_current_bb = s3.cs_current_bb /\ t.vs_inst_idx = LENGTH s3.cs_current_insts /\
  sa.cs_next_var <= s3.cs_next_var /\
  expr_body_pre_mods mods ce cx env (^selected_call_expr) es0 /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  ce.ce_func_return_type (nsid_to_string (src,name)) = ret ==>
  ?ops bb inst argv outs.
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME ((^selected_label),ops) /\
    eval_operands ops t = SOME argv /\ EVERY (\op. op_taint tn op = {}) ops /\
    outs = inst.inst_outputs /\ LENGTH outs = rc /\
    (!x. MEM x outs ==> ~not_fresh_at sa x) /\
    (rc = 0 ==> (^zero_result_layout)) /\
    (0 < rc ==> ALL_DISTINCT outs /\ (^register_buffer))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (BETA_RULE (SIMP_RULE bool_ss [LET_THM] caller_prepared_emission)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`st4`,`ops`,`bb`,`inst`] strip_assume_tac) >>
  qabbrev_tac `lbl = ^selected_label` >>
  qabbrev_tac `outs = inst.inst_outputs` >>
  `outs = inst.inst_outputs` by simp[Abbr `outs`] >>
  Cases_on `0 < rc` >- suspend "register" >>
  `rc = 0` by decide_tac >>
  qpat_x_assum `rc = 0 ==> st4 = sm /\ _` (drule_then strip_assume_tac) >>
  Cases_on `0 < rbs` >- suspend "sret" >>
  `rbs = 0` by decide_tac >> suspend "void"
QED

Resume caller_prepared_layout[register]:
  qpat_x_assum `0 < rc ==> ?buf results. _` (drule_then strip_assume_tac) >>
  rename1 `store_multi_results rbuf.buf_operand results 0 st4 = _` >>
  mp_tac (BETA_RULE (SIMP_RULE bool_ss [LET_THM] caller_register_layout)) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE fs[]))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl_tac [`ops`,`bb`,`inst`,`ws`,`outs`] >>
  `rc <> 0` by decide_tac >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (asm_rewrite_tac[] >> NO_TAC) ORELSE
    (disch_tac >> rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
      (qpat_x_assum `?buf root off ai st4. buf.buf_operand = _ /\ _` mp_tac >>
       asm_rewrite_tac[]))))
QED

Resume caller_prepared_layout[sret]:
  qpat_x_assum `rc = 0 /\ 0 < rbs ==> _` (drule_all_then strip_assume_tac) >>
  rename1 `emit_void _ _ _ = (u,sm)` >>
  rename1 `compile_alloc_buffer rbs sa = (rbuf,s2)` >>
  `type_memory_size rtv = rbs` by (irule caller_sret_size >> simp[] >> metis_tac[]) >>
  mp_tac (BETA_RULE (SIMP_RULE bool_ss [LET_THM] caller_sret_layout)) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE fs[]))) >>
  disch_then (qx_choose_then `argv` (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`ops`,`bb`,`inst`,`argv`,`outs`] >>
  map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
    [`ops = rbuf.buf_operand :: _`,`outs = inst.inst_outputs`,`rc = 0`,
     `t.vs_current_bb = s3.cs_current_bb`,`t.vs_inst_idx = LENGTH s3.cs_current_insts`] >>
  simp_tac bool_ss [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO] >>
  rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE
     (asm_rewrite_tac[] >> NO_TAC))
QED

Resume caller_prepared_layout[void]:
  qpat_x_assum `rc = 0 /\ rbs = 0 ==> _` (drule_all_then strip_assume_tac) >>
  rename1 `emit_void _ _ _ = (u,sm)` >>
  mp_tac (BETA_RULE caller_void_layout) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE fs[]))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl_tac [`ops`,`bb`,`inst`,`ws`,`outs`] >>
  `sm.cs_current_bb = s3.cs_current_bb` by metis_tac[] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (simp_tac bool_ss [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO] >> NO_TAC) ORELSE
    (disch_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) ORELSE
    (asm_rewrite_tac[]))
QED

Finalise caller_prepared_layout[local]

val caller_call_read = ``
  \(H : (bool # 256 word # type_value) list # num list) (res : value + exception)
    ee G1 tn1 s. ?v. res = INL v /\
    expr_post_mods H ctx func ce cx (^selected_call_expr) es0 sa sb s0 ee v op s /\
    expr_store_bound cx (post_value_type ce (^selected_call_expr)) v op s /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G1 tn1 s /\
    ptr_val_ok cx (post_value_type ce (^selected_call_expr)) v op G1 tn1 s /\
    (~is_word_type (post_value_type ce (^selected_call_expr)) ==>
      ptr_buf_ok ce (^selected_call_expr) op G1 s) /\
    ghost_kept_at lo ce es0 sa G0 tn0 s0 G1 tn1``;

val caller_read_exit = ``\(H : (bool # 256 word # type_value) list # num list)
  (res : value + exception) ee (gt : (string |-> num # num) # taint) r.
    expr_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

(* Use the callback of the very same case rule that restores the caller. *)
val selected_caller_outcome_cases =
  Q.INST [`P` |-> `^callee_return`, `Q` |-> `^selected_owned`]
    caller_callee_outcome_cases;

val selected_normal_callback =
  let
    val premises = strip_conj (fst (dest_imp (concl selected_caller_outcome_cases)))
    fun is_callback tm =
      let val (args,body) = strip_forall tm
      in length args = 7 andalso can dest_imp body end
  in
    case List.filter is_callback premises of
      [callback] => callback
    | _ => raise Fail "expected exactly one completed-callee callback"
  end;

Theorem caller_completed_normal_callback_adapter[local]:
  contract_inv mods exps ctx ce cx /\ (^caller_stage_frame) /\ (^reached_invoke) /\
  gas_admissible (^return_rest) expr_vv_res_ok es1 /\ (^reached_return) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ALOOKUP mods src = SOME tops /\ ALOOKUP ce.ce_modules ce.ce_module = SOME caller_tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  expr_body_pre_mods mods ce cx env (^selected_call_expr) es0 /\ (^caller_func_info) /\
  (rc = 0 ==> (^zero_result_layout)) /\
  (0 < rc ==> ALL_DISTINCT inst.inst_outputs /\ (^register_buffer)) /\
  outs = inst.inst_outputs /\ ~t.vs_halted /\ allocas_from lo t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ fn_inst_ids_distinct func ==>
  ^selected_normal_callback
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`Gc` |-> `Gc`, `args` |-> `args`, `argv` |-> `argv`,
    `bb` |-> `bb`, `callee` |-> `callee`, `cs` |-> `cs`, `dflts` |-> `dflts`,
    `ee` |-> `ee`, `entered` |-> `entered`, `inst` |-> `inst`, `ir` |-> `ir`,
    `lbl` |-> `lbl`, `marks` |-> `marks`, `ops` |-> `ops`, `outs` |-> `outs`,
    `pvs` |-> `pvs`, `rbs` |-> `rbs`, `rc` |-> `rc`, `ret` |-> `ret`,
    `tc` |-> `tc`, `tops` |-> `tops`, `v` |-> `v`, `caller_tops` |-> `caller_tops`]
    caller_completed_normal) >>
  (impl_tac >- (rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE
     (rpt conj_tac >> first_assum ACCEPT_TAC)))) >>
  disch_then ACCEPT_TAC
QED

(* Public linked caller restoration: the prepared packet fixes the reached
   INVOKE, while the supplied callee rule is consumed exactly once. *)
Theorem selected_caller_exit_restore_mods:
  contract_inv mods exps ctx ce cx /\ ALOOKUP mods src = SOME tops /\
  expr_body_pre_mods mods ce cx env (^selected_call_expr) es0 /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  (^caller_real_compile) /\ (^caller_shadow_compile) /\ (^caller_func_info) /\
  fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
  (^prepared_compile) /\ (^prepared_allocation) /\ (^prepared_frame) /\
  (^prepared_ops) /\ (^prepared_fetch) /\
  gas_admissible (^return_rest) expr_vv_res_ok es1 /\
  (^caller_stage_frame) /\ (^reached_invoke) /\ (^reached_return) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ALOOKUP ce.ce_modules ce.ce_module = SOME caller_tops /\
  (^caller_func_info) /\
  (rc = 0 ==> (^zero_result_layout)) /\
  (0 < rc ==> ALL_DISTINCT inst.inst_outputs /\ (^register_buffer)) /\
  outs = inst.inst_outputs /\ ~t.vs_halted /\ allocas_from lo t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ fn_inst_ids_distinct func /\
  (!callee entered bb inst lbl ops argv.
     gas_invoke_entry (ctx,func) t callee entered /\
     lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
     get_instruction bb t.vs_inst_idx = SOME inst /\
     inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops) /\
     eval_operands ops t = SOME argv ==>
       gas_outcome_full_mods (DF,lo,explicit,ctx,callee,MAP (op_prov G) ops)
         mods cx st0 (^return_source) (es1,entered,FEMPTY,tn with t_var := FEMPTY)
         (\H res out Gc tc s. F)
         (\H res out gt r. (expr_exit res r /\ halt_exit H cx out res r) \/
           (?v ir cs. res = INL v /\ r = IntRet ir cs /\
             (^callee_return) H v out gt ir cs))) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (^return_rest) (es1,t,G,tn) (^selected_owned) (^caller_exit) /\
  (!op sb shadow_sb.
     unwrap_value ce vv sm = (op,sb) /\
     unwrap_value ce vv shadow_sm = (op,shadow_sb) /\
     gas_shadow_state sb shadow_sb /\
     fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
     gas_admissible (bind (^return_rest) (read_result cx)) expr_res_ok es1 ==>
       gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
         (bind (^return_rest) (read_result cx)) (es1,t,G,tn)
         (^caller_call_read) (^caller_read_exit))
Proof
  strip_tac >>
  `gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (^return_rest) (es1,t,G,tn) (^selected_owned) (^caller_exit)` by
    (irule caller_callee_outcome_cases >>
     qexistsl_tac [`^callee_return`,`bb`,`callee`,`entered`,`inst`,`lbl`,`ops`] >>
     ((rpt strip_tac >>> NTH_GOAL (simp[SIMP_RULE bool_ss [LET_THM] caller_completed_normal]) 3 >>> NTH_GOAL (simp[SIMP_RULE bool_ss [LET_THM] caller_completed_normal]) 3 >>> NTH_GOAL (simp[SIMP_RULE bool_ss [LET_THM] caller_completed_normal]) 3 >>> NTH_GOAL (simp[SIMP_RULE bool_ss [LET_THM] caller_completed_normal]) 3 >>> NTH_GOAL (simp[SIMP_RULE bool_ss [LET_THM] caller_completed_normal]) 3 >>
       CONV_TAC (DEPTH_CONV BETA_CONV) >>
       mp_tac (SIMP_RULE bool_ss [LET_THM] caller_completed_normal) >>
       (impl_tac >- (rpt conj_tac >> (TRY (first_assum ACCEPT_TAC)) >> all_tac)) >>
       disch_then ACCEPT_TAC) >-
      (gen_tac >> strip_tac >>
       qpat_assum `!callee entered bb inst lbl ops argv. _` drule_all >>
       first_assum ACCEPT_TAC) >-
      (rpt gen_tac >> strip_tac >>
       irule caller_invoke_ptr_clean >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >-
      first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >-
      first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >-
      first_assum ACCEPT_TAC)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule selected_return_unwrap_mods >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

