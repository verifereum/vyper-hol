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
