(* The positive memory Pop writes one header word in a reached local. *)
Theory bodyPopLocalFrameMods
Ancestors
  bodyFullMemoryFrames exprSimPopNestedLocalPost exprSimWordArgs
  wordLoadStorePtr stateRelProj nameLoweringProps vyperTypeEnvPreservation
  vyperFiniteStoragePreservation venomMemProps loweringStateRelDefs exprLoweringProps
  loweringSlice compileEnv finite_map words vyperState venomState bodyInvSplit
  bodyFullShadowBodyInv bodyPtrDefs ptrDiscipline assignTuplePtrCopyLen
  valueEncodingProps valueEncodingDefs pred_set arithmetic loweringPosts
  bodyFullUnwrapRun localPtrsProps exprSimPop bodyFullPostsMods memoryValueEncoding

Theorem pop_local_region_transport[local]:
  MAP FDOM ef.scopes = MAP FDOM mid.scopes /\
  (!nm p n. FLOOKUP ce.ce_vars nm = SOME (PtrVar (Var p) n) ==>
     lookup_var p u = lookup_var p s) ==>
  !src nm b n.
    local_region (ce with ce_module := src) ef.scopes u nm b n <=>
    local_region (ce with ce_module := src) mid.scopes s nm b n
Proof
  strip_tac >> rpt gen_tac >>
  simp[local_region_def, GSYM optionTheory.IS_SOME_EXISTS] >>
  eq_tac >> strip_tac >>
  metis_tac[lookup_scopes_same_fdoms_some, optionTheory.IS_SOME_EXISTS]
QED

Theorem pop_local_immutable_rel[local]:
  immutable_alloca_sep func (ce with ce_module := src) cx mid s /\
  immutables_rel ce cx.txn.target src ce.ce_is_ctor mid s /\
  local_region ce mid.scopes s id b n /\ k+32 <= n /\
  u.vs_data_section = s.vs_data_section /\
  u.vs_memory = (mstore (b+k) wd s).vs_memory ==>
  immutables_rel ce cx.txn.target src ce.ce_is_ctor mid u
Proof
  strip_tac >> irule immutables_rel_mem_agree >> qexists_tac `s` >>
  simp[mstore_memory_nondecreasing] >> rpt strip_tac >>
  `local_region (ce with ce_module := src) mid.scopes s id b n` by
    fs[local_region_def] >>
  `regions_disjoint off (type_memory_size tv) b n` by
    (qpat_assum `immutable_alloca_sep _ _ _ _ _`
       (mp_tac o CONJUNCT2 o REWRITE_RULE [immutable_alloca_sep_def]) >>
     simp[] >> disch_then (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  simp[] >> irule mstore_mem_bytes_at_disjoint >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem pop_local_linked_immutable[local]:
  immutable_frame_mods func ce cx mid s /\
  local_region ce mid.scopes s id b n /\ k+32 <= n /\
  ef.immutables = mid.immutables /\
  u.vs_data_section = s.vs_data_section /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  u.vs_memory = (mstore (b+k) wd s).vs_memory /\
  (!src nm at len. local_region (ce with ce_module := src) ef.scopes u nm at len ==>
      local_region (ce with ce_module := src) mid.scopes s nm at len) ==>
  immutable_frame_mods func ce cx ef u
Proof
  strip_tac >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `immutables_rel ce cx.txn.target src ce.ce_is_ctor mid u` by
        (irule pop_local_immutable_rel >>
         goal_assum (drule_at (Pat `u.vs_memory = _`)) >>
         goal_assum (drule_at (Pat `local_region ce mid.scopes s id b n`)) >>
         qexists_tac `func` >> simp[] >> metis_tac[]) >>
      qpat_x_assum `immutables_rel _ _ src _ mid u` mp_tac >>
      simp[immutables_rel_def]) >>
  rpt gen_tac >> disch_tac >> irule immutable_alloca_sep_fields >>
  qexistsl_tac [`s`,`mid`] >> simp[] >> metis_tac[]
QED

Theorem pop_local_state[local]:
  stmt_state_rel H ctx func ce cx mid s /\
  local_ptrs_rel func ce (ef:evaluation_state).scopes u /\
  ef = mid with scopes := ef.scopes /\
  u = s with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
               vs_inst_idx := u.vs_inst_idx|> /\
  u.vs_memory = (mstore (b+k) wd s).vs_memory /\
  local_region ce mid.scopes s id b n /\ k+32 <= n /\
  (!nm at len. local_region ce ef.scopes u nm at len ==>
     local_region ce mid.scopes s nm at len) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==> lookup_var x u = lookup_var x s) ==>
  stmt_state_rel H ctx func ce cx ef u
Proof
  strip_tac >> qabbrev_tac `q = u with vs_inst_idx := s.vs_inst_idx` >>
  `q = s with <|vs_vars := q.vs_vars; vs_memory := q.vs_memory|>` by
    (simp[Abbr `q`] >> qpat_assum `u = s with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>` (once_rewrite_tac o single) >> simp[]) >>
  `q.vs_data_section = s.vs_data_section /\ q.vs_labels = s.vs_labels` by
    (qpat_assum `q = s with <|vs_vars := _; vs_memory := _|>` (once_rewrite_tac o single) >> simp[]) >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor mid q` by
    (drule_then assume_tac stmt_state_rel_state_rel >>
     drule_then assume_tac state_rel_immutables_rel >>
     `q.vs_memory = (mstore (b+k) wd s).vs_memory` by simp[Abbr `q`] >>
     irule pop_local_immutable_rel >>
     goal_assum (drule_at (Pat `immutables_rel _ _ _ _ mid s`)) >>
     goal_assum (drule_at (Pat `q.vs_memory = _`)) >>
     goal_assum (drule_at (Pat `local_region ce mid.scopes s id b n`)) >>
     qexists_tac `func` >> simp[compile_env_component_equality] >>
     fs[stmt_state_rel_def]) >>
  `immutable_base_zero ce q` by
    (drule_then assume_tac stmt_state_rel_immutable_base_zero >>
     irule immutable_base_zero_frame >> qexists_tac `s` >>
     fs[Abbr `q`, lookup_var_def]) >>
  `!nm at len. local_region ce ef.scopes q nm at len ==>
     local_region ce mid.scopes s nm at len` by
    (qpat_assum `!nm at len. local_region ce ef.scopes u nm at len ==> _` mp_tac >>
     simp[Abbr `q`, local_region_def, lookup_var_def]) >>
  `local_ptrs_rel func ce ef.scopes q` by simp[Abbr `q`, local_ptrs_rel_inst_idx] >>
  `LENGTH s.vs_memory <= LENGTH q.vs_memory` by
    simp[Abbr `q`, mstore_memory_nondecreasing] >>
  `stmt_state_rel H ctx func ce cx (mid with scopes := ef.scopes) q` suffices_by
    (simp[Abbr `q`, stmt_state_rel_inst_idx] >> metis_tac[]) >>
  irule pop_stmt_state_rel_scopes >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `s` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> metis_tac[]
QED

Theorem pop_local_other_regions[local]:
  local_ptrs_rel func ce mid.scopes s /\
  local_region ce mid.scopes s id b n /\ k+32 <= n /\
  j <> id /\ local_region ce mid.scopes s j a cap ==>
  a+cap <= b+k \/ b+k+32 <= a
Proof
  strip_tac >>
  `regions_disjoint b n a cap` by (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem pop_local_ghost[local]:
  ghost_inv_at_mods D lo d ce cx mid G tn s /\
  local_ptrs_rel func ce mid.scopes s /\ local_ptrs_reserved ce sm /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x) /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  lookup_scopes id mid.scopes = SOME old /\
  lookup_scopes id ef.scopes = SOME upd /\
  (!j. j <> id ==> lookup_scopes j ef.scopes = lookup_scopes j mid.scopes) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) n) /\ lookup_var root s = SOME bw /\
  (!m. mem_agree_outside tn'.t_mem u.vs_memory m ==>
      val_in_memory upd.type upd.value (w2n bw) m) /\
  (!j a cap. j <> id /\ local_region ce mid.scopes s j a cap ==>
      a+cap <= w2n bw+k \/ w2n bw+k+32 <= a) /\
  u.vs_memory = (mstore (w2n bw+k) wd s).vs_memory /\
  tn'.t_mem = tn.t_mem DIFF {i | w2n bw+k <= i /\ i < w2n bw+k+32} /\
  mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  u.vs_accounts = s.vs_accounts /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next ==>
  ghost_inv_at_mods D lo d ce cx ef G' tn' u
Proof
  strip_tac >>
  `!p n. not_fresh_at sm p /\ ptr_covers G tn p s n ==>
      ptr_covers G' tn' p u n` by
    (rpt strip_tac >> irule ptr_covers_lookup_frame >>
     goal_assum (drule_at Any) >> simp[]) >>
  fs[ghost_inv_at_mods_def] >> conj_tac >- suspend "locals" >>
  conj_tac
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME pair)` >> PairCases_on `pair` >>
      fs[return_buf_ptr_def] >> metis_tac[]) >>
  simp[stor_taint_ok_at_def, allocas_from_def] >>
  conj_tac >- fs[stor_taint_ok_at_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by metis_tac[local_ptrs_reserved_imm_base] >>
      metis_tac[]) >>
  fs[allocas_from_def]
QED

Resume pop_local_ghost[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sm p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  Cases_on `name = id`
  >- (gvs[] >> metis_tac[]) >>
  `lookup_scopes name mid.scopes = SOME entry` by metis_tac[] >>
  qpat_assum `!name entry p sz. _ ==> ptr_covers G tn p s sz /\ _`
    (drule_all_then strip_assume_tac) >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `local_region ce mid.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `w2n w+sz <= k+w2n bw \/ k+(w2n bw+32) <= w2n w` by
    (qpat_assum `!j a cap. _ ==> _ <= _ \/ _ <= _` (drule_all_then ACCEPT_TAC)) >>
  irule mstore_local_robust >> goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lookup_scopes _ mid.scopes = SOME _`)) >>
  simp[AC ADD_ASSOC ADD_COMM] >>
  qexistsl_tac [`k+w2n bw`,`tn.t_mem`,`wd`] >>
  fs[AC ADD_ASSOC ADD_COMM]
QED

Finalise pop_local_ghost

(* The source cut supplies the scope update, snapshot, and robust new root.
   The physical cut supplies one word store and frames all old registers. *)
Theorem pop_local_write_frame_mods:
  contract_inv mods exps ctx ce cx /\ expr_sim_inv_mods mods ce cx env es /\
  dead_lo_ok_mods H (DF H) lo ce cx /\
  stmt_state_rel H ctx func ce cx es s0 /\
  stmt_state_rel H ctx func ce cx mid s /\ immutable_frame_mods func ce cx mid s /\
  immutable_decl_sep_mods ce cx mid.scopes s.vs_vars s.vs_allocas s.vs_alloca_next /\
  storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx mid G tn s /\
  wb_frame ce es mid sa s0 s /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x) /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  local_region ce mid.scopes s id (w2n bw) n /\ k+32 <= n /\
  dynarray_len_untupled ce id k /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) n) /\ lookup_var root s = SOME bw /\
  u = s with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory; vs_inst_idx := u.vs_inst_idx|> /\
  u.vs_memory = (mstore (w2n bw+k) wd s).vs_memory /\
  tn'.t_mem = tn.t_mem DIFF {i | w2n bw+k <= i /\ i < w2n bw+k+32} /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  ef = mid with scopes := ef.scopes /\ MAP FDOM ef.scopes = MAP FDOM mid.scopes /\
  lookup_scopes id mid.scopes = SOME entry /\
  lookup_scopes id ef.scopes = SOME (entry with <|value := updated; popped := hnew::entry.popped|>) /\
  (!j. j <> id ==> lookup_scopes j ef.scopes = lookup_scopes j mid.scopes) /\
  snapshot_in entry.type (w2n bw) n hnew u.vs_memory /\
  EVERY (\q. ?err. evaluate_subscripts entry.type entry.value q = INR err) (MAP FST entry.popped) /\
  evaluate_subscripts entry.type entry.value path = INL arr /\
  mem_path_offset entry.type path = SOME (k,ArrayTV etv (Dynamic cap)) /\
  value_has_type entry.type updated /\
  (!m. mem_agree_outside tn'.t_mem u.vs_memory m ==>
      val_in_memory entry.type updated (w2n bw) m) ==>
  stmt_state_rel H ctx func ce cx ef u /\ immutable_frame_mods func ce cx ef u /\
  storage_well_formed_on cx ef (FST H) /\ wb_frame ce es ef sa s0 u /\
  ghost_inv_at_mods (DF H) lo d ce cx ef G' tn' u /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G' tn'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `local_ptrs_reserved ce sm` by (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  `!j p len. FLOOKUP ce.ce_vars j = SOME (PtrVar (Var p) len) ==>
     lookup_var p u = lookup_var p s` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  drule_all_then assume_tac pop_local_region_transport >>
  `!j a len. local_region ce ef.scopes u j a len <=> local_region ce mid.scopes s j a len` by
    (`ce with ce_module := ce.ce_module = ce` by simp[compile_env_component_equality] >>
     pop_assum (fn eq => qpat_assum `!src nm b n. local_region _ _ _ _ _ _ <=> _`
       (qspec_then `ce.ce_module` (ACCEPT_TAC o REWRITE_RULE [eq])))) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_data_section = s.vs_data_section /\ u.vs_accounts = s.vs_accounts /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables` by
    (qpat_assum `u = s with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>` (once_rewrite_tac o single) >> simp[]) >>
  `0 < n` by decide_tac >>
  `lo <= w2n bw` by (irule body_full_local_region_lower_bound_mods >> metis_tac[]) >>
  `mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (simp[] >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `!j a cap. j <> id /\ local_region ce mid.scopes s j a cap ==>
      a+cap <= w2n bw+k \/ w2n bw+k+32 <= a` by
    (rpt gen_tac >> strip_tac >> irule pop_local_other_regions >>
     goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
     qexistsl_tac [`id`,`j`,`n`] >> simp[]) >>
  conj_tac >- suspend "state" >>
  conj_tac
  >- (irule pop_local_linked_immutable >>
      goal_assum (drule_at (Pat `immutable_frame_mods func ce cx mid s`)) >>
      goal_assum (drule_at (Pat `u.vs_memory = _`)) >>
      goal_assum (drule_at (Pat `local_region ce mid.scopes s id (w2n bw) n`)) >>
      simp[] >> qpat_assum `ef = mid with scopes := _`
        (mp_tac o Q.AP_TERM `(\e:evaluation_state. e.immutables)`) >> simp[]) >>
  conj_tac
  >- (qpat_assum `ef = mid with scopes := _` (once_rewrite_tac o single) >>
      simp[storage_well_formed_on_scopes]) >>
  conj_tac >- suspend "wb" >>
  conj_tac >- suspend "ghost" >>
  irule ghost_kept_at_clean_suffix >> goal_assum (drule_at Any) >>
  simp[SUBSET_DEF, loweringShapeDefsTheory.not_fresh_at_mono] >>
  metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
QED

Resume pop_local_write_frame_mods[state]:
  irule pop_local_state >> reverse conj_tac
  >- (goal_assum (drule_at (Pat `stmt_state_rel H ctx func ce cx mid s`)) >>
      goal_assum (drule_at (Pat `u.vs_memory = _`)) >>
      goal_assum (drule_at (Pat `local_region ce mid.scopes s id (w2n bw) n`)) >>
      simp[] >> rpt strip_tac >> metis_tac[local_ptrs_reserved_imm_base]) >>
  irule local_ptrs_rel_write_local >>
  goal_assum (drule_at (Pat `lookup_scopes id ef.scopes = _`)) >>
  goal_assum (drule_at (Pat `lookup_var root s = SOME bw`)) >>
  simp[] >>
  `local_backed func root s (w2n bw) n /\ w2n bw+n <= s.vs_alloca_next /\
   type_memory_size entry.type <= n` by
    (drule_all nameLoweringPropsTheory.local_ptrs_rel_value >> simp[eval_operand_def]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> sym_tac >> irule mstore_mem_bytes_at_disjoint >>
      qpat_assum `!j a cap. _ ==> _ <= _ \/ _ <= _` (drule_all_then mp_tac) >>
      decide_tac) >>
  conj_tac >- (rpt strip_tac >> fs[local_ptrs_rel_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> gvs[]) >>
  conj_tac >- simp[valueEncodingTypingTheory.value_has_type_val_wf] >>
  irule val_in_memory_memory_value_rel >> simp[] >>
  qpat_assum `!m. mem_agree_outside _ _ m ==> _`
    (qspec_then `u.vs_memory` mp_tac) >> simp[mem_agree_outside_def]
QED

Resume pop_local_write_frame_mods[wb]:
  `wb_frame ce mid ef sm s u` by
    (irule pop_path_wb_frame >>
     conj_tac >- (rpt strip_tac >> metis_tac[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
     goal_assum (drule_at (Pat `lookup_scopes id mid.scopes = _`)) >>
     goal_assum (drule_at (Pat `lookup_scopes id ef.scopes = _`)) >>
     goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
     goal_assum (drule_at (Pat `evaluate_subscripts _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `snapshot_in _ _ _ _ _`)) >>
     qexists_tac `wd` >> simp[ADD_COMM]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by fs[wb_frame_def, locals_kept_def] >>
  irule exprSimWordArgsTheory.wb_frame_trans >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (goal_assum (drule_at (Pat `wb_frame ce es mid sa s0 s`)) >>
      simp[]) >>
  goal_assum (drule_at (Pat `stmt_state_rel H ctx func ce cx es s0`))
QED

Resume pop_local_write_frame_mods[ghost]:
  irule pop_local_ghost >>
  goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  goal_assum (drule_at (Pat `u.vs_memory = _`)) >>
  goal_assum (drule_at (Pat `lookup_scopes id ef.scopes = _`)) >>
  goal_assum (drule_at (Pat `lookup_scopes id mid.scopes = _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP ce.ce_vars id = _`)) >>
  goal_assum (drule_at (Pat `ghost_inv_at_mods (DF H) lo d ce cx mid G tn s`)) >>
  qexistsl_tac [`entry`,`sm`] >> fs[AC ADD_ASSOC ADD_COMM] >>
  first_assum ACCEPT_TAC
QED

Finalise pop_local_write_frame_mods
