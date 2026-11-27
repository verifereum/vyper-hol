(* Final-store restoration starts after any allocating normalization. *)
Theory immutableDeployAssignRestore
Ancestors
  immutableDeployAssignStateFrame immutableDeployAssignMemoryFrame
  immutableDeployAssignSourceFrame immutableDeployAssignFacts
  exprLoweringProps exprSimHypsDefs compileEnv loweringStateRelDefs vyperPlaceFrames vyperState
  venomState finite_map alist valueEncodingProps vyperTypeInvariants placeMemoryPathRebuild
  exprSimSubscriptArrayLiveImmutableView vyperTypeInitialState loweringPosts
  bodyInvSplit supportedNameRoot gasContext list

(* The legacy expression invariant can expose an inactive bare global
   only as a constant. An immutable layout cannot allocate such a cell. *)
Theorem immutable_store_layout_active:
  expr_sim_inv ce cx env es /\
  immutable_section_layout_mods ce.ce_modules ce /\
  FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) ==>
  src = ce.ce_module
Proof
  strip_tac >> spose_not_then assume_tac >>
  `bare_globals_layout ce.ce_is_ctor ce.ce_module_var_type ce.ce_module_vars
     ce.ce_modules cx env.bare_globals env.bare_global_assignable` by
    fs[expr_sim_inv_def] >>
  `?ty. FLOOKUP env.bare_globals (src,name) = SOME ty` by
    metis_tac[bare_globals_layout_def] >>
  `cx_const_name cx (src,name)` by (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `?tops vis ty slot.
    ALOOKUP ce.ce_modules src = SOME tops /\
    MEM (VariableDecl vis Immutable name ty slot) tops` by
    (fs[immutable_section_layout_mods_def, immutable_region_mods_def] >>
     metis_tac[MEM_APPEND, MEM]) >>
  `get_module_code cx src = SOME tops /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops))` by
    metis_tac[bare_globals_layout_def] >>
  `src = NONE /\ cx_tops cx = tops` by
    (fs[cx_const_name_def] >> metis_tac[cx_tops_module]) >>
  gvs[cx_const_name_def] >>
  drule_then (drule_then strip_assume_tac)
    distinct_module_consts_env_names_constant >>
  drule_all_then assume_tac (SPEC_ALL supported_variable_decl_distinct_mem) >>
  fs[]
QED

Theorem immutable_store_stmt_state_rel_frame[local]:
  stmt_state_rel H ctx func ce cx es s /\ expr_sim_inv ce cx env es /\
  immutable_section_layout_mods ce.ce_modules ce /\
  local_ptrs_reserved ce sa /\ ce.ce_is_ctor /\ src = ce.ce_module /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  FLOOKUP ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  write_place cx (ImmutablePlace src id path) v es = (INL (),es') /\
  immutables_rel ce cx.txn.target src T es' q /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
  LENGTH s.vs_memory <= LENGTH q.vs_memory /\
  (!a k. regions_disjoint a k off (type_memory_size tv) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  stmt_state_rel H ctx func ce cx es' q
Proof
  strip_tac >> gvs[] >>
  `q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
   q.vs_fmp = s.vs_fmp /\ q.vs_initial_fmp = s.vs_initial_fmp /\
   q.vs_labels = s.vs_labels /\
   q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
   q.vs_call_ctx = s.vs_call_ctx /\ q.vs_tx_ctx = s.vs_tx_ctx /\
   q.vs_block_ctx = s.vs_block_ctx /\ q.vs_logs = s.vs_logs /\
   q.vs_outcomes = s.vs_outcomes /\ q.vs_requests = s.vs_requests /\
   q.vs_pending_deletions = s.vs_pending_deletions /\ q.vs_code = s.vs_code` by
    (qpat_x_assum `_ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `?imms. es' = es with immutables := imms` by
    (drule write_immutable_place_frame >> simp[]) >>
  `?mods old. ALOOKUP es.immutables cx.txn.target = SOME mods /\
    FLOOKUP (get_source_immutables ce.ce_module mods) id = SOME (tv,old)` by
    (drule_all immutable_assign_source_lookup >> simp[]) >>
  `ce.ce_module_var_type (ce.ce_module,id) = SOME ty` by
    (fs[expr_sim_inv_def, bare_globals_layout_def]) >>
  `local_ptrs_rel func ce es.scopes s /\
   immutable_decl_sep ce cx es.scopes s.vs_vars s.vs_allocas s.vs_alloca_next /\
   immutable_alloca_sep func ce cx es s /\ immutable_base_zero ce s /\
   immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es s` by
    (fs[stmt_state_rel_def, state_rel_def, immutable_alloca_sep_def] >>
     first_assum ACCEPT_TAC) >>
  `local_ptrs_rel func ce es'.scopes q` by
    (gvs[] >> irule immutable_store_local_ptrs_frame >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `immutable_alloca_sep func ce cx es' q` by
    (drule_all immutable_path_store_alloca_sep_frame >> simp[]) >>
  `immutable_base_zero ce q` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!src name off. src <> ce.ce_module ==>
     FLOOKUP ce.ce_module_vars (src,name) <> SOME (ImmutableLoc off)` by
    metis_tac[immutable_store_layout_active] >>
  `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==>
     immutable_alloca_sep func (ce with ce_module := src) cx es' q` by
    (rpt strip_tac >> Cases_on `src = ce.ce_module`
     >- gvs[compile_env_component_equality] >>
     simp[immutable_alloca_sep_def, immutable_decl_sep_alt] >>
     metis_tac[]) >>
  `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==>
     immutables_rel ce cx.txn.target src T es' q` by
    (rpt strip_tac >> Cases_on `src = ce.ce_module`
     >- gvs[] >> simp[immutables_rel_def] >> metis_tac[]) >>
  irule stmt_state_rel_allocas_frame >> simp[] >>
  reverse conj_tac >- (qexistsl_tac [`es`, `s`] >> simp[]) >>
  gvs[state_rel_def, stmt_state_rel_def, storage_rel_def, transient_rel_def,
      accounts_rel_def, logs_rel_def, contract_storage_def, contract_transient_def]
QED

Theorem immutable_store_stmt_state_rel:
  stmt_state_rel H ctx func ce cx es s /\ expr_sim_inv ce cx env es /\
  immutable_section_layout_mods ce.ce_modules ce /\
  local_ptrs_reserved ce sa /\ ce.ce_is_ctor /\ src = ce.ce_module /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  FLOOKUP ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  write_place cx (ImmutablePlace src id []) v es = (INL (),es') /\
  immutable_value_admissible tv v /\ val_in_memory tv v off q.vs_memory /\
  immutable_value_bytes_rel tv v
    (mem_bytes_at off (type_memory_size tv) q.vs_memory) /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
  LENGTH s.vs_memory <= LENGTH q.vs_memory /\
  (!a k. regions_disjoint a k off (type_memory_size tv) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  stmt_state_rel H ctx func ce cx es' q
Proof
  strip_tac >> gvs[] >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es s` by
    fs[stmt_state_rel_def,state_rel_def] >>
  `immutables_rel ce cx.txn.target ce.ce_module T es' q` by
    (qpat_assum `ce.ce_is_ctor` (fn th => once_rewrite_tac [GSYM (EQT_INTRO th)]) >>
     drule_all immutable_store_immutables_frame >> simp[]) >>
  irule immutable_store_stmt_state_rel_frame >>
  rpt (CHANGED_TAC (first_assum (irule_at Any))) >> simp[]
QED

Theorem immutable_ctor_relation_memory[local]:
  s.vs_memory = q.vs_memory ==>
  (immutables_rel ce addr src T es s <=> immutables_rel ce addr src T es q)
Proof
  simp[immutables_rel_def]
QED

Theorem immutable_path_store_stmt_state_rel:
  stmt_state_rel H ctx func ce cx es s /\ expr_sim_inv ce cx env es /\
  immutable_section_layout_mods ce.ce_modules ce /\
  local_ptrs_reserved ce sa /\ ce.ce_is_ctor /\ src = ce.ce_module /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  FLOOKUP ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) ty = SOME itv /\
  mem_path_offset itv path = SOME (k,ptv) /\
  write_place cx (ImmutablePlace src id path) v es = (INL (),es') /\
  value_has_type ptv v /\ val_in_memory ptv v (off+k) q.vs_memory /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
  LENGTH s.vs_memory <= LENGTH q.vs_memory /\
  (!b n. regions_disjoint b n (off+k) (type_memory_size ptv) ==>
    mem_bytes_at b n q.vs_memory = mem_bytes_at b n s.vs_memory) ==>
  stmt_state_rel H ctx func ce cx es' q
Proof
  strip_tac >> gvs[] >>
  `?imms old. ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables ce.ce_module imms) id = SOME (itv,old)` by
    (drule_all immutable_assign_source_lookup >> simp[]) >>
  `value_has_type itv old /\ well_formed_type_value itv` by
    (qspecl_then [`ce`,`cx`,`env`,`es`,`ce.ce_module`,`id`,
      `[]`,`itv`,`old`,`0`,`itv`,`old`] mp_tac
      exprSimSubscriptArrayLiveImmutableViewTheory.imm_place_at_value_type >>
     simp[mem_path_offset_def,evaluate_subscripts_def]) >>
  drule_then strip_assume_tac exprSimPropsTheory.mem_path_offset_sound >>
  `immutables_rel ce cx.txn.target ce.ce_module T es s` by
    fs[stmt_state_rel_def,state_rel_def] >>
  `!name at ot ov.
     name <> id /\
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc at) /\
     FLOOKUP (get_source_immutables ce.ce_module imms) name = SOME (ot,ov) ==>
     regions_disjoint at (type_memory_size ot) off (type_memory_size itv)` by
    suspend "disjoint" >>
  `!b n. regions_disjoint b n off (type_memory_size itv) ==>
    regions_disjoint b n (off+k) (type_memory_size ptv)` by
    (simp[regions_disjoint_def] >> decide_tac) >>
  `immutables_rel ce cx.txn.target ce.ce_module T es' (s with vs_memory := q.vs_memory)` by
    (MATCH_MP_TAC (Q.INST [`cx` |-> `cx`,`id` |-> `id`,
       `off` |-> `off`,`itv` |-> `itv`,`ptv` |-> `ptv`,`path` |-> `path`,
       `k` |-> `k`,`v` |-> `v`,`imms` |-> `imms`,`old` |-> `old`,
       `src` |-> `ce.ce_module`,`s` |-> `s`,`es` |-> `es`]
       immutable_path_write_immutables_rel) >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `immutables_rel ce cx.txn.target ce.ce_module T es' q` by
    (mp_tac (Q.INST [`s` |-> `s with vs_memory := q.vs_memory`,
       `q` |-> `q`,`ce` |-> `ce`,`addr` |-> `cx.txn.target`,
       `src` |-> `ce.ce_module`,`es` |-> `es'`] immutable_ctor_relation_memory) >>
     (impl_tac >- simp[]) >> strip_tac >>
     first_x_assum (irule o iffLR) >> first_assum ACCEPT_TAC) >>
  `!a n. regions_disjoint a n off (type_memory_size itv) ==>
    mem_bytes_at a n q.vs_memory = mem_bytes_at a n s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!b n. regions_disjoint b n (k+off) (type_memory_size ptv) ==> _` irule >>
     fs[regions_disjoint_def] >> decide_tac) >>
  MATCH_MP_TAC (Q.INST [`env` |-> `env`,`es` |-> `es`,`id` |-> `id`,
    `off` |-> `off`,`path` |-> `path`,`s` |-> `s`,`sa` |-> `sa`,
    `ty` |-> `ty`,`tv` |-> `itv`,`v` |-> `v`,`src` |-> `ce.ce_module`]
    immutable_store_stmt_state_rel_frame) >> simp[]
QED

Resume immutable_path_store_stmt_state_rel[disjoint]:
  rpt strip_tac >>
  `bare_globals_layout ce.ce_is_ctor ce.ce_module_var_type ce.ce_module_vars
     ce.ce_modules cx env.bare_globals env.bare_global_assignable /\
     env_immutables_consistent env cx es` by fs[expr_sim_inv_def,env_consistent_def] >>
  `?ty'. FLOOKUP env.bare_globals (ce.ce_module,name) = SOME ty'` by
    metis_tac[bare_globals_layout_def] >>
  `evaluate_type (get_tenv cx) ty' = SOME ot` by
    (qpat_assum `env_immutables_consistent env cx es` mp_tac >>
     qpat_assum `ALOOKUP es.immutables cx.txn.target = SOME imms`
       (fn th => rewrite_tac[env_immutables_consistent_def,th]) >>
     simp[] >> strip_tac >>
     qpat_assum `!src id ty tv v. _ /\ _ ==> evaluate_type _ _ = SOME _`
       (qspecl_then [`ce.ce_module`,`name`,`ty'`,`ot`,`ov`] mp_tac) >>
     simp[]) >>
  fs[bare_globals_layout_def] >>
  qpat_x_assum `!src id1 id2 ty1 ty2 off1 off2 tv1 tv2. _`
    (drule_all_then mp_tac) >> simp[]
QED

Finalise immutable_path_store_stmt_state_rel
