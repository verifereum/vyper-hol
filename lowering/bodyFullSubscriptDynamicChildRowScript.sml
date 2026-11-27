(* The in-range child is read from the covered local row at the index cut.
   The represented parent fixes coordinates, not which owner serves the read. *)
Theory bodyFullSubscriptDynamicChildRow
Ancestors
  bodyFullSubscriptLocalCutOrigin bodyFullSubscriptCoveredRow stateRelProj
  abiEncodeArgsSim abiDecodeStaticProps exprBopSimProps exprLoweringProps
  typedMemoryCopy vyperTypeValues vyperTypeStatePreservation
  vyperTypeEvalProofs vyperPlaceTyping vyperStorageFootprint
  vyperPlaceResultTyping exprSimHypsDefs exprSimProps loweringPosts
  loweringStateRelDefs arithmetic words

Theorem subscript_dynamic_child_input:
  expr_body_pre_mods mods ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et (Dynamic cap) /\
  eval_expr cx obj (es with gas_obs := gs1) =
    (INL (PlaceR (MemoryPlace id path)),mid) /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs2) =
    (INL (IntV i),fin) /\
  storage_trace_domain cx st0 fin.storage_trace /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gm tnm /\
  ghost_kept_at lo ce mid sm Gm tnm s Gi tni /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx fn ce cx es s0 /\
    ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0 /\
    vv_post H ctx fn ce cx obj es sa sm s0 mid (PlaceR (MemoryPlace id path)) bvv s /\
    expr_post H ctx fn ce cx idx mid sm sn s fin (IntV i) iop u /\
    ghost_inv_at (DF H) lo d ce cx fin Gi tni u) /\
  lookup_scopes id fin.scopes = SOME entry /\
  runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV tv (Dynamic cap)) /\
  read_result cx (PlaceR (MemoryPlace id path)) fin = (INL (ArrayV (DynArrayV vs)),fin) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  place_ptr_rel ce cx u (PlaceR (MemoryPlace id path)) a (SOME LocMemory)
    (Type (ArrayT et (Dynamic cap))) /\
  0 <= i /\ Num i < LENGTH vs ==>
  ?v root ssz base rt k.
    read_result cx (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))) fin =
      (INL v,fin) /\ value_has_type tv v /\
    (!m. mem_agree_outside tni.t_mem u.vs_memory m ==>
      val_in_memory tv v (w2n a + 32 + Num i * type_memory_size tv) m) /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) ssz) /\
    lookup_var root u = SOME base /\
    ce.ce_var_type id = SOME rt /\ evaluate_type (get_tenv cx) rt = SOME entry.type /\
    mem_path_offset entry.type (path ++ [ValueSubscript (IntV i)]) = SOME (k,tv) /\
    w2n a + 32 + Num i * type_memory_size tv = w2n base + k /\
    k + type_memory_size tv <= ssz
Proof
  strip_tac >>
  drule_all subscript_local_cut_returned_paths >> strip_tac >>
  qpat_x_assum `!cap etv vs i. _`
    (qspecl_then [`cap`, `tv`, `vs`, `i`] mp_tac) >> simp[] >> strip_tac >>
  `?events. entry_pop_trace initial events entry /\ entry_pop_trace_valid events` by
    (qpat_assum `typed_scope_transition es fin` (strip_assume_tac o REWRITE_RULE [typed_scope_transition_def]) >>
     drule_all scope_pop_trace_lookup >> strip_tac >> gvs[] >>
     goal_assum (drule_at Any) >> irule entry_events_valid >> simp[]) >>
  drule entry_pop_trace_metadata >> strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  drule_all abi_args_local_type_coherent >> strip_tac >>
  `well_formed_type_value initial.type /\ value_has_type initial.type initial.value /\
   value_has_type entry.type entry.value` by
    metis_tac[evaluate_type_well_formed_type_value, lookup_scopes_state_well_typed_value_has_type] >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  qhdtm_x_assum `vv_post` (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  qhdtm_x_assum `expr_post` (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `popped_kept ce es fin s0 u` by
    (drule_all locals_kept_trans >> simp[locals_kept_def]) >>
  qhdtm_x_assum `place_ptr_rel`
    (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >>
  rename [`FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) ssz)`,
          `lookup_var root u = SOME roww`, `a = roww + n2w j`,
          `mem_path_offset tv0 path = SOME (j,_)`] >>
  `tv0 = entry.type` by metis_tac[optionTheory.SOME_11] >>
  `mem_path_offset entry.type path = SOME (j,ArrayTV tv (Dynamic cap))` by
    (drule mem_path_offset_sound >>
     fs[runtime_place_typed_memory] >> metis_tac[optionTheory.SOME_11]) >>
  `?B. lookup_var root s0 = SOME B /\ type_memory_size initial.type <= ssz` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s0`
       (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
     qpat_x_assum `local_ptrs_rel _ _ _ s0`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
     disch_then (qspecl_then [`id`, `initial`, `root`, `ssz`] mp_tac) >> simp[] >> metis_tac[]) >>
  `not_fresh_at sa root /\ not_fresh_at sm root` by
    (conj_tac
     >- (qpat_assum `local_ptrs_reserved ce sa`
           (drule o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [local_ptrs_reserved_def]) >> simp[]) >>
     qpat_assum `local_ptrs_reserved ce sm`
       (drule o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [local_ptrs_reserved_def]) >> simp[]) >>
  `lookup_var root s = SOME roww /\ lookup_var root s0 = SOME roww` by
    (`lookup_var root s = SOME B` by
       (qpat_assum `!x w. not_fresh_at sa x /\ _ ==> _` drule_all >> simp[]) >>
     `lookup_var root u = SOME B` by
       (qpat_assum `!x w. not_fresh_at sm x /\ _ ==> _` drule_all >> simp[]) >>
     fs[]) >>
  `local_region ce mid.scopes s id (w2n roww) ssz` by
    (`IS_SOME (lookup_scopes id mid.scopes)` by
       (irule vyperTypeEnvPreservationTheory.lookup_scopes_same_fdoms_some >>
        qexistsl [`initial`, `es.scopes`] >> fs[locals_kept_def]) >>
     fs[local_region_def, optionTheory.IS_SOME_EXISTS]) >>
  `w2n roww + ssz <= u.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ fin u`
       (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
     qpat_x_assum `local_ptrs_rel _ _ _ u`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
     disch_then (qspecl_then [`id`, `entry`, `root`, `ssz`] mp_tac) >> simp[]) >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_alloca_room, alloca_room_next_lt] >>
  `type_memory_size entry.type <= ssz` by simp[] >>
  `w2n a = w2n roww + j` by
    (qpat_assum `mem_path_offset entry.type path = _`
       (mp_then Any strip_assume_tac mem_path_offset_sound) >>
     qpat_assum `a = roww + n2w j` SUBST1_TAC >>
     irule w2n_add_n2w_lt >> decide_tac) >>
  `Num i < cap` by
    (drule typed_copy_dynarray_typed_value >> simp[] >> decide_tac) >>
  qabbrev_tac `child = path ++ [ValueSubscript (IntV i)]` >>
  qabbrev_tac `k = j + (32 + Num i * type_memory_size tv)` >>
  `mem_path_offset entry.type child = SOME (k,tv)` by
    (simp[Abbr `child`, Abbr `k`] >> irule mem_path_offset_snoc >>
     qexists `ArrayTV tv (Dynamic cap)` >> gvs[mem_step_offset_def]) >>
  `k + type_memory_size tv <= ssz` by
    (qpat_assum `mem_path_offset entry.type child = _` (mp_then Any strip_assume_tac mem_path_offset_sound) >>
     decide_tac) >>
  qabbrev_tac `child_addr = (n2w (w2n roww + k) : bytes32)` >>
  `w2n child_addr = w2n roww + k` by
    (simp[Abbr `child_addr`] >> irule LESS_MOD >> decide_tac) >>
  `?v. read_result cx (PlaceR (MemoryPlace id child)) fin = (INL v,fin) /\
       value_has_type tv v /\ well_formed_type_value tv /\ k + type_memory_size tv <= ssz /\
       !m. mem_agree_outside tni.t_mem u.vs_memory m ==> val_in_memory tv v (w2n child_addr) m` by
    (irule subscript_covered_row_read_robust >>
     qpat_assum `ghost_inv_at _ _ _ _ _ es G0 tn0 s0` (irule_at Any) >>
     qpat_assum `ghost_inv_at _ _ _ _ _ fin Gi tni u` (irule_at Any) >>
     qpat_assum `ghost_kept_at _ _ es _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ghost_kept_at _ _ mid _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `local_region ce mid.scopes s id _ ssz` (irule_at Any) >>
     qpat_assum `entry_pop_trace initial events entry` (irule_at Any) >>
     qpat_assum `lookup_var root u = SOME roww` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `w2n a + (Num i * type_memory_size tv + 32) = k + w2n roww` by
    (qpat_assum `w2n a = w2n roww + j` SUBST1_TAC >>
     simp[NoAsms, Abbr `k`]) >>
  qexistsl [`v`, `root`, `ssz`, `roww`, `ty`, `k`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (qpat_assum `!m. mem_agree_outside _ _ m ==> val_in_memory _ _ (w2n child_addr) m` mp_tac >>
      qpat_assum `w2n child_addr = _` SUBST1_TAC >>
      qpat_assum `w2n a + (_ + 32) = _` SUBST1_TAC >> simp[NoAsms]) >>
  qpat_assum `entry.type = initial.type` SUBST1_TAC >> first_assum ACCEPT_TAC
QED
