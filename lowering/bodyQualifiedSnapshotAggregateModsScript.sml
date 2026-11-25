(* Successful suffix of a forced, nonword qualified Assign snapshot. *)
Theory bodyQualifiedSnapshotAggregateMods
Ancestors
  bodyQualifiedPlaceRhsPostMods bodyQualifiedSnapshotStoreEntryMods
  bodyQualifiedSnapshotStoreEffectMods bodyQualifiedSnapshotFreshFrameMods
  bodyWriteSubscriptSourceMods bodyFullIfExpReach gasOriginPtrLabels fragGasPath
  exprLoweringProps stateRelProj valueEncodingTyping vyperStorageTrace
  vyperStorageFootprint vyperState vyperInterpreter words freshWrites
  bodyFullShadowBodyInv exprSimProps venomState typedMemoryCopy typedCopyOriginPtrBase
  fragGasOriginPtr

Theorem qualified_place_snapshot_aggregate_suffix_mods:
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type cenv e) /\
  type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256) /\
  assign_place_rhs_code_mods cenv bt e sa = (SOME vv,sr) /\
  assign_place_rhs_code_mods (gas_shadow_env T cenv) (gas_shadow_target bt)
    (gas_shadow_expr e) shadow_sa = (SOME vv,shadow_sr) /\
  gas_shadow_state sr shadow_sr /\ expr_can_mutate cenv (target_to_expr bt) /\
  compile_expr cenv (expr_type e) e sa = (raw,sm) /\
  compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) raw) sm = (vv,sr) /\
  fn_has_code sm sr func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ return_buf_frame d cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst t. frag_reachable ctx func s0 fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!tail. eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL pv,mid with gas_obs := tail)) /\
  mid.gas_obs = [] /\ read_result cx pv mid = (INL v,mid) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) marks (OK s,G,tn) /\
    vv_post_mods H ctx func cenv cx e es sa sm s0 mid pv raw s /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) mid pv raw s /\
  ptr_vv_ok cx (post_value_type cenv e) pv raw mid G tn s /\
  (!tag op. raw = StackValue tag op /\ ~is_word_type (post_value_type cenv e) ==>
     ptr_buf_ok cenv e op G s) /\
  (!tag p. raw = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location raw = SOME LocCode ==>
    ?v'. read_result cx pv mid = (INL v',mid) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand raw) s = SOME w ==>
           w2n w + type_memory_size rt <= lo /\
           (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
              val_in_memory rt v' (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u Gu tu. !H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu) /\
    qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
      es sa shadow_sa sr shadow_sr (SOME vv) s0 G0 tn0 H v mid Gu tu u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `gs = gas_explicit marks s0.vs_gas_readings` >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := gs) = (INL pv,mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn upd =>
       qpat_assum `!tail. eval_expr cx e (es with gas_obs := gs ++ tail) =
                            (INL pv,mid with gas_obs := tail)`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL,upd])))) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid)` by
    simp[Once bind_def] >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := gs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` irule >>
     `valid_horizon cx st0 H (es with gas_obs := gs).storage_trace` suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:eval_result``] valid_horizon_frame) >>
     qexistsl_tac [`eval_expr cx e`,`INL pv`,`mid`] >>
     simp[cj 5 evaluate_storage_trace_frame]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `~s.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then (strip_assume_tac o cj 1)) >>
     drule_then assume_tac gas_origin_ptr_path_erase >>
     drule_then (ACCEPT_TAC o cj 1) gas_path_normal) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    vv_post_mods H ctx func cenv cx e es sa sm s0 mid pv raw s /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
  suspend "store_input"
QED

Resume qualified_place_snapshot_aggregate_suffix_mods[store_input]:
  drule_all qualified_snapshot_store_entry_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`p`,`dw`,`src`,`sw`,`su`,`z`,`Gz`,`tz`,`rt`]
      (map_every assume_tac o CONJUNCTS))) >>
  suspend "store"
QED

Resume qualified_place_snapshot_aggregate_suffix_mods[store]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ z /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ z`
    (mp_then Any (assume_tac o cj 2) stmt_state_rel_local_ptrs_alloca) >>
  `z.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ z`
       (mp_then Any assume_tac stmt_state_rel_alloca_room) >>
     drule_then ACCEPT_TAC alloca_room_next_lt) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ lo d cenv cx mid Gz tz z`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `0 < type_memory_size rt ==> ?x w. src = Var x /\ not_fresh_at su x /\
      lookup_var x z = SOME w /\ ptr_covers Gz tz x z (type_memory_size rt) /\
      w2n w + val_store_size rt v <= z.vs_alloca_next /\
      (!m. mem_agree_outside tz.t_mem z.vs_memory m ==> val_in_memory rt v (w2n w) m)` by
    (disch_tac >>
     qpat_assum `0 < type_memory_size rt ==> _` (drule_then strip_assume_tac) >>
     qexistsl_tac [`x`,`sw`] >>
     `val_store_size rt v <= type_memory_size rt` by simp[val_store_size_le] >>
     fs[eval_operand_def] >> decide_tac) >>
  `lookup_var p z = SOME (n2w (w2n dw))` by simp[] >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`cap` |-> `type_memory_size rt`] qualified_snapshot_same_type_store_mods)) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "store_frame"
QED

Resume qualified_place_snapshot_aggregate_suffix_mods[store_frame]:
  `sm.cs_next_id < sr.cs_next_id` by decide_tac >>
  `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at su x` by
    (rpt strip_tac >> irule local_ptrs_reserved_imm_base >> qexists `cenv` >> simp[]) >>
  `!x. not_fresh_at su x ==>
     FLOOKUP Gu x = FLOOKUP Gz x /\ op_taint tu (Var x) = op_taint tz (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at su x ==> lookup_var x u = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  `!i. ~(w2n dw <= i /\ i < w2n dw + val_store_size rt v) ==>
     (i IN tu.t_mem <=> i IN tz.t_mem)` by
    (gen_tac >> disch_tac >> first_x_assum irule >> fs[DE_MORGAN_THM]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) qualified_snapshot_fresh_store_frame_mods >>
  `u.vs_alloca_next = z.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ z u`
       (mp_tac o AP_TERM ``\s. s.vs_alloca_next`` o CONJUNCT1 o
        REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (drule_then (fn th => simp[th]) typed_copy_state_frame_allocas_below_fmp) >>
  `local_ptrs_reserved cenv sr` by
    (irule local_ptrs_reserved_next_var >> qexists `su` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `su` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `su` >> simp[]) >>
  suspend "post"
QED

Resume qualified_place_snapshot_aggregate_suffix_mods[post]:
  qexistsl_tac [`u`,`Gu`,`tu`] >> gen_tac >> disch_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ (z,Gz,tz) [] _` (qspec_then `DF H` assume_tac) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] _`
       (qspec_then `DF H` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
     simp[NoAsms] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` (drule_then (assume_tac o CONJUNCT1))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) marks (OK u,Gu,tu)` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks _`
       (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`s`,`G`,`tn`,`[]`] mp_tac) >>
     simp[NoAsms] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  `!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK u,Gu,tu)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     disch_then (fn th => rpt gen_tac >> disch_tac >>
       qspecl_then [`fn`,`inst`,`t`] mp_tac th) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
    (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  simp[qualified_place_rhs_post_mods_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`p`,`sm.cs_next_id`,`w2n dw`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Finalise qualified_place_snapshot_aggregate_suffix_mods
