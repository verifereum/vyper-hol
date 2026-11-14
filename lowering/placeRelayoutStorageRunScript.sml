Theory placeRelayoutStorageRun
Ancestors
  placeStore placeDestinationBounds placeRelayoutSource allocaSiteResource
  exprSimHypsDefs exprLoweringProps stmtSimDefs loweringPosts allocLimits
  vyperTypeArgFits vyperTypeSystem venomMemDefs
  placeRelayoutNormalizeFrame placeStoreSlots
  placeStoreStorage freshWrites stmtLoweringMono vyperScopePreservation
  loweringHalt fragExec typedMemoryCopy exprSimTypedAlloc compileEnv loweringStateRelDefs venomState
  vyperValue tuplePlaceValueStorageFrame vyperStorageFootprint
Libs monadsyntax horizonTypeLib

Theorem place_relayout_storage_run:
  !cx st0 ctx func cenv env ee ff s p w loc dst op src_loc dty sty stv v sa sb
   cfn bt e sc sd sw.
    compile_assign_value cenv dst loc op (is_word_type dty) src_loc dty sty
      (type_memory_bytes cenv dty) sa = ((),sb) /\
    compile_get_target_ptr cfn cenv bt sc = ((dst,SOME loc,SOME (ValPT dty)),sd) /\
    (loc = LocStorage \/ loc = LocTransient) /\
    assign_alloc_ok cenv bt e /\ lowered_value_type cenv e = sty /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    eval_operand dst s = SOME w /\ eval_operand op s = SOME sw /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\ assignable_type (get_tenv cx) sty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    ~is_word_type sty /\ expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
       b <= w2n sw /\ w2n sw + type_memory_size stv <= b + sz) /\
    expr_sim_inv cenv cx env ee /\ acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\
    (?H. valid_horizon cx st0 H ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee s /\ storage_place_observed H p /\
      regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H)) /\
    write_place cx p v ee = (INL (),ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==>
          stmt_state_rel H ctx func cenv cx ff t) /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_frame cenv ee sa s cenv ff t
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon _ _ H _`
    (qx_choose_then `H` assume_tac) >>
  `stmt_state_rel H ctx func cenv cx ee s /\ storage_place_observed H p /\
    regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H)` by
    metis_tac[] >> pop_assum strip_assume_tac >>
  `loc <> LocMemory` by (Cases_on `loc` >> gvs[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  first_x_assum (qx_choosel_then [`aid0`,`off0`,`len0`] strip_assume_tac) >>
  `!sw. eval_operand op s = SOME sw ==>
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
       w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw` by
    (qx_gen_tac `sw'` >> disch_tac >>
     `sw' = sw` by gvs[] >> pop_assum SUBST_ALL_TAC >>
     conj_tac
     >- (drule_all alloca_site_registered_below >> decide_tac) >>
     map_every qx_gen_tac [`aid1`,`off1`,`len1`] >> strip_tac >>
     `aid0 <> aid1` by decide_tac >>
     `off0 + len0 <= off1 \/ off1 + len1 <= off0` by
       metis_tac[alloca_inv_def, allocas_non_overlapping_def] >> decide_tac) >>
  `!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==> 0 < type_slot_size dtv` by
    metis_tac[type_widens_to_assignable_type, assignable_type_slot_size_pos] >>
  `loc <> LocMemory /\ dty <> sty /\
    ~(is_bytestring_type dty /\ is_bytestring_type sty) ==> type_alloc_ok cenv dty` by
    (strip_tac >> simp[type_alloc_ok_def] >>
     drule storage_target_normalization_bound >> simp[] >>
     disch_then drule >> metis_tac[]) >>
  `type_alloc_ok cenv dty` by metis_tac[] >>
  drule_all place_store_destination_alloc_bound >> strip_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `val_in_memory stv v (w2n sw) s.vs_memory` by
    (gvs[expr_val_rel_def]) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (`s.vs_alloca_next < dimword (:256)` by
      (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
     first_x_assum (qspec_then `sw` mp_tac) >> simp[] >> decide_tac) >>
  `!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (Cases_on `p` >> fs[place_ptr_rel_def]) >>
  qpat_assum `!sw. eval_operand op s = SOME sw ==> _`
    (qspec_then `sw` mp_tac) >> simp[] >> strip_tac >>
  qspecl_then [`H`, `ctx`, `func`, `cenv`, `cx`, `env`, `ee`, `ff`, `s`, `p`,
    `w`, `loc`, `dst`, `op`, `src_loc`, `dty`, `sty`, `stv`, `v`, `sa`, `sb`]
    mp_tac tuple_place_value_storage_run_frame >>
  (impl_tac >- (simp[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists_tac `t` >> simp[] >>
  irule (horizonTypeLib.at_horizon_named "H" alloca_frame_of_mem_frame) >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len a n. _`
        (qspecl_then [`aid`, `off`, `sz`, `off`, `sz`] mp_tac) >> simp[])
  >- metis_tac[write_place_scopes_dom]
  >> qexistsl_tac [`H`, `ctx`, `cx`, `func`] >> first_assum ACCEPT_TAC
QED
