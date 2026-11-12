Theory placeRelayoutStorageRun
Ancestors
  placeStore placeDestinationBounds placeRelayoutSource allocaSiteResource
  exprSimHypsDefs exprLoweringProps stmtSimDefs loweringPosts allocLimits
  vyperTypeArgFits vyperTypeSystem venomMemDefs
  placeRelayoutNormalizeFrame placeRelayoutStorageFrame placeStoreDynPrepare
  placeStoreStorage freshWrites stmtLoweringMono vyperScopePreservation
  loweringHalt fragExec typedMemoryCopy exprSimTypedAlloc compileEnv loweringStateRelDefs venomState
  vyperValue
Libs monadsyntax

Theorem place_relayout_storage_compile_cut[local]:
  compile_assign_value cenv dst loc op (is_word_type dty) src_loc dty sty
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et + 31) DIV 32, type_memory_bytes cenv et)
     | _ => NONE) (type_memory_bytes cenv dty) sa = ((),sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  type_memory_bytes cenv dty = type_memory_size dtv ==>
  ?buf sm sn.
    compile_alloc_buffer (type_memory_bytes cenv dty) sa = (buf,sm) /\
    compile_store_memory_typed cenv buf.buf_operand dty op sty sm = ((),sn) /\
    ((?et n. dty = ArrayT et (Dynamic n) /\
       compile_dynarray_to_storage buf.buf_operand dst
         ((type_memory_bytes cenv et + 31) DIV 32) (type_memory_bytes cenv et)
         (loc = LocTransient) sn = ((),sb)) \/
     ((!et n. dty <> ArrayT et (Dynamic n)) /\
      (if type_memory_size dtv <= 32 then
        ?loaded sd. emit_op MLOAD [buf.buf_operand] sn = (loaded,sd) /\
          emit_void (if loc = LocTransient then TSTORE else SSTORE) [dst;loaded] sd = ((),sb)
       else ?r. (if loc = LocTransient then compile_memory_to_transient else compile_memory_to_storage)
         buf.buf_operand dst (type_memory_size dtv DIV 32) sn = (r,sb))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `?et n. dty = ArrayT et (Dynamic n)`
  >- (pop_assum strip_assume_tac >> gvs[is_word_type_def] >>
      drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)
        place_dyn_assign_compile_cut >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `(if _ then _ else _) sa = _` mp_tac >>
      simp[comp_bind_def, comp_return_def] >>
      Cases_on `compile_alloc_buffer (type_memory_size dtv) sa` >>
      rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
      Cases_on `compile_store_memory_typed cenv buf.buf_operand (ArrayT et (Dynamic n)) op sty sm` >>
      rename1 `compile_store_memory_typed _ _ _ _ _ _ = (unitv,sn)` >>
      Cases_on `unitv` >> simp[] >> strip_tac >> gvs[] >>
      qexistsl_tac [`buf`, `sm`, `sn`] >> simp[]) >>
  `!et n. dty <> ArrayT et (Dynamic n)` by metis_tac[] >>
  `loc = slot_loc (loc = LocTransient)` by (Cases_on `loc` >> gvs[slot_loc_def]) >>
  mp_tac (Q.INST [`tr` |-> `loc = LocTransient`, `src` |-> `op`]
    (SPEC_ALL place_store_storage_compile)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  qexistsl_tac [`a`, `sm`, `sc'`] >> simp[]
QED

Theorem place_relayout_storage_run:
  !ctx func cenv cx env ee ff s p w loc dst op src_loc dty sty stv v sa sb
   cfn bt e sc sd sw.
    compile_assign_value cenv dst loc op (is_word_type dty) src_loc dty sty
      (case dty of ArrayT et (Dynamic _) =>
         SOME ((type_memory_bytes cenv et + 31) DIV 32, type_memory_bytes cenv et)
       | _ => NONE) (type_memory_bytes cenv dty) sa = ((),sb) /\
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
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    stmt_state_rel ctx func cenv cx ee s /\ write_place cx p v ee = (INL (),ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_frame cenv ee sa s cenv ff t
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
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
  drule place_relayout_storage_compile_cut >>
  disch_then (qspec_then `dtv` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`a`, `sm`, `sn`] (map_every assume_tac o CONJUNCTS)) >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by (drule typed_return_store_mono >> simp[ci_mono_def]) >>
  `cs_extends sn sb` by
    (qpat_x_assum `(?et n. _ /\ _) \/ _` strip_assume_tac
     >- (mp_tac (cj 7 ci_mono_context_helpers) >>
         disch_then (qspecl_then [`a.buf_operand`, `dst`,
           `(type_memory_bytes cenv et + 31) DIV 32`, `type_memory_bytes cenv et`,
           `loc = LocTransient`, `sn`] mp_tac) >> simp[ci_mono_def]) >>
     Cases_on `type_memory_size dtv <= 32`
     >- (qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
         `cs_extends sn sd' /\ cs_extends sd' sb` by
           metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
         irule cs_extends_trans >> qexists_tac `sd'` >> simp[]) >>
     qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
     Cases_on `loc = LocTransient` >> gvs[] >>
     mp_tac (cj 1 ci_mono_context_helpers) >> mp_tac (cj 2 ci_mono_context_helpers) >>
     disch_then (qspecl_then [`a.buf_operand`, `dst`, `type_memory_size dtv DIV 32`, `sn`] mp_tac) >>
     simp[ci_mono_def] >> disch_then kall_tac >>
     disch_then (qspecl_then [`a.buf_operand`, `dst`, `type_memory_size dtv DIV 32`, `sn`] mp_tac) >>
     simp[ci_mono_def]) >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func /\ fn_has_code sa sm func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `compile_alloc_buffer (type_memory_bytes cenv dty) sa = (a,sm)` by simp[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv dty))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule entryArgPtrsTheory.entry_alloc_buffer_inst >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule place_normalize_framed_path >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ s`)) >>
  disch_then (drule_at (Pat `eval_operand _ s = _`)) >>
  disch_then (qspecl_then [`stv`, `dtv`, `v`] mp_tac) >>
  (impl_tac >- (simp[arithmeticTheory.ADD_COMM] >>
     conj_tac >- first_assum ACCEPT_TAC >> disj1_tac >>
     qexistsl_tac [`aid0`, `off0`, `len0`] >> simp[])) >>
  disch_then (qx_choosel_then [`u`, `uw`] strip_assume_tac) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule compile_alloc_buffer_emission >> strip_tac >> simp[]) >>
  `sm.cs_next_var <= sn.cs_next_var` by
    (drule typed_return_store_mono >> simp[ci_mono_def]) >>
  `sa.cs_next_var <= sn.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. a.buf_operand = Var x ==> not_fresh_at sm x` by
    (drule compile_alloc_buffer_emission >> strip_tac >> gvs[]) >>
  `!x. a.buf_operand = Var x \/ dst = Var x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  `u.vs_labels = s.vs_labels` by
    metis_tac[stmtSimAugAssignPlaceMemoryTheory.aug_place_marked_path_labels] >>
  `eval_operand dst u = SOME w` by
    (qspecl_then [`sa`, `s`, `u`, `dst`] mp_tac
       stmtSimReturnTheory.eval_operand_old_vars >> simp[]) >>
  `well_formed_type_value dtv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `?t. gas_marked_path F ctx func u 0 (OK t) /\
       stmt_state_rel ctx func cenv cx ff t /\
       (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x u) /\
       t.vs_memory = u.vs_memory /\ t.vs_allocas = u.vs_allocas /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qpat_x_assum `(?et n. _ /\ _) \/ _` strip_assume_tac
     >- suspend "dynamic_suffix"
     >> suspend "static_suffix") >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  `alloca_frame cenv ee sa s cenv ff t` by
    (irule alloca_frame_of_mem_frame >>
     `MAP FDOM ff.scopes = MAP FDOM ee.scopes` by
       metis_tac[write_place_scopes_dom] >>
     simp[] >> reverse conj_tac >- metis_tac[] >>
     rpt strip_tac >>
     `regions_disjoint (w2n uw) (type_memory_size dtv) off sz` by metis_tac[] >>
     fs[regions_disjoint_def]) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_0] >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Resume place_relayout_storage_run[static_suffix]:
  drule_all place_store_storage_destination >> strip_tac >>
  qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >> gvs[] >>
  drule_all place_store_storage_write_inv >> strip_tac >> gvs[] >>
  drule_all place_store_storage_leaf_bounds >> strip_tac >>
  `type_memory_size dtv = 32 * type_slot_size dtv` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  `n2w (w2n root + delta) = root + n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w] >>
  drule_at (Pat `val_in_memory _ _ _ u.vs_memory`)
    place_relayout_typed_storage_suffix_framed_run >>
  disch_then (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`)) >>
  disch_then (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `encode_value _ _ = _`)) >>
  disch_then (qspec_then `w2n root + delta` mp_tac) >>
  disch_then (qspecl_then [`a.buf_operand`, `sb`, `sn`, `dst`] mp_tac) >>
  (impl_tac >- (simp[] >> Cases_on `tr` >> fs[slot_loc_def] >> metis_tac[])) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED
Resume place_relayout_storage_run[dynamic_suffix]:
  `place_ptr_rel cenv cx u (PlaceR p) w (SOME loc) (Type dty)` by
    (qpat_x_assum `local_ptrs_reserved cenv sn` kall_tac >>
     irule targetPlaceSimCasesBaseTheory.place_ptr_rel_vars_frame >>
     qexists_tac `s` >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `dty = _` SUBST_ALL_TAC >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = _`
    (strip_assume_tac o REWRITE_RULE [Once evaluate_type_def, AllCaseEqs()]) >>
  gvs[] >>
  rename1 `evaluate_type (get_tenv cx) et = SOME etv` >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_size etv = 32 * type_slot_size etv` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  `?vs. v = ArrayV (DynArrayV vs)` by
    (Cases_on `v` >> fs[vyperTypingTheory.value_has_type_def] >>
     rename1 `value_has_type _ (ArrayV av)` >> Cases_on `av` >> fs[vyperTypingTheory.value_has_type_def]) >>
  pop_assum SUBST_ALL_TAC >>
  irule place_relayout_dyn_storage_suffix_framed_run >> simp[] >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`)) >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  simp[] >>
  goal_assum (drule_at (Pat `place_ptr_rel _ _ u _ _ _ _`)) >>
  goal_assum (drule_at (Pat `val_in_memory _ _ _ u.vs_memory`)) >>
  qexistsl_tac [`dst`, `a.buf_operand`] >>
  simp[evaluate_type_def] >>
  fs[arithmeticTheory.ADD_DIV_ADD_DIV, arithmeticTheory.MULT_DIV] >>
  first_assum ACCEPT_TAC
QED
Finalise place_relayout_storage_run
