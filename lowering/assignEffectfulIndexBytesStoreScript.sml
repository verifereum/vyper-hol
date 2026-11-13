Theory assignEffectfulIndexBytesStore
Ancestors
  assignEffectfulIndexOwnedStore aggregateStoreSizePath valueCopyBytes
  aggregateEvaluatedLayout placeMemoryCopyEffect context vyperTypeSystem
  eventTopicValueProps tuplePlaceStaging placeMemoryStagingFrame
  placeMemoryProtectedFrame placeMemoryLiveRegion placeMemoryStateRebuild
  abiBuiltinEncodeReusedInput freshWrites exprSimProps stmtLowering
  exprLoweringProps vyperScopePreservation tuplePlaceStep
  assignEffectfulIndexSnapshotFrame tuplePlaceSnapshot loweringPosts
  vyperTypeArgFits exprSimHyps compileEnv rich_list fragExec
  abiTupleProps loweringHalt venomState

Theorem bytes_store_size_effect[local]:
  is_bytestring_type dty /\ is_bytestring_type sty /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ val_wf stv v /\ value_has_type dtv v /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_size stv + 64 < dimword (:256) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  compile_store_memory cenv src dst dty sty sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size dtv)
Proof
  strip_tac >>
  `~is_word_type sty /\ ~is_word_type dty` by
    metis_tac[bytestring_type_not_word] >>
  `compile_store_memory cenv src dst sty sty sa = ((),sb)` by
    gvs[compile_store_memory_def] >>
  drule compile_store_memory_same_type_size_forward >>
  disch_then (qspec_then `v` mp_tac) >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ sty = _`)) >>
  simp[] >> disch_then (qspecl_then [`func`, `ctx`] mp_tac) >>
  simp[] >> strip_tac >>
  `type_memory_size stv <= type_memory_size dtv` by
    (Cases_on `sty = dty` >- gvs[] >>
     irule (cj 1 arg_fits_evaluated_memory_size) >>
     qexistsl_tac [`sty`, `tenv`, `dty`] >> fs[type_widens_to_def]) >>
  qexists_tac `t` >> conj_tac
  >- (irule bytestring_val_in_memory_transfer >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[SF SFY_ss]) >>
  simp[typed_copy_effect_def] >> conj_tac
  >- (qpat_x_assum `(t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = s`
       (mp_tac o Q.AP_TERM `\z. z with <|vs_prev_bb := s.vs_prev_bb;
         vs_current_bb := s.vs_current_bb|>`) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `(t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = s`
       (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem assign_effectful_snapshot_bytes_store_ready:
  loc = LocMemory /\ is_bytestring_type dty /\
  is_bytestring_type (lowered_value_type cenv e) /\
  target_post ctx func cenv cx ee ss st u mid (PlaceR p) (Type dty)
    (dst,SOME loc,SOME (ValPT dty)) s /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ val_wf stv v /\
  eval_operand (vv_operand snap) u = SOME sw /\
  (!x. vv_operand snap = Var x ==> not_fresh_at ss x) /\
  (!l. vv_operand snap <> Label l) /\
  ss.cs_next_var <= st.cs_next_var /\ ss.cs_next_id <= st.cs_next_id /\
  (if is_word_type (lowered_value_type cenv e) then
     vv_location snap = NONE /\ sw = typed_val_to_w256 stv v
   else vv_location snap = SOME LocMemory /\
     val_in_memory stv v (w2n sw) u.vs_memory /\
     ?aid sz. aid < ss.cs_next_id /\
       FLOOKUP u.vs_allocas aid = SOME (w2n sw,sz) /\
       type_memory_size stv <= sz /\
       (!n b len. local_region cenv ee.scopes u n b len ==>
         w2n sw + sz <= b \/ b+len <= w2n sw)) /\
  compile_assign_value cenv dst loc (vv_operand snap) (is_word_type dty)
    (vv_location snap) dty (lowered_value_type cenv e)
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et + 31) DIV 32,
             type_memory_bytes cenv et) | _ => NONE)
    (type_memory_bytes cenv dty) st = ((),sf) /\
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
  expr_sim_inv cenv cx env mid /\ cenv.ce_target CapMcopy /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv st /\ storage_place_region cx p /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id mid.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  (loc = LocMemory ==> w2n dw + type_memory_size dtv < dimword (:256)) /\
  (loc = LocMemory ==> 0 < type_memory_size dtv) /\
  (loc = LocMemory /\ ~is_word_type (lowered_value_type cenv e) ==>
    0 < type_memory_size stv /\ type_memory_size stv + 64 < dimword (:256)) /\
  eval_operand dst s = SOME dw /\
  0 < type_slot_size dtv /\
  (loc <> LocMemory /\ dty <> lowered_value_type cenv e /\
    ~(is_bytestring_type dty /\ is_bytestring_type (lowered_value_type cenv e)) ==>
    type_alloc_ok cenv dty) /\
  write_place cx p v mid = (INL (),ff) /\
  fn_has_code st sf func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?z. gas_marked_path F ctx func s 0 (OK z) /\
    stmt_state_rel ctx func cenv cx ff z /\
    (!x. not_fresh_at st x ==> lookup_var x z = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
    ~z.vs_halted /\ z.vs_current_bb = sf.cs_current_bb /\
    z.vs_inst_idx = LENGTH sf.cs_current_insts /\
    alloca_frame cenv mid st s cenv ff z
Proof
  strip_tac >>
  `~is_word_type dty /\ ~is_word_type (lowered_value_type cenv e)` by
    metis_tac[bytestring_type_not_word] >> gvs[] >>
  `eval_operand (vv_operand snap) s = SOME sw` by
    metis_tac[tuple_place_target_operand] >>
  `val_in_memory stv v (w2n sw) s.vs_memory` by
    metis_tac[assign_effectful_target_snapshot_value, arithmeticTheory.ADD_COMM] >>
  `stmt_state_rel ctx func cenv cx mid s /\
   place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type dty) /\
   (!x. dst = Var x ==> not_fresh_at st x)` by gvs[target_post_def] >>
  `!x. vv_operand snap = Var x ==> not_fresh_at st x` by
    metis_tac[not_fresh_at_mono] >>
  `?aid sz. aid < st.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (w2n sw,sz) /\
    type_memory_size stv <= sz` by
    (gvs[target_post_def] >> qexistsl_tac [`aid`, `sz`] >>
     simp[]) >>
  `value_has_type dtv v` by
    (drule_all type_widens_to_value_has_type >> simp[]) >>
  `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv` by
    metis_tac[expr_sim_inv_memory_size] >>
  suspend "staging"
QED

Resume assign_effectful_snapshot_bytes_store_ready[staging]:
  gvs[compile_assign_value_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_alloc_buffer (type_memory_size stv) st = (buf,sm)` >>
  rename1 `compile_copy_memory buf.buf_operand (vv_operand snap) (type_memory_size stv) sm = ((),sn)` >>
  `cs_extends st sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by
    (drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends sn sf` by
    (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     qspecl_then [`cenv`, `buf.buf_operand`, `dst`, `dty`, `lowered_value_type cenv e`, `sn`]
       mp_tac ci_mono_compile_store_memory >>
     simp[ci_mono_def] >> rpt strip_tac >> gvs[]) >>
  `cs_extends st sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code st sn func /\ fn_has_code sn sf func` by metis_tac[fn_has_code_split] >>
  `type_memory_size stv < dimword (:256)` by decide_tac >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) tuple_place_staging_positive >>
  disch_then (drule_at (Pat `compile_copy_memory _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ s.vs_memory`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`sz'`, `w2n sw`] mp_tac) >>
  simp[] >>
  impl_tac >- (disj2_tac >> qexists_tac `aid'` >> simp[]) >>
  disch_then (qx_choose_then `r` (qx_choose_then `su`
    (qx_choose_then `tw` (map_every assume_tac o CONJUNCTS)))) >>
  suspend "store"
QED

Resume assign_effectful_snapshot_bytes_store_ready[store]:
  `su.vs_labels = s.vs_labels` by
    (qpat_assum `_ = r` (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >>
     qpat_assum `_ = s` (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
  `eval_operand dst su = SOME dw` by
    (Cases_on `dst` >> fs[eval_operand_def] >> metis_tac[]) >>
  `(!x. dst = Var x ==> not_fresh_at sn x) /\
   (!x. buf.buf_operand = Var x ==> not_fresh_at sn x)` by
    (`st.cs_next_var <= sm.cs_next_var` by
       (drule compile_alloc_buffer_parts >> simp[]) >>
     `sm.cs_next_var <= sn.cs_next_var` by
       (qpat_assum `compile_copy_memory _ _ _ _ = _` mp_tac >>
        qspecl_then [`buf.buf_operand`, `vv_operand snap`, `type_memory_size stv`, `sm`]
          mp_tac ci_mono_compile_copy_memory >> simp[ci_mono_def] >> metis_tac[]) >>
     conj_tac
     >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `st` >> simp[] >> decide_tac) >>
     rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> gvs[]) >>
  `?z. val_in_memory dtv v (w2n dw) z.vs_memory /\
    typed_copy_effect ctx func sn sf su z (w2n dw) (type_memory_size dtv)` by
    (irule bytes_store_size_effect >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`stv`, `tw`, `get_tenv cx`] >> simp[]) >>
  suspend "rebuild"
QED
Resume assign_effectful_snapshot_bytes_store_ready[rebuild]:
  `!name b len. local_region cenv mid.scopes s name b len ==>
    local_region cenv mid.scopes r name b len` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `st.cs_next_var <= sn.cs_next_var` by
    (qspec_then `type_memory_size stv` (qspec_then `st` mp_tac)
       ci_mono_compile_alloc_buffer >>
     qspecl_then [`buf.buf_operand`, `vv_operand snap`, `type_memory_size stv`, `sm`]
       mp_tac ci_mono_compile_copy_memory >> simp[ci_mono_def]) >>
  drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`) staging_store_local_frame >>
  disch_then (qspecl_then [`w2n tw`, `type_memory_size stv`] mp_tac) >>
  disch_then (qspecl_then [`mid.scopes`, `st`, `s`, `r`, `cenv`] mp_tac) >>
  (impl_tac >- (simp[arithmeticTheory.ADD_COMM] >> metis_tac[arithmeticTheory.ADD_COMM])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "protected"
QED
Resume assign_effectful_snapshot_bytes_store_ready[protected]:
  drule_all memory_place_live_region >> strip_tac >>
  `immutable_alloca_sep func cenv cx mid s` by metis_tac[stmt_state_rel_def] >>
  `cenv.ce_is_ctor ==> !nm tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (tv,iv) ==>
    off + type_memory_size tv <= w2n dw \/ w2n dw + type_memory_size dtv <= off` by
    (rpt strip_tac >>
     qpat_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[immutable_alloca_sep_def] >>
     disch_then (mp_tac o CONJUNCT2) >>
     disch_then drule >>
     disch_then (qspecl_then [`nm`, `tv`, `iv`, `off`] mp_tac) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!id b sz. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `cenv.ce_is_ctor ==> !nm tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (tv,iv) ==>
    mem_bytes_at off (type_memory_size tv) z.vs_memory =
    mem_bytes_at off (type_memory_size tv) r.vs_memory` by
    (rpt strip_tac >>
     `fn_has_code st sm func` by metis_tac[fn_has_code_split] >>
     `off + type_memory_size tv <= w2n tw \/ w2n tw + type_memory_size stv <= off` by
       (irule compile_alloc_buffer_immutable_disjoint >>
        goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
        goal_assum (drule_at (Pat `immutable_alloca_sep _ _ _ _ _`)) >>
        simp[] >> goal_assum (drule_at Any) >> simp[]) >>
     irule staging_copy_protected_bytes >>
     goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >>
     qexistsl_tac [`s`, `type_memory_size stv`, `w2n tw`] >>
     simp[arithmeticTheory.ADD_COMM] >> conj_tac
     >- (qpat_x_assum `cenv.ce_is_ctor ==> !nm tv iv off. _ ==> _ \/ _` mp_tac >>
         simp[] >> disch_then (qspecl_then [`nm`, `tv`, `iv`, `off`] mp_tac) >> simp[]) >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  suspend "finish"
QED
Resume assign_effectful_snapshot_bytes_store_ready[finish]:
  `stmt_state_rel ctx func cenv cx ff z` by
    (irule memory_place_write_stmt_state >>
     goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ dty = _`)) >>
     goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
     qexistsl_tac [`dtv`, `r`, `st`] >> simp[] >>
     rpt conj_tac >> gvs[]) >>
  `!aid b len a n. aid < st.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= a /\ a+n <= b+len ==>
    a+n <= w2n tw \/ w2n tw+type_memory_size stv <= a` by
    (map_every qx_gen_tac [`sep_id`, `ob`, `ol`, `oa`, `on`] >> strip_tac >>
     `w2n tw + type_memory_size stv <= ob \/ ob+ol <= w2n tw` by
       (irule abi_builtin_allocate_separate >>
        qexistsl_tac [`sep_id`, `s`, `st.cs_next_id`] >> simp[] >>
        qpat_x_assum `stmt_state_rel ctx func cenv cx mid s` mp_tac >>
        simp[stmt_state_rel_def]) >> decide_tac) >>
  qexists_tac `z` >> simp[] >>
  `MAP FDOM mid.scopes = MAP FDOM ff.scopes` by metis_tac[write_place_scopes_dom] >>
  irule tuple_place_store_alloca_frame >> simp[] >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >> simp[] >>
  goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> rpt strip_tac >>
  (irule staging_copy_protected_bytes >>
  goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`s`, `type_memory_size stv`, `w2n tw`] >>
  simp[arithmeticTheory.ADD_COMM] >> conj_tac
  >- (qpat_assum `!a len. _ ==> mem_bytes_at a len su.vs_memory = _` mp_tac >>
      simp[arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `!aid b len a n. _ ==> _ \/ _`
    (qspecl_then [`aid''`, `off`, `sz''`, `off`, `sz''`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM])
QED
Finalise assign_effectful_snapshot_bytes_store_ready
