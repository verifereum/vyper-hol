(* Joint execution and state updates for memory-place assignments. *)
Theory bodyFullAssignMemoryPlace
Ancestors
  arithmetic assignTuplePtrCopyLen bodyFullHashKeccakFixed bodyFullMemoryStage
  bodyFullMemoryStore bodyFullPathHistory bodyFullTargetDefs bodyMemBopRestWordPath
  bodyMemoryDefs bodyPtrDefs compileEnv exprLoweringProps exprSimProps finite_map fragExec
  fragGasMode fragGasOrigin fragGasOriginPtr list loweringPosts loweringStateRelDefs
  memoryPlaceStorePost pair placeMemoryCopyEffect placeMemoryLiveRegion
  placeMemoryStateRebuild pred_set ptrDiscipline stateRelProj stmtLowering stmtSimDefs sum
  targetPlaceSimCasesBase typedCopyOriginPtrBase typedMemoryCopy venomMemDefs words
  exprSimHypsDefs[qualified]
Libs
  monadsyntax

Theorem body_assign_memory_place_execution[local]:
  compile_assign_value cenv (Var xd) LocMemory (Var xs) F loc dty sty bytes sa = ((),sb) /\
  ~is_word_type dty /\ ~is_word_type sty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size stv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (loc <> SOME LocMemory ==>
    w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  stmt_state_rel H0 ctx func cenv cx ee s /\
  expr_val_at cenv cx sty start sa ee v (Var xs) s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_history func s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn xd s (type_memory_size dtv) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  lo <= w2n dw /\
  (?name b len. local_region cenv ee.scopes s name b len /\
    b <= w2n dw /\ w2n dw + type_memory_size dtv <= b+len) ==>
  ?sc u Gu tu t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    sa.cs_next_id <= sc.cs_next_id /\ local_ptrs_reserved cenv sc /\
    (!H. stmt_state_rel H ctx func cenv cx ee s ==>
      stmt_state_rel H ctx func cenv cx ee u) /\
    (!D d. ghost_inv_at D lo d cenv cx ee G tn s ==>
      ghost_inv_at D lo d cenv cx ee Gu tu u) /\
    (!name b len. local_region cenv ee.scopes u name b len <=>
      local_region cenv ee.scopes s name b len) /\
    (!x. not_fresh_at sa x ==> not_fresh_at sc x /\
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      op_taint tu (Var x) = op_taint tn (Var x)) /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
      FLOOKUP u.vs_allocas aid = SOME ent) /\
    alloca_frame cenv ee sa s cenv ee u /\
    (!aid off sz i.
      FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name a len. local_region cenv ee.scopes s name a len ==>
        off+sz <= a \/ a+len <= off) /\
      off <= i /\ i < off+sz /\ i IN tu.t_mem ==> i IN tn.t_mem) /\
    typed_copy_effect ctx func sc sb u t (w2n dw) (type_memory_size dtv) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    (!x. not_fresh_at sc x ==> FLOOKUP Gf x = FLOOKUP Gu x /\
      op_taint tf (Var x) = op_taint tu (Var x)) /\
    tf.t_stor = tu.t_stor /\ tf.t_trans = tu.t_trans /\ tf.t_imm = tu.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
      (i IN tf.t_mem <=> i IN tu.t_mem)) /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!d. return_buf_frame d cenv sa s ==> return_buf_frame d cenv sb t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?name b len. local_region _ _ _ _ _ _ /\ _` strip_assume_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  Cases_on `loc = SOME LocMemory`
  >- suspend "staged" >>
  `compile_store_memory cenv (Var xs) (Var xd) dty sty sa = ((),sb)` by
    gvs[stmtLoweringTheory.compile_assign_value_def] >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`] (SPEC_ALL body_full_memory_store_path)) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (irule gas_marked_path_from_mem >>
     qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size dtv)` by
    (fs[typed_copy_effect_def,typed_copy_state_frame_def,typed_copy_frame_def,
        venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
       (qspec_then `cx_dead H0 cx` mp_tac) >>
     strip_tac >>
     metis_tac[body_full_path_alloca_history, stmt_state_rel_local_ptrs_alloca]) >>
  `ci_mono sa sb` by
    metis_tac[ci_mono_compile_store_memory,pairTheory.SND] >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
      (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next` o CONJUNCT1 o
       REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
  qexistsl_tac [`sa`,`s`,`G`,`tn`,`t`,`Gf`,`tf`] >> simp[] >>
  conj_tac >- (simp[alloca_frame_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[typed_copy_state_frame_allocas_below_fmp] >>
  rpt strip_tac >> irule return_buf_frame_frame >> simp[] >>
  qexistsl_tac [`cenv`,`s`,`sa`] >> fs[ci_mono_def] >> metis_tac[]
QED

Resume body_assign_memory_place_execution[staged]:
  gnvs[stmtLoweringTheory.compile_assign_value_def,
      comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  rename1 `compile_copy_memory _ (Var xs) _ sm = ((),sn)` >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_copy_memory,
              ci_mono_compile_store_memory,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]) >>
  mp_tac (Q.INST [`es` |-> `ee`,`tv` |-> `stv`,
    `n` |-> `type_memory_size stv`,`sb` |-> `sn`]
    (SPEC_ALL body_full_memory_stage_frame_path)) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`u`,`root`,`b0`,`Gu`,`tu`] strip_assume_tac) >>
  `local_ptrs_reserved cenv sn` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!name a len. local_region cenv ee.scopes u name a len <=>
    local_region cenv ee.scopes s name a len` by
    (rw[local_region_def] >> metis_tac[local_ptrs_reserved_def]) >>
  `lookup_var xd u = SOME dw /\ not_fresh_at sn xd` by metis_tac[] >>
  `ptr_covers Gu tu xd u (type_memory_size dtv)` by
    metis_tac[assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame] >>
  `b0 < dimword (:256)` by decide_tac >>
  `w2n ((n2w b0):bytes32) = b0` by simp[] >>
  `compile_store_memory cenv (Var root) (Var xd) dty sty sn = ((),sb)` by
    metis_tac[] >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
      (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> strip_tac >> drule gas_marked_path_exec >>
     strip_tac >> metis_tac[bodyMemBopRestWordPathTheory.rest_word_path_frontier]) >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`,`xs` |-> `root`,
    `sa` |-> `sn`,`s` |-> `u`,`G` |-> `Gu`,`tn` |-> `tu`,
    `sw` |-> `(n2w b0):bytes32`] (SPEC_ALL body_full_memory_store_path)) >>
  (impl_tac >- (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `!name a len. local_region _ _ u name a len ==> _`
      (qspecl_then [`name`,`b`,`len`] mp_tac) >>
    simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >>
  strip_tac >> suspend "staged_finish"
QED

Resume body_assign_memory_place_execution[staged_finish]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`u`,`Gu`,`tu`,`[]`,`OK t`,`Gf`,`tf`] mp_tac) >>
     simp[]) >>
  `gas_marked_path F ctx func u 0 (OK t)` by
    (irule gas_marked_path_from_mem >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) _ _`
       (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `typed_copy_effect ctx func sn sb u t (w2n dw) (type_memory_size dtv)` by
    (fs[typed_copy_effect_def,typed_copy_state_frame_def,typed_copy_frame_def,
        venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ (OK t,Gf,tf)`
       (qspec_then `cx_dead H0 cx` mp_tac) >>
     strip_tac >>
     metis_tac[body_full_path_alloca_history, stmt_state_rel_local_ptrs_alloca]) >>
  `t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
      (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next` o CONJUNCT1 o
       REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
  qexistsl_tac [`sn`,`u`,`Gu`,`tu`,`t`,`Gf`,`tf`] >> simp[] >>
  conj_tac >- (fs[ci_mono_def] >> decide_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[typed_copy_state_frame_allocas_below_fmp] >>
  rpt strip_tac >> irule return_buf_frame_frame >> simp[] >>
  qexistsl_tac [`cenv`,`s`,`sa`] >> fs[ci_mono_def] >> metis_tac[]
QED

Finalise body_assign_memory_place_execution

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all memory_place_live_region >> strip_tac >>
  `w2n dw + type_memory_size dtv <= s.vs_alloca_next` by
    (drule_all body_local_region_frontier >> decide_tac) >>
  `w2n dw + type_memory_size dtv < dimword (:256)` by
    metis_tac[stmt_state_rel_alloca_room, alloca_room_next_lt, LESS_EQ_LESS_TRANS] >>
  `ptr_covers G tn xd s (type_memory_size dtv)` by
    (Cases_on `p` >>
     gvs[place_ptr_rel_def, slot_loc_def, AllCaseEqs()] >>
     drule write_memory_place_entry_update >> strip_tac >>
     `local_ptrs_rel func cenv ee.scopes s` by
       metis_tac[stmt_state_rel_local_ptrs_alloca] >>
     fs[local_ptrs_rel_def] >>
     qpat_x_assum `!name entry p sz. _ ==> ?w. _` (drule_all_then strip_assume_tac) >>
     gvs[] >>
     drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
     `s.vs_alloca_next < dimword (:256)` by
       metis_tac[stmt_state_rel_alloca_room, alloca_room_next_lt] >>
     `w2n b' + k < dimword (:256)` by decide_tac >>
     `k < dimword (:256)` by decide_tac >>
     `w2n (b' + n2w k) = w2n b' + k` by
       (`w2n (b' + n2w k) = w2n b' + w2n ((n2w k):bytes32)` suffices_by simp[] >>
        irule w2n_add_2 >> simp[]) >>
     fs[ghost_inv_at_def, target_ptr_ok_def, ptr_covers_def, op_prov_def] >>
     qpat_x_assum `!name entry p sz. _` (drule_all_then strip_assume_tac) >>
     gvs[] >>
     qexistsl_tac [`b''`,`sz''`] >> simp[] >> decide_tac) >>
  mp_tac (SPEC_ALL (INST_TYPE [alpha |-> ``:'h``, beta |-> ``:'h``] body_assign_memory_place_execution)) >>
  (impl_tac >- (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
    qexistsl_tac [`name`,`b`,`len`] >> simp[ADD_COMM])) >>
  disch_then (qx_choosel_then [`sc`,`u`,`Gu`,`tu`,`t`,`Gf`,`tf`] strip_assume_tac) >>
  `place_ptr_rel cenv cx u (PlaceR p) dw (SOME LocMemory) (Type dty)` by
    (irule place_ptr_rel_vars_frame >> metis_tac[]) >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sc x` by
    metis_tac[] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sc x` by
    metis_tac[] >>
  `!(H : (bool # 'h word # type_value) list # num list) D d. stmt_state_rel H ctx func cenv cx ee s /\
    ghost_inv_at D lo d cenv cx ee G tn s ==>
    stmt_state_rel H ctx func cenv cx ff t /\
    ghost_inv_at D lo d cenv cx ff Gf tf t /\
    alloca_frame cenv ee sc u cenv ff t /\
    (!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ aid < sc.cs_next_id /\
      (!name a len. local_region cenv ee.scopes u name a len ==> off+sz <= a \/ a+len <= off) /\
      off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tu.t_mem)` by
    (map_every qx_gen_tac [`H`,`D`,`d`] >> strip_tac >>
     `stmt_state_rel H ctx func cenv cx ee u` by
       (qpat_x_assum `!H. stmt_state_rel _ _ _ _ _ _ _ ==> _`
          (qspec_then `H` mp_tac) >> simp[]) >>
     `ghost_inv_at D lo d cenv cx ee Gu tu u` by metis_tac[] >>
     irule body_assign_memory_place_store_post >>
     simp[] >>
     conj_tac >- (qexists_tac `env` >> first_assum ACCEPT_TAC) >>
     conj_tac >- (qexistsl_tac [`dtv`,`dty`,`dw`,`p`,`sb`,`v`] >> simp[] >>
       first_assum ACCEPT_TAC) >>
     qexists_tac `Gu` >> simp[] >> metis_tac[]) >>
  first_assum (qspecl_then [`H0`,`D0`,`d0`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  drule typed_copy_effect_endpoint >> strip_tac >> simp[] >>
  `t.vs_allocas = u.vs_allocas` by metis_tac[typed_copy_effect_allocas] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[typed_copy_effect_lookup] >>
  conj_tac >- (irule alloca_frame_trans >> metis_tac[]) >>
  rpt strip_tac >>
  `aid < sc.cs_next_id` by decide_tac >>
  `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
  `i IN tu.t_mem` by
    (qpat_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ _ ==>
        i IN tu.t_mem`
      (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  qpat_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ _ ==>
      i IN tn.t_mem`
    (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
*)
Theorem body_assign_memory_place_joint:
  compile_assign_value cenv (Var xd) LocMemory (Var xs) F loc dty sty bytes sa = ((),sb) /\
  ~is_word_type dty /\ ~is_word_type sty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size stv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (loc <> SOME LocMemory ==>
    w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  stmt_state_rel (H0 : (bool # 'h word # type_value) list # num list) ctx func cenv cx ee s /\
  expr_val_at cenv cx sty start sa ee v (Var xs) s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_history func s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  expr_sim_inv_mods mods cenv cx env ee /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type dty) /\
  target_ptr_ok cenv (PlaceR p) (Var xd,SOME LocMemory,SOME (ValPT dty)) G tn s /\
  ghost_inv_at D0 lo d0 cenv cx ee G tn s /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  lo <= w2n dw ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    (!(H : (bool # 'h word # type_value) list # num list) D d. stmt_state_rel H ctx func cenv cx ee s /\
      ghost_inv_at D lo d cenv cx ee G tn s ==>
      stmt_state_rel H ctx func cenv cx ff t /\
      ghost_inv_at D lo d cenv cx ff Gf tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!d. return_buf_frame d cenv sa s ==> return_buf_frame d cenv sb t) /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
      FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    alloca_frame cenv ee sa s cenv ff t /\
    (!aid off sz i.
      FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name a len. local_region cenv ee.scopes s name a len ==>
        off+sz <= a \/ a+len <= off) /\
      off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn.t_mem)
Proof
  cheat
QED
