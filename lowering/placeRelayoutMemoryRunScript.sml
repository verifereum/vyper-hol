Theory placeRelayoutMemoryRun
Ancestors
  placeRelayoutState placeDestinationBounds annassignRelayoutBounds
  annassignRelayoutCode annassignRelayoutStage bodySimAugPlaceLoad
  placeMemoryCopyEffect exprSimHypsDefs loweringPosts exprLoweringProps
  stmtLowering compileEnv context words fragGasPath fragGasSeq
  emitHelperProps allocaSiteResource stmtFragPtr loweringHalt fragExec
  placeMemoryLiveRegion exprSimOperands venomInst targetPlaceSimCasesBase
  venomExecSemantics venomState fragGasMode stmtSimAugAssignPlaceMemory
  stmtSimDefs localMemoryStorePath vyperScopePreservation venomMemDefs
Libs monadsyntax

Theorem place_relayout_memory_run:
  !ctx func cenv cx env ee ff s p dw dst src src_loc dty sty stv dtv v sa sb info bytes sw.
  compile_assign_value cenv dst LocMemory src F src_loc dty sty info bytes sa = ((),sb) /\
  (src_loc = NONE \/ src_loc = SOME LocMemory) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  expr_sim_inv cenv cx env ee /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  (src_loc = NONE ==> w2n sw + type_memory_size stv <= w2n dw \/
                       w2n dw + type_memory_size dtv <= w2n sw) /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  0 < type_memory_size stv /\ type_memory_bytes cenv sty < dimword (:256) /\
  val_footprint stv v <= type_memory_size stv /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type dty) /\
  stmt_state_rel ctx func cenv cx ee s /\ write_place cx p v ee = (INL (),ff) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
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
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
                                  sz = type_memory_size tv) fields)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (rpt strip_tac >> metis_tac[aug_place_entry_type_agrees]) >>
  `w2n dw + type_memory_size dtv < dimword (:256)` by
    (drule_all memory_place_destination_bound >> simp[]) >>
  Cases_on `src_loc = SOME LocMemory`
  >- suspend "staged" >>
  `src_loc = NONE` by metis_tac[] >>
  `w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw` by metis_tac[] >>
  `compile_store_memory cenv src dst dty sty sa = ((),sb)` by
    gvs[compile_assign_value_def] >>
  `?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
       typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size dtv)` by
    (irule compile_store_memory_relayout_effect >>
     simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = SOME dtv`)) >>
     goal_assum (drule_at (Pat `eval_operand src s = _`)) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ff t` by
    (irule memory_place_write_copy_effect >>
     goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >>
     metis_tac[]) >>
  `alloca_frame cenv ee sa s cenv ff t` by suspend "direct_frame" >>
  qexists_tac `t` >> simp[] >>
  metis_tac[typed_copy_effect_endpoint, typed_copy_effect_lookup,
            typed_copy_effect_allocas, typed_copy_effect_path]
QED

Resume place_relayout_memory_run[staged]:
  markerLib.RESUME_TAC >> (rpt strip_tac >>
  qpat_x_assum `src_loc = SOME LocMemory` SUBST_ALL_TAC >>
  drule_all assign_memory_relayout_code >>
  disch_then (qx_choosel_then [`buf`,`sm`,`ss`] strip_assume_tac) >>
  drule compile_alloc_buffer_emission >>
  disch_then (qx_choosel_then [`sx`,`q`] strip_assume_tac) >>
  `emit_void MCOPY [Var q; src; Lit (n2w (type_memory_bytes cenv sty))]
    sm = ((),ss)` by
    (Cases_on `type_memory_bytes cenv sty` >> gvs[compile_copy_memory_def]) >>
  `fn_has_code sx sm func` by metis_tac[fn_has_code_split] >>
  `MEM (mk_inst sx.cs_next_id ALLOCA
     [Lit (n2w (type_memory_bytes cenv sty))] [q]) (fn_insts func)` by
    (irule emit_inst_fn_member >> qexists_tac `sm` >> simp[]) >>
  `not_local_ptr cenv ee.scopes q` by
    (fs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  `src <> Var q /\ dst <> Var q` by metis_tac[] >>
  `s.vs_current_bb = sx.cs_current_bb /\
   s.vs_inst_idx = LENGTH sx.cs_current_insts` by simp[] >>
  `type_memory_bytes cenv sty <= type_memory_bytes cenv sty /\
   val_footprint stv v <= type_memory_bytes cenv sty` by simp[] >>
  drule_all alloc_copy_memory_framed_capacity_path >>
  disch_then (qx_choosel_then [`u`,`uw`] strip_assume_tac) >>
  `venomMemDefs$allocas_non_overlapping u` by
    fs[stmt_state_rel_def, state_rel_def, alloca_inv_def] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x u = SOME w` by
    (rpt strip_tac >> `x <> q` by metis_tac[] >>
     qpat_x_assum `!x. x <> q ==> _` drule >> simp[]) >>
  `alloca_frame cenv ee sa s cenv ee u` by
    (`stmt_state_rel ctx func cenv cx ee s /\ local_ptrs_reserved cenv sa /\
      (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
             lookup_var x u = SOME w) /\
      venomMemDefs$allocas_non_overlapping u /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                   FLOOKUP u.vs_allocas aid = SOME entry) /\
      FLOOKUP u.vs_allocas sx.cs_next_id =
        SOME (w2n uw,type_memory_bytes cenv sty) /\
      sa.cs_next_id <= sx.cs_next_id /\
      (!ad len. ad + len <= w2n uw \/
                w2n uw + type_memory_bytes cenv sty <= ad ==>
        mem_bytes_at ad len u.vs_memory = mem_bytes_at ad len s.vs_memory)`
       suffices_by
       (rpt (pop_assum kall_tac) >> strip_tac >>
        drule_all alloca_frame_owned_copy >> simp[]) >>
     gvs[] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ u.vs_memory = _` irule >>
     decide_tac) >>
  drule_all memory_place_live_region >>
  disch_then (qx_choosel_then [`name`,`b`,`len`] strip_assume_tac) >>
  `local_region cenv ee.scopes u name b len` by
    (fs[local_region_def, not_local_ptr_def] >> metis_tac[]) >>
  `w2n uw + type_memory_bytes cenv sty <= b \/ b + len <= w2n uw` by
    (irule alloca_clear_of_locals >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`)) >>
     goal_assum (drule_at (Pat `local_region _ _ u _ _ _`)) >>
     qexistsl_tac [`mk_inst sx.cs_next_id ALLOCA
       [Lit (n2w (type_memory_bytes cenv sty))] [q]`,`q`] >> gvs[mk_inst_def]) >>
  `w2n uw + type_memory_size stv < dimword (:256)` by
    (`w2n uw + type_memory_bytes cenv sty <= u.vs_alloca_next` by
       (irule alloca_site_registered_below >> fs[stmt_state_rel_def] >> metis_tac[]) >>
     `u.vs_alloca_next < dimword (:256)` by
       (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
     decide_tac) >>
  `w2n uw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n uw` by decide_tac >>
  `cs_extends sa ss /\ sa.cs_next_var <= ss.cs_next_var` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at ss x /\ x <> q` by
    (rpt strip_tac >- (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     metis_tac[]) >>
  `not_fresh_at ss q` by
    (irule not_fresh_at_mono >> qexists_tac `sm` >> fs[ci_mono_def]) >>
  `local_ptrs_reserved cenv ss` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `u.vs_labels = s.vs_labels` by metis_tac[aug_place_marked_path_labels] >>
  `eval_operand dst u = SOME dw` by
    (Cases_on `dst` >> fs[eval_operand_def]) >>
  `!x. dst = Var x ==> not_fresh_at ss x` by metis_tac[] >>
  `!x. Var q = Var x ==> not_fresh_at ss x` by simp[] >>
  `eval_operand (Var q) u = SOME uw` by simp[eval_operand_def] >>
  `place_ptr_rel cenv cx u (PlaceR p) dw (SOME LocMemory) (Type dty)` by
    (irule place_ptr_rel_vars_frame >>
     goal_assum (drule_at (Pat `place_ptr_rel _ _ s _ _ _ _`)) >>
     qexists_tac `sa` >> simp[]) >>
  `?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
       typed_copy_effect ctx func ss sb u t (w2n dw) (type_memory_size dtv)` by
    (irule compile_store_memory_relayout_effect >>
     ntac 8 (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`cenv`, `dst`, `dty`, `Var q`, `stv`, `sty`, `uw`, `get_tenv cx`] >>
     simp[] >> conj_tac >-
       (qpat_x_assum `!nm fields. FLOOKUP cenv.ce_struct_fields nm = SOME fields ==> _` mp_tac >>
        simp[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
     qpat_x_assum `compile_store_memory cenv buf.buf_operand dst dty sty ss = _` mp_tac >>
     simp[]) >>
  `stmt_state_rel ctx func cenv cx ff t` by
    (irule memory_place_write_copy_effect >>
     goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >> metis_tac[]) >>
  `gas_marked_path F ctx func u 0 (OK t)` by metis_tac[typed_copy_effect_path] >>
  `gas_marked_path F ctx func s (0 + 0) (OK t)` by
    (irule gas_marked_path_then >> goal_assum (drule_at Any) >> simp[]) >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  `!x. not_fresh_at ss x ==> lookup_var x t = lookup_var x u` by
    metis_tac[typed_copy_effect_lookup] >>
  `t.vs_allocas = u.vs_allocas` by metis_tac[typed_copy_effect_allocas] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     qpat_x_assum `!x. not_fresh_at sa x ==> not_fresh_at ss x /\ x <> q` drule >>
     strip_tac >> simp[]) >>
  `alloca_frame cenv ee sa s cenv ff t` by
    (irule alloca_frame_of_mem_frame >>
     conj_tac >- (rpt strip_tac >> simp[]) >>
     conj_tac >- (
     map_every qx_gen_tac [`aid`, `off`, `sz`] >> strip_tac >>
     `mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s.vs_memory` by
       (qpat_x_assum `alloca_frame _ _ _ _ _ _ u` mp_tac >>
        rewrite_tac[alloca_frame_def] >>
        disch_then (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
        (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> simp[]) >>
     `mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz u.vs_memory` suffices_by simp[] >>
     irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >>
     qpat_x_assum `!n b sz'. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[] >> decide_tac) >>
     conj_tac
     >- metis_tac[vyperScopePreservationTheory.write_place_scopes_dom] >>
     metis_tac[]) >>
  qexists_tac `t` >> fs[] >>
  rpt strip_tac >> first_x_assum drule >> simp[])
QED

Resume place_relayout_memory_run[direct_frame]:
  markerLib.RESUME_TAC >> (rpt strip_tac >>
  drule_all memory_place_live_region >> strip_tac >>
  irule alloca_frame_of_mem_frame >>
  simp[] >> conj_tac >- metis_tac[typed_copy_effect_lookup] >>
  reverse conj_tac
  >- (conj_tac
      >- metis_tac[vyperScopePreservationTheory.write_place_scopes_dom] >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >>
  qpat_x_assum `!n b sz'. local_region _ _ _ _ _ _ ==> _` drule >>
  simp[] >> decide_tac)
QED

Finalise place_relayout_memory_run
