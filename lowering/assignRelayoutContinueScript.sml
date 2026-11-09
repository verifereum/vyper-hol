(* Execute assignment relayout into a live local, with optional source staging. *)
Theory assignRelayoutContinue
Ancestors
  assignRelayoutFrame assignRelayoutSource annassignRelayoutSource
  annassignRelayoutContinue annassignRelayoutPost annassignRelayoutStage loweringPosts vyperLookup
  annassignRelayoutCode exprSimOperands exprSimAggregateChildren
  fragGasMode fragGasPath placeMemoryCopyEffect
  stmtLowering context compileEnv exprLoweringProps emitHelperProps
  loweringSlice loweringHalt fragExec venomState venomInst
  allocaSiteResource stmtFragPtr localMemoryStorePath stmtSimDefs
Libs monadsyntax

Theorem assign_relayout_store_post_path:
  !ctx func cenv cx e es es1 s0 s sa sb sf op id p cap dw v stv dtv sty dty
   pre scope entry rest loc info bytes.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    post_value_type cenv e = sty /\ sty <> expr_type e /\
    type_widens_to (get_tenv cx) sty (expr_type e) /\
    ~is_word_type sty /\ val_footprint stv v = type_memory_size stv /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    local_ptrs_reserved cenv sb /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv.
         evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\ entry.type = dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    type_memory_bytes cenv sty = type_memory_size stv /\
    type_memory_bytes cenv sty < dimword (:256) /\ type_memory_size dtv <= cap /\
    compile_assign_value cenv (Var p) LocMemory op F loc
      dty sty info bytes sb = ((),sf) /\ (loc = NONE \/ loc = SOME LocMemory) /\
    fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    find_containing_scope id es1.scopes = SOME (pre,scope,entry,rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\ lookup_var p s = SOME dw ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es1 with scopes := pre ++
            (scope |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
        t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
        (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
                     FLOOKUP t.vs_allocas aid = SOME ent) /\
        gas_marked_path F ctx func s 0 (OK t) /\
        alloca_frame cenv es1 sb s cenv
          (es1 with scopes := pre ++
            (scope |+ (id, entry with <|value := v; popped := []|>)) :: rest) t
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `0 < type_memory_size stv` by
    (irule strict_widening_source_positive >> metis_tac[]) >>
  `lookup_scopes id es1.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?sw. eval_operand op s = SOME sw /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      local_backed func p s (w2n dw) cap /\
      w2n dw + cap <= s.vs_alloca_next /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw)` by
    (irule expr_post_live_destination_source >> simp[] >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es1 s` by fs[expr_post_def] >>
  `not_fresh_at sb p` by metis_tac[local_ptrs_reserved_def] >>
  `MAP FDOM (pre ++
      (scope |+ (id, entry with <|value := v; popped := []|>)) :: rest) =
    MAP FDOM es1.scopes` by
    (drule find_containing_scope_structure >> strip_tac >>
     gvs[finite_mapTheory.FDOM_FUPDATE, finite_mapTheory.FLOOKUP_DEF,
         pred_setTheory.ABSORPTION]) >>
  (Cases_on `loc = SOME LocMemory`
   >- suspend "staged"
   >> suspend "direct")
QED

Resume assign_relayout_store_post_path[direct]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `compile_store_memory cenv op (Var p) dty sty sb = ((),sf)` by
    gvs[compile_assign_value_def] >>
  drule local_memory_relayout_store_path >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `find_containing_scope _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  simp[] >> disch_then drule >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  drule typed_copy_effect_allocas >> strip_tac >>
  drule typed_copy_effect_path >> strip_tac >>
  `!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s` by
    metis_tac[typed_copy_effect_lookup] >>
  qexists_tac `t` >> simp[] >>
  irule alloca_frame_local_store >>
  simp[] >>
  (conj_tac >- metis_tac[]) >>
  qexistsl_tac [`w2n dw`, `es1`, `id`, `type_memory_size dtv`, `s`, `cap`] >>
  `alloca_frame cenv es1 sb s cenv es1 s` by
    (irule alloca_frame_same >> simp[]) >>
  `local_region cenv es1.scopes s id (w2n dw) cap` by
    (simp[local_region_def] >> metis_tac[]) >>
  fs[] >>
  conj_tac
  >- (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  fs[typed_copy_effect_def, local_ptrs_reserved_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume assign_relayout_store_post_path[staged]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qpat_x_assum `loc = SOME LocMemory` SUBST_ALL_TAC >>
  drule_all assign_memory_relayout_code >>
  disch_then (qx_choosel_then [`buf`,`sm`,`ss`] strip_assume_tac) >>
  drule compile_alloc_buffer_emission >>
  disch_then (qx_choosel_then [`sx`,`q`] strip_assume_tac) >>
  `emit_void MCOPY [Var q; op; Lit (n2w (type_memory_bytes cenv sty))]
    sm = ((),ss)` by
    (Cases_on `type_memory_bytes cenv sty` >>
     gvs[compile_copy_memory_def]) >>
  `fn_has_code sx sm func` by metis_tac[fn_has_code_split] >>
  `MEM (mk_inst sx.cs_next_id ALLOCA
     [Lit (n2w (type_memory_bytes cenv sty))] [q]) (fn_insts func)` by
    (irule emit_inst_fn_member >> qexists_tac `sm` >> simp[]) >>
  `not_local_ptr cenv es1.scopes q` by
    (fs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  `op <> Var q /\ p <> q` by metis_tac[] >>
  `s.vs_current_bb = sx.cs_current_bb /\
   s.vs_inst_idx = LENGTH sx.cs_current_insts` by simp[] >>
  `type_memory_bytes cenv sty <= type_memory_bytes cenv sty /\
   val_footprint stv v <= type_memory_bytes cenv sty` by simp[] >>
  drule_all alloc_copy_memory_framed_capacity_path >>
  disch_then (qx_choosel_then [`u`,`uw`] strip_assume_tac) >>
  `lookup_var p u = SOME dw` by simp[] >>
  `local_region cenv es1.scopes u id (w2n dw) cap` by
    (simp[local_region_def] >> metis_tac[]) >>
  `w2n uw + type_memory_bytes cenv sty <= w2n dw \/
   w2n dw + cap <= w2n uw` by
    (irule alloca_clear_of_locals >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
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
  `cs_extends sb ss /\ sb.cs_next_var <= ss.cs_next_var` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `not_fresh_at ss q` by
    (irule not_fresh_at_mono >> qexists_tac `sm` >> fs[ci_mono_def]) >>
  `local_ptrs_reserved cenv ss` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sb` >> simp[]) >>
  `!x. Var q = Var x ==> not_fresh_at ss x` by simp[] >>
  `eval_operand (Var q) u = SOME uw` by simp[eval_operand_def] >>
  `compile_store_memory cenv (Var q) (Var p) dty sty ss = ((),sf)` by metis_tac[] >>
  drule local_memory_relayout_store_path >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`)) >>
  disch_then (drule_at (Pat `find_containing_scope _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ u.vs_memory`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = SOME _`)) >>
  simp[] >> (impl_tac >-
    (qpat_x_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> _` mp_tac >>
     simp[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[])) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  `gas_marked_path F ctx func u 0 (OK t)` by
    metis_tac[typed_copy_effect_path] >>
  `gas_marked_path F ctx func s (0 + 0) (OK t)` by
    (irule gas_marked_path_then >> goal_assum (drule_at Any) >> simp[]) >>
  `!x. not_fresh_at sb x ==> not_fresh_at ss x /\ x <> q` by
    (rpt strip_tac >- (irule not_fresh_at_mono >> qexists_tac `sb` >> simp[]) >>
     metis_tac[]) >>
  `!x. not_fresh_at ss x ==> lookup_var x t = lookup_var x u` by
    metis_tac[typed_copy_effect_lookup] >>
  `t.vs_allocas = u.vs_allocas` by metis_tac[typed_copy_effect_allocas] >>
  `sx.cs_next_id = sb.cs_next_id` by simp[] >>
  `venomMemDefs$allocas_non_overlapping u` by
    (qpat_x_assum `stmt_state_rel ctx func cenv cx es1 u` mp_tac >>
     simp[stmt_state_rel_def, state_rel_def, venomMemDefsTheory.alloca_inv_def]) >>
  `!x w. not_fresh_at sb x /\ lookup_var x s = SOME w ==>
    lookup_var x u = SOME w` by metis_tac[] >>
  `alloca_frame cenv es1 sb s cenv es1 u` by
    (irule alloca_frame_owned_copy >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >-
       (qexistsl_tac [`w2n uw`, `sx.cs_next_id`, `type_memory_bytes cenv sty`] >>
        pure_asm_rewrite_tac [] >> simp[])) >>
     (conj_tac >- first_assum ACCEPT_TAC) >> metis_tac[]) >>
  `alloca_frame cenv es1 sb s cenv
    (es1 with scopes := pre ++
      (scope |+ (id, entry with <|value := v; popped := []|>)) :: rest) t` by
    (irule alloca_frame_local_store >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- metis_tac[]) >>
     qexists_tac `w2n dw` >>
     qexists_tac `es1` >>
     qexists_tac `id` >>
     qexists_tac `type_memory_size dtv` >>
     qexists_tac `u` >> qexists_tac `cap` >>
     pure_asm_rewrite_tac [] >>
     fs[typed_copy_effect_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  qexists_tac `t` >> fs[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Finalise assign_relayout_store_post_path
