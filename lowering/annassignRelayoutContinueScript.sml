(* Typed relayout into a reserved, not yet bound declaration allocation. *)
Theory annassignRelayoutContinue
Ancestors
  annassignRelayoutPost annassignRelayoutStage annassignRelayoutFrame
  annassignRelayoutBounds annassignRelayoutCode exprSimAggregateChildren fragGasMode
  stmtSimDeclMem exprOpenCopies loweringHalt context stmtLowering
  compileEnv exprLoweringProps emitHelperProps loweringSlice
  placeMemoryCopyEffect venomState words loweringPosts stmtFragPtr fragExec
  exprOpenPrimitives venomInst
Libs monadsyntax

Theorem annassign_relayout_effect_path[local]:
  !ctx func cenv cx es s id p sz w inst v stv dtv sc rest a src sty dty sa sb sw.
    compile_store_memory cenv src (Var p) dty sty sa = ((),sb) /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv.
         evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    eval_operand src s = SOME sw /\ lookup_var p s = SOME w /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n w + type_memory_size dtv < dimword (:256) /\
    (w2n sw + type_memory_size stv <= w2n w \/
     w2n w + type_memory_size dtv <= w2n sw) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    type_memory_size dtv <= sz /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
            (sc |+ (id, <|assignable := a; type := dtv; value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all compile_store_memory_relayout_effect >>
  disch_then (qspec_then `ctx` (qx_choose_then `t` strip_assume_tac)) >>
  `typed_copy_effect ctx func sa sb s t (w2n w) sz` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `t` >> conj_tac
  >- (irule stmt_state_rel_declare_copy_effect >> simp[] >>
      goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >>
      simp[] >> goal_assum (drule_at (Pat `MEM _ _`)) >> simp[] >>
      fs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  drule typed_copy_effect_endpoint >> strip_tac >> simp[] >>
  conj_tac >- metis_tac[typed_copy_effect_lookup] >>
  conj_tac >- metis_tac[typed_copy_effect_allocas] >>
  metis_tac[typed_copy_effect_path]
QED

Theorem annassign_relayout_store_post_path:
  !ctx func cenv cx e es es1 s0 s sa sb sf op id p sz w inst v stv dtv sty dty
   sc rest a loc info bytes.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    post_value_type cenv e = sty /\ sty <> expr_type e /\
    type_widens_to (get_tenv cx) sty (expr_type e) /\
    ~is_word_type sty /\ val_footprint stv v = type_memory_size stv /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    local_ptrs_reserved cenv sa /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv.
         evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    type_memory_bytes cenv sty = type_memory_size stv /\
    type_memory_bytes cenv sty < dimword (:256) /\
    type_memory_size dtv <= sz /\
    compile_assign_value cenv (Var p) LocMemory op F loc
      dty sty info bytes sb = ((),sf) /\ (loc = NONE \/ loc = SOME LocMemory) /\
    fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es1.scopes p /\ not_fresh_at sa p /\ lookup_var p s0 = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    inst.inst_id < sa.cs_next_id ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es1 with scopes :=
            (sc |+ (id, <|assignable := a; type := dtv; value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
        t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
               lookup_var x t = SOME u) /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?sw. eval_operand op s = SOME sw /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      lookup_var p s = SOME w /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n w + type_memory_size dtv < dimword (:256) /\
      (w2n sw + type_memory_size stv <= w2n w \/
       w2n w + type_memory_size dtv <= w2n sw)` by
    (irule expr_post_reserved_destination_source >> simp[] >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es1 s` by fs[expr_post_def] >>
  `not_fresh_at sb p` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  (Cases_on `loc = SOME LocMemory`
   >- suspend "staged"
   >> suspend "direct")
QED

Resume annassign_relayout_store_post_path[direct]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `compile_store_memory cenv op (Var p) dty sty sb = ((),sf)` by
    gvs[compile_assign_value_def] >>
  drule annassign_relayout_effect_path >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = SOME _`)) >>
  disch_then (drule_at (Pat `_.inst_outputs = [p]`)) >>
  disch_then (drule_at (Pat `_.scopes = _ :: _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (qspec_then `a` mp_tac) >>
  simp[] >> disch_then drule >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  gnvs[expr_post_def] >> RULE_L_ASSUM_TAC CONJUNCTS >>
  rpt strip_tac >>
  `not_fresh_at sb x` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  metis_tac[]
QED

Resume annassign_relayout_store_post_path[staged]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qpat_x_assum `loc = SOME LocMemory` SUBST_ALL_TAC >>
  drule_all assign_memory_relayout_code >>
  disch_then (qx_choosel_then [`buf`, `sm`, `ss`] strip_assume_tac) >>
  drule compile_alloc_buffer_emission >>
  disch_then (qx_choosel_then [`sx`, `q`] strip_assume_tac) >>
  `0 < type_memory_size stv` by
    (irule strict_widening_source_positive >> metis_tac[]) >>
  `emit_void MCOPY [Var q; op; Lit (n2w (type_memory_bytes cenv sty))]
    sm = ((),ss)` by
    (Cases_on `type_memory_bytes cenv sty` >>
     gvs[compile_copy_memory_def]) >>
  `fn_has_code sx sm func` by
    (metis_tac[fn_has_code_split]) >>
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
  drule_all alloc_copy_memory_framed_path >>
  disch_then (qx_choosel_then [`u`, `uw`] strip_assume_tac) >>
  `lookup_var p u = SOME w /\
   FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,sz)` by simp[] >>
  `inst.inst_id <> sx.cs_next_id` by
    (fs[ci_mono_def, cs_extends_def] >> decide_tac) >>
  `w2n uw + type_memory_size stv < dimword (:256) /\
   (w2n uw + type_memory_size stv <= w2n w \/
    w2n w + type_memory_size dtv <= w2n uw)` by
    (irule aggregate_allocated_source_bounds >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexistsl_tac [`w2n uw`, `sx.cs_next_id`, `w2n w`, `inst.inst_id`, `sz`, `type_memory_bytes cenv sty`] >> simp[]) >>
  `cs_extends sb ss /\ sb.cs_next_var <= ss.cs_next_var` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `not_fresh_at ss p` by
    (irule not_fresh_at_mono >> qexists_tac `sb` >> simp[]) >>
  `not_fresh_at ss q` by
    (irule not_fresh_at_mono >> qexists_tac `sm` >> fs[ci_mono_def]) >>
  `local_ptrs_reserved cenv ss` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sb` >> simp[]) >>
  `!x. Var q = Var x ==> not_fresh_at ss x` by simp[] >>
  `eval_operand (Var q) u = SOME uw` by simp[eval_operand_def] >>
  `compile_store_memory cenv (Var q) (Var p) dty sty ss = ((),sf)` by metis_tac[] >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _`) annassign_relayout_effect_path >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ ss = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = SOME _`)) >>
  disch_then (drule_at (Pat `_.inst_outputs = [p]`)) >>
  disch_then (drule_at (Pat `_.scopes = _ :: _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (qspec_then `a` mp_tac) >>
  simp[] >> disch_then drule >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `gas_marked_path F ctx func s (0 + 0) (OK t)` by
    (irule gas_marked_path_then >> goal_assum (drule_at Any) >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at ss x /\ x <> q` by
    (gen_tac >> disch_tac >>
     `not_fresh_at sb x` by
       (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     conj_tac >- (irule not_fresh_at_mono >> qexists_tac `sb` >> simp[]) >>
     metis_tac[]) >>
  qexists_tac `t` >> simp[] >>
  gnvs[expr_post_def] >> RULE_L_ASSUM_TAC CONJUNCTS >>
  rpt strip_tac >> metis_tac[]
QED

Finalise annassign_relayout_store_post_path

Theorem compile_assign_memory_relayout_open:
  !cenv dst src dty sty info bytes loc sa sf.
    compile_assign_value cenv dst LocMemory src F loc dty sty info bytes sa = ((),sf) /\
    (loc = NONE \/ loc = SOME LocMemory) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\ ~block_is_terminated sa ==>
    ~block_is_terminated sf
Proof
  rpt gen_tac >> disch_tac >> Cases_on `loc = SOME LocMemory`
  >- (gvs[] >>
      Cases_on `compile_alloc_buffer (type_memory_bytes cenv sty) sa` >>
      rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
      Cases_on `compile_copy_memory buf.buf_operand src (type_memory_bytes cenv sty) sm` >>
      rename1 `compile_copy_memory _ _ _ sm = (u,ss)` >> Cases_on `u` >>
      gvs[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      `~block_is_terminated sm` by metis_tac[exprOpenPrimitivesTheory.compile_alloc_buffer_open] >>
      `~block_is_terminated ss` by
        (Cases_on `type_memory_bytes cenv sty` >>
         gvs[compile_copy_memory_def, comp_return_def] >>
         drule emit_void_terminated >> simp[is_terminator_def]) >>
      (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`) compile_store_memory_open >> simp[])) >>
  gvs[compile_assign_value_def] >> irule compile_store_memory_open >>
  qexistsl_tac [`cenv`, `dst`, `dty`, `()`, `sa`, `src`, `sty`] >> simp[]
QED
