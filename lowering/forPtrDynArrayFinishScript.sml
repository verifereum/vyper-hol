(* Dynamic callback cleanup preserves the saved length as an old register. *)
Theory forPtrDynArrayFinish
Ancestors forPtrArrayFinish forPtrArraySnapshot forPtrRangeCallback whitelistForIterDynLoop
  forPtrRangeBackedge forPtrControl forPtrArrayInvariant forPtrRangeLanding
  stmtFragPtr compileEnv loweringStateRelDefs bodyPtrDefs loweringPosts
  finite_map venomState venomInst words arithmetic fragExec ptrDiscipline
  stmtSimForArrayFrame stmtSimForArrayLoop list exprLoweringProps stmtSimProps
  vyperState vyperEvalPreservesScopes forPtrSourceScopes localPtrsProps fragGasPathPtr

Theorem for_dynarray_backedge_restore_ptr:
  !sf Gf tf.
  dynarray_for_code func cenv bc ty stmts id et tv stride (Var bp)
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  s.vs_current_bb = incr_lbl /\ s.vs_inst_idx = 0 /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME snapshot /\
  lookup_scopes id es.scopes = NONE /\ k < LENGTH vs /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var bp s = SOME arr_base /\
  lookup_var p s = SOME dst /\ FLOOKUP G idx = NONE /\
  op_taint tn (Var idx) = {} /\ ptr_covers G tn p s sz /\
  ptr_covers G tn bp s (LENGTH vs * type_memory_size tv) /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  (!nm lo z. local_region cenv es.scopes s nm lo z ==>
    regions_disjoint (w2n dst) sz lo z) /\ ret_pc_ok cenv st s /\
  (!r q. cenv.ce_return_buf = SOME (PtrVar (Var r) q) ==> not_fresh_at st r) /\
  (!x. not_fresh_at st x ==> x <> idx /\ x <> nv) /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x s = SOME v) /\
  (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  lookup_var lv s = SOME (n2w (LENGTH vs)) /\
  FLOOKUP G lv = NONE /\ op_taint tn (Var lv) = {} /\
  sf = jump_to cond_lbl (update_var idx (n2w (SUC k))
    (update_var nv (n2w (SUC k)) s)) /\
  Gf = DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {idx}) /\
  tf = (tn with t_var := (tn.t_var |+ (nv,{})) |+ (idx,{})) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK sf) /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond_lbl st s0 G0 tn0 d name snapshot (SUC k) es Gf tf sf /\
  lookup_var lv sf = SOME (n2w (LENGTH vs)) /\
  FLOOKUP Gf lv = NONE /\ op_taint tf (Var lv) = {}
Proof
  rpt gen_tac >> strip_tac >>
  `(!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs nv) /\
   p <> idx /\ p <> nv /\ bp <> idx /\ bp <> nv /\
   lv <> idx /\ lv <> nv` by
    fs[dynarray_for_code_def, ALL_DISTINCT] >>
  `(!q. cenv.ce_return_buf <> SOME (PtrVar (Var idx) q)) /\
   (!q. cenv.ce_return_buf <> SOME (PtrVar (Var nv) q))` by metis_tac[] >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK sf)` by
    (gvs[] >> irule (SRULE [] for_array_increment_block_path_ptr) >> simp[] >>
     metis_tac[dynarray_for_code_def]) >>
  `stmt_state_rel ctx func cenv cx es sf /\
   ghost_inv d cenv cx es Gf tf sf` by
    (gvs[] >> irule (SRULE [] for_backedge_state_ghost_transport) >> simp[]) >>
  `ptr_covers Gf tf p sf sz /\ sf.vs_allocas = s.vs_allocas /\
   sf.vs_inst_idx = 0 /\ sf.vs_current_bb = cond_lbl /\
   sf.vs_halted = s.vs_halted /\
   (!nm lo z. local_region cenv es.scopes sf nm lo z <=>
     local_region cenv es.scopes s nm lo z) /\
   (!x. x <> idx /\ x <> nv ==> lookup_var x sf = lookup_var x s /\
     FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))` by
    (irule for_backedge_reserved_frame >> simp[] >> metis_tac[]) >>
  `ptr_covers Gf tf bp sf (LENGTH vs * type_memory_size tv)` by
    (irule (cj 1 for_backedge_reserved_frame) >> simp[] >> metis_tac[]) >>
  `(!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
      lookup_var x sf = SOME v) /\
   (!x. not_fresh_at st x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
      op_taint tf (Var x) = op_taint tn0 (Var x))` by
    (conj_tac >> rpt strip_tac >> metis_tac[]) >>
  `ret_pc_ok cenv st sf` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s`, `st`] >>
     simp[] >> rpt strip_tac >> metis_tac[]) >>
  simp[for_array_inv_ptr_def, array_loop_inv_def, eval_operand_def] >>
  gvs[lookup_var_def, update_var_def, jump_to_def, FLOOKUP_UPDATE,
      FLOOKUP_DRESTRICT, op_taint_def] >> first_assum ACCEPT_TAC
QED

Theorem for_dynarray_outer_not_local_ptr[local]:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  not_local_ptr bc (FEMPTY :: rest) p /\ lookup_scopes id rest = NONE ==>
  not_local_ptr cenv rest p
Proof
  simp[dynarray_for_code_def, not_local_ptr_def, lookup_scopes_def] >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >> `name <> id` by metis_tac[] >> metis_tac[]) >>
  qpat_x_assum `bc with <| ce_vars := _; ce_dynarray_capacity := _;
    ce_var_type := _ |> = cenv`
    (mp_tac o Q.AP_TERM `\ce:compile_env. ce.ce_imm_alloca`) >>
  simp[] >> metis_tac[]
QED

Theorem for_dynarray_callback_finish_ptr:
  dynarray_for_code func cenv bc ty stmts id et tv stride (Var bp)
    p sz ainst idx dv ov tot ep nv lv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  supported_stmts tops bindings stmts /\
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty stmts = SOME env' /\
  iterator_unmodified (Array (Name aty name)) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  lookup_scopes name esk.scopes = SOME snapshot /\
  lookup_scopes id esk.scopes = NONE /\ k < LENGTH vs /\
  not_local_ptr bc (FEMPTY :: esk.scopes) p /\
  cenv_top_ext cenv bc ((FEMPTY |+ (id,entry)) :: esk.scopes) /\
  eval_stmts cx stmts (esk with scopes :=
    (FEMPTY |+ (id,entry)) :: esk.scopes) = (res,ee) /\
  ee.scopes = sc :: rest /\ lookup_scopes id rest = NONE /\
  (!nm. nm IN FDOM sc ==> lookup_scopes nm rest = NONE) /\
  cenv_top_ext bc c3 ee.scopes /\ stmt_state_rel ctx func c3 cx ee s /\
  ghost_inv d c3 cx ee G tn s /\
  ptr_covers Gi ti p si sz /\
  FLOOKUP si.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  not_fresh_at sb0 p /\
  (!x w. not_fresh_at sb0 x /\ lookup_var x si = SOME w ==>
    lookup_var x s = SOME w) /\
  (!x. not_fresh_at sb0 x ==> FLOOKUP G x = FLOOKUP Gi x /\
    op_taint tn (Var x) = op_taint ti (Var x)) /\
  gas_path_ptr (cx_dead cx) lo ctx func PG Gi ti si steps G tn (OK s) /\
  st.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at st x ==> FLOOKUP Gi x = FLOOKUP G0 x /\
    op_taint ti (Var x) = op_taint tn0 (Var x)) /\
  ptr_covers G tn bp s (LENGTH vs * type_memory_size tv) /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var bp s = SOME arr_base /\
  lookup_var p s = SOME dst /\ FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  lookup_var lv s = SOME (n2w (LENGTH vs)) /\
  FLOOKUP G lv = NONE /\ op_taint tn (Var lv) = {} /\
  stmt_lands (InLoop exit_lbl incr_lbl) sb1 res s /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ (res = INL () ==> ~block_is_terminated sb1) /\
  ret_pc_ok cenv st s /\
  (!r q. cenv.ce_return_buf = SOME (PtrVar (Var r) q) ==> not_fresh_at st r) /\
  (!x. not_fresh_at st x ==> x <> idx /\ x <> nv) /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x s = SOME v) ==>
  ?t gf tf.
    gas_path_ptr D 0 ctx func PG G tn s 0 gf tf (OK t) /\
    (res = INR BreakException ==>
      for_array_done_ptr ctx func cenv cx exit_lbl st s0 G0 tn0 d
        (ee with scopes := rest) gf tf t) /\
    (res <> INR BreakException ==>
      for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
        cond_lbl st s0 G0 tn0 d name snapshot (SUC k)
        (ee with scopes := rest) gf tf t /\
      lookup_var lv t = SOME (n2w (LENGTH vs)) /\
      FLOOKUP gf lv = NONE /\ op_taint tf (Var lv) = {})
Proof
  strip_tac >>
  `ghost_inv d cenv cx (ee with scopes := rest) G tn s /\
   ptr_covers G tn p s sz /\
   FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
   (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
     op_taint tn (Var x) = op_taint tn0 (Var x))` by
    (irule for_array_callback_recovery_ptr >> conj_tac
     >- metis_tac[] >> conj_tac
     >- (goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >> simp[] >>
         metis_tac[]) >>
     goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> qexists_tac `sb0` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (ee with scopes := rest) s` by
    (irule array_body_scope_projection >> conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >> simp[] >> metis_tac[]) >>
  suspend "landing"
QED

Resume for_dynarray_callback_finish_ptr[landing]:
  `gas_path_ptr D 0 ctx func PG G tn s 0 G tn
    (OK (if res = INL () then jump_to incr_lbl s else s)) /\
   (if res = INL () then jump_to incr_lbl s else s).vs_inst_idx = 0 /\
   (res = INR BreakException ==> s.vs_current_bb = exit_lbl) /\
   (res <> INR BreakException ==>
     (if res = INL () then jump_to incr_lbl s else s).vs_current_bb = incr_lbl)` by
    (irule for_body_lands_path_ptr >> simp[] >>
     qexistsl_tac [`sb1`, `sj`] >> fs[dynarray_for_code_def]) >>
  qabbrev_tac `land = if res = INL () then jump_to incr_lbl s else s` >>
  `stmt_state_rel ctx func cenv cx (ee with scopes := rest) land /\
   ghost_inv d cenv cx (ee with scopes := rest) G tn land /\
   ptr_covers G tn p land sz /\ ~land.vs_halted = ~s.vs_halted /\
   land.vs_allocas = s.vs_allocas /\ (!x. lookup_var x land = lookup_var x s)` by
    (Cases_on `res = INL ()` >> gvs[Abbr `land`] >>
     rewrite_tac[stmt_state_rel_jump_to, ghost_inv_jump_to] >>
     fs[ptr_covers_def, jump_to_def, lookup_var_def, ghost_inv_jump_to]) >>
  `(!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x land = SOME v)` by metis_tac[] >>
  Cases_on `res = INR BreakException`
  >- (qexistsl_tac [`land`, `G`, `tn`] >>
      simp[for_array_done_ptr_def, Abbr `land`]) >>
  suspend "next"
QED
Resume for_dynarray_callback_finish_ptr[next]:
  `lookup_scopes name rest = SOME snapshot` by
    (irule for_array_callback_pop_snapshot_ptr >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >> simp[] >> metis_tac[]) >>
  `ret_pc_ok cenv st land` by
    (Cases_on `res = INL ()` >> gvs[Abbr `land`, ret_pc_ok_jump_to]) >>
  `ptr_covers G tn bp land (LENGTH vs * type_memory_size tv)` by
    (Cases_on `res = INL ()` >> gvs[Abbr `land`, ptr_covers_def,
       jump_to_def, lookup_var_def]) >>
  `lookup_var idx land = SOME (n2w k) /\ lookup_var bp land = SOME arr_base /\
   lookup_var p land = SOME dst /\
   lookup_var lv land = SOME (n2w (LENGTH vs)) /\
   FLOOKUP land.vs_allocas ainst.inst_id = SOME (w2n dst,sz)` by simp[] >>
  `MAP FDOM rest = MAP FDOM esk.scopes` by
    (drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def]) >>
  `not_local_ptr cenv rest p` by
    (irule not_local_ptr_scope_domains >>
     qexists_tac `esk.scopes` >> simp[] >>
     irule for_dynarray_outer_not_local_ptr >>
     goal_assum (drule_at (Pat `dynarray_for_code _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `!nm lo z. local_region cenv rest land nm lo z ==>
    regions_disjoint (w2n dst) sz lo z` by
    (rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     qexistsl_tac [`func`, `ainst`, `p`] >>
     fs[stmt_state_rel_def, state_rel_def, dynarray_for_code_def]) >>
  mp_tac (SRULE [] (Q.INST
    [`es` |-> `ee with scopes := rest`, `s` |-> `land`]
    for_dynarray_backedge_restore_ptr)) >>
  (impl_tac >- (simp[] >>
    qpat_x_assum `!nm lo z. local_region _ _ land nm lo z ==> _` mp_tac >> simp[])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn land 0 gf tf (OK fin)` >>
  qexistsl_tac [`fin`, `gf`, `tf`] >> simp[] >>
  drule_all gas_path_ptr_then >> simp[Abbr `fin`, jump_to_def, lookup_var_def]
QED
Finalise for_dynarray_callback_finish_ptr
