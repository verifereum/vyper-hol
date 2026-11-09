(* Array callback resources are recovered using only the actual older-variable
   frame. Memory taint may change arbitrarily during the source body. *)
Theory forPtrArrayFinish
Ancestors forPtrArrayInvariant forPtrRangeCallback stmtSimForArrayLoop
  stmtFragPtr compileEnv bodyPtrDefs loweringPosts finite_map
  forPtrAllocationFrame gasSummaryComposePtr stmtSimProps stmtLowering vyperState forPtrScope forPtrSourceScopes
  exprLoweringProps localPtrsProps vyperEvalPreservesScopes
  forPtrRangeLanding forPtrRangeBackedge forPtrControl venomState fragGasPathPtr
  venomInst words arithmetic fragExec ptrDiscipline stmtSimForArrayFrame
  vyperInterpreter

Theorem for_array_callback_control_ptr:
  array_for_code func cenv bc ty stmts id et tv n stride (Var bp)
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  sa.cs_next_var <= sb0.cs_next_var /\
  ptr_covers G0 tn0 p s0 sz /\ ptr_covers G0 tn0 bp s0 extent /\
  lookup_var idx s0 = SOME counter /\
  FLOOKUP G0 idx = NONE /\ op_taint tn0 (Var idx) = {} /\
  (!x w. not_fresh_at sb0 x /\ lookup_var x s0 = SOME w ==>
    lookup_var x t = SOME w) /\
  (!x. not_fresh_at sb0 x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  ptr_covers G tn p t sz /\ ptr_covers G tn bp t extent /\
  lookup_var idx t = SOME counter /\
  FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {}
Proof
  strip_tac >>
  `not_fresh_at sa p /\ not_fresh_at sa bp /\ not_fresh_at sa idx` by
    fs[array_for_code_def] >>
  `not_fresh_at sb0 p /\ not_fresh_at sb0 bp /\ not_fresh_at sb0 idx` by
    metis_tac[not_fresh_at_mono] >>
  conj_tac
  >- (irule callback_old_pointer_coverage >> goal_assum (drule_at Any) >>
      metis_tac[]) >>
  conj_tac
  >- (irule callback_old_pointer_coverage >> goal_assum (drule_at Any) >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem for_array_callback_contract_ptr:
  array_for_code func cenv bc ty stmts id et tv n stride (Var bp)
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  sa.cs_next_var <= sb0.cs_next_var /\
  stmt_frag_ptr d ctx PG func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) es /\
  stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = (bc',sb1) /\
  ~ctx_has_dalloca ctx /\ ~bc.ce_is_ctor /\ ret_pc_ok bc sb0 s0 /\
  (!x z. bc.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sb0 x) /\
  gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit_lbl incr_lbl)) es /\
  stmt_state_rel ctx func bc cx es s0 /\ ghost_inv d bc cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sb0.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sb0.cs_current_insts /\
  ptr_covers G0 tn0 p s0 sz /\ ptr_covers G0 tn0 bp s0 extent /\
  lookup_var idx s0 = SOME counter /\
  FLOOKUP G0 idx = NONE /\ op_taint tn0 (Var idx) = {} ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG (eval_stmts cx stmts)
    (es,s0,G0,tn0)
    (\res ee G tn t. ((?c3.
      stmt_lands (InLoop exit_lbl incr_lbl) sb1 res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb1 /\ c3 = bc') /\
      cenv_top_ext bc c3 ee.scopes /\ stmt_state_rel ctx func c3 cx ee t /\
      ghost_inv d c3 cx ee G tn t /\
      (!x w. not_fresh_at sb0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!x. not_fresh_at sb0 x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x))) /\
      ptr_covers G tn p t sz /\ ptr_covers G tn bp t extent /\
      lookup_var idx t = SOME counter /\ FLOOKUP G idx = NONE /\
      op_taint tn (Var idx) = {}) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b))
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> ho_match_mp_tac gas_outcome_ptr_allocation_frame >>
  `fn_has_code sb0 sb1 func /\ local_ptrs_reserved bc sb0 /\
   ~block_is_terminated sb0 /\ fn_inst_ids_distinct func` by fs[array_for_code_def] >>
  qpat_x_assum `stmt_frag_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_ptr_def] >> disch_then drule_all >> strip_tac >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  reverse conj_tac >- simp[] >> rpt gen_tac >>
  simp_tac bool_ss [] >> strip_tac >>
  irule for_array_callback_control_ptr >> goal_assum (drule_at Any) >> metis_tac[]
QED

(* Arbitrary head scopes serve both preparation and cleanup. *)
Theorem for_array_code_top_ext_ptr:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  lookup_scopes id rest = NONE ==>
  cenv_top_ext cenv bc (sc :: rest)
Proof
  strip_tac >> fs[array_for_code_def, cenv_top_ext_def] >>
  rpt strip_tac >> `n' = id` by metis_tac[] >> gvs[] >> metis_tac[]
QED

Theorem for_array_code_outer_not_local_ptr:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  not_local_ptr bc (FEMPTY :: rest) p /\ lookup_scopes id rest = NONE ==>
  not_local_ptr cenv rest p
Proof
  simp[array_for_code_def, not_local_ptr_def, lookup_scopes_def] >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >> `name <> id` by metis_tac[] >> metis_tac[]) >>
  qpat_x_assum `bc with <| ce_vars := _; ce_dynarray_capacity := _;
    ce_var_type := _ |> = cenv`
    (mp_tac o Q.AP_TERM `\ce:compile_env. ce.ce_imm_alloca`) >>
  simp[] >> metis_tac[]
QED

Theorem for_array_callback_outer_state_ptr:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  lookup_scopes id esk.scopes = NONE /\
  not_local_ptr bc (FEMPTY :: esk.scopes) p /\
  eval_stmts cx stmts (esk with scopes :=
    (FEMPTY |+ (id,entry)) :: esk.scopes) = (res,ee) /\
  cenv_top_ext bc c3 ee.scopes /\ stmt_state_rel ctx func c3 cx ee t /\
  ghost_inv d c3 cx ee G tn t /\
  FLOOKUP t.vs_allocas ainst.inst_id = SOME (w2n w,sz) ==>
  ?sc rest. ee.scopes = sc :: rest /\
    lookup_scopes id rest = NONE /\
    stmt_state_rel ctx func cenv cx (ee with scopes := rest) t /\
    ghost_inv d cenv cx (ee with scopes := rest) G tn t /\
    (!name lo z. local_region cenv rest t name lo z ==>
      regions_disjoint (w2n w) sz lo z)
Proof
  strip_tac >> drule_all fresh_body_scope_shape >> strip_tac >>
  qexistsl_tac [`sc`, `rest`] >> simp[] >>
  `cenv_top_ext cenv bc ((FEMPTY |+ (id,entry)) :: esk.scopes)` by
    (metis_tac[for_array_code_top_ext_ptr]) >>
  `stmt_state_rel ctx func cenv cx (ee with scopes := rest) t` by
    (irule array_body_scope_projection >> conj_tac
     >- (qexists_tac `sc` >> simp[]) >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >> simp[] >> metis_tac[]) >>
  `ghost_inv d cenv cx (ee with scopes := rest) G tn t` by
    (irule ghost_inv_body_scope_projection >> conj_tac
     >- (qexists_tac `sc` >> simp[]) >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >> simp[] >> metis_tac[]) >>
  simp[] >>
  `not_local_ptr cenv esk.scopes p` by
    (drule_all for_array_code_outer_not_local_ptr >> simp[]) >>
  `MAP FDOM rest = MAP FDOM esk.scopes` by
    (drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def]) >>
  `not_local_ptr cenv rest p` by
    (irule not_local_ptr_scope_domains >> metis_tac[]) >>
  `alloca_inv t /\ local_ptrs_rel func cenv rest t` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `fn_inst_ids_distinct func /\ MEM ainst (fn_insts func) /\
   ainst.inst_outputs = [p]` by fs[array_for_code_def] >>
  rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
  goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
  qexistsl_tac [`func`, `ainst`, `p`] >> simp[]
QED

Theorem for_array_callback_landing_ptr:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  lookup_scopes id esk.scopes = NONE /\
  not_local_ptr bc (FEMPTY :: esk.scopes) p /\
  eval_stmts cx stmts (esk with scopes :=
    (FEMPTY |+ (id,entry)) :: esk.scopes) = (res,ee) /\
  cenv_top_ext bc c3 ee.scopes /\ stmt_state_rel ctx func c3 cx ee s /\
  ghost_inv d c3 cx ee G tn s /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n a,sz) /\
  ptr_covers G tn p s sz /\ ptr_covers G tn bp s extent /\
  stmt_lands (InLoop exit_lbl incr_lbl) sb1 res s /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ (res = INL () ==> ~block_is_terminated sb1) ==>
  ?sc rest t.
    ee.scopes = sc :: rest /\ lookup_scopes id rest = NONE /\
    t = (if res = INL () then jump_to incr_lbl s else s) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK t) /\
    t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    (res = INR BreakException ==> t.vs_current_bb = exit_lbl) /\
    (res <> INR BreakException ==> t.vs_current_bb = incr_lbl) /\
    stmt_state_rel ctx func cenv cx (ee with scopes := rest) t /\
    ghost_inv d cenv cx (ee with scopes := rest) G tn t /\
    ptr_covers G tn p t sz /\ ptr_covers G tn bp t extent /\
    t.vs_allocas = s.vs_allocas /\ (!x. lookup_var x t = lookup_var x s) /\
    (!name lo z. local_region cenv rest t name lo z ==>
      regions_disjoint (w2n a) sz lo z)
Proof
  strip_tac >> drule_all for_array_callback_outer_state_ptr >> strip_tac >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 G tn
    (OK (if res = INL () then jump_to incr_lbl s else s)) /\
   (if res = INL () then jump_to incr_lbl s else s).vs_inst_idx = 0 /\
   (res = INR BreakException ==> s.vs_current_bb = exit_lbl) /\
   (res <> INR BreakException ==>
     (if res = INL () then jump_to incr_lbl s else s).vs_current_bb = incr_lbl)` by
    (irule for_body_lands_path_ptr >> simp[] >>
     qexistsl_tac [`sb1`, `sj`] >> fs[array_for_code_def]) >>
  qexistsl_tac [`sc`, `rest`,
    `if res = INL () then jump_to incr_lbl s else s`] >> simp[] >>
  Cases_on `res = INL ()` >> gvs[] >>
  rewrite_tac[stmt_state_rel_jump_to] >>
  fs[local_region_def, ptr_covers_def, jump_to_def,
     lookup_var_def, ghost_inv_jump_to] >> first_assum ACCEPT_TAC
QED

Theorem for_array_increment_block_path_ptr:
  lookup_block incr_lbl func.fn_blocks =
    SOME <| bb_label := incr_lbl;
      bb_instructions := [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
        mk_inst i2 ASSIGN [Var nv] [idx];
        mk_inst i3 JMP [Label cond_lbl] []] |> /\
  s.vs_current_bb = incr_lbl /\ s.vs_inst_idx = 0 /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_var idx s = SOME (n2w k) /\
  FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {idx}))
    (tn with t_var := (tn.t_var |+ (nv,{})) |+ (idx,{}))
    (OK (jump_to cond_lbl (update_var idx (n2w (SUC k))
      (update_var nv (n2w (SUC k)) s))))
Proof
  strip_tac >> rewrite_tac[GSYM word_add_n2w, ADD1] >>
  irule for_counter_backedge_path_ptr >> simp[] >>
  conj_tac
  >- (qexistsl_tac [`i1`, `i2`] >> simp[get_instruction_def]) >>
  qexistsl_tac [`(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := incr_lbl;
      cs_current_insts := [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
        mk_inst i2 ASSIGN [Var nv] [idx]]; cs_next_id := i3 |>`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := incr_lbl;
      cs_current_insts := [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
        mk_inst i2 ASSIGN [Var nv] [idx];
        mk_inst i3 JMP [Label cond_lbl] []] |>`] >>
  simp[fn_has_code_def, emitted_blocks_def]
QED

Theorem for_array_backedge_restore_ptr:
  !sf Gf tf.
  array_for_code func cenv bc ty stmts id et tv n stride (Var bp)
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
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
  sf = jump_to cond_lbl (update_var idx (n2w (SUC k))
    (update_var nv (n2w (SUC k)) s)) /\
  Gf = DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {idx}) /\
  tf = (tn with t_var := (tn.t_var |+ (nv,{})) |+ (idx,{})) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK sf) /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond_lbl st s0 G0 tn0 d name snapshot (SUC k) es Gf tf sf
Proof
  rpt gen_tac >> strip_tac >>
  `(!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs nv) /\
   p <> idx /\ p <> nv /\ bp <> idx /\ bp <> nv` by
    fs[array_for_code_def] >>
  `(!q. cenv.ce_return_buf <> SOME (PtrVar (Var idx) q)) /\
   (!q. cenv.ce_return_buf <> SOME (PtrVar (Var nv) q))` by metis_tac[] >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK sf)` by
    (gvs[] >> irule (SRULE [] for_array_increment_block_path_ptr) >> simp[] >>
     metis_tac[array_for_code_increment]) >>
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

Theorem for_array_callback_pop_snapshot_ptr:
  supported_stmts tops bindings stmts /\
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty stmts = SOME env' /\
  iterator_unmodified (Array (Name aty name)) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  eval_stmts cx stmts (es with scopes := tmp :: es.scopes) = (res,ee) /\
  ee.scopes = sc :: rest /\ lookup_scopes name es.scopes = SOME snapshot ==>
  lookup_scopes name rest = SOME snapshot
Proof
  strip_tac >>
  `finally (eval_stmts cx stmts) pop_scope (es with scopes := tmp :: es.scopes) =
    (res,ee with scopes := rest)` by
    (Cases_on `res` >>
     simp[finally_def, pop_scope_def, ignore_bind_def, bind_def, return_def, raise_def]) >>
  drule_at (Pat `finally _ _ _ = _`) array_body_pop_snapshot >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem for_array_callback_finish_ptr:
  array_for_code func cenv bc ty stmts id et tv n stride (Var bp)
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  supported_stmts tops bindings stmts /\
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty stmts = SOME env' /\
  iterator_unmodified (Array (Name aty name)) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  lookup_scopes name esk.scopes = SOME snapshot /\
  lookup_scopes id esk.scopes = NONE /\ k < LENGTH vs /\
  not_local_ptr bc (FEMPTY :: esk.scopes) p /\
  eval_stmts cx stmts (esk with scopes :=
    (FEMPTY |+ (id,entry)) :: esk.scopes) = (res,ee) /\
  cenv_top_ext bc c3 ee.scopes /\ stmt_state_rel ctx func c3 cx ee s /\
  ghost_inv d c3 cx ee G tn s /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ptr_covers G tn p s sz /\ ptr_covers G tn bp s (LENGTH vs * type_memory_size tv) /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var bp s = SOME arr_base /\
  lookup_var p s = SOME dst /\ FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  stmt_lands (InLoop exit_lbl incr_lbl) sb1 res s /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ (res = INL () ==> ~block_is_terminated sb1) /\
  ret_pc_ok cenv st s /\
  (!r q. cenv.ce_return_buf = SOME (PtrVar (Var r) q) ==> not_fresh_at st r) /\
  (!x. not_fresh_at st x ==> x <> idx /\ x <> nv) /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x s = SOME v) /\
  (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  ?sc rest t gf tf.
    ee.scopes = sc :: rest /\
    gas_path_ptr D 0 ctx func PG G tn s 0 gf tf (OK t) /\
    (res = INR BreakException ==>
      for_array_done_ptr ctx func cenv cx exit_lbl st s0 G0 tn0 d
        (ee with scopes := rest) gf tf t) /\
    (res <> INR BreakException ==>
      for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
        cond_lbl st s0 G0 tn0 d name snapshot (SUC k)
        (ee with scopes := rest) gf tf t)
Proof
  strip_tac >> drule_all for_array_callback_landing_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK land)` >>
  `(!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x land = SOME v)` by metis_tac[] >>
  Cases_on `res = INR BreakException`
  >- (qexistsl_tac [`sc`, `rest`, `land`, `G`, `tn`] >>
      simp[for_array_done_ptr_def]) >>
  suspend "next"
QED

Resume for_array_callback_finish_ptr[next]:
  `lookup_scopes name rest = SOME snapshot` by
    (irule for_array_callback_pop_snapshot_ptr >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >> simp[] >> metis_tac[]) >>
  `ret_pc_ok cenv st land` by
    (Cases_on `res = INL ()` >> gvs[Abbr `land`, ret_pc_ok_jump_to]) >>
  `lookup_var idx land = SOME (n2w k) /\ lookup_var bp land = SOME arr_base /\
   lookup_var p land = SOME dst /\
   FLOOKUP land.vs_allocas ainst.inst_id = SOME (w2n dst,sz)` by simp[] >>
  mp_tac (SRULE [] (Q.INST
    [`es` |-> `ee with scopes := rest`, `s` |-> `land`]
    for_array_backedge_restore_ptr)) >>
  (impl_tac >- (simp[] >>
    qpat_x_assum `!nm lo z. local_region _ _ land nm lo z ==> _` mp_tac >> simp[])) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn land 0 gf tf (OK fin)` >>
  qexistsl_tac [`sc`, `rest`, `fin`, `gf`, `tf`] >> simp[] >>
  drule_all gas_path_ptr_then >> simp[]
QED
Finalise for_array_callback_finish_ptr
