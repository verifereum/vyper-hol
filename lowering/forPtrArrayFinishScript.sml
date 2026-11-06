(* Array callback resources are recovered using only the actual older-variable
   frame. Memory taint may change arbitrarily during the source body. *)
Theory forPtrArrayFinish
Ancestors forPtrArrayInvariant forPtrRangeCallback stmtSimForArrayLoop
  stmtFragPtr compileEnv bodyPtrDefs loweringPosts finite_map
  forPtrAllocationFrame gasSummaryComposePtr stmtSimProps stmtLowering vyperState forPtrScope forPtrSourceScopes
  exprLoweringProps localPtrsProps vyperEvalPreservesScopes

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
