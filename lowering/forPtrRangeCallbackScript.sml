(* Recovery facts at the actual For body callback boundary.  Coverage
   depends only on the reserved pointer's value and variable ghosts;
   no memory-taint frame is required of the body. *)
Theory forPtrRangeCallback
Ancestors forPtrScope forPtrBytes forPtrAllocationFrame forPtrSourceScopes
  stmtSimForLoop bodyPtrDefs loweringPosts gasSummaryComposePtr
  compileEnv vyperEvalPreservesScopes localPtrsProps exprLoweringProps
  stmtSimForArrayLoop vyperState

Theorem for_code_callback_reserved:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj ==>
  !x. MEM x [cv;ev;p] ==> not_fresh_at sb0 x
Proof
  simp[for_code_def] >> metis_tac[]
QED

Theorem callback_old_pointer_coverage:
  not_fresh_at sa p /\ ptr_covers G0 tn0 p s0 sz /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x t = SOME w) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  ptr_covers G tn p t sz
Proof
  strip_tac >>
  `lookup_var p t = lookup_var p s0` by
    (fs[ptr_covers_def] >> metis_tac[]) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> strip_tac >>
  drule_all for_ptr_covers_transport >> simp[]
QED

Theorem for_range_callback_control:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  ptr_covers G0 tn0 p s0 sz /\
  lookup_var cv s0 = SOME c /\ lookup_var ev s0 = SOME e /\
  FLOOKUP G0 cv = NONE /\ FLOOKUP G0 ev = NONE /\
  op_taint tn0 (Var cv) = {} /\ op_taint tn0 (Var ev) = {} /\
  (!x w. not_fresh_at sb0 x /\ lookup_var x s0 = SOME w ==>
    lookup_var x t = SOME w) /\
  (!x. not_fresh_at sb0 x ==>
    FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  ptr_covers G tn p t sz /\
  lookup_var cv t = SOME c /\ lookup_var ev t = SOME e /\
  FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
  op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {}
Proof
  strip_tac >> drule for_code_callback_reserved >> strip_tac >>
  `not_fresh_at sb0 p /\ not_fresh_at sb0 cv /\ not_fresh_at sb0 ev` by
    metis_tac[listTheory.MEM] >>
  conj_tac >- (irule callback_old_pointer_coverage >>
    goal_assum (drule_at Any) >> metis_tac[]) >>
  metis_tac[]
QED

Theorem for_code_pushed_top_ext:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  lookup_scopes id rest = NONE ==>
  cenv_top_ext cenv bc ((FEMPTY |+ (id,entry)) :: rest)
Proof
  simp[for_code_def, cenv_top_ext_def] >> strip_tac >>
  rpt strip_tac >> `n = id` by metis_tac[] >> gvs[] >> metis_tac[]
QED

Theorem for_range_callback_scope:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  ei.scopes = (FEMPTY |+ (id,entry)) :: esk.scopes /\
  lookup_scopes id esk.scopes = NONE /\
  eval_stmts cx stmts ei = (res,ee) /\
  cenv_top_ext bc c3 ee.scopes /\
  ghost_inv d c3 cx ee G tn t /\ ee.scopes = sc :: rest /\
  (!name. name IN FDOM sc ==> lookup_scopes name rest = NONE) ==>
  ghost_inv d cenv cx (ee with scopes := rest) G tn t
Proof
  strip_tac >>
  `cenv_top_ext cenv bc ei.scopes` by
    (drule_all for_code_pushed_top_ext >> simp[]) >>
  irule ghost_inv_body_scope_projection >> conj_tac
  >- (qexists_tac `sc` >> simp[]) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

(* This instantiates the real callback judgment, not an abstract round.
   The original post is retained verbatim alongside recovered control facts. *)
Theorem for_range_callback_contract:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  stmt_frag_ptr d ctx PG func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) es /\
  stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = (bc',sb1) /\
  ~ctx_has_dalloca ctx /\ ~bc.ce_is_ctor /\ ret_pc_ok bc sb0 s0 /\
  (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb0 x) /\
  gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit_lbl incr_lbl)) es /\
  stmt_state_rel ctx func bc cx es s0 /\ ghost_inv d bc cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sb0.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sb0.cs_current_insts /\
  ptr_covers G0 tn0 p s0 sz /\
  lookup_var cv s0 = SOME c /\ lookup_var ev s0 = SOME e /\
  FLOOKUP G0 cv = NONE /\ FLOOKUP G0 ev = NONE /\
  op_taint tn0 (Var cv) = {} /\ op_taint tn0 (Var ev) = {} ==>
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
      ptr_covers G tn p t sz /\
      lookup_var cv t = SOME c /\ lookup_var ev t = SOME e /\
      FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
      op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {}) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b))
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> ho_match_mp_tac gas_outcome_ptr_allocation_frame >>
  `fn_has_code sb0 sb1 func /\ local_ptrs_reserved bc sb0 /\
   ~block_is_terminated sb0 /\ fn_inst_ids_distinct func` by fs[for_code_def] >>
  qpat_x_assum `stmt_frag_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_ptr_def] >> disch_then drule_all >> strip_tac >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  reverse conj_tac >- simp[] >> rpt gen_tac >>
  simp_tac bool_ss [] >> strip_tac >>
  irule for_range_callback_control >> goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem not_local_ptr_scope_domains:
  not_local_ptr cenv before p /\ MAP FDOM before = MAP FDOM after ==>
  not_local_ptr cenv after p
Proof
  simp[not_local_ptr_def] >> strip_tac >> simp[] >> rpt strip_tac >>
  Cases_on `lookup_scopes name before`
  >- (drule_all lookup_scopes_none_map_fdom >> simp[]) >>
  metis_tac[]
QED

Theorem for_code_outer_not_local:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  not_local_ptr bc (FEMPTY :: rest) p /\ lookup_scopes id rest = NONE ==>
  not_local_ptr cenv rest p
Proof
  simp[for_code_def, not_local_ptr_def, lookup_scopes_def] >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >> `name <> id` by metis_tac[] >> metis_tac[]) >>
  qpat_x_assum `bc with <| ce_vars := _; ce_dynarray_capacity := _;
    ce_var_type := _ |> = cenv`
    (mp_tac o Q.AP_TERM `\ce:compile_env. ce.ce_imm_alloca`) >>
  simp[] >> metis_tac[]
QED

Theorem for_range_callback_outer_state:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
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
    (metis_tac[for_code_pushed_top_ext]) >>
  `stmt_state_rel ctx func cenv cx (ee with scopes := rest) t` by
    (irule array_body_scope_projection >> conj_tac
     >- (qexists_tac `sc` >> simp[]) >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  `ghost_inv d cenv cx (ee with scopes := rest) G tn t` by
    (irule ghost_inv_body_scope_projection >> conj_tac
     >- (qexists_tac `sc` >> simp[]) >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  simp[] >>
  `not_local_ptr cenv esk.scopes p` by
    (drule_all for_code_outer_not_local >> simp[]) >>
  `MAP FDOM rest = MAP FDOM esk.scopes` by
    (drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def]) >>
  `not_local_ptr cenv rest p` by
    (irule not_local_ptr_scope_domains >> metis_tac[]) >>
  `alloca_inv t /\ local_ptrs_rel func cenv rest t` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `fn_inst_ids_distinct func /\ MEM ainst (fn_insts func) /\
   ainst.inst_outputs = [p]` by fs[for_code_def] >>
  rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
  goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
  qexistsl_tac [`func`, `ainst`, `p`] >> simp[]
QED
