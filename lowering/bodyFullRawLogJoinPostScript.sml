(* Pointwise post transport for a RawLog continuation after its topics. *)
Theory bodyFullRawLogJoinPost
Ancestors
  bodyPtrDefs exprSimWordArgs exprSimProps loweringPosts
  loweringStateRelDefs stmtSimDefs exprLoweringProps loweringShapeDefs compileEnv vyperAST list finite_map arithmetic

Theorem raw_log_topics_continuation_post:
  stmt_state_rel H ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  wb_frame cenv es mid sa s u /\
  ghost_kept_at lo cenv es sa G0 tn0 s Gm tnm /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  expr_has_effect (Call ann RawLog [Builtin a (MakeArray elem bd) topics;data] dflt) /\
  expr_post H ctx func cenv cx
    (Call ann RawLog [Builtin a (MakeArray elem bd) topics;data] dflt)
    mid sm sb u ee v (Lit 0w) t /\
  expr_store_bound cx
    (expr_type (Call ann RawLog [Builtin a (MakeArray elem bd) topics;data] dflt))
    v (Lit 0w) t /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ u.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx ee G tn t /\
  ptr_val_ok cx
    (post_value_type cenv (Call ann RawLog [Builtin a (MakeArray elem bd) topics;data] dflt))
    v (Lit 0w) G tn t /\
  (~is_word_type (post_value_type cenv
      (Call ann RawLog [Builtin a (MakeArray elem bd) topics;data] dflt)) ==>
    ptr_buf_ok cenv (Call ann RawLog [Builtin a (MakeArray elem bd) topics;data] dflt)
      (Lit 0w) G t) /\
  ghost_kept_at lo cenv mid sm Gm tnm u G tn ==>
  expr_post H ctx func cenv cx
    (Call ann RawLog [Builtin a (MakeArray elem bd) topics;data] dflt)
    es sa sb s ee v (Lit 0w) t /\
  expr_store_bound cx
    (expr_type (Call ann RawLog [Builtin a (MakeArray elem bd) topics;data] dflt))
    v (Lit 0w) t /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx ee G tn t /\
  ptr_val_ok cx
    (post_value_type cenv (Call ann RawLog [Builtin a (MakeArray elem bd) topics;data] dflt))
    v (Lit 0w) G tn t /\
  (~is_word_type (post_value_type cenv
      (Call ann RawLog [Builtin a (MakeArray elem bd) topics;data] dflt)) ==>
    ptr_buf_ok cenv (Call ann RawLog [Builtin a (MakeArray elem bd) topics;data] dflt)
      (Lit 0w) G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s G tn
Proof
  strip_tac >>
  `wb_frame cenv mid ee sm u t` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es ee sa s t` by
    (irule wb_frame_trans >> simp[] >> conj_tac
     >- (qexistsl [`mid`,`sm`,`u`] >> simp[]) >>
     qexistsl [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!n b sz. local_region cenv mid.scopes u n b sz <=>
            local_region cenv es.scopes s n b sz` by
    (rpt gen_tac >> eq_tac >> strip_tac
     >- (irule local_region_frame >> metis_tac[wb_frame_def]) >>
     irule local_region_frame_fwd >> metis_tac[wb_frame_def]) >>
  conj_tac
  >- (fs[expr_post_def, wb_frame_def] >> conj_tac
      >- (irule expr_val_at_start_mono >> goal_assum (drule_at Any) >> simp[]) >>
      metis_tac[]) >>
  simp[] >>
  fs[ghost_kept_at_def, wb_frame_def] >>
  conj_tac >- (rpt strip_tac >>
    `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    `aid < sm.cs_next_id` by decide_tac >>
    `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
    `i IN tnm.t_mem` by
      (qpat_x_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = _ /\ _ ==> _`
         (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >> simp[] >> metis_tac[]) >>
    qpat_x_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _`
      (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED
