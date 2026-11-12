(* Pointwise composition at the RawLog topic boundary. *)
Theory bodyFullRawLogTopicsPost
Ancestors
  bodyFullPreds bodySimFull bodyRawLogArgPre exprSimSource exprSimProps
  exprSimWordArgs loweringPosts bodyPtrDefs exprLoweringProps
  vyperInterpreter vyperState vyperAST list finite_map
  loweringStateRelDefs loweringShapeDefs

Theorem raw_log_topics_ghost_cons[local]:
  expr_body_pre cenv cx env
    (Call ann RawLog
      [Builtin a (MakeArray elem bd) (pre ++ e::rest); data] dflt) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := xs ++ tail) = (INL v, mid with gas_obs := tail)) /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  expr_post H ctx func cenv cx e es sa sm s mid v op u /\
  ghost_kept_at lo cenv es sa G0 tn0 s G1 tn1 /\
  ghost_kept_at lo cenv mid sm G1 tn1 u G tn ==>
  ghost_kept_at lo cenv es sa G0 tn0 s G tn
Proof
  strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
     strip_tac >> drule (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `!n b sz. local_region cenv es.scopes s n b sz <=>
             local_region cenv mid.scopes u n b sz` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule local_region_frame_fwd >>
         qexistsl_tac [`s`, `sa`, `es.scopes`] >> gvs[expr_post_def] >> metis_tac[]) >>
     strip_tac >> irule local_region_frame >>
     conj_tac
     >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`, `mid.scopes`, `u`] >>
     gvs[expr_post_def] >> metis_tac[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def, ghost_kept_at_def] >>
  fs[ghost_kept_at_def] >> rpt strip_tac
  >- metis_tac[not_fresh_at_mono]
  >- metis_tac[not_fresh_at_mono]
  >- (`aid < sm.cs_next_id` by decide_tac >>
      `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `i IN tn1.t_mem` by
        (qpat_x_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = _ /\ _ ==> _` irule >>
         reverse conj_tac >- simp[] >>
         qexistsl_tac [`aid`, `off`, `sz`] >> asm_rewrite_tac[]) >>
      qpat_x_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _` irule >>
      reverse conj_tac >- simp[] >>
      qexistsl_tac [`aid`, `off`, `sz`] >> asm_rewrite_tac[]) >>
  metis_tac[]
QED
