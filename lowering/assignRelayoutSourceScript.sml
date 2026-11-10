(* Owned RHS buffers are separated from live destinations, including borrowed locals. *)
Theory assignRelayoutSource
Ancestors
  annassignRelayoutSource allocaSiteResource exprLoweringProps loweringPosts
  compileEnv loweringStateRelDefs

Theorem expr_post_live_destination_source:
  !ctx func cenv cx e es sa sb s0 es' v op s sty stv
   id entry p cap dw dlen.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    post_value_type cenv e = sty /\ sty <> expr_type e /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ ~is_word_type sty /\
    val_footprint stv v = type_memory_size stv /\ 0 < type_memory_size stv /\
    lookup_scopes id es'.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
    lookup_var p s = SOME dw /\ dlen <= cap ==>
    ?sw. eval_operand op s = SOME sw /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      local_backed func p s (w2n dw) cap /\
      w2n dw + cap <= s.vs_alloca_next /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + dlen < dimword (:256) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + dlen <= w2n sw)
Proof
  rpt gen_tac >> strip_tac >>
  gnvs[expr_post_def] >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `local_backed func p s (w2n dw) cap /\
   w2n dw + cap <= s.vs_alloca_next` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     qpat_x_assum `!name entry' p' sz. _` (qspecl_then [`id`,`entry`,`p`,`cap`] mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `local_region cenv es'.scopes s id (w2n dw) cap` by
    (simp[local_region_def] >> metis_tac[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  qpat_x_assum `expr_val_own _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_own_def] >> strip_tac >>
  `b + sz <= s.vs_alloca_next` by
    (irule alloca_site_registered_below >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  `b + sz <= w2n dw \/ w2n dw + cap <= b` by metis_tac[] >>
  qexists_tac `w` >> simp[] >>
  fs[expr_val_rel_def]
QED
