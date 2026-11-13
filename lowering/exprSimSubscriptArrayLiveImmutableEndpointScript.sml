(* Frame composition for a currently represented immutable base. *)
Theory exprSimSubscriptArrayLiveImmutableEndpoint
Ancestors
  exprSimSubscriptArrayEndpoint exprSimWordArgs exprSimHash exprSimProps exprSimVVFrame
  exprSimSubscriptArrayFrame loweringPosts exprLoweringProps compileEnv

Theorem live_immutable_base_endpoint:
  vv_post ctx func cenv cx obj es sa sb s0 t r (LocatedValue (ArrayT et bd) p) u /\
  expr_post ctx func cenv cx idx t sb sc u ee iv iop v /\
  expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  is_word_type (expr_type idx) /\ p.ptr_location = LocCode /\
  r = PlaceR (ImmutablePlace src id path) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sd.cs_next_id /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM t.scopes /\
  (!x w. not_fresh_at sc x /\ lookup_var x v = SOME w ==> lookup_var x q = SOME w) /\
  (!aid a. FLOOKUP v.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
  q.vs_memory = v.vs_memory /\ stmt_state_rel ctx func cenv cx ee q /\
  vv_holds cenv cx (ArrayT et bd) r (LocatedValue (ArrayT et bd) p) ee q /\
  vv_place_ptr cenv cx ee q r (LocatedValue (ArrayT et bd) p) ==>
  vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee r
    (LocatedValue (ArrayT et bd) p) q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_post ctx func cenv cx idx t sb sd u ee iv iop q` by
    (irule word_expr_post_readonly_tail >> simp[] >>
     qexistsl_tac [`v`,`sc`] >> simp[]) >>
  `wb_frame cenv es t sa s0 u` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [vv_post_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     simp[wb_frame_def] >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv t ee sb u q` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es ee sa s0 q` by
    (drule_all wb_frame_trans >> simp[]) >>
  `~expr_has_effect obj /\ ~expr_has_effect idx ==>
    pure_frame cenv func es sa s0 q` by
    (strip_tac >>
     `pure_frame cenv func es sa s0 u` by fs[vv_post_def] >>
     `pure_frame cenv func t sb u q` by
       (drule_all expr_post_pure_frame >> simp[]) >>
     irule pure_frame_trans >> simp[] >>
     qexistsl_tac [`t`,`sb`,`u`] >> fs[wb_frame_def]) >>
  irule vv_post_frame_intro >>
  simp[vyperASTTheory.expr_type_def, expr_has_effect_thm,
       vv_at_def, vv_storage_live_def] >> metis_tac[]
QED
