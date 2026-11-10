(* Compiler and endpoint packaging for framed array subscripts. *)
Theory exprSimSubscriptArrayEndpoint
Ancestors
  exprSimSubscriptArrayFramed exprSimSubscriptArrayFrame
  exprSimWordArgs exprSimHash exprSimVVFrame exprLoweringProps
  loweringPosts compileEnv freshWrites finite_map

Theorem word_expr_post_readonly_tail:
  expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
  is_word_type (expr_type e) /\ sa.cs_next_var <= sb.cs_next_var /\
  (!x. op = Var x ==> not_fresh_at sb x) /\ (!l. op <> Label l) /\
  (!x w. not_fresh_at sb x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
  (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
  t.vs_memory = s.vs_memory /\ stmt_state_rel ctx func cenv cx es' t ==>
  expr_post ctx func cenv cx e es sa sc s0 es' v op t
Proof
  strip_tac >>
  `wb_frame cenv es sa s0 s` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es sa s0 t` by
    (irule wb_frame_readonly_tail >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `~expr_has_effect e ==> pure_frame cenv func es sa s0 t` by
    (strip_tac >> irule exprSimPropsTheory.pure_frame_mem_tail >> qexists_tac `s` >> simp[] >>
     drule_all expr_post_pure_frame >> simp[]) >>
  `!w. eval_operand op s = SOME w ==> eval_operand op t = SOME w` by
    (rpt strip_tac >> irule exprBopSimPropsTheory.eval_operand_frame >> simp[] >>
     qexistsl_tac [`sb`,`s`] >> simp[]) >>
  gvs[expr_post_def, expr_val_at_def, expr_val_rel_def, wb_frame_def] >>
  metis_tac[]
QED

Theorem framed_array_base_endpoint:
  vv_post ctx func cenv cx obj es sa sb s0 t r (LocatedValue (ArrayT et bd) p) u /\
  expr_post ctx func cenv cx idx t sb sc u t' iv iop v /\
  expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  is_word_type (expr_type idx) /\
  ((~cenv.ce_is_ctor /\ p.ptr_location = LocCode) \/
   ((?n. bd = Fixed n) /\
    (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
    p.ptr_location = LocMemory)) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  t'.scopes = t.scopes /\ t'.immutables = t.immutables /\
  expr_sim_inv cenv cx env t /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM t.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sd.cs_next_id /\
  (!x w. not_fresh_at sc x /\ lookup_var x v = SOME w ==> lookup_var x q = SOME w) /\
  (!aid a. FLOOKUP v.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
  q.vs_memory = v.vs_memory /\ stmt_state_rel ctx func cenv cx t' q ==>
  vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 t' r
    (LocatedValue (ArrayT et bd) p) q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_post ctx func cenv cx idx t sb sd u t' iv iop q` by
    (irule word_expr_post_readonly_tail >> simp[] >>
     qexistsl_tac [`v`,`sc`] >> simp[]) >>
  drule_all_then strip_assume_tac framed_array_base_transport >>
  `wb_frame cenv es sa s0 u` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [vv_post_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     simp[wb_frame_def] >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv t sb u q` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es sa s0 q` by
    (drule_all wb_frame_trans >> simp[]) >>
  `~expr_has_effect obj /\ ~expr_has_effect idx ==> pure_frame cenv func es sa s0 q` by
    (strip_tac >>
     `pure_frame cenv func es sa s0 u` by
       (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[vv_post_def]) >>
     `pure_frame cenv func t sb u q` by
       (match_mp_tac expr_post_pure_frame >>
        qexistsl_tac [`cx`, `idx`, `sd`, `t'`, `iv`, `iop`, `ctx`] >> simp[]) >>
     match_mp_tac exprSimPropsTheory.pure_frame_trans >>
     qexistsl_tac [`t`, `sb`, `u`] >> fs[wb_frame_def]) >>
  irule vv_post_frame_intro >> simp[vyperASTTheory.expr_type_def, expr_has_effect_thm] >>
  qpat_x_assum `_ \/ _` strip_assume_tac >> simp[]
QED
