(* Framing a captured storage array across its index and readonly suffix. *)
Theory exprSimSubscriptArrayLiveStorageEndpoint
Ancestors
  exprSimSubscriptArrayLiveStorage exprSimSubscriptArrayEndpoint
  exprSimHash exprSimWordArgs exprSimDefs exprSimProps exprBopSimProps exprLoweringProps loweringPosts
  loweringStateRelDefs context compileEnv freshWrites vyperAST finite_map

Theorem live_storage_array_base_endpoint:
  vv_post ctx func cenv cx obj es sa sb s0 t
    (PlaceR (StoragePlace tr slot (ArrayTV etv bd))) (LocatedValue (ArrayT et bd) p) u /\
  expr_post ctx func cenv cx idx t sb sc u t' iv iop v /\
  expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  is_word_type (expr_type idx) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  well_formed_type_value (ArrayTV etv bd) /\
  storage_read_live cx tr (get_storage cx t' tr) slot (ArrayTV etv bd) /\
  slots_in_range (get_storage cx t' tr) (w2n slot) (ArrayTV etv bd) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  expr_sim_inv cenv cx env t /\ stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM t.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sd.cs_next_id /\
  (!x w. not_fresh_at sc x /\ lookup_var x v = SOME w ==> lookup_var x q = SOME w) /\
  (!aid a. FLOOKUP v.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
  q.vs_memory = v.vs_memory /\ stmt_state_rel ctx func cenv cx t' q ==>
  vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 t'
    (PlaceR (StoragePlace tr slot (ArrayTV etv bd))) (LocatedValue (ArrayT et bd) p) q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_post ctx func cenv cx idx t sb sd u t' iv iop q` by
    (irule word_expr_post_readonly_tail >> simp[] >>
     qexistsl_tac [`v`,`sc`] >> simp[]) >>
  `wb_frame cenv es t sa s0 u` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [vv_post_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     simp[wb_frame_def] >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv t t' sb u q` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es t' sa s0 q` by
    (drule_all wb_frame_trans >> simp[]) >>
  `p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand u = SOME slot` by
    fs[vv_post_def, vv_place_ptr_def] >>
  `eval_operand p.ptr_operand q = SOME slot` by
    (irule exprBopSimPropsTheory.eval_operand_frame >> simp[] >>
     qexistsl_tac [`sb`,`u`] >> fs[wb_frame_def]) >>
  `storage_holds cx tr (ArrayT et bd)
     (PlaceR (StoragePlace tr slot (ArrayTV etv bd))) slot t u` by
    (Cases_on `tr` >> fs[vv_post_def, vv_holds_def, slot_loc_def]) >>
  `storage_holds cx tr (ArrayT et bd)
     (PlaceR (StoragePlace tr slot (ArrayTV etv bd))) slot t' q` by
    (irule live_storage_holds_current >> simp[SF SFY_ss]) >>
  `~expr_has_effect obj /\ ~expr_has_effect idx ==> pure_frame cenv func es sa s0 q` by
    (strip_tac >>
     `pure_frame cenv func es sa s0 u` by fs[vv_post_def] >>
     `pure_frame cenv func t sb u q` by metis_tac[expr_post_pure_frame] >>
     irule exprSimPropsTheory.pure_frame_trans >> conj_tac >- simp[] >>
     qexistsl_tac [`t`,`sb`,`u`] >> fs[wb_frame_def] >> metis_tac[]) >>
  irule vv_post_frame_intro >>
  simp[expr_type_def, expr_has_effect_thm, vv_holds_def, vv_at_def,
       vv_place_ptr_def, slot_loc_def] >>
  Cases_on `tr` >> fs[slot_loc_def]
QED
