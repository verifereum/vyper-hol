Theory bodyFullBopRestWordPost
Ancestors
  bodySimFull exprSimBopRestWordCompose wordArgsPtr exprSimWordArgs
  vyperTypeSystem valueEncoding bodyPtrDefs vyperAST exprSimMemDefs
  compileEnv loweringPosts vyperInterpreter vyperValue

Theorem rest_word_full_parent_post:
  (bop = In \/ bop = NotIn) /\ ann = BaseT BoolT /\
  compile_var_array_membership cenv x vv (ArrayT ety bd) (bop = In) sm = (out,ct) /\
  expr_post H ctx func cenv cx e1 es sa s1 s0 mid needle x t /\
  vv_post H ctx func cenv cx e2 mid s1 sm t fin tv vv q /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel H ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  eval_operand out q = SOME (bool_to_word
    (if bop = In then evaluate_in_array (ArrayTV et bd) needle av
     else ~evaluate_in_array (ArrayTV et bd) needle av)) /\
  op_prov G out = NONE /\ op_taint tn out = {} /\
  q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts /\
  alloca_history func q /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  t.vs_alloca_next <= q.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx fin G tn q /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv mid s1 G1 tn1 t G tn ==>
  expr_post H ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
    es sa ct s0 fin
    (BoolV (if bop = In then evaluate_in_array (ArrayTV et bd) needle av
            else ~evaluate_in_array (ArrayTV et bd) needle av)) out q /\
  expr_store_bound cx (expr_type (Builtin ann (Bop bop) [e1;e2]))
    (BoolV (if bop = In then evaluate_in_array (ArrayTV et bd) needle av
            else ~evaluate_in_array (ArrayTV et bd) needle av)) out q /\
  q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts /\
  alloca_history func q /\ s0.vs_alloca_next <= q.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx fin G tn q /\
  ptr_val_ok cx (post_value_type cenv (Builtin ann (Bop bop) [e1;e2]))
    (BoolV (if bop = In then evaluate_in_array (ArrayTV et bd) needle av
            else ~evaluate_in_array (ArrayTV et bd) needle av)) out G tn q /\
  (~is_word_type (post_value_type cenv (Builtin ann (Bop bop) [e1;e2])) ==>
    ptr_buf_ok cenv (Builtin ann (Bop bop) [e1;e2]) out G q) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
   ghost_kept cenv mid s1 G1 tn1 t G tn` by
    (fs[ghost_kept_def, ghost_kept_at_def] >> metis_tac[]) >>
  `wb_frame cenv es mid sa s0 t` by metis_tac[expr_post_frame] >>
  `ghost_kept cenv es sa G0 tn0 s0 G tn` by
    (irule wordArgsPtrTheory.ghost_kept_wb_trans >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` by
    (fs[ghost_kept_def, ghost_kept_at_def] >> metis_tac[]) >>
  gvs[expr_type_def, expr_store_bound_def, ptr_val_ok_def, is_word_type_def] >>
  irule rest_word_mixed_post >>
  simp[expr_val_at_def, expr_val_rel_def, is_word_type_def,
       evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  Cases_on `evaluate_in_array (ArrayTV et bd) needle av` >>
  simp[venomExecSemanticsTheory.bool_to_word_def] >>
  metis_tac[]
QED
