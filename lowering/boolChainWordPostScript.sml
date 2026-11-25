Theory boolChainWordPost
Ancestors
  exprSimWordArgs exprSimProps exprLoweringProps loweringPosts
  loweringStateRelDefs venomState finite_map

(* The branch changes only the PC: carry the incoming frame over the
   jump before composing it with the selected operand's frame. *)
Theorem word_post_selected_prefix:
  expr_post H ctx func ce cx prefix es sa sp s0 em pv pop t /\
  expr_post H ctx func ce cx e em sc sd (jump_to lbl t) ee v op u /\
  stmt_state_rel H ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM em.scopes /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  is_word_type (expr_type out) /\ word_value v /\
  eval_operand op u = SOME (val_to_w256 v) /\
  (~expr_has_effect out ==> ~expr_has_effect prefix /\ ~expr_has_effect e) ==>
  expr_post H ctx func ce cx out es sa sb s0 ee v op u
Proof
  strip_tac >>
  `wb_frame ce es em sa s0 t` by metis_tac[expr_post_frame] >>
  `wb_frame ce es em sa s0 (jump_to lbl t)` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sa`, `t`] >>
     simp[jump_to_def, lookup_var_def]) >>
  `wb_frame ce em ee sc (jump_to lbl t) u` by metis_tac[expr_post_frame] >>
  `~expr_has_effect out ==> pure_frame ce func es sa s0 u` by
    (disch_tac >>
     `pure_frame ce func es sa s0 t` by metis_tac[expr_post_pure_frame] >>
     `pure_frame ce func es sa s0 (jump_to lbl t)` by
       (irule pure_frame_mem_tail >> qexists_tac `t` >> simp[jump_to_def]) >>
     `pure_frame ce func em sc (jump_to lbl t) u` by metis_tac[expr_post_pure_frame] >>
     irule pure_frame_trans >> simp[] >>
     qexistsl_tac [`em`, `sc`, `jump_to lbl t`] >>
     fs[wb_frame_def]) >>
  `wb_frame ce es ee sa s0 u` by metis_tac[wb_frame_trans] >>
  match_mp_tac expr_post_word_intro >> simp[] >> fs[expr_post_def]
QED

(* The result slot is fresh at the origin, not necessarily at the
   point of assignment. The operand can be a literal or a variable. *)
Theorem word_post_fresh_assign_exit:
  expr_post H ctx func ce cx e es sa sm s0 ee v op u /\
  local_ptrs_reserved ce sa /\ ~not_fresh_at sa rv /\
  is_word_type (expr_type out) /\ word_value v /\
  eval_operand src u = SOME (val_to_w256 v) /\
  (~expr_has_effect out ==> ~expr_has_effect e) ==>
  expr_post H ctx func ce cx out es sa sb s0 ee v (Var rv)
    (jump_to xl (update_var rv (val_to_w256 v) u with vs_inst_idx := k))
Proof
  strip_tac >>
  qabbrev_tac `z = jump_to xl (update_var rv (val_to_w256 v) u with vs_inst_idx := k)` >>
  `stmt_state_rel H ctx func ce cx ee (update_var rv (val_to_w256 v) u)` by
    (simp[update_var_def] >> irule stmt_state_rel_vars_frame >>
     simp[lookup_var_def, FLOOKUP_UPDATE] >>
     `stmt_state_rel H ctx func ce cx ee u` by metis_tac[expr_post_state] >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `z.vs_memory = u.vs_memory /\ z.vs_allocas = u.vs_allocas /\
   eval_operand (Var rv) z = SOME (val_to_w256 v) /\
   (!x. x <> rv ==> lookup_var x z = lookup_var x u)` by
    simp[Abbr `z`, eval_operand_def, jump_to_def, update_var_def, lookup_var_def,
         FLOOKUP_UPDATE] >>
  `wb_frame ce es ee sa s0 z` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sa`, `u`] >>
     simp[] >> metis_tac[expr_post_frame]) >>
  `~expr_has_effect out ==> pure_frame ce func es sa s0 z` by
    (disch_tac >> irule pure_frame_mem_tail >> qexists_tac `u` >>
     simp[] >> metis_tac[expr_post_pure_frame]) >>
  `stmt_state_rel H ctx func ce cx ee z` by
    simp[Abbr `z`, stmt_state_rel_jump_to, stmt_state_rel_inst_idx] >>
  match_mp_tac expr_post_word_intro >> simp[] >> fs[expr_post_def]
QED
