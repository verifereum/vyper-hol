Theory exprSimIfExpWidenedPost
Ancestors
  exprSimIfExp exprSimUnwrapProps exprSimIfExpWidenedArm loweringPosts
  exprSimDefs compileEnv vyperAST vyperState exprSimIfExpWidenedProvenance

Theorem normalized_ifexp_root_vv_post:
  (~expr_has_effect (IfExp ann c a b) ==> ~expr_has_effect (IfExp ann nc na nb)) /\
  expr_post ctx func ce cx c es sa s1 s0 es1 cv cop tt /\
  expr_post ctx func ce cx (IfExp ann nc na nb)
    es1 sc sd (jump_to lbl tt) ee v aop u /\
  (~is_word_type ann ==> vv_at ce cx ann sc sd ee tv
    (LocatedValue ann (mk_ptr aop LocMemory)) u) /\
  eval_operand aop u = SOME w /\
  read_result cx tv ee = (INL v,ee) /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id ==>
  vv_post ctx func ce cx (IfExp ann c a b) es sa sb s0 ee tv
    (if is_word_type ann then StackValue ann (Var rv)
     else LocatedValue ann (mk_ptr (Var rv) LocMemory))
    (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  strip_tac >>
  `expr_post ctx func ce cx (IfExp ann c a b) es sa sb s0 ee v (Var rv)
    (jump_to xl (update_var rv w u with vs_inst_idx := k))` by
    (irule expr_post_ifexp >>
     simp[post_value_type_def, expr_type_def] >>
     conj_tac >- metis_tac[] >>
     qexistsl [`aop`, `cop`, `IfExp ann nc na nb`, `es1`, `lbl`,
               `s1`, `sc`, `sd`, `tt`, `cv`] >>
     simp[post_value_type_def, expr_type_def]) >>
  irule (SIMP_RULE (srw_ss()) [expr_type_def]
    (Q.INST [`e` |-> `IfExp ann c a b`] ifexp_root_vv_post_of_expr_post_read)) >>
  simp[post_value_type_def, expr_type_def] >>
  rpt strip_tac >> irule vv_at_assigned_root_frame >>
  simp[] >> conj_tac >- metis_tac[] >>
  qexistsl [`aop`, `sc`, `sd`] >> simp[] >> decide_tac
QED
