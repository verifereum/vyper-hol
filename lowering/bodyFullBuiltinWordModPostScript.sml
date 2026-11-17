(* Parent post for the three modular operands and their read-only suffix. *)
Theory bodyFullBuiltinWordModPost
Ancestors
  exprSimWordArgs exprSimProps exprLoweringProps loweringPosts
  compileEnv vyperAST finite_map list

Theorem modular_parent_post:
  expr_post H1 ctx func cenv cx e1 es sa s1 s0 mid1 v1 x t1 /\
  expr_post H2 ctx func cenv cx e2 mid1 s1 s2 t1 mid2 v2 y t2 /\
  expr_post H3 ctx func cenv cx e3 mid2 s2 s3 t2 fin v3 z t3 /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid1.scopes /\
  MAP FDOM es.scopes = MAP FDOM mid2.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id /\
  sa.cs_next_var <= s3.cs_next_var /\ is_word_type ann /\ word_value w /\
  stmt_state_rel H ctx func cenv cx fin u /\
  storage_well_formed_on cx fin (FST H) /\
  eval_operand op u = SOME (val_to_w256 w) /\
  (!q a. not_fresh_at s3 q /\ lookup_var q t3 = SOME a ==>
    lookup_var q u = SOME a) /\
  (!aid b. FLOOKUP t3.vs_allocas aid = SOME b ==>
    FLOOKUP u.vs_allocas aid = SOME b) /\
  u.vs_memory = t3.vs_memory ==>
  expr_post H ctx func cenv cx (Builtin ann bt [e1;e2;e3])
    es sa sb s0 fin w op u
Proof
  strip_tac >>
  `wb_frame cenv es mid1 sa s0 t1 /\
   wb_frame cenv mid1 mid2 s1 t1 t2 /\
   wb_frame cenv mid2 fin s2 t2 t3` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es mid2 sa s0 t2` by
    metis_tac[wb_frame_trans] >>
  `wb_frame cenv es fin sa s0 t3` by
    metis_tac[wb_frame_trans] >>
  `wb_frame cenv es fin sa s0 u` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`s3`, `t3`] >> simp[]) >>
  irule expr_post_word_intro >> simp[expr_type_def, expr_has_effect_thm] >> strip_tac >>
  `pure_frame cenv func es sa s0 t1 /\
   pure_frame cenv func mid1 s1 t1 t2 /\
   pure_frame cenv func mid2 s2 t2 t3` by metis_tac[expr_post_pure_frame] >>
  `pure_frame cenv func es sa s0 t2` by
    (MATCH_MP_TAC (Q.SPECL [`cenv`, `func`, `es`, `mid1`, `sa`, `s1`,
       `s0`, `t1`, `t2`] pure_frame_trans) >> fs[wb_frame_def]) >>
  `pure_frame cenv func es sa s0 t3` by
    (MATCH_MP_TAC (Q.SPECL [`cenv`, `func`, `es`, `mid2`, `sa`, `s2`,
       `s0`, `t2`, `t3`] pure_frame_trans) >> fs[wb_frame_def]) >>
  metis_tac[pure_frame_mem_tail]
QED
