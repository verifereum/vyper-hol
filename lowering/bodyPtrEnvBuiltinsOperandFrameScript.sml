(* Arbitrary operands may allocate: use expr_post preservation, not equality. *)
Theory bodyPtrEnvBuiltinsOperandFrame
Ancestors
  bodyPtrEnvBuiltinsGhostCompose bodyPtrDefs exprLoweringProps
  exprBopSimProps loweringPosts exprSimProps compileEnv
  venomState finite_map list vyperInterpreter stmtFragPtr

Theorem operand_suffix_ghost_kept:
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es sa sb s0 ee v op s1 /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv ee sb G1 tn1 s1 G2 tn2 /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_reserved cenv sa ==>
  ghost_kept cenv es sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >>
  `cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
   sa.cs_next_id <= sb.cs_next_id` by
    metis_tac[cj 2 compile_expr_grows] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    metis_tac[not_fresh_at_mono] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    metis_tac[bop_value_scopes_dom] >>
  `(!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < sa.cs_next_id ==> FLOOKUP s1.vs_allocas aid = SOME (off,sz)) /\
   (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
          lookup_var x s1 = SOME w)` by
    (gvs[expr_post_def] >> metis_tac[]) >>
  drule_all ghost_kept_locals_trans >> simp[]
QED
