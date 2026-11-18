(* First-point preparation for the full EC arithmetic execution. *)
Theory bodyFullBuiltinECArithOperands
Ancestors
  bodyMemEcArithOperands loweringPosts valueEncoding

Theorem ec_first_point_staging_ready:
  post_value_type cenv e1 = expr_type e1 /\
  expr_post H ctx func cenv cx e1 es sa s1 s0 es1 v1 x t /\
  expr_post H ctx func cenv cx e2 es1 s1 s2 t es' v2 y u /\
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_sim_inv cenv cx env es /\
  (!w. eval_operand x t = SOME w ==> eval_operand x u = SOME w) /\
  local_ptrs_reserved cenv s1 /\ MAP FDOM es1.scopes = MAP FDOM es'.scopes /\
  s1.cs_next_id <= s2.cs_next_id /\
  expr_store_bound cx (expr_type e1) v1 x t /\
  t.vs_alloca_next <= u.vs_alloca_next ==>
  ?w. eval_operand x t = SOME w /\ eval_operand x u = SOME w /\
      w2n w + 64 <= u.vs_alloca_next /\
      expr_val_rel cx (expr_type e1) v1 x u /\
      expr_val_at cenv cx (expr_type e1) sa s2 es' v1 x u
Proof
  rpt strip_tac >>
  drule_all ec_point_operand_kept >> strip_tac >>
  `?w. eval_operand x t = SOME w` by
    fs[expr_post_def, expr_val_rel_def] >>
  `eval_operand x u = SOME w` by metis_tac[] >>
  qexists_tac `w` >> simp[] >>
  irule ec_point_read_capacity >> metis_tac[]
QED
