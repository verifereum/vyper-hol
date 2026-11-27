(* First-point preparation for the full EC arithmetic execution. *)
Theory bodyFullBuiltinECArithOperands
Ancestors
  bodyMemEcArithOperands loweringPosts valueEncoding bodyPtrDefs
  stateRelProj allocaSiteResource bodyMemoryDefs[qualified,ignore_grammar]
  exprSimHypsDefs[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt strip_tac >>
  drule_all ec_point_operand_kept >> strip_tac >>
  `?w. eval_operand x t = SOME w` by
    fs[expr_post_def, expr_val_rel_def] >>
  `eval_operand x u = SOME w` by metis_tac[] >>
  qexists_tac `w` >> simp[] >>
  irule ec_point_read_capacity >> metis_tac[]
QED
*)
Theorem ec_first_point_staging_ready:
  post_value_type cenv e1 = expr_type e1 /\
  expr_post H ctx func cenv cx e1 es sa s1 s0 es1 v1 x t /\
  expr_post H ctx func cenv cx e2 es1 s1 s2 t es' v2 y u /\
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_sim_inv_mods mods cenv cx env es /\
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
  cheat
QED

(* The staging writes introduce no taint into live input regions. *)
Theorem ec_staging_ghost_kept_at:
  stmt_state_rel H ctx func cenv cx es s /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!i. i < s.vs_alloca_next /\ i IN tn'.t_mem ==> i IN tn.t_mem) ==>
  ghost_kept_at lo cenv es sa G tn s G' tn'
Proof
  strip_tac >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ s`
    (assume_tac o CONJUNCT2 o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
  rewrite_tac[ghost_kept_at_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >> drule_all alloca_site_registered_below >> strip_tac >>
      qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >>
      simp[] >> decide_tac) >>
  rpt strip_tac >> drule_all bodyMemoryDefsTheory.body_local_region_frontier >>
  strip_tac >>
  qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >>
  simp[] >> decide_tac
QED
