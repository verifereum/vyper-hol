Theory bodyPtrBopInArgsPost
Ancestors bodyPtrBopInWordBoundary typedWordArgsPostPtr bodyPtrDefs
  exprSimWordArgs compileEnv list argsTailPtr gasSummaryComposePtr

(* The existing typed list post keeps the semantic frame and taint.  EQ
   additionally needs the provenance fact, so retain it at the cons boundary. *)
Theorem membership_typed_args_cons:
  expr_post ctx func cenv cx e es sa s1 s0 es1 v x t /\
  typed_args_post_ptr d ctx func cenv cx es1 s1 t G1 tn1 ee args xs vs G tn u /\
  EVERY (\op. op_prov G op = NONE) xs /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv s1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 ==>
  typed_args_post_ptr d ctx func cenv cx es sa s0 G0 tn0 ee
    (e::args) (x::xs) (v::vs) G tn u /\
  EVERY (\op. op_prov G op = NONE) (x::xs)
Proof
  strip_tac >> conj_tac
  >- (irule typed_args_post_ptr_cons >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[typed_args_post_ptr_def] >>
  drule_all membership_word_result_kept >> simp[]
QED

Theorem membership_typed_args_cons_tail:
  expr_post ctx func cenv cx e es sa s1 s0 es1 v x t /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv s1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG (eval_exprs cx args)
    (es1,t,G1,tn1)
    (\rr ee G tn u. ?vs. rr = INL vs /\
       typed_args_post_ptr d ctx func cenv cx es1 s1 t G1 tn1 ee
         args xs vs G tn u /\ EVERY (\op. op_prov G op = NONE) xs /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee ghosts r. wb_args_exit rr r) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (do vs <- eval_exprs cx args; return (v::vs) od) (es1,t,G1,tn1)
    (\rr ee G tn u. ?vs. rr = INL vs /\
       typed_args_post_ptr d ctx func cenv cx es sa s0 G0 tn0 ee
         (e::args) (x::xs) vs G tn u /\
       EVERY (\op. op_prov G op = NONE) (x::xs) /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee ghosts r. wb_args_exit rr r)
Proof
  strip_tac >> irule gas_outcome_ptr_return_map >>
  goal_assum (drule_at Any) >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      drule_all membership_typed_args_cons >> simp[]) >>
  Cases_on `rr` >> simp[wb_args_exit_def]
QED
