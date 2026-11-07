Theory argsTailPtr
Ancestors
  typedWordArgsPostPtr exprSimWordArgs gasSummaryComposePtr fragGasPathPtr
  gasExemptCert vyperState sum

Theorem gas_marked_exec_ptr_return_map:
  gas_marked_exec_ptr D (ctx,func) PG source (es,s0,G0,tn0)
    marks rr mid G tn r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (do v <- source; return (f v) od) (es,s0,G0,tn0)
    marks (case rr of INL v => INL (f v) | INR exc => INR exc) mid G tn r
Proof
  rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >>
  simp[] >> gen_tac >> simp[bind_def] >> Cases_on `rr` >> simp[return_def]
QED

Theorem gas_outcome_ptr_return_map:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) Q R /\
  (!rr ee G tn t. Q rr ee G tn t ==>
    Q' (case rr of INL v => INL (f v) | INR exc => INR exc) ee G tn t) /\
  (!rr ee gt r. R rr ee gt r ==>
    R' (case rr of INL v => INL (f v) | INR exc => INR exc) ee gt r) ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (do v <- source; return (f v) od) (es,s0,G0,tn0) Q' R'
Proof
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
  strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      drule gas_marked_exec_ptr_return_map >>
      disch_then (qspec_then `f` assume_tac) >> metis_tac[])
  >- (qexists_tac `marks` >> disj1_tac >>
      drule gas_marked_exec_ptr_return_map >>
      disch_then (qspec_then `f` assume_tac) >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >>
  gvs[ignore_bind_def, bind_assoc, bind_return] >> metis_tac[]
QED

Theorem lower_typed_args_cons_tail_ptr:
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
         args xs vs G tn u /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee ghosts r. wb_args_exit rr r) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (do vs <- eval_exprs cx args; return (v::vs) od) (es1,t,G1,tn1)
    (\rr ee G tn u. ?vs. rr = INL vs /\
       typed_args_post_ptr d ctx func cenv cx es sa s0 G0 tn0 ee
         (e::args) (x::xs) vs G tn u /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee ghosts r. wb_args_exit rr r)
Proof
  strip_tac >> irule gas_outcome_ptr_return_map >>
  goal_assum (drule_at Any) >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      irule typed_args_post_ptr_cons >> metis_tac[]) >>
  Cases_on `rr` >> simp[wb_args_exit_def]
QED
