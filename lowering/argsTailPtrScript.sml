Theory argsTailPtr
Ancestors
  typedWordArgsPostPtr exprSimWordArgs gasSummaryComposePtr fragGasPathPtr
  gasExemptCert gasStorage vyperStorageTrace vyperStorageFootprint vyperState sum

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
  gas_outcome_ptr D tops (ctx,func) PG cx st0 source (es,s0,G0,tn0) Q R /\
  (!H rr ee G tn t. Q H rr ee G tn t ==>
    Q' H (case rr of INL v => INL (f v) | INR exc => INR exc) ee G tn t) /\
  (!H rr ee gt r. R H rr ee gt r ==>
    R' H (case rr of INL v => INL (f v) | INR exc => INR exc) ee gt r) ==>
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (do v <- source; return (f v) od) (es,s0,G0,tn0) Q' R'
Proof
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
  strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> irule gas_bad_storage_at_bind_left >>
      goal_assum (drule_at Any) >> simp[storage_trace_frame_return])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [
        `case res of INL v => INL (f v) | INR exc => INR exc`,
        `es_end`, `G`, `tn`, `r`] >>
      conj_tac
      >- (gen_tac >> simp[bind_def] >> Cases_on `res` >> simp[return_def]) >>
      gen_tac >> disch_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >>
      strip_tac >> conj_tac >> gvs[] >>
      metis_tac[gas_marked_exec_ptr_return_map]) >>
  disj2_tac >> disj2_tac >>
  fs[ignore_bind_def, bind_assoc, bind_return] >> metis_tac[]
QED

Theorem lower_typed_args_cons_tail_ptr:
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    expr_post H ctx func cenv cx e es sa s1 s0 es1 v x t /\
    stmt_state_rel H ctx func cenv cx es s0) /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv s1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0 (eval_exprs cx args)
    (es1,t,G1,tn1)
    (\H rr ee G tn u. ?vs. rr = INL vs /\
       typed_args_post_ptr H d ctx func cenv cx es1 s1 t G1 tn1 ee
         args xs vs G tn u /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\H rr ee ghosts r. wb_args_exit rr r) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0
    (do vs <- eval_exprs cx args; return (v::vs) od) (es1,t,G1,tn1)
    (\H rr ee G tn u. ?vs. rr = INL vs /\
       typed_args_post_ptr H d ctx func cenv cx es sa s0 G0 tn0 ee
         (e::args) (x::xs) vs G tn u /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\H rr ee ghosts r. wb_args_exit rr r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
      disj1_tac >> irule gas_bad_storage_at_bind_left >>
      goal_assum (drule_at Any) >> simp[storage_trace_frame_return])
  >- (pop_assum (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >>
      rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
      disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_ptr_at_marked] >>
      qexistsl_tac [
        `case res of INL vs => INL (v::vs) | INR exc => INR exc`,
        `es_end`, `G`, `tn`, `r`] >>
      conj_tac
      >- (gen_tac >> simp[bind_def] >> Cases_on `res` >> simp[return_def]) >>
      gen_tac >> disch_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _` drule >>
      disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
      >- (irule gas_marked_exec_ptr_return_map >> goal_assum (drule_at Any)) >>
      `valid_horizon cx st0 H es1.storage_trace` by
        (qpat_assum `!tail. eval_exprs _ _ _ = _`
           (qspec_then `[]` assume_tac) >>
         `valid_horizon cx st0 H (es_end with gas_obs := []).storage_trace` by simp[] >>
         `storage_trace_frame (eval_exprs cx args)` by
           simp[evaluate_storage_trace_frame] >>
         drule_all valid_horizon_frame >> simp[]) >>
      qpat_x_assum `!H. valid_horizon _ _ H es1.storage_trace ==> _` drule >>
      strip_tac >> gvs[]
      >- (disj1_tac >> simp[] >>
          irule typed_args_post_ptr_cons >> metis_tac[]) >>
      disj2_tac >> Cases_on `res` >> gvs[wb_args_exit_def]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
  disj2_tac >> disj2_tac >>
  gvs[ignore_bind_def, bind_assoc, bind_return] >> metis_tac[]
QED
