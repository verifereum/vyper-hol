Theory bodyPtrBopInArgsPost
Ancestors bodyPtrBopInWordBoundary typedWordArgsPostPtr bodyPtrDefs
  exprSimWordArgs compileEnv list gasOutcomeMapPtr gasSummaryComposePtr
  gasOutcomeMarkedPtr vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState

(* The existing typed list post keeps the semantic frame and taint.  EQ
   additionally needs the provenance fact, so retain it at the cons boundary. *)
Theorem membership_typed_args_cons:
  expr_post H ctx func cenv cx e es sa s1 s0 es1 v x t /\
  typed_args_post_ptr H d ctx func cenv cx es1 s1 t G1 tn1 ee args xs vs G tn u /\
  EVERY (\op. op_prov G op = NONE) xs /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv s1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 ==>
  typed_args_post_ptr H d ctx func cenv cx es sa s0 G0 tn0 ee
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
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    expr_post H ctx func cenv cx e es sa s1 s0 es1 v x t /\
    stmt_state_rel H ctx func cenv cx es s0) /\
  local_ptrs_reserved cenv sa /\
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
         args xs vs G tn u /\ EVERY (\op. op_prov G op = NONE) xs /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\H rr ee ghosts r. wb_args_exit rr r) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0
    (do vs <- eval_exprs cx args; return (v::vs) od) (es1,t,G1,tn1)
    (\H rr ee G tn u. ?vs. rr = INL vs /\
       typed_args_post_ptr H d ctx func cenv cx es sa s0 G0 tn0 ee
         (e::args) (x::xs) vs G tn u /\
       EVERY (\op. op_prov G op = NONE) (x::xs) /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\H rr ee ghosts r. wb_args_exit rr r)
Proof
  strip_tac >>
  `gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0 (eval_exprs cx args)
    (es1,t,G1,tn1)
    (\H rr ee G tn u. ?vs. rr = INL vs /\
      typed_args_post_ptr H d ctx func cenv cx es sa s0 G0 tn0 ee
        (e::args) (x::xs) (v::vs) G tn u /\
      EVERY (\op. op_prov G op = NONE) (x::xs) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\H rr ee ghosts r. wb_args_exit rr r)` by
    (irule gas_outcome_ptr_marked_conseq >> goal_assum (drule_at Any) >>
     rpt gen_tac >> strip_tac >> gvs[] >>
     `valid_horizon cx st0 H es1.storage_trace` by
       (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
        qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` assume_tac) >>
        `storage_trace_frame (eval_exprs cx args)` by simp[evaluate_storage_trace_frame] >>
        `valid_horizon cx st0 H (mid with gas_obs := []).storage_trace` by simp[] >>
        drule_all valid_horizon_frame >> simp[]) >>
     qpat_x_assum `!H. valid_horizon _ _ _ es1.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     drule_all membership_typed_args_cons >> simp[]) >>
  irule gas_outcome_ptr_map_return >> goal_assum (drule_at Any) >> conj_tac
  >- (rpt strip_tac >> gvs[]) >>
  Cases_on `res` >> simp[wb_args_exit_def]
QED
