(* Pointer outcome composition for ABI tuple arguments. *)
Theory abiEncTuplePtrArgsCompose
Ancestors
  abiEncodeArgsSim wordArgsPtr stmtFragPtr argsTailPtr
  abiEncTuplePtrArgTransport exprSimAbiEncodeArgsCaptured
  exprSimAbiEncodeArgsMaterializePath exprSimProps
  exprSimWordArgs exprLoweringProps loweringStateRelDefs bodyPtrDefs
  fragGasPathPtr gasSummary vyperState loweringPosts list

Theorem abi_args_nil_ptr:
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  ghost_inv d ce cx es G0 tn0 s0 /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (eval_exprs cx []) (es,s0,G0,tn0)
    (\rr ee G tn t. ?vs. rr = INL vs /\
      abi_args_post ctx func ce cx es sa sa s0 ee [] [] vs t /\
      LIST_REL (\op ev. ptr_val_ok cx (lowered_value_type ce (FST ev))
        (SND ev) op G tn t) [] (ZIP ([],vs)) /\
      EVERY (abi_decoder_operand_live sa.cs_next_var) [] /\
      t.vs_current_bb = sa.cs_current_bb /\
      t.vs_inst_idx = LENGTH sa.cs_current_insts /\
      ghost_inv d ce cx ee G tn t /\
      ghost_kept ce es sa G0 tn0 s0 G tn)
    (\rr ee ghosts r. wb_args_exit rr r)
Proof
  strip_tac >> simp[gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >> simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL []`, `es`, `G0`, `tn0`, `OK s0`] >>
  simp[eval_exprs_nil, return_def, gas_explicit_def, gas_path_ptr_rules,
       abi_args_post_nil, wb_frame_def, ghost_kept_refl, ghost_inv_gas_obs] >>
  fs[stmt_state_rel_def, state_rel_gas_obs]
QED

(* The tail's scopes condition is the nonmutation contract; no assumption
   about annotation equality or cleanliness outside the value is made. *)
Theorem abi_args_uncaptured_cons_ptr:
  expr_post ctx func ce cx e es sa sm s0 es1 v op t /\
  expr_val_rel cx (lowered_value_type ce e) v op t /\
  expr_val_at ce cx (lowered_value_type ce e) sa sm es1 v op t /\
  ptr_val_ok cx (lowered_value_type ce e) v op G1 tn1 t /\
  ghost_kept ce es sa G0 tn0 s0 G1 tn1 /\
  stmt_state_rel ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  expr_sim_inv ce cx env es1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG (eval_exprs cx args)
    (es1,t,G1,tn1)
    (\rr ee G tn u. ?vs. rr = INL vs /\
      abi_args_post ctx func ce cx es1 sm sb t ee args ops vs u /\
      LIST_REL (\op ev. ptr_val_ok cx (lowered_value_type ce (FST ev))
        (SND ev) op G tn u) ops (ZIP (args,vs)) /\
      EVERY (abi_decoder_operand_live sb.cs_next_var) ops /\
      MAP FDOM ee.scopes = MAP FDOM es1.scopes /\
      (~is_word_type (lowered_value_type ce e) ==> ee.scopes = es1.scopes) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d ce cx ee G tn u /\ ghost_kept ce es1 sm G1 tn1 t G tn)
    (\rr ee ghosts r. wb_args_exit rr r) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (bind (eval_exprs cx args) (\vs. return (v::vs))) (es1,t,G1,tn1)
    (\rr ee G tn u. ?vs. rr = INL vs /\
      abi_args_post ctx func ce cx es sa sb s0 ee (e::args) (op::ops) vs u /\
      LIST_REL (\op ev. ptr_val_ok cx (lowered_value_type ce (FST ev))
        (SND ev) op G tn u) (op::ops) (ZIP (e::args,vs)) /\
      EVERY (abi_decoder_operand_live sb.cs_next_var) (op::ops) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d ce cx ee G tn u /\ ghost_kept ce es sa G0 tn0 s0 G tn)
    (\rr ee ghosts r. wb_args_exit rr r)
Proof
  strip_tac >> irule gas_outcome_ptr_return_map >>
  goal_assum (drule_at Any) >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      conj_tac
      >- (irule abi_args_post_cons_uncaptured >>
          gvs[ci_mono_def] >> metis_tac[]) >>
      conj_tac
      >- (Cases_on `is_word_type (lowered_value_type ce e)`
          >- (drule_all ghost_kept_operand >>
              Cases_on `op` >>
              gvs[ptr_val_ok_def, ghost_kept_def, ptrDisciplineTheory.op_prov_def, not_fresh_at_def]) >>
          `stmt_state_rel ctx func ce cx es1 t` by
            metis_tac[expr_post_def] >>
          `stmt_state_rel ctx func ce cx ee t' /\
           wb_frame ce es1 ee sm t t'` by metis_tac[abi_args_post_def] >>
          gvs[] >> irule abi_args_uncaptured_operand_ptr_transport >>
          qpat_assum `expr_val_at _ _ _ _ _ _ _ _ t` (irule_at Any) >>
          qpat_assum `ghost_kept _ es1 sm _ _ t _ _` (irule_at Any) >>
          simp[] >> metis_tac[]) >>
      conj_tac >- metis_tac[abi_args_operand_live] >>
      `wb_frame ce es es1 sa s0 t` by
        (gvs[expr_post_def, wb_frame_def] >> metis_tac[]) >>
      gvs[ci_mono_def] >> drule_all ghost_kept_wb_trans >> simp[]) >>
  Cases_on `rr` >> simp[wb_args_exit_def]
QED

(* Captured memory is owned, so only the domains (not all scopes) must
   survive the tail. The materializer supplies the allocation witness. *)
Theorem abi_args_captured_cons_ptr:
  materialize_owned_post ctx func ce cx e es sa mid sm s0 es1 v op tv t /\
  ptr_val_ok cx (lowered_value_type ce e) v op G1 tn1 t /\
  ghost_kept ce es sa G0 tn0 s0 G1 tn1 /\
  stmt_state_rel ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\ val_wf tv v /\
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG (eval_exprs cx args)
    (es1,t,G1,tn1)
    (\rr ee G tn u. ?vs. rr = INL vs /\
      abi_args_post ctx func ce cx es1 sm sb t ee args ops vs u /\
      LIST_REL (\op ev. ptr_val_ok cx (lowered_value_type ce (FST ev))
        (SND ev) op G tn u) ops (ZIP (args,vs)) /\
      EVERY (abi_decoder_operand_live sb.cs_next_var) ops /\
      MAP FDOM ee.scopes = MAP FDOM es1.scopes /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d ce cx ee G tn u /\ ghost_kept ce es1 sm G1 tn1 t G tn)
    (\rr ee ghosts r. wb_args_exit rr r) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (bind (eval_exprs cx args) (\vs. return (v::vs))) (es1,t,G1,tn1)
    (\rr ee G tn u. ?vs. rr = INL vs /\
      abi_args_post ctx func ce cx es sa sb s0 ee (e::args) (op::ops) vs u /\
      LIST_REL (\op ev. ptr_val_ok cx (lowered_value_type ce (FST ev))
        (SND ev) op G tn u) (op::ops) (ZIP (e::args,vs)) /\
      EVERY (abi_decoder_operand_live sb.cs_next_var) (op::ops) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d ce cx ee G tn u /\ ghost_kept ce es sa G0 tn0 s0 G tn)
    (\rr ee ghosts r. wb_args_exit rr r)
Proof
  strip_tac >> irule gas_outcome_ptr_return_map >>
  goal_assum (drule_at Any) >> conj_tac
  >- (rpt strip_tac >> gvs[] >> conj_tac
      >- (irule captured_owned_cons_post >> metis_tac[]) >>
      conj_tac
      >- (`wb_frame ce es1 ee sm t t'` by metis_tac[abi_args_post_def] >>
          irule abi_args_captured_operand_ptr_transport >>
          qpat_assum `ghost_kept _ es1 sm _ _ t _ _` (irule_at Any) >> simp[] >>
          qexists `ee` >> reverse conj_tac
          >- metis_tac[materialize_owned_post_def] >>
          rpt strip_tac >> gvs[] >>
          qpat_x_assum `materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
            (strip_assume_tac o REWRITE_RULE [materialize_owned_post_def]) >>
          gvs[] >> qexistsl [`mid.cs_next_id`, `w2n w`, `type_memory_size tv`] >>
          simp[val_footprint_le] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
      conj_tac >- metis_tac[abi_args_operand_live] >>
      `wb_frame ce es es1 sa s0 t` by metis_tac[materialize_owned_post_def] >>
      gvs[ci_mono_def] >> drule_all ghost_kept_wb_trans >> simp[]) >>
  Cases_on `rr` >> simp[wb_args_exit_def]
QED
