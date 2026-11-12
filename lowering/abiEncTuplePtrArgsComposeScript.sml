(* Pointer outcome composition for ABI tuple arguments. *)
Theory abiEncTuplePtrArgsCompose
Ancestors
  abiEncodeArgsSim wordArgsPtr stmtFragPtr
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
