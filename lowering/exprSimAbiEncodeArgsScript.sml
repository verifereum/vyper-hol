(*
 * Expression simulation: abi_encode's argument list, counted.
 *
 * compile_abi_encode_args compiles the operands of a tuple abi_encode,
 * materializing a composite operand when a later one may mutate.  From
 * the operands' case hypotheses, running the compiled list follows
 * eval_exprs as an actual counted path: on success every operand is
 * related to its value at the end, and every exception ends in its exit.
 *)

Theory exprSimAbiEncodeArgs
Ancestors
  abiEncodeArgsSim abiEncodeArgsCase exprSimAbiEncodeArgsUncaptured
  exprSimAbiEncodeArgsCaptured exprSimHypsDefs exprSimWordArgs
  abiDecoderReentry exprSimAbiGasBridge

Theorem compile_abi_encode_args_sim_live:
  !args ctx func ce cx Inv env es sa ops sb s0.
    abi_args_ready ctx func ce cx Inv args /\ Inv es /\
    (!s. Inv s ==> expr_sim_inv ce cx env s) /\
    (!s gs. Inv s ==> Inv (s with gas_obs := gs)) /\
    EVERY (\e. !s. Inv s ==> expr_body_pre ce cx env e s) args /\
    compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\
    stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
      (\rr ee t. ?vs. rr = INL vs /\
         abi_args_post ctx func ce cx es sa sb s0 ee args ops vs t /\
         EVERY (abi_decoder_operand_live sb.cs_next_var) ops /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\rr ee r. wb_args_exit rr r)
Proof
  cheat
QED

Theorem compile_abi_encode_args_sim:
  !args ctx func ce cx Inv env es sa ops sb s0.
    abi_args_ready ctx func ce cx Inv args /\ Inv es /\
    (!s. Inv s ==> expr_sim_inv ce cx env s) /\
    (!s gs. Inv s ==> Inv (s with gas_obs := gs)) /\
    EVERY (\e. !s. Inv s ==> expr_body_pre ce cx env e s) args /\
    compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\
    stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
      (\rr ee t. ?vs. rr = INL vs /\
         abi_args_post ctx func ce cx es sa sb s0 ee args ops vs t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\rr ee r. wb_args_exit rr r)
Proof
  cheat
QED

Theorem compile_abi_encode_args_case_gas_sim:
  !nocalls ctx func ce cx env ann ensure mid ty args es sa ops sb s0.
    exprs_case nocalls ctx func ce cx args /\
    expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
    (nocalls ==>
     int_calls_expr (TypeBuiltin ann (AbiEncode ensure mid) ty args) = []) /\
    compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\
    stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
      (\rr ee t. ?vs. rr = INL vs /\
         abi_args_post ctx func ce cx es sa sb s0 ee args ops vs t /\
         EVERY (abi_decoder_operand_live sb.cs_next_var) ops /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\rr ee r. wb_args_exit rr r)
Proof
  cheat
QED
