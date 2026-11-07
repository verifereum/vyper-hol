Theory abiEncodeArgsCase
Ancestors
  abiEncodeArgsSim exprSimHyps vyperTypeInvariants

Theorem abi_args_success_ready:
  expr_body_pre ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  expr_sim_inv ce cx env es' /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         value_has_type tv v /\ val_wf tv v /\
         type_memory_bytes ce (expr_type e) = type_memory_size tv /\
         type_memory_size tv < 2 ** 64 /\
         type_memory_size tv + 64 < dimword (:256))
Proof
  cheat
QED

Theorem abi_args_ready_cases:
  !args.
  exprs_case nocalls ctx func ce cx args /\
  EVERY (\e. !es. expr_sim_inv ce cx env es ==>
    expr_body_pre ce cx env e es /\ (nocalls ==> int_calls_expr e = [])) args ==>
  abi_args_ready ctx func ce cx (expr_sim_inv ce cx env) args
Proof
  cheat
QED

Theorem abi_args_body_pre_arg:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
  MEM e args /\ expr_sim_inv ce cx env es' ==>
  expr_body_pre ce cx env e es'
Proof
  cheat
QED

Theorem abi_args_ready_case:
  exprs_case nocalls ctx func ce cx args /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
  (nocalls ==> int_calls_expr (TypeBuiltin ann (AbiEncode ensure mid) ty args) = []) ==>
  abi_args_ready ctx func ce cx (expr_sim_inv ce cx env) args
Proof
  cheat
QED

Theorem compile_abi_encode_args_case_sim:
  exprs_case nocalls ctx func ce cx args /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
  (nocalls ==> int_calls_expr (TypeBuiltin ann (AbiEncode ensure mid) ty args) = []) /\
  compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
  eval_exprs cx args es = (rr,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    (\s. ?vs. rr = INL vs /\ abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s)
    (wb_args_exit rr)
Proof
  cheat
QED
