(* Memory case of the body induction (bodyMemory's body_mem_mutual): the
   builtins with no other case: not the binary operators, array literals,
   ecadd and ecmul, msg.data length (bodyCalldataMemory), or neg, abs and not
   on one operand. The environment reads are here: bodyEnvMemory's
   body_env_mem_case predates the gas-counted expr_sim_mem and needs porting. *)
Theory bodyMemBuiltinRest
Ancestors
  bodyMemoryPreds

Theorem body_builtin_rest_mem_case:
  !cx ty bt es.
    (!bop. bt <> Bop bop) /\ (!t n. bt <> MakeArray t n) /\
    bt <> ECAdd /\ bt <> ECMul /\ bt <> CalldataLen /\
    (!e. es = [e] ==> bt <> Neg /\ bt <> Abs /\ bt <> Not) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas ==>
       body_exprs_mem_ok cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_mem_ok cx (HD es)) ==>
    body_expr_mem_ok cx (Builtin ty bt es)
Proof
  cheat
QED
