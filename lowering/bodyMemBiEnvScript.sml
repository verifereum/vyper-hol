(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: environment reads (S1: exprSimLeaves' compile_env_case_ok;
   bodyEnvMemory has the old port). *)
Theory bodyMemBiEnv
Ancestors
  bodyMemoryPreds bodyEnvMemory bodyMemBiEnvMsgGas bodyMemBiEnvPrevHash

Theorem body_builtin_env_mem:
  !cx ty item es. body_expr_mem_ok cx (Builtin ty (Env item) es)
Proof
  rpt gen_tac >> Cases_on `item = PrevHash`
  >- simp[body_prevhash_mem_case] >>
  Cases_on `item = MsgGas`
  >- simp[body_msg_gas_mem_case] >>
  irule body_env_mem_case >> simp[]
QED
