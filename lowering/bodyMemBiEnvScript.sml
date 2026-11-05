(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: environment reads (S1: exprSimLeaves' compile_env_case_ok;
   bodyEnvMemory has the old port). *)
Theory bodyMemBiEnv
Ancestors
  bodyMemoryPreds

Theorem body_builtin_env_mem:
  !cx ty item es. body_expr_mem_ok cx (Builtin ty (Env item) es)
Proof
  cheat
QED
