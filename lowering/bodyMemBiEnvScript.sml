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

(* Check the exported leaf and its family boundaries for admissions. *)
val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then ()
     else raise Fail "environment memory proof inherited admission"
  end) [body_builtin_env_mem, body_env_mem_case,
        body_msg_gas_mem_case, body_prevhash_mem_case];
