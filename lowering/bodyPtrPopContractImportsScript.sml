Theory bodyPtrPopContractImports
Ancestors
  exprSimPtr bodyPtrAssignCases bodyPtrExitCases bodyPtrCtrlCases
  bodyPtrIntCallCase exprSimSource

(* Dependency certificate, not a semantic axiom. Theory.ancestry is transitive:
   fail the isolated import build if any selected interface depends on Pop
   or the mutual induction that consumes it. Print the closure for auditing. *)
val pop_contract_ancestors = Theory.ancestry "-";
val () = if List.exists (fn thy =>
    List.exists (fn forbidden => thy = forbidden)
      ["bodyPtrPop", "bodyPtrExprCases", "bodySimPtrMain"])
    pop_contract_ancestors
  then raise Fail "Pop operand interfaces have a circular ancestor"
  else print ("POP_CONTRACT_ANCESTORS: " ^
              String.concatWith " " pop_contract_ancestors ^ "\n");

(* These references also check that each selected signature is exported. *)
val _ = [leaf_expr_sim_ptr, body_assign_case_ptr, body_return_case_ptr,
         body_stmts_nil_case_ptr, body_stmts_cons_case_ptr,
         body_intcall_case_ptr, expr_sim_pre_body];
