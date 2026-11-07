(* Loading this library lets EVAL compute eval_constant (with cv_eval) and
   integer arithmetic, as translating Vyper's annotated AST needs. *)
signature vyperConstEvalLib = sig
  val eval_constant_conv : Term.term -> Thm.thm
end
