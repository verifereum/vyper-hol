Theory loweringBudgetCausalRecursion
Ancestors
  bodyFullPreds loweringCallBudgetHistory sourceCallCountWitness
Libs
  loweringBudgetCausalSyntaxLib

val _ = print ("Generated " ^ Int.toString (length loweringBudgetCausalSyntaxLib.case_terms) ^ " cases\n");


val _ = List.app (fn (n,t) => print (n ^ " free=" ^
  String.concatWith "," (map term_to_string (free_vars t)) ^ "\n"))
 [("expr-base",expr_base_exists_tm),("tuple",tuple_exists_tm)];
val _ = print (term_to_string expr_base_body ^ "\n");
val _ = print (term_to_string tuple_body ^ "\n");
