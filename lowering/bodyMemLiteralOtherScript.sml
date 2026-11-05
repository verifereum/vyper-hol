(* Memory case of the body induction (bodyMemory's body_mem_mutual): a literal
   of a non-word type (bodyLiteralForceMemory's body_literal_word_mem_case has
   the word case). *)
Theory bodyMemLiteralOther
Ancestors
  bodyMemoryPreds

Theorem body_literal_other_mem_case:
  !cx ann l. ~is_word_type ann ==> body_expr_mem_ok cx (Literal ann l)
Proof
  cheat
QED
