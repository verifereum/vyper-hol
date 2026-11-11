(* Memory case of the body induction (bodyMemory's body_mem_mutual): in and
   not in on an array literal. *)
Theory bodyMemBopInLiteral
Ancestors
  bodyMemoryPreds

Theorem body_bop_in_literal_mem_case:
  !cx ty bop e1 a t n elems.
    (bop = In \/ bop = NotIn) /\
    body_exprs_mem_ok cx [e1; Builtin a (MakeArray t n) elems] ==>
    body_expr_mem_ok cx
      (Builtin ty (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  cheat
QED
