(* Memory case of the body induction (bodyMemory's body_mem_mutual): a binary
   operator on two operands, but in and not in on an array literal. *)
Theory bodyMemBop
Ancestors
  bodyMemoryPreds

Theorem body_bop_mem_case:
  !cx ty bop e1 e2.
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
    body_exprs_mem_ok cx [e1; e2] ==> body_expr_mem_ok cx (Builtin ty (Bop bop) [e1; e2])
Proof
  cheat
QED
