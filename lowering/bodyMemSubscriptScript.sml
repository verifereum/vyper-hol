(* Memory case of the body induction (bodyMemory's body_mem_mutual):
   subscript. *)
Theory bodyMemSubscript
Ancestors
  bodyMemoryPreds bodyMemMapBase

Theorem body_subscript_mem_case:
  !cx v8 e1 e2.
    (!s'' res t s3 res' t'.
       eval_expr cx e1 s'' = (INL res,t) /\
       (if subscript_reads_base cx e1 e2 then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s3 = (INL res',t') ==>
       body_expr_mem_ok cx e2) /\
    body_expr_mem_ok cx e1 ==>
    body_expr_mem_ok cx (Subscript v8 e1 e2)
Proof
  cheat
QED
