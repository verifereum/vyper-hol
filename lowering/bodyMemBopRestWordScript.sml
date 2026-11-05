(* Memory case of the body induction: the binary operators bodyMemBop and
   bodyMemBopHeld leave, which typing narrows to in and not in with a word
   needle on an array that is not a literal.  The memory twin of S1's
   exprSimBopRestWord (compile_bop_rest_word_case). *)
Theory bodyMemBopRestWord
Ancestors
  bodyMemoryPreds compileEnv

Theorem body_bop_rest_word_mem:
  !cx ty bop e1 e2.
    ~((bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)) /\
    ~((bop = In \/ bop = NotIn) /\ ~is_word_type (expr_type e1)) /\
    ~(word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) /\
    ~((bop = Eq \/ bop = NotEq) /\
      (expr_type e1 = BaseT AddressT \/
       ?m. expr_type e1 = BaseT (BytesT (Fixed m)))) /\
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
    body_exprs_mem_ok cx [e1; e2] ==> body_expr_mem_ok cx (Builtin ty (Bop bop) [e1; e2])
Proof
  cheat
QED
