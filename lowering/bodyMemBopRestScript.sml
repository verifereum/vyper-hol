(* Memory case of the body induction for the binary operators that
   bodyMemBop leaves out: == and != on bytestrings, and in and not in on an
   array that is not a literal.  The memory twin of exprSimOperators'
   compile_bop_rest_case: bytestring equality and membership over non-words
   by bodyMemBopHeld (held for #742), membership over words by
   bodyMemBopRestWord. *)
Theory bodyMemBopRest
Ancestors
  bodyMemBopHeld bodyMemBopRestWord bodyMemoryPreds

Theorem body_bop_rest_mem_case:
  !cx ty bop e1 e2.
    ~(word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) /\
    ~((bop = Eq \/ bop = NotEq) /\
      (expr_type e1 = BaseT AddressT \/
       ?m. expr_type e1 = BaseT (BytesT (Fixed m)))) /\
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
    body_exprs_mem_ok cx [e1; e2] ==> body_expr_mem_ok cx (Builtin ty (Bop bop) [e1; e2])
Proof
  rpt strip_tac >>
  Cases_on `(bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) \/
            (bop = In \/ bop = NotIn) /\ ~is_word_type (expr_type e1)`
  >- (match_mp_tac body_bop_held_mem >> asm_rewrite_tac[]) >>
  match_mp_tac body_bop_rest_word_mem >> asm_rewrite_tac[] >> fs[]
QED
