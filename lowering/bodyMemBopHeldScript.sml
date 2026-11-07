(* Memory case of the body induction: the binary operators whose source
   semantics at the base disagree with their lowering.

   HELD for #742, as S1's exprSimBopHeld (compile_bop_bytestring_eqne_case,
   compile_bop_nonword_membership_case on s1-ops-widened-expr), which is
   false at the base: == and != on bytestrings compare keccak256 hashes in
   the lowering and the bytes in the source; in and not in on an array of
   non-words compare each element's word in the lowering and the values in
   the source. *)
Theory bodyMemBopHeld
Ancestors
  bodyMemoryPreds compileEnv bodyMemBopHeldFacts bodyMemBopHeldHash

Theorem body_bop_held_mem:
  !cx ty bop e1 e2.
    ((bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) \/
     (bop = In \/ bop = NotIn) /\ ~is_word_type (expr_type e1)) /\
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
