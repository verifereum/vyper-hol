(*
 * The pointer twin of S1's bodySimBopHeld: in and not in on an array
 * literal of non-words, the part not provable at the base.
 *
 * bop_in_literal_nonword_ptr_ok:
 * RESIDUAL, HELD for #742: false at this base (see
 * bodyPtrBopInNonwordEvidence's bop_in_expr_ptr_ok_counterexample): the
 * lowering compares each element's lowered word, a memory pointer for a
 * non-word type, while the source compares the values.  The source type
 * checker repair of vyper-hol PR #742 (integration copy #1092), which
 * restricts membership to primitive word elements, excludes this case; the
 * round that brings it in owns this admission, as it owns S1's
 * body_bop_in_literal_nonword_case.  Not open work here.
 *
 * TOP-LEVEL:
 *   bop_in_literal_nonword_ptr_ok — in and not in on a literal of non-words
 *)
Theory bodyPtrBopInHeld
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim vyperAST compileEnv

val _ = Parse.hide "body";

Theorem bop_in_literal_nonword_ptr_ok:
  !cx ty bop e1 a t n elems.
    ~is_word_type (expr_type e1) ==>
    (bop = In \/ bop = NotIn) /\
    body_exprs_ptr_ok cx [e1; Builtin a (MakeArray t n) elems] ==>
    body_expr_ptr_ok cx
      (Builtin ty (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  cheat
QED
