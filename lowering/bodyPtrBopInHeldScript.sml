(*
 * The pointer twin of S1's held membership facts (bodySimBopHeld,
 * exprSimBopHeld): the parts of in and not in not provable at the base.
 *
 * bop_in_nonword_ptr_ok:
 * RESIDUAL, HELD for #742: false at this base (see
 * bodyPtrBopInNonwordEvidence's bop_in_expr_ptr_ok_counterexample): on a
 * literal and on an array variable alike, the lowering compares the
 * needle's lowered word by EQ, a memory pointer for a non-word type, while
 * the source compares the values.  The source type checker repair of
 * vyper-hol PR #742 (integration copy #1092), which restricts membership to
 * primitive word elements, excludes this case; the round that brings it in
 * owns this admission, as it owns S1's body_bop_in_literal_nonword_case and
 * compile_bop_nonword_membership_case.  Not open work here.
 *
 * body_make_array_children_ptr_ok:
 * RESIDUAL, HELD for the bodySim child-closure wave, as S1's
 * body_make_array_children_ok: body_expr_ptr_ok of an array literal does
 * not give its elements', while in and not in on a literal compile the
 * elements directly.  Not open work here.
 *
 * TOP-LEVEL:
 *   bop_in_nonword_ptr_ok — in and not in with a non-word needle
 *   body_make_array_children_ptr_ok — the elements of an array literal
 *)
Theory bodyPtrBopInHeld
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim vyperAST compileEnv

val _ = Parse.hide "body";

Theorem bop_in_nonword_ptr_ok:
  !cx ty bop e1 e2.
    ~is_word_type (expr_type e1) ==>
    (bop = In \/ bop = NotIn) /\
    body_exprs_ptr_ok cx [e1; e2] ==>
    body_expr_ptr_ok cx (Builtin ty (Bop bop) [e1; e2])
Proof
  cheat
QED

Theorem body_make_array_children_ptr_ok:
  !cx a t n elems.
    body_expr_ptr_ok cx (Builtin a (MakeArray t n) elems) /\
    builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
    body_exprs_ptr_ok cx elems
Proof
  cheat
QED
