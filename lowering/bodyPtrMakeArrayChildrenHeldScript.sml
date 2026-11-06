(* RESIDUAL: held for bodySim child-closure wave. *)
Theory bodyPtrMakeArrayChildrenHeld
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim vyperAST compileEnv

val _ = Parse.hide "body";

Theorem body_make_array_children_ptr_ok:
  !cx a t n elems.
    body_expr_ptr_ok cx (Builtin a (MakeArray t n) elems) /\
    builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
    body_exprs_ptr_ok cx elems
Proof
  cheat
QED
