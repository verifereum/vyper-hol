(* Residual leaf for non-literal membership on an internal-call haystack. *)
Theory bodyPtrBopInCallHaystackResidual
Ancestors bodyPtrDefs bodySim exprSimHypsDefs loweringPosts bodyPtrPreds vyperAST compileEnv

(* RESIDUAL: internal-call haystack under Decision 18; held for the post_value_type_widens port, cf. exprSimBopRestWordCompose *)
Theorem bop_in_nonliteral_call_haystack_ptr:
  post_value_type cenv e2 <> expr_type e2 /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  expr_type e2 = ArrayT (expr_type e1) bd /\
  (!a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
  body_exprs_ptr_ok cx [e1;e2] /\ body_inv tops ctx cenv cx ==>
  expr_sim_ptr d ctx PG fn cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  cheat
QED
