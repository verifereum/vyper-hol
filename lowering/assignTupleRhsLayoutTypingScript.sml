(* Tuple RHS annotations retain tuple shape at the physical return layout. *)
Theory assignTupleRhsLayoutTyping
Ancestors
  assignTupleResidualBoundary exprSimHyps exprSimHypsDefs typedMemoryCopy
  exprLowering vyperAST vyperTypeSystem list

Theorem tuple_rhs_lowered_layout_fits:
  expr_body_pre cenv cx env e es /\ expr_type e = TupleT ats ==>
  ?sts. lowered_value_type cenv e = TupleT sts /\
    (sts = ats \/ arg_types_fit sts ats)
Proof
  strip_tac >>
  `well_typed_expr env e /\ expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all tuple_rhs_post_lowered_type >> strip_tac >>
  drule_all post_value_type_widens >>
  asm_rewrite_tac[] >> disch_tac >>
  irule typed_copy_tuple_widening >> metis_tac[]
QED
