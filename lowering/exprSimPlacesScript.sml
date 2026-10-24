(*
 * Expression simulation: places (#636, Places)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for subscripts,
 * attributes and pop.  All cheated, for the later #636 PRs.
 *
 * TOP-LEVEL:
 *   compile_subscript_sim — static and dynamic arrays with the bounds-check
 *                           abort, hashmaps, tuples (#558), Places row 1
 *   compile_attribute_sim — struct fields (#558), row 2
 *   compile_pop_sim       — pop on a dynamic array, with the empty-array
 *                           abort, row 3
 *
 * The induction hypothesis is expr_sim_ok of every smaller expression, so
 * of the index and of the whole base chain.  It does not cover a base
 * that is a storage, transient or hashmap place: such a base evaluates to
 * an ArrayRef or HashMapRef, not a value (expr_res_ok leaves those out),
 * and a hashmap is typed by type_place_expr, not well_typed_expr.  Nor does
 * expr_sim describe compile_expr's LocatedValue before unwrap_value, which
 * a subscript of a place reads.  These lemmas' proofs need a place
 * judgment for the base, proved by induction on the place chain with this
 * hypothesis for the indices.
 *)

Theory exprSimPlaces
Ancestors
  list exprSim exprSimHyps vyperAST

Theorem compile_subscript_sim:
  !cenv ann base idx.
    expr_sim_below cenv (expr_size (Subscript ann base idx)) ==>
    expr_sim_ok cenv (Subscript ann base idx)
Proof
  cheat
QED

Theorem compile_attribute_sim:
  !cenv ann base fld.
    expr_sim_below cenv (expr_size (Attribute ann base fld)) ==>
    expr_sim_ok cenv (Attribute ann base fld)
Proof
  cheat
QED

Theorem compile_pop_sim:
  !cenv ann tgt.
    expr_sim_below cenv (expr_size (Pop ann tgt)) ==>
    expr_sim_ok cenv (Pop ann tgt)
Proof
  cheat
QED
