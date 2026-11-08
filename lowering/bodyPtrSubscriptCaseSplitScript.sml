(*
 * The dispatch of a subscript on its base's place_type, for
 * bodyPtrSubscript's case split: a value-typed base's dispatch type is its
 * own type, and is an array's or a tuple's.  The S1 twins are exprSimPlaces'
 * compile_subscript_mismatch_case and subscript_base_array_or_tuple (local
 * there); the proofs are theirs.
 *
 * TOP-LEVEL:
 *   subscript_value_base_type
 *)
Theory bodyPtrSubscriptCaseSplit
Ancestors
  exprSimHypsDefs placeTypingProps exprLowering vyperAST vyperTypeSystem
  vyperTypeCallGraph

Theorem subscript_dispatch_type[local]:
  !cenv cx env ann obj idx es bt.
    expr_body_pre cenv cx env (Subscript ann obj idx) es /\
    place_type cenv obj = ValPT bt ==>
    bt = expr_type obj
Proof
  rpt gen_tac >> CCONTR_TAC >>
  gvs[expr_body_pre_def, expr_sim_inv_def] >>
  gvs[Once well_typed_expr_def]
  >- (drule_all place_type_well_typed_on_defined >> simp[]) >>
  drule_all place_type_checked_place_on_defined >> strip_tac >>
  drule type_place_expr_vtype_annotation >>
  Cases_on `vt` >> gvs[value_type_place_def, vtype_annotation_ok_def]
QED

Theorem subscript_base_array_or_tuple[local]:
  !cenv cx env ann obj idx es.
    expr_body_pre cenv cx env (Subscript ann obj idx) es /\
    place_type cenv obj = ValPT (expr_type obj) ==>
    (?et bd. expr_type obj = ArrayT et bd) \/ (?tys. expr_type obj = TupleT tys)
Proof
  rpt gen_tac >> simp[expr_body_pre_def, expr_sim_inv_def] >>
  simp[Once well_typed_expr_def] >> rpt strip_tac
  >- (Cases_on `expr_type obj` >> gvs[subscript_type_ok_def]) >>
  drule_all place_type_checked_place_on_defined >> strip_tac >>
  Cases_on `vt` >> gvs[value_type_place_def] >>
  Cases_on `expr_type obj` >> gvs[subscript_vtype_def]
QED

Theorem subscript_value_base_type:
  !cenv cx env ann obj idx es bt.
    expr_body_pre cenv cx env (Subscript ann obj idx) es /\
    place_type cenv obj = ValPT bt ==>
    bt = expr_type obj /\
    ((?et bd. expr_type obj = ArrayT et bd) \/
     (?tys. expr_type obj = TupleT tys))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all subscript_dispatch_type >> strip_tac >> gvs[] >>
  drule_all subscript_base_array_or_tuple >> simp[]
QED
