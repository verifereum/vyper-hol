(* A mismatched value dispatch is excluded by the source typing precondition. *)
Theory bodyMemSubscriptMismatch
Ancestors
  exprSimMemDefs exprSimHypsDefs exprSimSource exprLowering
  placeTypingProps vyperAST vyperTypeSystem

Theorem compile_subscript_mismatch_vv_sim_mem:
  place_type cenv obj = ValPT bt /\ bt <> expr_type obj /\
  expr_body_pre cenv cx env (Subscript ann obj idx) es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Subscript ann obj idx) es
Proof
  rw[expr_body_pre_def, expr_sim_inv_def] >>
  gvs[Once well_typed_expr_def]
  >- (drule_all place_type_well_typed_on_defined >> simp[]) >>
  drule_all place_type_checked_place_on_defined >> strip_tac >>
  drule type_place_expr_vtype_annotation >>
  Cases_on `vt` >> gvs[value_type_place_def, vtype_annotation_ok_def]
QED
