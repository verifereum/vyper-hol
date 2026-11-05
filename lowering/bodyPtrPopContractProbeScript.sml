Theory bodyPtrPopContractProbe
Ancestors
  vyperTypeSystem

(* The tuple bulk-copy diagnostic alone cannot supply a nested Pop target:
   target typing has no tuple-element projection, even for a literal index.
   This excludes tuple-root target paths only, not named struct fields. *)
Theorem pop_tuple_target_subscript_excluded:
  !env bt ts key.
    type_place_target env bt = SOME (Type (TupleT ts)) ==>
    type_place_target env (SubscriptTarget bt key) = NONE
Proof
  rpt strip_tac >>
  simp[Once well_typed_expr_def, subscript_vtype_def]
QED

Theorem pop_tuple_target_attribute_excluded:
  !env bt ts field.
    type_place_target env bt = SOME (Type (TupleT ts)) ==>
    type_place_target env (AttributeTarget bt field) = NONE
Proof
  rpt strip_tac >>
  simp[Once well_typed_expr_def, attribute_type_def]
QED
