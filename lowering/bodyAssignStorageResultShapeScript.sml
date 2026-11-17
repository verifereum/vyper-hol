(* Temporary worker: join the storage-backed result constructor boundaries. *)
Theory bodyAssignStorageResultShape
Ancestors
  bodyAssignStorageRecursion bodyAssignStorageBaseOrigin bodyAssignStorageExclusions

Theorem body_assign_storage_result_shape:
  body_inv tops ctx cenv cx /\
  compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  eval_expr cx e es = (INL pv,es1) ==>
  t = expr_type e /\ (!v. pv <> Value v)
Proof
  strip_tac >> mp_tac body_assign_storage_result_shape_from_cases >>
  (impl_tac >-
    (rpt conj_tac >>
     metis_tac[body_assign_storage_expr_cases, body_assign_storage_base_result])) >>
  disch_then drule >> metis_tac[]
QED
