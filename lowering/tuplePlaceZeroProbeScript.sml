(* Admissibility checks for the zero-layout tuple-store suspicion. *)
Theory tuplePlaceZeroProbe
Ancestors
  stmtLowering exprLowering vyperTypeSystem finite_map

Theorem zero_empty_tuple_not_assignable:
  !tenv. ~assignable_type tenv (TupleT [TupleT []])
Proof
  simp[assignable_type_def]
QED

Theorem zero_empty_tuple_evaluates:
  evaluate_type FEMPTY (TupleT [TupleT []]) = SOME (TupleTV [TupleTV []])
Proof
  EVAL_TAC
QED

Theorem zero_fixed_array_not_evaluable:
  !tenv ty. evaluate_type tenv (ArrayT ty (Fixed 0)) = NONE
Proof
  rpt gen_tac >> simp[Once vyperValueTheory.evaluate_type_def] >>
  Cases_on `evaluate_type tenv ty` >> simp[]
QED

Theorem zero_empty_struct_not_assignable:
  !tenv id. FLOOKUP tenv id = SOME (StructArgs []) ==>
    ~assignable_type tenv (TupleT [StructT id])
Proof
  rpt strip_tac >> gvs[assignable_type_def]
QED
