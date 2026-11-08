(* Assignability obstruction for the constructor containing the assignment. *)
Theory immutableDeployEmptyAssignedTyping
Ancestors
  immutableDeployEmptyAssignedSource immutableDeployEmptyAssignedCode
  immutableDeployEmptyValid immutableDeployEmptyStacked immutableDeployEmptySource
  immutableDeployEmptyDeployment vyperContext vyperTypeInvariants vyperTypeSystem

Theorem assigned_immutable_empty_type_not_assignable:
  ~assignable_type (get_tenv assigned_immutable_cx) (StructT (NONE,"Empty"))
Proof
  simp[assignable_type_def] >> EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED
