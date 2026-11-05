(* Ghost frames preserve provenance, but runtime address stability is separate. *)
Theory bodyPtrPrecompileBuiltinsGhost
Ancestors bodyPtrDefs ptrDiscipline venomState freshWrites

Theorem ghost_kept_operand_taint:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  op_taint tn op = op_taint tn0 op
Proof
  strip_tac >> Cases_on `op` >> gvs[op_taint_def, ghost_kept_def]
QED

Theorem ghost_kept_provenance:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ not_fresh_at sa p ==>
  FLOOKUP G p = FLOOKUP G0 p
Proof
  simp[ghost_kept_def]
QED

Theorem ghost_kept_ptr_covers:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ not_fresh_at sa p /\
  eval_operand (Var p) s0 = SOME w /\ eval_operand (Var p) s = SOME w /\
  ptr_covers G0 tn0 p s0 m ==>
  ptr_covers G tn p s m
Proof
  rw[ghost_kept_def, ptr_covers_def, eval_operand_def] >> gvs[] >>
  metis_tac[]
QED
