(* An emitted operand cannot alias a subsequently fresh unwrap output. *)
Theory bodyPtrStructLitUnwrapSeparation
Ancestors emitHelperProps compileEnv

Theorem emitted_operand_fresh_separation:
  emit_op opc ops sc = (dst,sm) /\ ~not_fresh_at sm out ==>
  ?r. dst = Var r /\ r <> out
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `r <> out` >>
  `not_fresh_at sm r` by
    simp[Abbr `r`, not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[]
QED
