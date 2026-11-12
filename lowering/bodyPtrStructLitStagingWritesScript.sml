(* A local output-exclusion probe: inputs may mention an older register,
   but the fresh output of an emitted operation cannot overwrite it. *)
Theory bodyPtrStructLitStagingWrites
Ancestors
  emitHelperProps compileEnv loweringStateRelDefs

Theorem emit_op_older_output_excluded:
  emit_op opc ops sa = (v,sb) /\ not_fresh_at sa x ==>
  !inst. MEM inst (emitted_insts sa sb) ==> ~MEM x inst.inst_outputs
Proof
  strip_tac >> drule emitted_insts_emit_op >>
  simp[not_fresh_at_def] >> rpt strip_tac >> gvs[] >>
  gvs[not_fresh_at_def]
QED
