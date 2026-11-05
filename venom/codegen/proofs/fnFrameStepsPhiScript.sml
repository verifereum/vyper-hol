(*
 * Helpers for fnFrameSteps$phi_prefix_frame_sim: a join block's PHI
 * prefix, run from the lineage entry state of its predecessor, against
 * frameRel$fn_frame_inv.
 *)

Theory fnFrameStepsPhi
Ancestors
  fnPlanLineageJoin genFrameSim fnPlanLineage frameRel contextCodegenRel codegenRel
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst livenessDefs dfgDefs cfgDefs

