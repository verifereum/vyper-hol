(*
 * Helpers for fnFrameBoundary$gen_invoke_frame_sim: the INVOKE step
 * against frameRel$fn_frame_inv, given the callee's function simulation.
 *)

Theory fnFrameBoundaryInvoke
Ancestors
  fnFrameBoundaryGenRet genFrameSim frameRel contextCodegenRel codegenRel
  regularPostfixSim preparedPrefixSim asmFrame prefixSim stackOpSim
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst fcgDefs livenessDefs dfgDefs
  venomWf venomEffects stackPlanOps asmIR frameViewFacts finite_map
  callLayoutDefs fmpWfDefs list rich_list reorderSim planWf stackModel
