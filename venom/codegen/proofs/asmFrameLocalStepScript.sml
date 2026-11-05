(*
 * Every instruction but CALL and STATICCALL against the frame's run:
 * the single-context steps (asmEvmStepStarve, asmEvmGasStep) moved into
 * the nested frame (evmStepTransplant), with the frame's trace and
 * run_call carried across the step (frameObsStep).
 *
 * TOP-LEVEL:
 *   asm_frame_local_step
 *)

Theory asmFrameLocalStep
Ancestors
  asmFrameRel frameObsStep evmStepTransplant asmEvmStepStarve asmEvmGasStep
  evmStepSim asmDataSuffixProps codegenRel asmSem asmWf symbolResolve
  callTrace frameOutcome vfmExecution vfmExecutionProp

Theorem asm_frame_local_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\ ~is_data_inst (EL as.as_pc prog) /\
  EL as.as_pc prog <> AsmOp "CALL" /\ EL as.as_pc prog <> AsmOp "STATICCALL" ==>
  asm_frame_step_ok prog data es0 as es
Proof
  cheat
QED
