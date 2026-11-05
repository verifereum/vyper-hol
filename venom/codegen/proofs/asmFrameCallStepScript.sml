(*
 * CALL and STATICCALL against the frame's run.  The EVM either takes the
 * call at the frame's depth (precompiles, calls that fail before a
 * child starts) or runs a child frame back to this one; either way the
 * frame's call trace records one request and its outcome, which is the
 * outcome the assembly takes from as_outcomes.
 *
 * TOP-LEVEL:
 *   asm_frame_call_step
 *)

Theory asmFrameCallStep
Ancestors
  asmFrameRel frameObsStep evmStepSim asmCallOracleProps asmDataSuffixProps
  codegenRel asmSem asmWf symbolResolve extCallOracle callTrace frameOutcome
  vfmExecution vfmExecutionProp vfmRunCall vfmContextLength vfmDecreasesGas

Theorem asm_frame_call_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\
  (EL as.as_pc prog = AsmOp "CALL" \/ EL as.as_pc prog = AsmOp "STATICCALL") ==>
  asm_frame_step_ok prog data es0 as es
Proof
  cheat
QED
