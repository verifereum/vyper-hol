(* Creation consumes the frame's observed creation outcome, including the
   creator nonce update on failure and the created address on success. *)
Theory asmFrameCreateStep
Ancestors
  asmFrameRel asmFrameCallStep frameObsStep asmCallOracleProps asmDataSuffixProps
  codegenRel asmSem asmWf symbolResolve extCallOracle callTrace frameOutcome
  vfmExecution vfmExecutionProp

Theorem asm_frame_create_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\
  (EL as.as_pc prog = AsmOp "CREATE" \/
   EL as.as_pc prog = AsmOp "CREATE2") ==>
  asm_frame_step_ok prog data es0 as es
Proof
  cheat
QED
