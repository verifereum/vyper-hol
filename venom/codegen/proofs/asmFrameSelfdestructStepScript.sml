(* The EIP-6780 branch is selected by the executing account's creation flag. *)
Theory asmFrameSelfdestructStep
Ancestors
  asmFrameRel asmFrameLocalStep frameObsStep evmStepTransplant asmEvmStepStarve
  evmStepSim asmDataSuffixProps codegenRel asmSem asmWf symbolResolve
  callTrace frameOutcome vfmExecution vfmExecutionProp

Theorem asm_frame_selfdestruct_step_created:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp "SELFDESTRUCT" /\
  (as.as_call_ctx.cc_created_in_tx =
   account_empty (lookup_account (FST (HD es.contexts)).msgParams.callee
                  es.originalAccounts)) ==>
  asm_frame_step_ok prog data es0 as es
Proof
  cheat
QED
