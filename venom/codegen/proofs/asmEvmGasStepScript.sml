(*
 * GAS against one EVM step of a single-context frame: the EVM raises
 * OutOfGas or StackOverflow, or pushes some word w, the reading, and the
 * assembly state with w pushed and the pc advanced corresponds to the
 * result.
 *
 * TOP-LEVEL:
 *   asm_evm_gas_step
 *)

Theory asmEvmGasStep
Ancestors
  evmStepSim asmDataSuffixProps codegenRel asmSem asmWf symbolResolve
  vfmExecution vfmExecutionProp

Theorem asm_evm_gas_step:
  !prog data as es.
    asm_encoding_wf prog /\
    asm_evm_rel (prog ++ [AsmDataItem data]) as es /\
    LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "GAS" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    ?es1 w. step es = (INL (), es1) /\ LENGTH es1.contexts = 1 /\
            (FST (HD es1.contexts)).stack = w :: (FST (HD es.contexts)).stack /\
            asm_evm_rel (prog ++ [AsmDataItem data])
              (as with <| as_stack := w :: as.as_stack;
                          as_pc := as.as_pc + 1 |>) es1
Proof
  cheat
QED
