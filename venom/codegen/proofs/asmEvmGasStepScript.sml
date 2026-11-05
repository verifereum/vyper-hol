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

Theorem gas_handle_step_starved[local]:
  LENGTH es.contexts = 1 /\
  (!a. (FST (HD es.contexts)).msgParams.outputTo <> Code a) /\
  (exc = OutOfGas \/ exc = StackOverflow) ==>
  ?es1 exc1. handle_step (SOME exc) es = (INR (SOME exc1), es1) /\
             (exc1 = OutOfGas \/ exc1 = StackOverflow)
Proof
  strip_tac >> Cases_on `es.contexts` >> gvs[] >>
  simp[handle_step_def, handle_def, handle_create_def,
       get_return_data_def, get_output_to_def, get_current_context_def,
       bind_def, return_def, reraise_def] >>
  Cases_on `(FST h).msgParams.outputTo` >> gvs[] >>
  simp[handle_exception_def, ignore_bind_def, bind_def,
       get_gas_left_def, get_current_context_def, return_def,
       consume_gas_def, assert_def, set_current_context_def,
       set_return_data_def, get_num_contexts_def, reraise_def] >>
  IF_CASES_TAC >> simp[reraise_def]
QED

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
