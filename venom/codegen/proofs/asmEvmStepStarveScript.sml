(*
 * One assembly step against one EVM step of a single-context frame,
 * with the EVM's resource limits as the only difference: the EVM step
 * matches the assembly step, or raises OutOfGas or StackOverflow, which
 * the assembly doesn't model.  Unlike evmStepSim's asm_evm_step there is
 * no stack bound, the frame's code may have a data suffix after the
 * program, and no other EVM exception is absorbed.  Data must come only
 * at the end of prog: a data item before a label would make the EVM
 * parse the label's JUMPDEST as push data.
 *
 * TOP-LEVEL:
 *   asm_evm_step_starve - every instruction but GAS and the calls
 *)

Theory asmEvmStepStarve
Ancestors
  evmStepSim asmDataSuffixProps codegenRel asmSem asmWf symbolResolve
  asmToBytecodeProofs vfmExecution vfmExecutionProp

(* TEMPORARY, until build_offset_to_pc maps only AsmLabel offsets (its
   own piece on the codegen branch): that map's domain is exactly the
   labels' offsets, each mapping to its label's index. *)
Theorem build_offset_to_pc_labels[local]:
  !prog off pc.
    FLOOKUP (build_offset_to_pc prog) off = SOME pc <=>
    pc < LENGTH prog /\ (?l. EL pc prog = AsmLabel l) /\
    off = asm_pc_to_offset prog pc
Proof
  cheat
QED

Theorem asm_evm_step_starve:
  !prog data as es.
    asm_encoding_wf prog /\
    asm_evm_rel (prog ++ [AsmDataItem data]) as es /\
    LENGTH es.contexts = 1 /\ (?d. es.msdomain = Collect d) /\
    ~(FST (HD es.contexts)).msgParams.static /\
    (!i. i < LENGTH prog /\ ~is_data_inst (EL i prog) ==>
         !j. j <= i ==> ~is_data_inst (EL j prog)) /\
    as.as_pc < LENGTH prog /\ ~is_data_inst (EL as.as_pc prog) /\
    (!name. EL as.as_pc prog = AsmOp name ==> ~is_evm_call_name name) /\
    EL as.as_pc prog <> AsmOp "GAS" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
                  (EL as.as_pc prog) as of
      AsmOK as1 =>
        ?es1. step es = (INL (), es1) /\ LENGTH es1.contexts = 1 /\
              asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmHalt as1 =>
        ?es1. step es = (INR NONE, es1) /\ LENGTH es1.contexts = 1 /\
              asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmRevert as1 =>
        ?es1. step es = (INR (SOME Reverted), es1) /\ LENGTH es1.contexts = 1 /\
              asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmFault as1 =>
        ?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> Reverted /\
                  ~vfm_abort (SOME exc) /\ LENGTH es1.contexts = 1 /\
                  (FST (HD es1.contexts)).returnData = []
    | AsmError _ => T
Proof
  cheat
QED
