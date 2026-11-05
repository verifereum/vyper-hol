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
  asmToBytecodeProofs asmEncodeParse vfmExecution vfmExecutionProp rich_list

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

Theorem starve_step_setup:
  !prog data as es.
    asm_encoding_wf prog /\
    asm_evm_rel (prog ++ [AsmDataItem data]) as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) ==>
    ?ctxt rb op.
      es.contexts = [(ctxt, rb)] /\
      FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME op /\
      wf_opname op /\
      opcode op = encode_inst (SND (compute_label_offsets prog))
                              (EL as.as_pc prog) /\
      ~(LENGTH (assemble (prog ++ [AsmDataItem data])) <= ctxt.pc) /\
      ctxt.msgParams.code = assemble (prog ++ [AsmDataItem data]) /\
      ctxt.msgParams.parsed =
        parse_code 0 FEMPTY (assemble (prog ++ [AsmDataItem data])) /\
      ctxt.stack = as.as_stack /\
      buffer_to_list ctxt.memory = as.as_memory /\
      buffer_length ctxt.memory = LENGTH as.as_memory /\
      ctxt.pc = asm_pc_to_offset prog as.as_pc /\
      ctxt.jumpDest = NONE /\ ctxt.returnData = as.as_returndata /\
      ctxt.logs = as.as_logs /\ es.rollback.accounts = as.as_accounts /\
      es.rollback.tStorage = as.as_transient /\
      es.rollback.toDelete = as.as_pending_deletions /\
      (!a. ctxt.msgParams.outputTo <> Code a)
Proof
  rpt strip_tac >>
  drule_at (Pos (el 2)) asm_evm_step_setup >>
  simp[data_suffix_encoding_wf, data_suffix_label_offsets,
       data_suffix_pc_offset, EL_APPEND1]
QED

Theorem starve_jump_target:
  !prog data off pc.
    asm_encoding_wf prog /\
    (!i. i < LENGTH prog /\ ~is_data_inst (EL i prog) ==>
         !j. j <= i ==> ~is_data_inst (EL j prog)) /\
    FLOOKUP (build_offset_to_pc prog) off = SOME pc ==>
    pc < LENGTH prog /\
    off = asm_pc_to_offset (prog ++ [AsmDataItem data]) pc /\
    off < LENGTH (assemble (prog ++ [AsmDataItem data])) /\
    FLOOKUP (parse_code 0 FEMPTY (assemble (prog ++ [AsmDataItem data])))
            off = SOME JumpDest
Proof
  rpt gen_tac >> strip_tac >>
  gvs[build_offset_to_pc_labels] >>
  `!j. j <= pc ==> ~is_data_inst (EL j prog)` by
    (qpat_x_assum `!i. _` (qspec_then `pc` mp_tac) >>
     simp[is_data_inst_def]) >>
  `!j. j <= pc ==>
       ~is_data_inst (EL j (prog ++ [AsmDataItem data]))` by
    (rpt gen_tac >> disch_tac >> `j < LENGTH prog` by decide_tac >>
     simp[EL_APPEND1]) >>
  `asm_encoding_wf (prog ++ [AsmDataItem data])` by
    simp[data_suffix_encoding_wf] >>
  `pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
  drule_all assemble_parse_exact >> strip_tac >>
  drule_all offset_in_bounds >>
  gvs[data_suffix_pc_offset, data_suffix_label_offsets, EL_APPEND1,
      encode_inst_def] >>
  drule_all opcode_byte_91_is_jumpdest >> simp[]
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
