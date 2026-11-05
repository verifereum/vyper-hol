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
  vfmExecution vfmExecutionProp vfmOperation list rich_list asmEncodeParse

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

Theorem gas_step_setup[local]:
  asm_encoding_wf prog /\
  asm_evm_rel (prog ++ [AsmDataItem data]) as es /\
  LENGTH es.contexts = 1 /\
  as.as_pc < LENGTH prog /\
  (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
  EL as.as_pc prog = AsmOp "GAS" ==>
  ?ctxt rb.
    es.contexts = [(ctxt,rb)] /\
    FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME Gas /\
    ctxt.jumpDest = NONE /\
    ctxt.pc = asm_pc_to_offset (prog ++ [AsmDataItem data]) as.as_pc /\
    ctxt.stack = as.as_stack /\
    (!a. ctxt.msgParams.outputTo <> Code a)
Proof
  strip_tac >>
  `asm_encoding_wf (prog ++ [AsmDataItem data])` by
    metis_tac[data_suffix_encoding_wf] >>
  `as.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
  `!j. j <= as.as_pc ==> ~is_data_inst (EL j (prog ++ [AsmDataItem data]))`
    by (gen_tac >> disch_tac >> `j < LENGTH prog` by decide_tac >>
        simp[EL_APPEND1]) >>
  `~is_data_inst (EL as.as_pc (prog ++ [AsmDataItem data]))` by simp[] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = Gas` by
    (irule opcode_wf_inj >> simp[opcode_def, wf_opname_def] >>
     gvs[EL_APPEND1, encode_inst_def, opcode_def, evm_opcode_byte_def, evm_opcode_table_def]) >>
  gvs[] >> metis_tac[]
QED

Theorem gas_singleton_step[local]:
  es.contexts = [(ctxt,rb)] /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME Gas /\
  ctxt.jumpDest = NONE /\
  (!a. ctxt.msgParams.outputTo <> Code a) ==>
  (?es1 exc. step es = (INR (SOME exc),es1) /\
             (exc = OutOfGas \/ exc = StackOverflow)) \/
  ?w gas. step es = (INL (), es with contexts :=
    [(ctxt with <|stack := w :: ctxt.stack; pc := ctxt.pc + 1;
                  gasUsed := gas|>, rb)])
Proof
  strip_tac >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def] >>
  simp[step_inst_def, step_context_def, bind_def, ignore_bind_def,
       consume_gas_def, get_current_context_def, return_def,
       assert_def, set_current_context_def] >>
  IF_CASES_TAC
  >- (simp[push_stack_def, bind_def, ignore_bind_def,
           get_current_context_def, return_def, assert_def,
           set_current_context_def] >>
      IF_CASES_TAC
      >- (simp[inc_pc_or_jump_def, bind_def, get_current_context_def,
               return_def, set_current_context_def, is_call_def, opcode_def] >>
          metis_tac[]) >>
      simp[] >> disj1_tac >> irule gas_handle_step_starved >> simp[]) >>
  simp[] >> disj1_tac >> irule gas_handle_step_starved >> simp[]
QED

Theorem gas_rel_next_stack[local]:
  asm_evm_rel prog as es /\ es.contexts = [(ctxt, rb)] /\
  as.as_pc < LENGTH prog /\ asm_inst_size (EL as.as_pc prog) = 1 ==>
  asm_evm_rel prog (as with <|as_stack := stk; as_pc := as.as_pc + 1|>)
    (es with contexts :=
      [(ctxt with <|stack := stk;
                    pc := asm_pc_to_offset prog as.as_pc + 1;
                    gasUsed := gas|>, rb)])
Proof
  strip_tac >>
  qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
  simp[asm_evm_rel_def] >> strip_tac >> gvs[] >>
  once_rewrite_tac[GSYM arithmeticTheory.ADD1] >>
  simp[asm_pc_to_offset_suc]
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
  rpt strip_tac >>
  drule_all gas_step_setup >> strip_tac >>
  drule_all gas_singleton_step >> strip_tac
  >- metis_tac[]
  >- metis_tac[] >>
  disj2_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  irule gas_rel_next_stack >>
  simp[EL_APPEND1, asm_inst_size_def]
QED
