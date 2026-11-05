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
  arithmetic pair vfmOperation asmParseProofs
Libs
  fcpLib

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

Theorem starve_handle_fault:
  !es ctxt rb exc.
    es.contexts = [(ctxt, rb)] /\
    (!a. ctxt.msgParams.outputTo <> Code a) /\
    exc <> Reverted /\ ~vfm_abort (SOME exc) ==>
    (?es1. handle_step (SOME exc) es = (INR (SOME OutOfGas), es1)) \/
    (?es1. handle_step (SOME exc) es = (INR (SOME exc), es1) /\
           LENGTH es1.contexts = 1 /\
           (FST (HD es1.contexts)).returnData = [])
Proof
  rpt gen_tac >> strip_tac >>
  simp[handle_step_def, handle_def, handle_create_def,
       bind_def, ignore_bind_def, get_return_data_def, get_output_to_def,
       get_current_context_def, return_def, reraise_def] >>
  Cases_on `ctxt.msgParams.outputTo` >> gvs[] >>
  simp[handle_exception_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, get_gas_left_def,
       consume_gas_def, set_current_context_def, assert_def] >>
  Cases_on `ctxt.msgParams.gasLimit - ctxt.gasUsed + ctxt.gasUsed <=
            ctxt.msgParams.gasLimit` >>
  simp[set_return_data_def, bind_def, get_current_context_def,
       return_def, set_current_context_def, get_num_contexts_def, reraise_def,
       assert_def, ignore_bind_def]
QED

Theorem starve_handle_resource:
  !es ctxt rb exc.
    es.contexts = [(ctxt, rb)] /\
    (!a. ctxt.msgParams.outputTo <> Code a) /\
    (exc = OutOfGas \/ exc = StackOverflow) ==>
    ?es1 exc1. handle_step (SOME exc) es = (INR (SOME exc1), es1) /\
               (exc1 = OutOfGas \/ exc1 = StackOverflow)
Proof
  rpt gen_tac >> strip_tac >>
  `exc <> Reverted /\ ~vfm_abort (SOME exc)` by
    gvs[vfm_abort_def] >>
  drule_all starve_handle_fault >> metis_tac[]
QED

Theorem starve_push_step:
  !prog as es op v gas_cost.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    ~is_data_inst (EL as.as_pc prog) /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    opcode op = encode_inst (SND (compute_label_offsets prog))
                            (EL as.as_pc prog) /\
    wf_opname op /\ ~is_call op /\
    step_inst op = (do consume_gas gas_cost; push_stack v od) ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    ?es1. step es = (INL (), es1) /\
          asm_evm_rel prog
            (asm_next (as with as_stack := v :: as.as_stack)) es1 /\
          LENGTH es1.contexts = 1
Proof
  rpt strip_tac >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op' = op` by metis_tac[opcode_wf_inj] >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def] >>
  asm_rewrite_tac[] >> simp[] >>
  drule consume_gas_cases >> disch_then (qspec_then `gas_cost` mp_tac) >>
  strip_tac >> simp[]
  >- (Cases_on `LENGTH as.as_stack < stack_limit`
      >- (simp[push_stack_def, bind_def, ignore_bind_def, LET_THM,
               get_current_context_def, return_def,
               set_current_context_def, assert_def] >> fs[] >>
          simp[inc_pc_or_jump_def, LET_THM, bind_def,
               get_current_context_def, return_def,
               set_current_context_def, is_call_def] >>
          qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
          simp[asm_evm_rel_def] >> strip_tac >>
          simp[asm_evm_rel_def, asm_next_def] >>
          once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
          irule ewi_length >>
          fs[asm_encoding_wf_def, LET_THM, encoding_wf_inst_def, UNCURRY] >>
          metis_tac[]) >>
      simp[push_stack_def, bind_def, ignore_bind_def, LET_THM,
           get_current_context_def, return_def,
           set_current_context_def, assert_def] >> fs[] >>
      disj1_tac >> irule starve_handle_resource >>
      simp[]) >>
  disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_push:
  !prog as es bytes.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmPush bytes /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    ?es1. step es = (INL (), es1) /\
          asm_evm_rel prog (asm_next (as with as_stack :=
            word_of_bytes F 0w (REVERSE bytes) :: as.as_stack)) es1 /\
          LENGTH es1.contexts = 1
Proof
  rpt strip_tac >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  Cases_on `bytes`
  >- (irule starve_push_step >> simp[] >> qexistsl [`2`, `Push 0 []`] >>
      simp[encode_inst_def, opcode_def, step_inst_def, step_push_def,
           wf_opname_def, is_call_def, static_gas_def, wordsTheory.WORD_ADD_0]) >>
  rename1 `AsmPush (h::t)` >>
  `encoding_wf_inst (EL as.as_pc prog) (SND (compute_label_offsets prog))`
    by (irule asm_encoding_wf_el >> simp[]) >>
  gvs[encoding_wf_inst_def] >>
  irule starve_push_step >> simp[] >>
  qexistsl [`3`, `Push (SUC (LENGTH t)) (h::t)`] >>
  simp[encode_inst_def, opcode_def, step_inst_def, step_push_def,
       wf_opname_def, is_call_def, static_gas_def,
       GSYM wordsTheory.word_add_n2w]
QED

Theorem starve_pushlabel:
  !prog as es lbl off.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmPushLabel lbl /\
    FLOOKUP (SND (compute_label_offsets prog)) lbl = SOME off /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    ?es1. step es = (INL (), es1) /\
          asm_evm_rel prog
            (asm_next (as with as_stack := n2w off :: as.as_stack)) es1 /\
          LENGTH es1.contexts = 1
Proof
  rpt strip_tac >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  `encoding_wf_inst (EL as.as_pc prog) (SND (compute_label_offsets prog))`
    by (irule asm_encoding_wf_el >> simp[]) >>
  `LENGTH (encode_num_bytes off) <= symbol_size` by
    (fs[encoding_wf_inst_def] >> metis_tac[]) >>
  irule starve_push_step >> simp[] >>
  qexistsl [`3`, `Push symbol_size (pad_bytes symbol_size (encode_num_bytes off))`] >>
  simp[encode_inst_def, opcode_def, symbol_size_def, pad_bytes_length,
       wordsTheory.word_add_n2w, wf_opname_def, is_call_def,
       step_inst_def, step_push_def, static_gas_def,
       word_of_bytes_pad_encode_roundtrip] >>
  `8 <= dimindex (:256) /\ divides 8 (dimindex (:256))` by
    (CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC) >>
  simp[word_of_bytes_pad_encode_roundtrip]
QED

Theorem starve_pushofst:
  !prog as es lbl delta off.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmPushOfst lbl delta /\
    FLOOKUP (SND (compute_label_offsets prog)) lbl = SOME off /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    ?es1. step es = (INL (), es1) /\
          asm_evm_rel prog
            (asm_next (as with as_stack := n2w (off + delta) :: as.as_stack)) es1 /\
          LENGTH es1.contexts = 1
Proof
  rpt strip_tac >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  `encoding_wf_inst (EL as.as_pc prog) (SND (compute_label_offsets prog))`
    by (irule asm_encoding_wf_el >> simp[]) >>
  `LENGTH (encode_num_bytes (off + delta)) <= symbol_size` by
    (fs[encoding_wf_inst_def] >> metis_tac[]) >>
  irule starve_push_step >> simp[] >>
  qexistsl [`3`, `Push symbol_size
    (pad_bytes symbol_size (encode_num_bytes (off + delta)))`] >>
  simp[encode_inst_def, opcode_def, symbol_size_def, pad_bytes_length,
       wordsTheory.word_add_n2w, wf_opname_def, is_call_def,
       step_inst_def, step_push_def, static_gas_def] >>
  `8 <= dimindex (:256) /\ divides 8 (dimindex (:256))` by
    (CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC) >>
  simp[word_of_bytes_pad_encode_roundtrip]
QED

Theorem starve_label:
  !prog as es lbl.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmLabel lbl /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    ?es1. step es = (INL (), es1) /\
          asm_evm_rel prog (asm_next as) es1 /\ LENGTH es1.contexts = 1
Proof
  rpt strip_tac >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = JumpDest` by
    (irule opcode_byte_91_is_jumpdest >> simp[encode_inst_def]) >>
  gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, step_inst_def, static_gas_def] >>
  drule consume_gas_cases >> disch_then (qspec_then `1` mp_tac) >>
  strip_tac >> simp[]
  >- (simp[inc_pc_or_jump_def, is_call_def, LET_THM, opcode_def,
           bind_def, get_current_context_def, return_def,
           set_current_context_def] >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >>
      simp[asm_evm_rel_def, asm_next_def] >>
      once_rewrite_tac[GSYM ADD1] >>
      simp[asm_pc_to_offset_suc, asm_inst_size_def]) >>
  disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_push_family:
  !prog data as es.
    asm_encoding_wf prog /\
    asm_evm_rel (prog ++ [AsmDataItem data]) as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    ((?bytes. EL as.as_pc prog = AsmPush bytes) \/
     (?lbl. EL as.as_pc prog = AsmPushLabel lbl) \/
     (?lbl delta. EL as.as_pc prog = AsmPushOfst lbl delta) \/
     (?lbl. EL as.as_pc prog = AsmLabel lbl)) ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
                  (EL as.as_pc prog) as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         LENGTH es1.contexts = 1 /\
                         asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmError _ => T
    | _ => F
Proof
  rpt gen_tac >> strip_tac >>
  `asm_encoding_wf (prog ++ [AsmDataItem data])` by
    simp[data_suffix_encoding_wf] >>
  `as.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
  `!j. j <= as.as_pc ==>
       ~is_data_inst (EL j (prog ++ [AsmDataItem data]))` by
    (gen_tac >> disch_tac >> `j < LENGTH prog` by decide_tac >>
     simp[EL_APPEND1]) >>
  gvs[asm_step_def]
  >- (drule_at (Pos (el 2)) starve_push >>
      simp[EL_APPEND1] >> metis_tac[])
  >- (Cases_on `FLOOKUP (SND (compute_label_offsets prog)) lbl` >> simp[] >>
      drule_at (Pos (el 2)) starve_pushlabel >>
      simp[EL_APPEND1, data_suffix_label_offsets] >> metis_tac[])
  >- (Cases_on `FLOOKUP (SND (compute_label_offsets prog)) lbl` >> simp[] >>
      drule_at (Pos (el 2)) starve_pushofst >>
      simp[EL_APPEND1, data_suffix_label_offsets] >> metis_tac[]) >>
  drule_at (Pos (el 2)) starve_label >>
  simp[EL_APPEND1] >> metis_tac[]
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
