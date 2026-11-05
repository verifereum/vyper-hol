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
  arithmetic pair vfmOperation asmParseProofs spillSim list
Libs
  fcpLib

(* build_offset_to_pc's domain is exactly the labels' offsets, each
   mapping to its label's index. *)
Theorem build_offset_to_pc_labels[local]:
  !prog off pc.
    FLOOKUP (build_offset_to_pc prog) off = SOME pc <=>
    pc < LENGTH prog /\ (?l. EL pc prog = AsmLabel l) /\
    off = asm_pc_to_offset prog pc
Proof
  rpt gen_tac >> eq_tac
  >- (strip_tac >> imp_res_tac offset_to_pc_reverse >>
      imp_res_tac offset_to_pc_label >> simp[] >> metis_tac[])
  >- (rw[] >> irule offset_to_pc_inverse_proof >> simp[])
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

Theorem starve_stack_step:
  !prog as es op n cost f.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    n <= LENGTH as.as_stack /\
    opcode op = encode_inst (SND (compute_label_offsets prog))
                            (EL as.as_pc prog) /\
    wf_opname op /\ ~is_call op /\
    step_inst op = (do args <- pop_stack n;
                      consume_gas (cost args); push_stack (f args) od) ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    ?es1. step es = (INL (), es1) /\
          asm_evm_rel prog (asm_next (as with as_stack :=
            f (TAKE n as.as_stack) :: DROP n as.as_stack)) es1 /\
          LENGTH es1.contexts = 1
Proof
  rpt strip_tac >>
  `~is_data_inst (EL as.as_pc prog)` by simp[] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op' = op` by metis_tac[opcode_wf_inj] >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def] >>
  asm_rewrite_tac[] >> simp[] >>
  simp[pop_stack_def, consume_gas_def, push_stack_def, bind_def,
       ignore_bind_def, get_current_context_def, return_def,
       set_current_context_def, assert_def] >> fs[] >>
  Cases_on `ctxt.gasUsed + cost (TAKE n as.as_stack) <= ctxt.msgParams.gasLimit`
  >- (simp[] >> Cases_on `LENGTH (DROP n as.as_stack) < stack_limit`
      >- (fs[] >>
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
      fs[] >> disj1_tac >> irule starve_handle_resource >> simp[]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_binop:
  !prog as es op f as1.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    opcode op = encode_inst (SND (compute_label_offsets prog))
                            (EL as.as_pc prog) /\
    wf_opname op /\ ~is_call op /\
    step_inst op = step_binop op f /\ asm_binop f as = AsmOK as1 ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    ?es1. step es = (INL (), es1) /\
          asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
Proof
  rpt strip_tac >>
  Cases_on `as.as_stack` >> gvs[asm_binop_def] >>
  Cases_on `t` >> gvs[] >>
  drule_at (Pos (el 2)) starve_stack_step >>
  disch_then (qspecl_then [`op`, `2`, `\args. static_gas op`,
                          `\args. f (EL 0 args) (EL 1 args)`] mp_tac) >>
  simp[step_binop_def]
QED

Theorem starve_unop:
  !prog as es op f as1.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    opcode op = encode_inst (SND (compute_label_offsets prog))
                            (EL as.as_pc prog) /\
    wf_opname op /\ ~is_call op /\
    step_inst op = step_monop op f /\ asm_unop f as = AsmOK as1 ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    ?es1. step es = (INL (), es1) /\
          asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
Proof
  rpt strip_tac >>
  Cases_on `as.as_stack` >> gvs[asm_unop_def] >>
  drule_at (Pos (el 2)) starve_stack_step >>
  disch_then (qspecl_then [`op`, `1`, `\args. static_gas op`,
                          `\args. f (EL 0 args)`] mp_tac) >>
  simp[step_monop_def]
QED

Theorem starve_ternop:
  !prog as es op f as1.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    opcode op = encode_inst (SND (compute_label_offsets prog))
                            (EL as.as_pc prog) /\
    wf_opname op /\ ~is_call op /\
    step_inst op = (do args <- pop_stack 3; consume_gas (static_gas op);
                      push_stack (f (EL 0 args) (EL 1 args) (EL 2 args)) od) /\
    asm_ternop f as = AsmOK as1 ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    ?es1. step es = (INL (), es1) /\
          asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
Proof
  rpt strip_tac >>
  Cases_on `as.as_stack` >> gvs[asm_ternop_def] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  drule_at (Pos (el 2)) starve_stack_step >>
  disch_then (qspecl_then [`op`, `3`, `\args. static_gas op`,
                          `\args. f (EL 0 args) (EL 1 args) (EL 2 args)`] mp_tac) >>
  simp[]
QED

Theorem starve_binop_result:
  !prog as es op f.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    opcode op = encode_inst (SND (compute_label_offsets prog))
                            (EL as.as_pc prog) /\
    wf_opname op /\ ~is_call op /\ step_inst op = step_binop op f ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_binop f as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `asm_binop f as` >> simp[]
  >- (irule starve_binop >> metis_tac[]) >>
  gvs[asm_binop_def, AllCaseEqs()]
QED

Theorem starve_unop_result:
  !prog as es op f.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    opcode op = encode_inst (SND (compute_label_offsets prog))
                            (EL as.as_pc prog) /\
    wf_opname op /\ ~is_call op /\ step_inst op = step_monop op f ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_unop f as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `asm_unop f as` >> simp[]
  >- (irule starve_unop >> metis_tac[]) >>
  gvs[asm_unop_def, AllCaseEqs()]
QED

(* Opcode selection is the only varying input to these pure stack cases. *)
fun starve_pure_dispatch_tac bridge opq extra =
  irule bridge >> simp[] >> qexists opq >>
  simp ([step_inst_def, opcode_def, encode_inst_def,
         wf_opname_def, is_call_def] @ extra) >> EVAL_TAC;

Theorem starve_compare_dispatch:
  !prog as es name r.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    asm_step_compare name as = SOME r ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case r of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `asm_step_compare _ _ = _` mp_tac >>
  simp[asm_step_compare_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[]
  >- starve_pure_dispatch_tac starve_binop_result `LT` []
  >- starve_pure_dispatch_tac starve_binop_result `GT` []
  >- starve_pure_dispatch_tac starve_binop_result `SLT` []
  >- starve_pure_dispatch_tac starve_binop_result `SGT` []
  >- starve_pure_dispatch_tac starve_binop_result `Eq` [] >>
  starve_pure_dispatch_tac starve_unop_result `IsZero` []
QED

Theorem starve_bitwise_dispatch:
  !prog as es name r.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    asm_step_bitwise name as = SOME r ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case r of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `asm_step_bitwise _ _ = _` mp_tac >>
  simp[asm_step_bitwise_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[]
  >- starve_pure_dispatch_tac starve_binop_result `And` []
  >- starve_pure_dispatch_tac starve_binop_result `Or` []
  >- starve_pure_dispatch_tac starve_binop_result `XOr` []
  >- starve_pure_dispatch_tac starve_unop_result `Not` []
  >- starve_pure_dispatch_tac starve_binop_result `ShL` []
  >- starve_pure_dispatch_tac starve_binop_result `ShR` []
  >- starve_pure_dispatch_tac starve_binop_result `SAR` []
  >- starve_pure_dispatch_tac starve_binop_result `SignExtend` [] >>
  starve_pure_dispatch_tac starve_binop_result `Byte` []
QED

Theorem starve_ternop_result:
  !prog as es op f.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    opcode op = encode_inst (SND (compute_label_offsets prog))
                            (EL as.as_pc prog) /\
    wf_opname op /\ ~is_call op /\
    step_inst op = (do args <- pop_stack 3; consume_gas (static_gas op);
                      push_stack (f (EL 0 args) (EL 1 args) (EL 2 args)) od) ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_ternop f as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `asm_ternop f as` >> simp[]
  >- (irule starve_ternop >> metis_tac[]) >>
  gvs[asm_ternop_def, AllCaseEqs()]
QED

Theorem starve_exp_result:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "EXP" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_binop word_exp as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >>
  Cases_on `as.as_stack` >> simp[asm_binop_def] >>
  Cases_on `t` >> simp[] >>
  drule_at (Pos (el 2)) starve_stack_step >>
  disch_then (qspecl_then [`Exp`, `2`,
    `\args. static_gas Exp + exp_per_byte_cost *
       (if EL 1 args = 0w then 0 else SUC (LOG2 (w2n (EL 1 args)) DIV 8))`,
    `\args. word_exp (EL 0 args) (EL 1 args)`] mp_tac) >>
  simp[step_inst_def, step_exp_def, LET_THM, opcode_def, encode_inst_def,
       wf_opname_def, is_call_def] >>
  EVAL_TAC
QED

Theorem starve_arith_dispatch:
  !prog as es name r.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    asm_step_arith name as = SOME r ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case r of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `asm_step_arith _ _ = _` mp_tac >>
  simp[asm_step_arith_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[]
  >- starve_pure_dispatch_tac starve_binop_result `Add` []
  >- starve_pure_dispatch_tac starve_binop_result `Mul` []
  >- starve_pure_dispatch_tac starve_binop_result `Sub` []
  >- starve_pure_dispatch_tac starve_binop_result `Div`
       [step_binop_def, with_zero_def]
  >- starve_pure_dispatch_tac starve_binop_result `SDiv`
       [step_binop_def, with_zero_def]
  >- starve_pure_dispatch_tac starve_binop_result `Mod`
       [step_binop_def, with_zero_def]
  >- starve_pure_dispatch_tac starve_binop_result `SMod`
       [step_binop_def, with_zero_def]
  >- (irule starve_exp_result >> simp[])
  >- starve_pure_dispatch_tac starve_ternop_result `AddMod`
       [step_modop_def, LET_THM, wordsTheory.w2n_eq_0] >>
  starve_pure_dispatch_tac starve_ternop_result `MulMod`
    [step_modop_def, LET_THM, wordsTheory.w2n_eq_0]
QED

Theorem starve_pop:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "POP" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_pop as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_pop_def] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = Pop` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def] >>
  simp[step_inst_def, step_pop_def, pop_stack_def, consume_gas_def,
       bind_def, ignore_bind_def, get_current_context_def, return_def,
       set_current_context_def, assert_def] >> fs[] >>
  IF_CASES_TAC
  >- (simp[] >> disj2_tac >>
      simp[inc_pc_or_jump_def, LET_THM, bind_def,
           get_current_context_def, return_def,
           set_current_context_def, is_call_def] >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >>
      simp[asm_evm_rel_def, asm_next_def] >>
      once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
      simp[opcode_def, asm_inst_size_def] >> EVAL_TAC) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_msize:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "MSIZE" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    ?es1. step es = (INL (), es1) /\ LENGTH es1.contexts = 1 /\
      asm_evm_rel prog (asm_next (as with as_stack :=
        n2w (LENGTH as.as_memory) :: as.as_stack)) es1
Proof
  rpt strip_tac >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = MSize` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def] >>
  simp[step_inst_def, step_context_def, consume_gas_def, push_stack_def,
       bind_def, ignore_bind_def, get_current_context_def, return_def,
       set_current_context_def, assert_def] >> fs[] >>
  IF_CASES_TAC
  >- (simp[] >> Cases_on `LENGTH as.as_stack < stack_limit`
      >- (fs[] >> simp[] >> disj2_tac >>
          simp[inc_pc_or_jump_def, LET_THM, bind_def,
               get_current_context_def, return_def,
               set_current_context_def, is_call_def] >>
          qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
          simp[asm_evm_rel_def] >> strip_tac >>
          simp[asm_evm_rel_def, asm_next_def] >>
          once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
          simp[opcode_def, asm_inst_size_def] >> EVAL_TAC) >>
      fs[] >> disj1_tac >> irule starve_handle_resource >> simp[]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_tload:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "TLOAD" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_tload as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_tload_def, LET_THM] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = TLoad` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def] >>
  simp[step_inst_def, step_sload_def, pop_stack_def, consume_gas_def,
       push_stack_def, get_callee_def, get_tStorage_def,
       lookup_transient_storage_def, vfmStateTheory.lookup_storage_def,
       bind_def, ignore_bind_def, get_current_context_def, return_def,
       set_current_context_def, assert_def, fail_def, LET_THM] >> fs[] >>
  IF_CASES_TAC
  >- (simp[] >> Cases_on `LENGTH t < stack_limit`
      >- (fs[] >> simp[] >> disj2_tac >>
          simp[inc_pc_or_jump_def, LET_THM, bind_def,
               get_current_context_def, return_def,
               set_current_context_def, is_call_def] >>
          qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
          simp[asm_evm_rel_def] >> strip_tac >>
          simp[asm_evm_rel_def, asm_next_def] >>
          once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
          simp[opcode_def, asm_inst_size_def] >> EVAL_TAC) >>
      fs[] >> disj1_tac >> irule starve_handle_resource >> simp[]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_tstore:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    ~(FST (HD es.contexts)).msgParams.static /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "TSTORE" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_tstore as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_tstore_def, LET_THM] >>
  Cases_on `t` >> simp[] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = TStore` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def] >>
  simp[step_inst_def, step_sstore_def, pop_stack_def, consume_gas_def,
       get_callee_def, get_tStorage_def, get_static_def, assert_not_static_def,
       write_transient_storage_def, set_tStorage_def,
       lookup_transient_storage_def, update_transient_storage_def,
       vfmStateTheory.update_storage_def,
       bind_def, ignore_bind_def, get_current_context_def, return_def,
       set_current_context_def, assert_def, fail_def, LET_THM] >> fs[] >>
  IF_CASES_TAC
  >- (simp[] >> disj2_tac >>
      simp[inc_pc_or_jump_def, LET_THM, bind_def,
           get_current_context_def, return_def,
           set_current_context_def, is_call_def] >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >>
      simp[asm_evm_rel_def, asm_next_def] >>
      once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
      simp[opcode_def, asm_inst_size_def] >> EVAL_TAC) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_word_bytes[local]:
  !bs:byte list. LENGTH bs = 32 ==>
    word_of_bytes T (0w:bytes32) bs =
    word_of_bytes F (0w:bytes32) (REVERSE bs)
Proof
  rpt strip_tac >>
  rewrite_tac[GSYM byteTheory.word_of_bytes_be_def,
              GSYM byteTheory.word_of_bytes_le_def] >>
  simp[cv_stdTheory.word_of_bytes_be_eq_num_of_bytes,
       cv_stdTheory.word_of_bytes_le_eq_num_of_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``, EVAL ``divides 8 256``] >>
  `TAKE 32 (bs ++ REPLICATE 32 0w) = bs` by
    (qpat_assum `LENGTH bs = 32` (fn th => once_rewrite_tac[GSYM th]) >>
     simp[TAKE_LENGTH_APPEND]) >>
  simp[byteTheory.be_bytes_thm]
QED

Theorem starve_mload_slice[local]:
  !off (mem:byte list).
    LENGTH (TAKE 32 (DROP off (asm_expand_memory (off + 32) mem))) = 32
Proof
  rpt gen_tac >> simp[listTheory.LENGTH_TAKE_EQ] >>
  `!n. n = n DIV 32 * 32 + n MOD 32 /\ n MOD 32 < 32` by
    (mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >> simp[]) >>
  first_x_assum (qspec_then `off + 63` strip_assume_tac) >>
  `off + 32 <= ((off + 32 + 31) DIV 32) * 32` by
    (`off + 32 + 31 = off + 63` by decide_tac >>
     pop_assum SUBST1_TAC >> decide_tac) >>
  Cases_on `32 * ((off + 63) DIV 32) <= LENGTH mem` >>
  simp[asm_expand_memory_def, LET_THM] >> decide_tac
QED

Theorem starve_mload_expand[local]:
  !off (mem:byte list).
    mem ++ REPLICATE (MAX (LENGTH mem) (32 * ((off + 63) DIV 32)) -
                     LENGTH mem) 0w = asm_expand_memory (off + 32) mem
Proof
  rpt gen_tac >> simp[asm_expand_memory_def, LET_THM, MAX_DEF] >>
  IF_CASES_TAC >> simp[]
QED

Theorem starve_mload:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "MLOAD" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_mload as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_mload_def, LET_THM] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = MLoad` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, step_mload_def, pop_stack_def, LET_THM] >>
  simp[consume_gas_def, push_stack_def,
       memory_expansion_info_def, expand_memory_def,
       read_memory_def, vfmConstantsTheory.word_size_def,
       assert_def, fail_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def, LET_THM] >>
  fs[] >> IF_CASES_TAC
  >- (simp[] >> Cases_on `LENGTH t < stack_limit`
      >- (fs[] >> simp[] >> disj2_tac >>
          simp[inc_pc_or_jump_def, LET_THM, opcode_def,
               bind_def, get_current_context_def, return_def,
               set_current_context_def, is_call_def] >>
          simp[vfmBufferTheory.buffer_take_to_list, vfmBufferTheory.buffer_to_list_extend,
               starve_mload_expand,
               starve_word_bytes, starve_mload_slice] >>
          qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
          simp[asm_evm_rel_def] >> strip_tac >>
          simp[asm_evm_rel_def, asm_next_def,
               vfmBufferTheory.buffer_to_list_extend,
               starve_mload_expand,
               starve_word_bytes, starve_mload_slice] >>
          once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
          simp[opcode_def, asm_inst_size_def] >> EVAL_TAC) >>
      fs[] >> disj1_tac >> irule starve_handle_resource >> simp[]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_word_to_bytes[local]:
  !v:bytes32. word_to_bytes v T = REVERSE (word_to_bytes v F)
Proof
  simp[GSYM byteTheory.word_to_bytes_be_def,
       GSYM byteTheory.word_to_bytes_le_def,
       cv_stdTheory.word_to_bytes_be_eq_bytes_of_num,
       cv_stdTheory.word_to_bytes_le_eq_bytes_of_num]
QED

Theorem starve_mstore_write[local]:
  !b off v.
    buffer_to_list (buffer_write off (REVERSE (word_to_bytes (v:bytes32) F))
      (buffer_extend
        (MAX (buffer_length b) (32 * ((off + 63) DIV 32)) - buffer_length b) b)) =
    TAKE off (asm_expand_memory (off + 32) (buffer_to_list b)) ++
    word_to_bytes v T ++
    DROP (off + 32) (asm_expand_memory (off + 32) (buffer_to_list b))
Proof
  rpt gen_tac >>
  `off <= buffer_length (buffer_extend
        (MAX (buffer_length b) (32 * ((off + 63) DIV 32)) - buffer_length b) b)` by
    (mp_tac (Q.SPECL [`off`, `buffer_to_list b`] starve_mload_slice) >>
     simp[GSYM starve_mload_expand, listTheory.LENGTH_TAKE_EQ, MAX_DEF] >>
     IF_CASES_TAC >> simp[] >> decide_tac) >>
  dep_rewrite.DEP_REWRITE_TAC[vfmBufferTheory.buffer_to_list_write_le] >> simp[] >>
  rewrite_tac[vfmBufferTheory.buffer_to_list_extend,
              GSYM vfmBufferTheory.LENGTH_buffer_to_list,
              starve_mload_expand] >>
  simp[starve_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem starve_mstore:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "MSTORE" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_mstore as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_mstore_def, LET_THM] >>
  Cases_on `t` >> simp[] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = MStore` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, step_mstore_def, pop_stack_def, LET_THM] >>
  simp[consume_gas_def, memory_expansion_info_def, expand_memory_def,
       write_memory_def, vfmConstantsTheory.word_size_def,
       assert_def, fail_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def, LET_THM] >>
  fs[] >> IF_CASES_TAC
  >- (simp[] >> disj2_tac >>
      simp[inc_pc_or_jump_def, LET_THM, opcode_def,
           bind_def, get_current_context_def, return_def,
           set_current_context_def, is_call_def] >>
      qspecl_then [`ctxt.memory`, `w2n h`, `h'`] mp_tac starve_mstore_write >>
      simp[] >> strip_tac >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >>
      simp[asm_evm_rel_def, asm_next_def] >>
      once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
      simp[opcode_def, asm_inst_size_def] >> EVAL_TAC) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_mstore8_expand[local]:
  !off (mem:byte list).
    mem ++ REPLICATE (MAX (LENGTH mem) (32 * ((off + 32) DIV 32)) -
                     LENGTH mem) 0w = asm_expand_memory (off + 1) mem
Proof
  rpt gen_tac >> simp[asm_expand_memory_def, LET_THM, MAX_DEF] >>
  IF_CASES_TAC >> simp[]
QED

Theorem starve_mstore8_write[local]:
  !b off (v:byte).
    buffer_to_list (buffer_write off [v]
      (buffer_extend
        (MAX (buffer_length b) (32 * ((off + 32) DIV 32)) - buffer_length b) b)) =
    TAKE off (asm_expand_memory (off + 1) (buffer_to_list b)) ++ [v] ++
    DROP (off + 1) (asm_expand_memory (off + 1) (buffer_to_list b))
Proof
  rpt gen_tac >>
  `!n. n = n DIV 32 * 32 + n MOD 32 /\ n MOD 32 < 32` by
    (mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >> simp[]) >>
  first_x_assum (qspec_then `off + 32` strip_assume_tac) >>
  `off <= buffer_length (buffer_extend
        (MAX (buffer_length b) (32 * ((off + 32) DIV 32)) - buffer_length b) b)` by
    (simp[MAX_DEF] >> IF_CASES_TAC >> simp[] >> decide_tac) >>
  dep_rewrite.DEP_REWRITE_TAC[vfmBufferTheory.buffer_to_list_write_le] >> simp[] >>
  rewrite_tac[vfmBufferTheory.buffer_to_list_extend,
              GSYM vfmBufferTheory.LENGTH_buffer_to_list,
              starve_mstore8_expand] >> simp[]
QED

Theorem starve_mstore8:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "MSTORE8" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_mstore8 as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_mstore8_def, LET_THM] >>
  Cases_on `t` >> simp[] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = MStore8` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, step_mstore_def, pop_stack_def, LET_THM] >>
  simp[consume_gas_def, memory_expansion_info_def, expand_memory_def,
       write_memory_def, vfmConstantsTheory.word_size_def,
       assert_def, fail_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def, LET_THM] >>
  fs[] >> IF_CASES_TAC
  >- (simp[] >> disj2_tac >>
      simp[inc_pc_or_jump_def, LET_THM, opcode_def,
           bind_def, get_current_context_def, return_def,
           set_current_context_def, is_call_def] >>
      qspecl_then [`ctxt.memory`, `w2n h`, `(w2w h'):byte`] mp_tac starve_mstore8_write >>
      simp[] >> strip_tac >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >>
      simp[asm_evm_rel_def, asm_next_def] >>
      once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
      simp[opcode_def, asm_inst_size_def] >> EVAL_TAC) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_sload:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ (?d. es.msdomain = Collect d) /\
    as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "SLOAD" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_sload as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_sload_def, LET_THM] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = SLoad` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, step_sload_def, pop_stack_def, consume_gas_def,
       push_stack_def, get_callee_def, get_accounts_def,
       access_slot_def, domain_check_def, set_domain_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.lookup_account_def,
       assert_def, fail_def, LET_THM] >>
  fs[] >> IF_CASES_TAC
  >- (simp[] >> Cases_on `LENGTH t < stack_limit`
      >- (fs[] >> simp[] >> disj2_tac >>
          simp[inc_pc_or_jump_def, LET_THM, opcode_def,
               bind_def, get_current_context_def, return_def,
               set_current_context_def, is_call_def] >>
          qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
          simp[asm_evm_rel_def] >> strip_tac >>
          simp[asm_evm_rel_def, asm_next_def] >>
          once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
          simp[opcode_def, asm_inst_size_def] >> EVAL_TAC) >>
      fs[] >> disj1_tac >> irule starve_handle_resource >> simp[]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_expand_memory_sum[local]:
  !off sz (mem:byte list).
    mem ++ REPLICATE (MAX (LENGTH mem) (32 * ((off + (sz + 31)) DIV 32)) -
                     LENGTH mem) 0w = asm_expand_memory (off + sz) mem
Proof
  rpt gen_tac >> simp[asm_expand_memory_def, LET_THM, MAX_DEF] >>
  IF_CASES_TAC >> simp[]
QED

Theorem starve_sha3:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "SHA3" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_sha3 as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_sha3_def, LET_THM] >>
  Cases_on `t` >> simp[] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = Keccak256` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  `h' = 0w \/ 0 < w2n h'` by
    (Cases_on `w2n h' = 0` >- gvs[wordsTheory.w2n_eq_0] >>
     disj2_tac >> decide_tac) >>
  Cases_on `h' = 0w` >> gvs[] >>
  simp[step_def, handle_def, step_inst_def, step_keccak256_def,
       bind_def, ignore_bind_def, get_current_context_def, return_def,
       set_current_context_def, pop_stack_def, consume_gas_def,
       push_stack_def, memory_expansion_info_def, expand_memory_def,
       read_memory_def, vfmConstantsTheory.word_size_def,
       vfmConstantsTheory.keccak256_per_word_cost_def,
       assert_def, fail_def, LET_THM] >> fs[] >>
  (IF_CASES_TAC
  >- (simp[] >> Cases_on `LENGTH t' < stack_limit`
      >- (fs[] >> simp[] >> disj2_tac >>
          simp[inc_pc_or_jump_def, LET_THM, opcode_def,
               bind_def, get_current_context_def, return_def,
               set_current_context_def, is_call_def] >>
          qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
          simp[asm_evm_rel_def] >> strip_tac >>
          simp[asm_evm_rel_def, asm_next_def,
               vfmBufferTheory.buffer_take_to_list,
               vfmBufferTheory.buffer_to_list_extend, starve_expand_memory_sum] >>
          once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
          simp[opcode_def, asm_inst_size_def] >> EVAL_TAC) >>
      fs[] >> disj1_tac >> irule starve_handle_resource >> simp[]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[])
QED

Theorem starve_log_opcode[local]:
  !name n labels.
    ALOOKUP log_table name = SOME n ==>
    encode_inst labels (AsmOp name) = opcode (Log n) /\
    wf_opname (Log n) /\ asm_inst_size (AsmOp name) = 1
Proof
  rpt gen_tac >> simp[log_table_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[] >>
  simp[encode_inst_def, opcode_def, wf_opname_def, asm_inst_size_def] >>
  EVAL_TAC >> simp[wordsTheory.WORD_ADD_0] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem starve_expand_memory_range[local]:
  !off (sz:bytes32) (mem:byte list).
    mem ++ REPLICATE
      (MAX (LENGTH mem)
        (if 0 < w2n sz then 32 * ((off + (w2n sz + 31)) DIV 32) else 0) -
       LENGTH mem) 0w =
    if sz = 0w then mem else asm_expand_memory (off + w2n sz) mem
Proof
  rpt gen_tac >> Cases_on `sz = 0w` >> simp[] >>
  `0 < w2n sz` by
    (Cases_on `w2n sz = 0` >- gvs[wordsTheory.w2n_eq_0] >> decide_tac) >>
  simp[starve_expand_memory_sum]
QED

Theorem starve_log:
  !prog as es name n.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    ~(FST (HD es.contexts)).msgParams.static /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp name /\ ALOOKUP log_table name = SOME n ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_log n as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> simp[asm_log_def, LET_THM] >>
  Cases_on `LENGTH as.as_stack < n + 2` >> simp[] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  drule starve_log_opcode >> disch_then (qspec_then `SND (compute_label_offsets prog)` strip_assume_tac) >>
  `op = Log n` by (irule opcode_wf_inj >> gvs[]) >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, step_log_def, pop_stack_def,
       consume_gas_def, memory_expansion_info_def, expand_memory_def,
       read_memory_def, push_logs_def, get_callee_def, get_static_def,
       assert_not_static_def, vfmConstantsTheory.word_size_def,
       assert_def, fail_def, LET_THM] >>
  fs[] >> IF_CASES_TAC
  >- (simp[] >> disj2_tac >>
      simp[inc_pc_or_jump_def, LET_THM, opcode_def,
           bind_def, get_current_context_def, return_def,
           set_current_context_def, is_call_def] >>
      simp[listTheory.EL_TAKE, listTheory.HD_TAKE, listTheory.DROP_TAKE] >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >>
      simp[asm_evm_rel_def, asm_next_def,
           vfmBufferTheory.buffer_take_to_list,
           vfmBufferTheory.buffer_to_list_extend, starve_expand_memory_range] >>
      once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_update_refund[local]:
  !refunds es.
    update_gas_refund refunds es =
      if es.contexts = [] then (INR (SOME Impossible), es)
      else (INL (), es with contexts :=
        (FST (HD es.contexts) with
          <|addRefund updated_by ($+ (FST refunds));
            subRefund updated_by ($+ (SND refunds))|>,
         SND (HD es.contexts)) :: TL es.contexts)
Proof
  rpt gen_tac >> PairCases_on `refunds` >>
  Cases_on `es.contexts` >>
  simp[update_gas_refund_def, bind_def, get_current_context_def,
       set_current_context_def, return_def, fail_def]
QED

Theorem starve_update_storage_eta[local]:
  update_storage k v = (k =+ v)
Proof
  simp[FUN_EQ_THM, vfmStateTheory.update_storage_def]
QED

Theorem starve_sstore:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ (?d. es.msdomain = Collect d) /\
    as.as_pc < LENGTH prog /\ ~(FST (HD es.contexts)).msgParams.static /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "SSTORE" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_sstore as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_sstore_def, LET_THM] >>
  Cases_on `t` >> simp[] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = SStore` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, step_sstore_def, pop_stack_def, LET_THM] >>
  simp[step_sstore_gas_consumption_def,
       get_gas_left_def, get_accounts_def, get_original_def,
       get_callee_def, get_static_def, access_slot_def, domain_check_def,
       set_domain_def, consume_gas_def, starve_update_refund,
       assert_not_static_def, assert_def, fail_def, LET_THM,
       bind_def, ignore_bind_def, get_current_context_def,
       return_def, set_current_context_def] >>
  fs[] >> IF_CASES_TAC
  >- (simp[] >> IF_CASES_TAC
      >- (simp[write_storage_def, get_callee_def, get_accounts_def,
               update_accounts_def, bind_def, ignore_bind_def,
               get_current_context_def, return_def, set_current_context_def] >>
          disj2_tac >>
          simp[inc_pc_or_jump_def, LET_THM, bind_def,
               get_current_context_def, return_def,
               set_current_context_def, is_call_def] >>
          qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
          simp[asm_evm_rel_def] >> strip_tac >>
          simp[asm_evm_rel_def, asm_next_def] >>
          once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
          simp[opcode_def, asm_inst_size_def, starve_update_storage_eta] >>
          Cases_on `lookup_account ctxt.msgParams.callee as.as_accounts` >>
          simp[vfmStateTheory.recordtype_account_state_seldef_storage_fupd_def]) >>
      simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_mcopy_write[local]:
  !b off src sz n.
    off + sz <= n /\ src + sz <= n ==>
    buffer_to_list (buffer_write off
      (buffer_take src sz (buffer_extend
        (MAX (buffer_length b) (32 * ((n + 31) DIV 32)) - buffer_length b) b))
      (buffer_extend
        (MAX (buffer_length b) (32 * ((n + 31) DIV 32)) - buffer_length b) b)) =
    TAKE off (asm_expand_memory n (buffer_to_list b)) ++
    TAKE sz (DROP src (asm_expand_memory n (buffer_to_list b))) ++
    DROP (off + sz) (asm_expand_memory n (buffer_to_list b))
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `buffer_write off bs expanded` >>
  `buffer_to_list expanded = asm_expand_memory n (buffer_to_list b)` by
    (simp[Abbr `expanded`, vfmBufferTheory.buffer_to_list_extend] >>
     pure_rewrite_tac[GSYM vfmBufferTheory.LENGTH_buffer_to_list] >>
     rewrite_tac[asm_expand_eq_evm_simp]) >>
  `n <= buffer_length expanded` by
    (mp_tac (Q.SPECL [`n`, `buffer_to_list b`]
      spillSimTheory.asm_expand_memory_length) >>
     metis_tac[vfmBufferTheory.LENGTH_buffer_to_list]) >>
  `src + sz <= LENGTH (asm_expand_memory n (buffer_to_list b)) /\
   off <= buffer_length expanded` by
    (mp_tac (Q.SPECL [`n`, `buffer_to_list b`]
      spillSimTheory.asm_expand_memory_length) >> decide_tac) >>
  `LENGTH bs = sz` by
    simp[Abbr `bs`, vfmBufferTheory.buffer_take_to_list, listTheory.LENGTH_TAKE_EQ] >>
  dep_rewrite.DEP_REWRITE_TAC[vfmBufferTheory.buffer_to_list_write_le] >>
  simp[Abbr `bs`, vfmBufferTheory.buffer_take_to_list]
QED

Theorem starve_mcopy:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "MCOPY" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_mcopy as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_mcopy_def, LET_THM] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = MCopy` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  Cases_on `h'' = 0w`
  >- suspend "zero" >>
  simp[step_def, handle_def, step_inst_def, step_copy_to_memory_def,
       copy_to_memory_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       pop_stack_def, max_expansion_range_def, LET_THM] >>
  Cases_on `w2n h + w2n h'' < w2n h' + w2n h''`
  >- suspend "src" >> suspend "dst"
QED

Resume starve_mcopy[zero]:
  gvs[] >>
  simp[step_def, handle_def, step_inst_def, step_copy_to_memory_def,
       copy_to_memory_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       pop_stack_def, max_expansion_range_def, memory_expansion_info_def,
       vfmConstantsTheory.word_size_def, consume_gas_def,
       expand_memory_def, read_memory_def, write_memory_def,
       assert_def, fail_def, LET_THM] >> fs[] >>
  IF_CASES_TAC
  >- (simp[] >> disj2_tac >>
      simp[inc_pc_or_jump_def, LET_THM, bind_def,
           get_current_context_def, return_def,
           set_current_context_def, is_call_def] >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >>
      simp[asm_evm_rel_def, asm_next_def] >>
      once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
      simp[opcode_def, asm_inst_size_def, vfmBufferTheory.buffer_take_def,
           Once vfmBufferTheory.read_bytes_def]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED
Resume starve_mcopy[src]:
  `w2n h < w2n h'` by decide_tac >>
  `w2n h'' <> 0` by metis_tac[wordsTheory.w2n_eq_0] >>
  simp[assert_def, fail_def, memory_expansion_info_def,
       vfmConstantsTheory.word_size_def, consume_gas_def,
       expand_memory_def, read_memory_def, write_memory_def,
       bind_def, ignore_bind_def, get_current_context_def, return_def,
       set_current_context_def, LET_THM] >> fs[] >>
  IF_CASES_TAC
  >- (simp[] >> disj2_tac >>
      simp[inc_pc_or_jump_def, LET_THM, bind_def,
           get_current_context_def, return_def,
           set_current_context_def, is_call_def] >>
      qspecl_then [`ctxt.memory`, `w2n h`, `w2n h'`, `w2n h''`,
                    `w2n h' + w2n h''`] mp_tac starve_mcopy_write >>
      (impl_tac >- decide_tac) >> strip_tac >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >>
      `MAX (w2n h' + w2n h'') (w2n h + w2n h'') = w2n h' + w2n h''`
        by simp[MAX_DEF] >>
      gvs[GSYM ADD_ASSOC] >>
      simp[asm_evm_rel_def, asm_next_def] >>
      once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
      simp[opcode_def, asm_inst_size_def]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED
Resume starve_mcopy[dst]:
  `~(w2n h < w2n h')` by decide_tac >>
  `w2n h'' <> 0` by metis_tac[wordsTheory.w2n_eq_0] >>
  simp[assert_def, fail_def, memory_expansion_info_def,
       vfmConstantsTheory.word_size_def, consume_gas_def,
       expand_memory_def, read_memory_def, write_memory_def,
       bind_def, ignore_bind_def, get_current_context_def, return_def,
       set_current_context_def, LET_THM] >> fs[] >>
  IF_CASES_TAC
  >- (simp[] >> disj2_tac >>
      simp[inc_pc_or_jump_def, LET_THM, bind_def,
           get_current_context_def, return_def,
           set_current_context_def, is_call_def] >>
      qspecl_then [`ctxt.memory`, `w2n h`, `w2n h'`, `w2n h''`,
                    `w2n h + w2n h''`] mp_tac starve_mcopy_write >>
      (impl_tac >- decide_tac) >> strip_tac >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >>
      `MAX (w2n h' + w2n h'') (w2n h + w2n h'') = w2n h + w2n h''`
        by simp[MAX_DEF] >>
      gvs[GSYM ADD_ASSOC] >>
      simp[asm_evm_rel_def, asm_next_def] >>
      once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
      simp[opcode_def, asm_inst_size_def]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED
Finalise starve_mcopy

Theorem starve_memory_dispatch:
  !prog as es name r.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ (?d. es.msdomain = Collect d) /\
    as.as_pc < LENGTH prog /\ ~(FST (HD es.contexts)).msgParams.static /\
    EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    asm_step_memory name as = SOME r ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case r of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `asm_step_memory _ _ = _` mp_tac >>
  simp[asm_step_memory_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[]
  >- (irule starve_pop >> simp[])
  >- (irule starve_mload >> simp[])
  >- (irule starve_mstore >> simp[])
  >- (irule starve_mstore8 >> simp[])
  >- (irule starve_mcopy >> simp[])
  >- (simp[asm_push_val_def] >> drule_all starve_msize >> simp[] >> metis_tac[])
  >- (irule starve_sload >> simp[] >> metis_tac[])
  >- (irule starve_sstore >> simp[] >> metis_tac[])
  >- (irule starve_tload >> simp[])
  >- (irule starve_tstore >> simp[])
  >> irule starve_sha3 >> simp[]
QED

Theorem starve_stop:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "STOP" ==>
    ?es1. step es = (INR NONE, es1) /\ LENGTH es1.contexts = 1 /\
          asm_evm_rel prog (as with as_returndata := []) es1
Proof
  rpt strip_tac >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = Stop` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, set_return_data_def, finish_def, LET_THM] >>
  simp[handle_step_none_single_context] >>
  qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
  simp[asm_evm_rel_def] >> strip_tac >> gvs[asm_evm_rel_def]
QED

Theorem starve_invalid:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "INVALID" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    ?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> Reverted /\
              ~vfm_abort (SOME exc) /\ LENGTH es1.contexts = 1 /\
              (FST (HD es1.contexts)).returnData = []
Proof
  rpt strip_tac >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = Invalid` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, fail_def, LET_THM] >>
  drule starve_handle_fault >>
  disch_then (qspec_then `InvalidOpcode` mp_tac) >>
  simp[vfm_abort_def] >> strip_tac
  >- (disj1_tac >> qexistsl [`es1`, `OutOfGas`] >> simp[]) >>
  disj2_tac >> qexistsl [`es1`, `InvalidOpcode`] >> simp[vfm_abort_def]
QED

Theorem starve_jumpdest:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmOp "JUMPDEST" /\
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
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
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

Theorem starve_jump:
  !prog data as es.
    asm_encoding_wf prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!i. i < LENGTH prog /\ ~is_data_inst (EL i prog) ==>
         !j. j <= i ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "JUMP" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_jump (build_offset_to_pc prog) as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\ LENGTH es1.contexts = 1 /\
                         asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_jump_def] >>
  rename1 `(dest:bytes32) :: stk` >>
  Cases_on `FLOOKUP (build_offset_to_pc prog) (w2n dest)` >> simp[] >>
  rename1 `FLOOKUP _ _ = SOME pc` >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  `!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)` by metis_tac[] >>
  drule_all starve_step_setup >> strip_tac >>
  `op = Jump` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  drule_all starve_jump_target >>
  disch_then (qspec_then `data` strip_assume_tac) >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, step_jump_def, pop_stack_def,
       consume_gas_def, assert_def, LET_THM, set_jump_dest_def] >> fs[] >>
  IF_CASES_TAC
  >- (simp[inc_pc_or_jump_def, LET_THM, bind_def, get_current_context_def,
           return_def, set_current_context_def, is_call_def, opcode_def,
           assert_def, ignore_bind_def] >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >> gvs[asm_evm_rel_def]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_jumpi:
  !prog data as es.
    asm_encoding_wf prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!i. i < LENGTH prog /\ ~is_data_inst (EL i prog) ==>
         !j. j <= i ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "JUMPI" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_jumpi (build_offset_to_pc prog) as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\ LENGTH es1.contexts = 1 /\
                         asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_jumpi_def] >>
  rename1 `(dest:bytes32) :: rest` >> Cases_on `rest` >> simp[] >>
  rename1 `dest :: (cond:bytes32) :: stk` >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  `!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)` by metis_tac[] >>
  drule_all starve_step_setup >> strip_tac >>
  `op = JumpI` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  Cases_on `cond = 0w`
  >- (simp[step_def, handle_def, bind_def, ignore_bind_def,
           get_current_context_def, return_def, set_current_context_def,
           step_inst_def, step_jumpi_def, pop_stack_def,
           consume_gas_def, assert_def, LET_THM, set_jump_dest_def] >> fs[] >>
      IF_CASES_TAC
      >- (simp[inc_pc_or_jump_def, LET_THM, bind_def, get_current_context_def,
               return_def, set_current_context_def, is_call_def, opcode_def] >>
          qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
          simp[asm_evm_rel_def] >> strip_tac >>
          simp[asm_evm_rel_def, asm_next_def] >>
          once_rewrite_tac[GSYM ADD1] >>
          qpat_x_assum `asm_pc_to_offset prog _ = _` kall_tac >>
          simp[asm_pc_to_offset_suc, EL_APPEND1, asm_inst_size_def]) >>
      simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]) >>
  simp[] >> Cases_on `FLOOKUP (build_offset_to_pc prog) (w2n dest)` >> simp[] >>
  drule_all starve_jump_target >>
  disch_then (qspec_then `data` strip_assume_tac) >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, step_jumpi_def, pop_stack_def,
       consume_gas_def, assert_def, LET_THM, set_jump_dest_def] >> fs[] >>
  IF_CASES_TAC
  >- (simp[inc_pc_or_jump_def, LET_THM, bind_def, get_current_context_def,
           return_def, set_current_context_def, is_call_def, opcode_def,
           assert_def, ignore_bind_def] >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >> gvs[asm_evm_rel_def]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_return:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "RETURN" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_return_op as of
      AsmHalt as1 => ?es1. step es = (INR NONE, es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_return_op_def, LET_THM] >>
  Cases_on `t` >> simp[] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = Return` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  `h' = 0w \/ 0 < w2n h'` by
    (Cases_on `w2n h' = 0` >- gvs[wordsTheory.w2n_eq_0] >>
     disj2_tac >> decide_tac) >>
  Cases_on `h' = 0w` >> gvs[] >>
  simp[step_def, handle_def, step_inst_def, step_return_def,
       bind_def, ignore_bind_def, get_current_context_def, return_def,
       set_current_context_def, pop_stack_def, consume_gas_def,
       memory_expansion_info_def, expand_memory_def,
       read_memory_def, set_return_data_def, finish_def,
       vfmConstantsTheory.word_size_def, assert_def, fail_def, LET_THM] >> fs[] >>
  (IF_CASES_TAC
   >- (simp[handle_step_none_single_context] >>
       qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
       simp[asm_evm_rel_def] >> strip_tac >>
       simp[asm_evm_rel_def, vfmBufferTheory.buffer_take_to_list,
            vfmBufferTheory.buffer_to_list_extend, starve_expand_memory_sum]) >>
   simp[] >> disj1_tac >> irule starve_handle_resource >> simp[])
QED

Theorem starve_revert:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "REVERT" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_revert_op as of
      AsmRevert as1 => ?es1. step es = (INR (SOME Reverted), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_revert_op_def, LET_THM] >>
  Cases_on `t` >> simp[] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = Revert` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  `h' = 0w \/ 0 < w2n h'` by
    (Cases_on `w2n h' = 0` >- gvs[wordsTheory.w2n_eq_0] >>
     disj2_tac >> decide_tac) >>
  Cases_on `h' = 0w` >> gvs[] >>
  simp[step_def, handle_def, step_inst_def, step_return_def,
       bind_def, ignore_bind_def, get_current_context_def, return_def,
       set_current_context_def, pop_stack_def, consume_gas_def,
       memory_expansion_info_def, expand_memory_def,
       read_memory_def, set_return_data_def, revert_def,
       vfmConstantsTheory.word_size_def, assert_def, fail_def, LET_THM] >> fs[] >>
  (IF_CASES_TAC
   >- (simp[handle_step_reverted_single_context] >>
       qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
       simp[asm_evm_rel_def] >> strip_tac >>
       simp[asm_evm_rel_def, vfmBufferTheory.buffer_take_to_list,
            vfmBufferTheory.buffer_to_list_extend, starve_expand_memory_sum]) >>
   simp[] >> disj1_tac >> irule starve_handle_resource >> simp[])
QED

Theorem starve_control_dispatch:
  !prog data as es name ar.
    asm_encoding_wf prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!i. i < LENGTH prog /\ ~is_data_inst (EL i prog) ==>
         !j. j <= i ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp name /\
    asm_step_control (build_offset_to_pc prog) name as = SOME ar ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case ar of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\ LENGTH es1.contexts = 1 /\
                         asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmHalt as1 => ?es1. step es = (INR NONE, es1) /\ LENGTH es1.contexts = 1 /\
                         asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmRevert as1 => ?es1. step es = (INR (SOME Reverted), es1) /\
                         LENGTH es1.contexts = 1 /\
                         asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\
                         exc <> Reverted /\ ~vfm_abort (SOME exc) /\
                         LENGTH es1.contexts = 1 /\
                         (FST (HD es1.contexts)).returnData = []
    | AsmError _ => T
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `name = "JUMP"`
  >- (gvs[asm_step_control_def] >> drule_all starve_jump >>
      Cases_on `asm_jump (build_offset_to_pc prog) as` >> gvs[]) >>
  Cases_on `name = "JUMPI"`
  >- (gvs[asm_step_control_def] >> drule_all starve_jumpi >>
      Cases_on `asm_jumpi (build_offset_to_pc prog) as` >> gvs[]) >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  `!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)` by metis_tac[] >>
  `asm_encoding_wf (prog ++ [AsmDataItem data])` by
    simp[data_suffix_encoding_wf] >>
  `as.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
  `EL as.as_pc (prog ++ [AsmDataItem data]) = AsmOp name` by
    simp[EL_APPEND1] >>
  `!j. j <= as.as_pc ==>
       ~is_data_inst (EL j (prog ++ [AsmDataItem data]))` by
    (rpt strip_tac >> `j < LENGTH prog` by decide_tac >> gvs[EL_APPEND1]) >>
  qpat_x_assum `asm_step_control _ _ _ = _` mp_tac >>
  simp[asm_step_control_def] >> rpt (IF_CASES_TAC >> simp[]) >>
  strip_tac >> gvs[]
  >- (drule_at (Pos (el 2)) starve_jumpdest >> simp[] >> metis_tac[])
  >- (drule_at (Pos (el 2)) starve_stop >> simp[] >> metis_tac[])
  >- (drule_at (Pos (el 2)) starve_return >>
      Cases_on `asm_return_op as` >> gvs[] >> metis_tac[])
  >- (drule_at (Pos (el 2)) starve_revert >>
      Cases_on `asm_revert_op as` >> gvs[] >> metis_tac[]) >>
  drule_at (Pos (el 2)) starve_invalid >> simp[]
QED

Theorem starve_copy_write[local]:
  !b off bs sz.
    LENGTH bs = sz ==>
    buffer_to_list (buffer_write off bs
      (buffer_extend (MAX (buffer_length b) (32 * ((off + sz + 31) DIV 32)) -
                      buffer_length b) b)) =
    TAKE off (asm_expand_memory (off + sz) (buffer_to_list b)) ++ bs ++
    DROP (off + sz) (asm_expand_memory (off + sz) (buffer_to_list b))
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `buffer_write off bs expanded` >>
  `buffer_to_list expanded = asm_expand_memory (off + sz) (buffer_to_list b)` by
    (simp[Abbr `expanded`, vfmBufferTheory.buffer_to_list_extend] >>
     pure_rewrite_tac[GSYM vfmBufferTheory.LENGTH_buffer_to_list] >>
     once_rewrite_tac[GSYM asm_expand_eq_evm_simp] >> simp[GSYM ADD_ASSOC]) >>
  `off + sz <= buffer_length expanded` by
    (mp_tac (Q.SPECL [`off + sz`, `buffer_to_list b`]
       spillSimTheory.asm_expand_memory_length) >>
     metis_tac[vfmBufferTheory.LENGTH_buffer_to_list]) >>
  dep_rewrite.DEP_REWRITE_TAC[vfmBufferTheory.buffer_to_list_write_le] >> simp[]
QED

Theorem starve_calldatacopy:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "CALLDATACOPY" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_copy_to_mem as.as_call_ctx.cc_calldata as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_copy_to_mem_def, LET_THM] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = CallDataCopy` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  `h'' = 0w \/ 0 < w2n h''` by
    (Cases_on `w2n h'' = 0` >- gvs[wordsTheory.w2n_eq_0] >>
     disj2_tac >> decide_tac) >>
  Cases_on `h'' = 0w` >> gvs[] >>
  simp[step_def, handle_def, step_inst_def, step_copy_to_memory_def,
       copy_to_memory_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       pop_stack_def, consume_gas_def, memory_expansion_info_def,
       expand_memory_def, write_memory_def, get_call_data_def,
       vfmConstantsTheory.word_size_def, vfmConstantsTheory.memory_copy_cost_def,
       assert_def, fail_def, LET_THM] >> fs[] >>
  (IF_CASES_TAC
   >- (simp[] >> disj2_tac >>
       simp[inc_pc_or_jump_def, LET_THM, opcode_def, bind_def,
            get_current_context_def, return_def, set_current_context_def, is_call_def] >>
       qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
       simp[asm_evm_rel_def] >> strip_tac >>
       gvs[asm_evm_rel_def, asm_next_def, take_drop_expand_eq_pad,
           starve_copy_write, vfmTypesTheory.LENGTH_take_pad_0,
           vfmTypesTheory.take_pad_0_0] >>
       once_rewrite_tac[GSYM ADD1] >>
       simp[asm_pc_to_offset_suc, asm_inst_size_def] >>
       qspec_then `ctxt.memory` mp_tac starve_copy_write >>
       simp[GSYM ADD_ASSOC] >>
       disch_then (qspecl_then [`w2n h`,
         `take_pad_0 (w2n h'') (DROP (w2n h') (buffer_to_list ctxt.msgParams.data))`]
         mp_tac) >> simp[vfmTypesTheory.LENGTH_take_pad_0]) >>
   simp[] >> disj1_tac >> irule starve_handle_resource >> simp[])
QED

Theorem starve_codecopy:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "CODECOPY" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_copy_to_mem as.as_code as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_copy_to_mem_def, LET_THM] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = CodeCopy` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  `h'' = 0w \/ 0 < w2n h''` by
    (Cases_on `w2n h'' = 0` >- gvs[wordsTheory.w2n_eq_0] >>
     disj2_tac >> decide_tac) >>
  Cases_on `h'' = 0w` >> gvs[] >>
  simp[step_def, handle_def, step_inst_def, step_copy_to_memory_def,
       copy_to_memory_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       pop_stack_def, consume_gas_def, memory_expansion_info_def,
       expand_memory_def, write_memory_def, get_current_code_def,
       vfmConstantsTheory.word_size_def, vfmConstantsTheory.memory_copy_cost_def,
       assert_def, fail_def, LET_THM] >> fs[] >>
  (IF_CASES_TAC
   >- (simp[] >> disj2_tac >>
       simp[inc_pc_or_jump_def, LET_THM, opcode_def, bind_def,
            get_current_context_def, return_def, set_current_context_def, is_call_def] >>
       qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
       simp[asm_evm_rel_def] >> strip_tac >>
       gvs[asm_evm_rel_def, asm_next_def, take_drop_expand_eq_pad,
           starve_copy_write, vfmTypesTheory.LENGTH_take_pad_0,
           vfmTypesTheory.take_pad_0_0] >>
       once_rewrite_tac[GSYM ADD1] >>
       simp[asm_pc_to_offset_suc, asm_inst_size_def] >>
       qspec_then `ctxt.memory` mp_tac starve_copy_write >>
       simp[GSYM ADD_ASSOC] >>
       disch_then (qspecl_then [`w2n h`,
         `take_pad_0 (w2n h'') (DROP (w2n h') (assemble prog))`]
         mp_tac) >> simp[vfmTypesTheory.LENGTH_take_pad_0]) >>
   simp[] >> disj1_tac >> irule starve_handle_resource >> simp[])
QED

Theorem starve_returndatacopy:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "RETURNDATACOPY" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_returndatacopy as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\
                         exc <> Reverted /\ ~vfm_abort (SOME exc) /\
                         LENGTH es1.contexts = 1 /\
                         (FST (HD es1.contexts)).returnData = []
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_returndatacopy_def, LET_THM] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = ReturnDataCopy` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  `h'' = 0w \/ 0 < w2n h''` by
    (Cases_on `w2n h'' = 0` >- gvs[wordsTheory.w2n_eq_0] >>
     disj2_tac >> decide_tac) >>
  Cases_on `h'' = 0w` >> gvs[] >>
  simp[step_def, handle_def, step_inst_def, step_return_data_copy_def,
       step_copy_to_memory_def, copy_to_memory_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       pop_stack_def, consume_gas_def, memory_expansion_info_def,
       expand_memory_def, write_memory_def, get_return_data_check_def,
       get_return_data_def, vfmConstantsTheory.word_size_def,
       vfmConstantsTheory.memory_copy_cost_def,
       assert_def, fail_def, LET_THM] >> fs[] >>
  (IF_CASES_TAC
   >- (simp[] >> IF_CASES_TAC >> gvs[]
       >- suspend "in_bounds" >> suspend "out_of_bounds") >>
   simp[] >> disj1_tac >> irule starve_handle_resource >> simp[])
QED

Resume starve_returndatacopy[out_of_bounds]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `handle_step (SOME OutOfBoundsRead) s` >>
  qspec_then `s` mp_tac starve_handle_fault >>
  simp[Abbr `s`] >>
  disch_then (qspec_then `OutOfBoundsRead` mp_tac) >>
  simp[vfm_abort_def] >>
  (strip_tac
   >- (disj1_tac >> qexistsl [`es1`, `OutOfGas`] >> simp[]) >>
   disj2_tac >> qexistsl [`es1`, `OutOfBoundsRead`] >> simp[vfm_abort_def])
QED

Resume starve_returndatacopy[in_bounds]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  disj2_tac >>
  simp[inc_pc_or_jump_def, LET_THM, opcode_def, bind_def,
       get_current_context_def, return_def, set_current_context_def, is_call_def] >>
  qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
  simp[asm_evm_rel_def] >> strip_tac >>
  gvs[asm_evm_rel_def, asm_next_def, vfmTypesTheory.take_pad_0_0] >>
  once_rewrite_tac[GSYM ADD1] >>
  simp[asm_pc_to_offset_suc, asm_inst_size_def] >>
  qspec_then `ctxt.memory` mp_tac starve_copy_write >>
  simp[GSYM ADD_ASSOC] >>
  disch_then (qspecl_then [`w2n h`,
    `TAKE (w2n h'') (DROP (w2n h') as.as_returndata)`] mp_tac) >>
  simp[vfmTypesTheory.take_pad_0_def, listTheory.PAD_RIGHT,
       GSYM rich_listTheory.REPLICATE_GENLIST, LENGTH_TAKE_EQ, LENGTH_DROP]
QED

Finalise starve_returndatacopy

Theorem starve_extcodecopy:
  !prog as es.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ (?d. es.msdomain = Collect d) /\
    as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "EXTCODECOPY" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_extcodecopy as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> Cases_on `as.as_stack` >> simp[asm_extcodecopy_def, LET_THM] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  rename1 `as.as_stack = addr :: dest :: src :: rest` >>
  Cases_on `rest` >> simp[] >>
  rename1 `as.as_stack = addr :: dest :: src :: sz :: stk` >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = ExtCodeCopy` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def] >>
     gvs[encode_inst_def] >> EVAL_TAC) >> gvs[] >>
  `sz = 0w \/ 0 < w2n sz` by
    (Cases_on `w2n sz = 0` >- gvs[wordsTheory.w2n_eq_0] >>
     disj2_tac >> decide_tac) >>
  Cases_on `sz = 0w` >> gvs[] >>
  simp[step_def, handle_def, step_inst_def, step_ext_code_copy_def,
       step_copy_to_memory_def, copy_to_memory_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       pop_stack_def, consume_gas_def, memory_expansion_info_def,
       expand_memory_def, write_memory_def, get_code_def, get_accounts_def,
       access_address_def, domain_check_def, set_domain_def,
       vfmConstantsTheory.word_size_def, vfmConstantsTheory.memory_copy_cost_def,
       assert_def, fail_def, LET_THM] >> fs[] >>
  (IF_CASES_TAC
   >- (simp[] >> suspend "copy_ok") >>
   simp[] >> disj1_tac >> irule starve_handle_resource >> simp[])
QED

Resume starve_extcodecopy[copy_ok]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  disj2_tac >>
  simp[inc_pc_or_jump_def, LET_THM, opcode_def, bind_def,
       get_current_context_def, return_def, set_current_context_def, is_call_def] >>
  qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
  simp[asm_evm_rel_def] >> strip_tac >>
  gvs[asm_evm_rel_def, asm_next_def, take_drop_expand_eq_pad,
      vfmTypesTheory.LENGTH_take_pad_0, vfmTypesTheory.take_pad_0_0] >>
  once_rewrite_tac[GSYM ADD1] >>
  simp[asm_pc_to_offset_suc, asm_inst_size_def] >>
  qspec_then `ctxt.memory` mp_tac starve_copy_write >>
  simp[GSYM ADD_ASSOC] >>
  disch_then (qspecl_then [`w2n dest`,
    `take_pad_0 (w2n sz) (DROP (w2n src)
      (lookup_account (w2w addr) as.as_accounts).code)`] mp_tac) >>
  simp[vfmTypesTheory.LENGTH_take_pad_0]
QED

Finalise starve_extcodecopy

Theorem starve_copy_dispatch:
  !prog as es name ar.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ (?d. es.msdomain = Collect d) /\
    as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp name /\ asm_step_copy name as = SOME ar ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case ar of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\ LENGTH es1.contexts = 1 /\
                         asm_evm_rel prog as1 es1
    | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\
                         exc <> Reverted /\ ~vfm_abort (SOME exc) /\
                         LENGTH es1.contexts = 1 /\
                         (FST (HD es1.contexts)).returnData = []
    | AsmError _ => T
    | _ => F
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `asm_step_copy _ _ = _` mp_tac >>
  simp[asm_step_copy_def] >> rpt (IF_CASES_TAC >> simp[]) >>
  strip_tac >> gvs[]
  >- (drule_all starve_calldatacopy >>
      Cases_on `asm_copy_to_mem as.as_call_ctx.cc_calldata as` >> gvs[] >> metis_tac[])
  >- (drule_all starve_returndatacopy >>
      Cases_on `asm_returndatacopy as` >> gvs[] >> metis_tac[])
  >- (drule_all starve_codecopy >>
      Cases_on `asm_copy_to_mem as.as_code as` >> gvs[] >> metis_tac[]) >>
  drule_at (Pos (el 2)) starve_extcodecopy >>
  simp[] >> Cases_on `asm_extcodecopy as` >> gvs[] >> metis_tac[]
QED

Theorem starve_dup:
  !prog as es n.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    opcode (Dup n) = encode_inst (SND (compute_label_offsets prog))
                                (EL as.as_pc prog) /\ n < 16 ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_dup n as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> simp[asm_dup_def] >>
  Cases_on `n < LENGTH as.as_stack` >> simp[] >>
  `~is_data_inst (EL as.as_pc prog)` by metis_tac[LESS_EQ_REFL] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = Dup n` by
    (irule opcode_wf_inj >> simp[wf_opname_def] >> metis_tac[]) >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def] >>
  simp[step_inst_def, step_dup_def, consume_gas_def, push_stack_def,
       bind_def, ignore_bind_def, get_current_context_def, return_def,
       set_current_context_def, assert_def, LET_THM] >> fs[] >>
  IF_CASES_TAC
  >- (simp[] >> Cases_on `LENGTH as.as_stack < stack_limit`
      >- (fs[] >> simp[] >> disj2_tac >>
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
      fs[] >> disj1_tac >> irule starve_handle_resource >> simp[]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_swap_stack[local]:
  !n stk. SUC n < LENGTH stk ==>
    LUPDATE (HD stk) (SUC n) (LUPDATE (EL (SUC n) stk) 0 stk) =
      EL n (TL stk) :: TAKE n (TL stk) ++ [HD stk] ++ DROP (SUC n) (TL stk)
Proof
  Cases_on `stk` >> simp[LUPDATE_def, lupdate_take_drop]
QED

Theorem starve_swap:
  !prog as es n.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    opcode (Swap n) = encode_inst (SND (compute_label_offsets prog))
                                 (EL as.as_pc prog) /\ n < 16 ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_swap (SUC n) as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt strip_tac >> simp[asm_swap_def] >>
  Cases_on `SUC n < LENGTH as.as_stack` >> simp[LET_THM] >>
  `~is_data_inst (EL as.as_pc prog)` by metis_tac[LESS_EQ_REFL] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op = Swap n` by
    (irule opcode_wf_inj >> simp[wf_opname_def] >> metis_tac[]) >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def] >>
  simp[step_inst_def, step_swap_def, consume_gas_def,
       bind_def, ignore_bind_def, get_current_context_def, return_def,
       set_current_context_def, assert_def, LET_THM] >> fs[] >>
  IF_CASES_TAC
  >- (simp[] >> disj2_tac >>
      simp[inc_pc_or_jump_def, LET_THM, bind_def,
           get_current_context_def, return_def,
           set_current_context_def, is_call_def] >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >>
      simp[asm_evm_rel_def, asm_next_def, starve_swap_stack] >>
      once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
      irule ewi_length >>
      fs[asm_encoding_wf_def, LET_THM, encoding_wf_inst_def, UNCURRY] >>
      metis_tac[]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Theorem starve_dup_dispatch:
  !prog as es name n.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    ALOOKUP dup_table name = SOME n ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_dup n as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ALOOKUP dup_table _ = _` mp_tac >>
  simp[dup_table_def] >> rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[] >>
  irule starve_dup >> simp[opcode_def, encode_inst_def] >> EVAL_TAC
QED

Theorem starve_swap_dispatch:
  !prog as es name n.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    ALOOKUP swap_table name = SOME n ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_swap n as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ALOOKUP swap_table _ = _` mp_tac >>
  simp[swap_table_def] >> rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `asm_swap k as` >>
  drule_at (Pos (el 2)) starve_swap >> simp[] >>
  disch_then (qspec_then `k - 1` mp_tac) >>
  (impl_tac >- (simp[Abbr `k`, opcode_def, encode_inst_def] >> EVAL_TAC)) >>
  simp[Abbr `k`]
QED

fun starve_identify_tac opq =
  drule opcode_wf_inj >> disch_then (qspec_then opq mp_tac) >>
  (impl_tac >- (simp[wf_opname_def, opcode_def] >>
    qpat_x_assum `opcode _ = _` mp_tac >>
    simp[encode_inst_def] >> EVAL_TAC)) >>
  strip_tac >> gvs[];

val starve_context_push_tac =
  simp[asm_push_val_def] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, step_inst_def,
       step_msgParams_def, step_context_def, step_txParams_def,
       get_tx_params_def, step_self_balance_def, get_accounts_def,
       get_callee_def, consume_gas_def, push_stack_def,
       set_current_context_def, assert_def, LET_THM] >> fs[] >>
  IF_CASES_TAC
  >- (simp[] >> Cases_on `LENGTH as.as_stack < stack_limit`
      >- (fs[] >> simp[] >> disj2_tac >>
          simp[inc_pc_or_jump_def, LET_THM, bind_def,
               get_current_context_def, return_def,
               set_current_context_def, is_call_def] >>
          qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
          simp[asm_evm_rel_def] >> strip_tac >>
          simp[asm_evm_rel_def, asm_next_def] >>
          once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
          simp[asm_inst_size_def, encode_inst_def] >> EVAL_TAC) >>
      fs[] >> disj1_tac >> irule starve_handle_resource >> simp[]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[];

val starve_context_unop_tac =
  Cases_on `as.as_stack` >> simp[asm_state_unop_def] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, step_inst_def,
       step_call_data_load_def, step_block_hash_def, step_blob_hash_def,
       step_balance_def, step_ext_code_size_def, step_ext_code_hash_def,
       pop_stack_def, push_stack_def, consume_gas_def,
       get_accounts_def, get_call_data_def, get_tx_params_def,
       access_address_def, domain_check_def, set_domain_def,
       get_callee_def, fail_def, set_current_context_def,
       assert_def, LET_THM] >> fs[] >>
  IF_CASES_TAC
  >- (simp[] >> IF_CASES_TAC
      >- (simp[] >> disj2_tac >>
          simp[inc_pc_or_jump_def, LET_THM, bind_def,
               get_current_context_def, return_def,
               set_current_context_def, is_call_def] >>
          qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
          simp[asm_evm_rel_def] >> strip_tac >>
          simp[asm_evm_rel_def, asm_next_def] >>
          once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
          simp[asm_inst_size_def, encode_inst_def] >> EVAL_TAC) >>
      simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[];

Theorem starve_context_dispatch:
  !prog as es name r.
    asm_encoding_wf prog /\ asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\ as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    (?d. es.msdomain = Collect d) /\ name <> "GAS" /\
    asm_step_context name as = SOME r ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case r of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\
                         asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
    | AsmError _ => T
    | _ => F
Proof
  rpt gen_tac >> strip_tac >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac >>
  qpat_x_assum `asm_step_context _ _ = _` mp_tac >>
  simp[asm_step_context_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[]
  >- (starve_identify_tac `Caller` >> starve_context_push_tac)
  >- (starve_identify_tac `Address` >> starve_context_push_tac)
  >- (starve_identify_tac `CallValue` >> starve_context_push_tac)
  >- (starve_identify_tac `CallDataSize` >> starve_context_push_tac)
  >- (starve_identify_tac `CallDataLoad` >> starve_context_unop_tac)
  >- (starve_identify_tac `Origin` >> starve_context_push_tac)
  >- (starve_identify_tac `GasPrice` >> starve_context_push_tac)
  >- (starve_identify_tac `ChainId` >> starve_context_push_tac)
  >- (starve_identify_tac `CoinBase` >> starve_context_push_tac)
  >- (starve_identify_tac `TimeStamp` >> starve_context_push_tac)
  >- (starve_identify_tac `Number` >> starve_context_push_tac)
  >- (starve_identify_tac `PrevRandao` >> starve_context_push_tac)
  >- (starve_identify_tac `GasLimit` >> starve_context_push_tac)
  >- (starve_identify_tac `BaseFee` >> starve_context_push_tac)
  >- (starve_identify_tac `BlobBaseFee` >> starve_context_push_tac)
  >- (starve_identify_tac `BlockHash` >> suspend "blockhash")
  >- (starve_identify_tac `BlobHash` >> starve_context_unop_tac)
  >- (starve_identify_tac `Balance` >> starve_context_unop_tac)
  >- (starve_identify_tac `SelfBalance` >> starve_context_push_tac)
  >- (starve_identify_tac `CodeSize` >> starve_context_push_tac)
  >- (starve_identify_tac `ExtCodeSize` >> starve_context_unop_tac)
  >- (starve_identify_tac `ExtCodeHash` >> starve_context_unop_tac) >>
  starve_identify_tac `ReturnDataSize` >> (starve_context_push_tac)
QED


Resume starve_context_dispatch[blockhash]:
  Cases_on `as.as_stack` >> simp[asm_state_unop_def] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, step_inst_def,
       step_block_hash_def, pop_stack_def, push_stack_def, consume_gas_def,
       get_tx_params_def, set_current_context_def, assert_def, LET_THM] >> fs[] >>
  IF_CASES_TAC
  >- (simp[] >> IF_CASES_TAC
      >- (simp[] >> disj2_tac >>
          simp[inc_pc_or_jump_def, LET_THM, bind_def,
               get_current_context_def, return_def,
               set_current_context_def, is_call_def] >>
          qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
          simp[asm_evm_rel_def] >> strip_tac >>
          simp[asm_evm_rel_def, asm_next_def] >>
          once_rewrite_tac[GSYM ADD1] >> simp[asm_pc_to_offset_suc] >>
          simp[opcode_def, asm_inst_size_def] >> EVAL_TAC) >>
      simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]) >>
  simp[] >> disj1_tac >> irule starve_handle_resource >> simp[]
QED

Finalise starve_context_dispatch

Theorem starve_extcall_excluded:
  !name as. ~is_evm_call_name name ==> asm_step_extcall name as = NONE
Proof
  simp[is_evm_call_name_def, asm_step_extcall_def]
QED

Theorem starve_op_dispatch:
  !prog data as es name.
    asm_encoding_wf prog /\
    asm_evm_rel (prog ++ [AsmDataItem data]) as es /\
    LENGTH es.contexts = 1 /\ (?d. es.msdomain = Collect d) /\
    ~(FST (HD es.contexts)).msgParams.static /\
    (!i. i < LENGTH prog /\ ~is_data_inst (EL i prog) ==>
         !j. j <= i ==> ~is_data_inst (EL j prog)) /\
    as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp name /\
    ~is_evm_call_name name /\ name <> "GAS" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_step_op (build_offset_to_pc prog) name as of
      AsmOK as1 => ?es1. step es = (INL (), es1) /\ LENGTH es1.contexts = 1 /\
                    asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmHalt as1 => ?es1. step es = (INR NONE, es1) /\ LENGTH es1.contexts = 1 /\
                    asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmRevert as1 => ?es1. step es = (INR (SOME Reverted), es1) /\
                    LENGTH es1.contexts = 1 /\
                    asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> Reverted /\
                    ~vfm_abort (SOME exc) /\ LENGTH es1.contexts = 1 /\
                    (FST (HD es1.contexts)).returnData = []
    | AsmError _ => T
Proof
  rpt gen_tac >> strip_tac >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  `!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)` by metis_tac[] >>
  `asm_encoding_wf (prog ++ [AsmDataItem data])` by simp[data_suffix_encoding_wf] >>
  `as.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
  `EL as.as_pc (prog ++ [AsmDataItem data]) = AsmOp name` by simp[EL_APPEND1] >>
  `!j. j <= as.as_pc ==> ~is_data_inst (EL j (prog ++ [AsmDataItem data]))` by
    (rpt strip_tac >> `j < LENGTH prog` by decide_tac >> gvs[EL_APPEND1]) >>
  rewrite_tac[asm_step_op_def] >>
  reverse (Cases_on `asm_step_arith name as`) >> simp[]
  >- (drule_at (Pos (el 2)) starve_arith_dispatch >> simp[] >>
      Cases_on `x` >> gvs[] >> metis_tac[]) >>
  reverse (Cases_on `asm_step_compare name as`) >> simp[]
  >- (drule_at (Pos (el 2)) starve_compare_dispatch >> simp[] >>
      Cases_on `x` >> gvs[] >> metis_tac[]) >>
  reverse (Cases_on `asm_step_bitwise name as`) >> simp[]
  >- (drule_at (Pos (el 2)) starve_bitwise_dispatch >> simp[] >>
      Cases_on `x` >> gvs[] >> metis_tac[]) >>
  reverse (Cases_on `asm_step_memory name as`) >> simp[]
  >- (drule_at (Pos (el 2)) starve_memory_dispatch >> simp[] >>
      Cases_on `x` >> gvs[] >> metis_tac[]) >>
  reverse (Cases_on `asm_step_control (build_offset_to_pc prog) name as`) >> simp[]
  >- (drule_all starve_control_dispatch >> simp[]) >>
  simp[starve_extcall_excluded] >>
  reverse (Cases_on `asm_step_copy name as`) >> simp[]
  >- (drule_at (Pos (el 2)) starve_copy_dispatch >> simp[] >>
      Cases_on `x` >> gvs[] >> metis_tac[]) >>
  reverse (Cases_on `asm_step_context name as`) >> simp[]
  >- (drule_at (Pos (el 2)) starve_context_dispatch >> simp[] >>
      Cases_on `x` >> gvs[] >> metis_tac[]) >>
  reverse (Cases_on `ALOOKUP dup_table name`) >> simp[]
  >- (drule_at (Pos (el 2)) starve_dup_dispatch >> simp[] >>
      Cases_on `asm_dup x as` >> gvs[] >> metis_tac[]) >>
  reverse (Cases_on `ALOOKUP swap_table name`) >> simp[]
  >- (drule_at (Pos (el 2)) starve_swap_dispatch >> simp[] >>
      Cases_on `asm_swap x as` >> gvs[] >> metis_tac[]) >>
  reverse (Cases_on `ALOOKUP log_table name`) >> simp[] >>
  drule_at (Pos (el 2)) starve_log >> simp[] >>
  Cases_on `asm_log x as` >> gvs[] >> metis_tac[]
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
  rpt gen_tac >> strip_tac >>
  `!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)` by metis_tac[] >>
  Cases_on `EL as.as_pc prog` >> gvs[is_data_inst_def]
  >- (drule_at (Pos (el 2)) starve_op_dispatch >> simp[asm_step_def] >>
      metis_tac[]) >>
  drule_at (Pos (el 2)) starve_push_family >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  Cases_on `asm_step (SND (compute_label_offsets prog))
                    (build_offset_to_pc prog) (EL as.as_pc prog) as` >>
  gvs[] >> metis_tac[]
QED

(* Audit the final theorem's dependency tags; the frozen label-map oracle
   is deliberately retained above, as required by this task. *)
val _ = let
  val (oracles, _) = Tag.dest_tag (Thm.tag asm_evm_step_starve)
in
  print ("asm_evm_step_starve dependency oracles: " ^
         String.concatWith ", " oracles ^ "\n")
end;
