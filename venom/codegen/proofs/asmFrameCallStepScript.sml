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
  vfmAccountFrame asmEncodeParse rich_list vfmOperation regularMemorySim vfmBuffer vfmTypes list

Theorem asm_call_child_parent_msgParams:
  step_call op s = (q,e) /\ s.contexts <> [] /\
  LENGTH s.contexts < LENGTH e.contexts /\
  wf_state e /\ run_call e = SOME (INL (),t) ==>
  (FST (HD t.contexts)).msgParams =
  (FST (HD s.contexts)).msgParams
Proof
  strip_tac >> drule step_call_push_structure >> simp[] >> strip_tac >>
  `2 <= LENGTH e.contexts` by
    (Cases_on `s.contexts` >> gvs[] >> decide_tac) >>
  drule_all run_call_parent_msgParams >> strip_tac >>
  Cases_on `e.contexts` >> gvs[] >>
  rename1 `e.contexts = child :: parents` >>
  Cases_on `parents` >> gvs[]
QED

Theorem asm_frame_call_decode:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\
  (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL") ==>
  next_opcode (FST (HD es.contexts)) =
    SOME (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall)
Proof
  strip_tac >>
  `asm_encoding_wf (prog ++ [AsmDataItem data])` by
    gvs[asm_frame_prog_ok_def, data_suffix_encoding_wf] >>
  `a.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
  `!j. j <= a.as_pc ==> ~is_data_inst (EL j (prog ++ [AsmDataItem data]))` by
    (rpt strip_tac >> `j < LENGTH prog` by decide_tac >>
     gvs[EL_APPEND1, asm_frame_prog_ok_def] >>
     metis_tac[is_data_inst_def]) >>
  drule_all assemble_parse_exact >> strip_tac >>
  `asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc <
     LENGTH (assemble (prog ++ [AsmDataItem data]))` by
    (irule offset_in_bounds >> simp[]) >>
  gvs[EL_APPEND1, encode_inst_def, evm_opcode_byte_def, evm_opcode_table_def] >>
  `op = (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall)` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def]) >>
  Cases_on `es.contexts` >> gvs[asm_evm_rel_def] >>
  PairCases_on `h` >> gvs[asm_evm_rel_def, next_opcode_def]
QED

Theorem asm_frame_call_observable:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\
  ((EL a.as_pc prog = AsmOp "CALL" /\ 7 <= LENGTH a.as_stack) \/
   (EL a.as_pc prog = AsmOp "STATICCALL" /\ 6 <= LENGTH a.as_stack)) ==>
  observable_call (FST (HD es.contexts))
Proof
  strip_tac >>
  `next_opcode (FST (HD es.contexts)) =
     SOME (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall)` by
    (irule asm_frame_call_decode >> metis_tac[]) >>
  Cases_on `es.contexts` >> gvs[asm_evm_rel_def] >>
  PairCases_on `h` >> gvs[asm_evm_rel_def, observable_call_def]
QED

Theorem asm_call_input_buffer:
  TAKE sz (DROP off (asm_expand_memory (off + sz) (buffer_to_list mem))) =
  buffer_read off sz mem
Proof
  simp[expanded_slice_padded_range, buffer_read_to_list,
       take_pad_0_def, PAD_RIGHT, GSYM REPLICATE_GENLIST] >>
  irule LIST_EQ >> simp[LENGTH_TAKE_EQ] >>
  rpt strip_tac >>
  simp[EL_GENLIST, read_byte_def, EL_APPEND_EQN, EL_TAKE, EL_DROP,
       EL_REPLICATE] >>
  IF_CASES_TAC >> gvs[LENGTH_TAKE_EQ, EL_DROP, EL_REPLICATE] >>
  rpt (IF_CASES_TAC >> gvs[EL_REPLICATE])
QED

Theorem asm_frame_call_request:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "CALL" /\
  a.as_stack = gas :: addr :: value :: ao :: sz :: ro :: rs :: stk ==>
  asm_call_request a addr value (w2n ao) (w2n sz) F = request_of es
Proof
  strip_tac >>
  `next_opcode (FST (HD es.contexts)) = SOME Call` by
    (drule asm_frame_call_decode >>
     disch_then (qspecl_then [`es`, `data`, `a`] mp_tac) >> simp[]) >>
  Cases_on `es.contexts` >> gvs[asm_evm_rel_def] >>
  PairCases_on `h` >> gvs[asm_evm_rel_def] >>
  simp[request_of_def, asm_call_request_def, GSYM asm_call_input_buffer,
       expanded_slice_padded_range]
QED

Theorem asm_frame_staticcall_request:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "STATICCALL" /\
  a.as_stack = gas :: addr :: ao :: sz :: ro :: rs :: stk ==>
  asm_call_request a addr 0w (w2n ao) (w2n sz) T = request_of es
Proof
  strip_tac >>
  `next_opcode (FST (HD es.contexts)) = SOME StaticCall` by
    (drule asm_frame_call_decode >>
     disch_then (qspecl_then [`es`, `data`, `a`] mp_tac) >> simp[]) >>
  Cases_on `es.contexts` >> gvs[asm_evm_rel_def] >>
  PairCases_on `h` >> gvs[asm_evm_rel_def] >>
  simp[request_of_def, asm_call_request_def, GSYM asm_call_input_buffer,
       expanded_slice_padded_range]
QED

Theorem asm_call_underflow:
  LENGTH a.as_stack < 7 ==>
  asm_step lo otp (AsmOp "CALL") a = AsmError "call: stack underflow"
Proof
  simp[asm_step_call_staticcall_gas] >>
  Cases_on `a.as_stack` >> simp[asm_exec_call_def] >>
  Cases_on `t` >> simp[asm_exec_call_def] >>
  Cases_on `t'` >> simp[asm_exec_call_def] >>
  Cases_on `t` >> simp[asm_exec_call_def] >>
  Cases_on `t'` >> simp[asm_exec_call_def] >>
  Cases_on `t` >> simp[asm_exec_call_def] >>
  Cases_on `t'` >> simp[asm_exec_call_def]
QED

Theorem asm_staticcall_underflow:
  LENGTH a.as_stack < 6 ==>
  asm_step lo otp (AsmOp "STATICCALL") a = AsmError "staticcall: stack underflow"
Proof
  simp[asm_step_call_staticcall_gas] >>
  Cases_on `a.as_stack` >> simp[asm_exec_staticcall_def] >>
  Cases_on `t` >> simp[asm_exec_staticcall_def] >>
  Cases_on `t'` >> simp[asm_exec_staticcall_def] >>
  Cases_on `t` >> simp[asm_exec_staticcall_def] >>
  Cases_on `t'` >> simp[asm_exec_staticcall_def] >>
  Cases_on `t` >> simp[asm_exec_staticcall_def]
QED

Theorem asm_frame_call_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\
  (EL as.as_pc prog = AsmOp "CALL" \/ EL as.as_pc prog = AsmOp "STATICCALL") ==>
  asm_frame_step_ok prog data es0 as es
Proof
  cheat
QED
