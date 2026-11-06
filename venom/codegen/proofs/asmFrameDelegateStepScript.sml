(* Delegate calls use the frame's observed message-call outcomes. *)
Theory asmFrameDelegateStep
Ancestors
  asmFrameRel asmFrameCallStep frameObsStep asmCallOracleProps asmDataSuffixProps
  codegenRel asmSem asmWf symbolResolve extCallOracle callTrace frameOutcome
  vfmExecution vfmExecutionProp asmEncodeParse vfmOperation rich_list list regularMemorySim

(* Check the delegated request boundary without equating its zero value
   with the inherited EVM message value. *)
Theorem asm_delegate_request_fields[local]:
  s.contexts = (c,rb)::rest /\ next_opcode c = SOME DelegateCall ==>
  (request_of s).cr_kind = DelegateMessageCall /\
  (request_of s).cr_value = 0 /\
  (request_of s).cr_static = c.msgParams.static /\
  ~computed_precompile (request_of s)
Proof
  simp[request_of_def, computed_precompile_def]
QED

Theorem asm_delegate_outcome_view[local]:
  outcome_of DelegateMessageCall s n m = outcome_of MessageCall s n m
Proof
  simp[outcome_of_def]
QED

(* A delegated child runs the parent's identities and value, not the
   request's target/value pair.  This is an entry-interface diagnostic. *)
Theorem asm_delegate_enter_view[local]:
  s.contexts = (parent,prb)::rest /\
  ~fIN address precompile_addresses /\
  proceed_call DelegateCall sender address 0 ao az code stipend (Memory mr) s =
    (INL (),t) ==>
  ?child. t.contexts = (child,s.rollback)::(parent,prb)::rest /\
    child.msgParams.callee = sender /\
    child.msgParams.caller = parent.msgParams.caller /\
    child.msgParams.value = parent.msgParams.value /\
    child.msgParams.static = parent.msgParams.static /\
    child.msgParams.outputTo = Memory mr /\ child.logs = [] /\
    t.rollback = s.rollback
Proof
  strip_tac >>
  qhdtm_x_assum `proceed_call` mp_tac >>
  simp[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_caller_def,
       get_value_def, get_static_def, push_context_def,
       get_current_context_def, return_def] >>
  strip_tac >>
  gvs[vfmContextTheory.initial_context_def,
      vfmContextTheory.initial_msg_params_def]
QED

Theorem asm_frame_delegate_decode[local]:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "DELEGATECALL" ==>
  next_opcode (FST (HD es.contexts)) = SOME DelegateCall
Proof
  strip_tac >>
  `asm_encoding_wf (prog ++ [AsmDataItem data])` by
    gvs[asm_frame_prog_ok_def, data_suffix_encoding_wf] >>
  `a.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
  `!j. j <= a.as_pc ==> ~is_data_inst (EL j (prog ++ [AsmDataItem data]))` by
    (rpt strip_tac >> `j < LENGTH prog` by decide_tac >>
     gvs[EL_APPEND1, asm_frame_prog_ok_def] >> metis_tac[is_data_inst_def]) >>
  drule_all assemble_parse_exact >> strip_tac >>
  `asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc <
     LENGTH (assemble (prog ++ [AsmDataItem data]))` by
    (irule offset_in_bounds >> simp[]) >>
  gvs[EL_APPEND1, encode_inst_def, evm_opcode_byte_def, evm_opcode_table_def] >>
  `op = DelegateCall` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def]) >>
  Cases_on `es.contexts` >> gvs[asm_evm_rel_def] >>
  PairCases_on `h` >> gvs[asm_evm_rel_def, next_opcode_def]
QED

Theorem asm_frame_delegate_pc_increment[local]:
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "DELEGATECALL" ==>
  asm_pc_to_offset (prog ++ [AsmDataItem data]) (a.as_pc + 1) =
    asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc + 1
Proof
  strip_tac >>
  `a.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
  drule asm_pc_to_offset_suc >>
  simp[arithmeticTheory.ADD1, EL_APPEND1, asm_inst_size_def]
QED

Theorem asm_step_delegate[local]:
  asm_step lo otp (AsmOp "DELEGATECALL") a = asm_exec_delegatecall a
Proof
  simp[asm_step_def, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_step_control_def, asm_step_extcall_def, asm_step_copy_def,
       asm_step_context_def]
QED

Theorem asm_delegate_underflow[local]:
  LENGTH a.as_stack < 6 ==>
  asm_step lo otp (AsmOp "DELEGATECALL") a = AsmError "delegatecall: stack underflow"
Proof
  simp[asm_step_delegate] >>
  Cases_on `a.as_stack` >> simp[asm_exec_delegatecall_def] >>
  Cases_on `t` >> simp[asm_exec_delegatecall_def] >>
  Cases_on `t'` >> simp[asm_exec_delegatecall_def] >>
  Cases_on `t` >> simp[asm_exec_delegatecall_def] >>
  Cases_on `t'` >> simp[asm_exec_delegatecall_def] >>
  Cases_on `t` >> simp[asm_exec_delegatecall_def]
QED

Theorem asm_frame_delegate_request[local]:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "DELEGATECALL" /\
  a.as_stack = gas :: addr :: ao :: sz :: ro :: rs :: stk ==>
  (asm_call_request a addr 0w (w2n ao) (w2n sz) F with
     cr_kind := DelegateMessageCall) = request_of es
Proof
  strip_tac >>
  `next_opcode (FST (HD es.contexts)) = SOME DelegateCall` by
    (drule_all asm_frame_delegate_decode >> simp[]) >>
  Cases_on `es.contexts` >> gvs[asm_evm_rel_def] >>
  PairCases_on `h` >> gvs[asm_evm_rel_def] >>
  simp[request_of_def, asm_call_request_def, GSYM asm_call_input_buffer,
       expanded_slice_padded_range]
QED

Theorem asm_frame_delegate_consume[local]:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "DELEGATECALL" /\
  s.contexts = (c,rb)::rest /\
  asm_call_prepare DelegateCall s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) ==>
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (EL a.as_pc prog) a =
  asm_consume_call_outcome (request_of s) ro rs (DROP 6 a.as_stack)
    (a with as_memory := asm_call_memory ao az ro rs a.as_memory)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a s /\
   ~c.msgParams.static /\ ?d. s.msdomain = Collect d` by
    (fs[asm_frame_rel_def] >> metis_tac[]) >>
  drule_at (Pat `asm_call_prepare _ _ = _`) asm_message_prepare_success_view >>
  disch_then (qspecl_then [`rest`,`rb`,`d`,`c`] mp_tac) >>
  (impl_tac >- simp[]) >>
  simp_tac (srw_ss()) [LET_THM, call_has_value_def] >> strip_tac >>
  qpat_x_assum `u = _` kall_tac >>
  `c.stack = a.as_stack` by gvs[asm_evm_rel_def] >>
  `?gas addr x y z w stk. a.as_stack = gas::addr::x::y::z::w::stk` by
    (qpat_x_assum `6 <= LENGTH _` mp_tac >>
     namedCases_on `a.as_stack` ["", "gas t1"] >> simp[] >>
     namedCases_on `t1` ["", "addr t2"] >> simp[] >>
     namedCases_on `t2` ["", "x t3"] >> simp[] >>
     namedCases_on `t3` ["", "y t4"] >> simp[] >>
     namedCases_on `t4` ["", "z t5"] >> simp[] >>
     namedCases_on `t5` ["", "w stk"] >> simp[]) >>
  drule_all asm_frame_delegate_request >> disch_tac >>
  gvs[] >> simp[asm_step_delegate, asm_exec_delegatecall_def]
QED

Theorem asm_frame_delegate_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp "DELEGATECALL" ==>
  asm_frame_step_ok prog data es0 as es
Proof
  cheat
QED
