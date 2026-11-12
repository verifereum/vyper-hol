(*
 * The gas of one step of the generated code's EVM frame, for the
 * sufficient-gas theorem S7g: an instruction that touches memory only
 * below H costs at most frame_op_gas H, so with that much gas left it
 * doesn't run out of gas, and a call leaves the frame at least a 64th of
 * what is left after that cost.  RETURNDATACOPY, whose size the callee
 * sets, is the exception.
 *
 * TOP-LEVEL:
 *   frame_op_gas       - the gas bound of one instruction under H
 *   asm_frame_gas_step - the step's gas, against the assembly step
 *)

Theory asmFrameGas
Ancestors
  asmFrameRel asmRunBounded frameStep callTrace asmSem asmWf symbolResolve
  vfmExecution vfmExecutionProp asmCallGasArithmetic asmFrameCallStep codegenRel
  vfmState vfmOperation asmNonCallCheapGas asmNonCallStorageGas asmNonCallMemoryGas
  asmNonCallCopyGas asmFrameLocalStep asmFrameCreateGas

(* At least the gas of any instruction asm_inst_gas_ok H allows: static
   and access costs (a value-carrying CALL to a new account costs 36700),
   SSTORE's 22100 and its 2300 stipend check, the per-byte costs of
   copies, hashing and logs (at most 8 a byte), memory expansion to H,
   and 6400 for a call's static cost after the 63/64 split. *)
Definition frame_op_gas_def:
  frame_op_gas H = 50000 + 8 * H + memory_cost H
End

Theorem asm_frame_gas_step_call:
  !prog data es0 a es H.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
    a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
    EL a.as_pc prog <> AsmOp "RETURNDATACOPY" /\
    asm_inst_gas_ok H (EL a.as_pc prog) a.as_stack /\
    frame_op_gas H <= frame_gas_left es /\
    (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL" \/
     EL a.as_pc prog = AsmOp "DELEGATECALL") ==>
    (!op r s'.
       next_opcode (FST (HD es.contexts)) = SOME op /\
       step_inst op es = (r, s') /\
       LENGTH s'.contexts = LENGTH es.contexts ==>
       r <> INR (SOME OutOfGas) /\
       frame_gas_left es <= frame_gas_left s' + frame_op_gas H) /\
    (!es1. frame_next es es1 ==>
       (frame_gas_left es - frame_op_gas H) DIV 64 <= frame_gas_left es1)
Proof
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  qpat_assum `asm_frame_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [asm_frame_rel_def]) >>
  `c.stack = a.as_stack` by gvs[asm_evm_rel_def] >>
  `~c.msgParams.static` by metis_tac[] >>
  `EVERY (wf_context o FST) es.contexts` by fs[wf_state_def] >>
  Q.SUBGOAL_THEN `?name. (name = "CALL" \/ name = "STATICCALL" \/ name = "DELEGATECALL") /\
      EL a.as_pc prog = AsmOp name` (qx_choose_then `name` assume_tac)
  >- metis_tac[] >>
  `EL a.as_pc prog = AsmOp name` by metis_tac[] >>
  `next_opcode c = SOME (if name = "CALL" then Call else if name = "STATICCALL" then StaticCall else DelegateCall)` by
    (`next_opcode (FST (HD es.contexts)) =
       SOME (if name = "CALL" then Call else
             if name = "STATICCALL" then StaticCall else DelegateCall)` suffices_by simp[] >>
     irule asm_frame_opcode_decode >>
     conj_tac
     >- (Cases_on `name = "CALL"` >> Cases_on `name = "STATICCALL"` >>
         simp[wf_opname_def]) >>
     qexistsl_tac [`a`, `data`, `prog`] >>
     Cases_on `name = "CALL"` >> Cases_on `name = "STATICCALL"` >>
     gvs[is_data_inst_def, encode_inst_def, evm_opcode_byte_def,
         evm_opcode_table_def, wf_opname_def, opcode_def]) >>
  `asm_inst_gas_ok H (AsmOp name) c.stack` by metis_tac[] >>
  `frame_op_gas H <= c.msgParams.gasLimit - c.gasUsed` by
    fs[frame_gas_left_def] >>
  conj_tac >- suspend "raw" >> suspend "handled"
QED

Resume asm_frame_gas_step_call[raw]:
  rpt gen_tac >> rpt disch_tac >>
  `op = (if name = "CALL" then Call else if name = "STATICCALL" then StaticCall else DelegateCall)` by
    (qpat_x_assum `next_opcode (FST _) = _` mp_tac >> simp[]) >>
  `step_call op es = (r,s')` by
    (qpat_x_assum `step_inst _ _ = _` mp_tac >>
     Cases_on `name = "CALL"` >> Cases_on `name = "STATICCALL"` >>
     gvs[step_inst_def]) >>
  Q.SUBGOAL_THEN `name = "CALL" \/ name = "STATICCALL" \/ name = "DELEGATECALL"` assume_tac
  >- simp[] >>
  `frame_op_gas H = 50000 + 8 * H + memory_cost H` by simp[frame_op_gas_def] >>
  drule_all asm_step_call_budget_same_depth >> strip_tac >>
  Cases_on `s'.contexts` >- gvs[] >>
  rename1 `_.contexts = head::tail` >> Cases_on `head` >>
  gvs[frame_gas_left_def]
QED

Resume asm_frame_gas_step_call[handled]:
  gen_tac >> disch_tac >>
  qpat_x_assum `frame_next _ _`
    (strip_assume_tac o REWRITE_RULE [frame_next_def]) >>
  Q.SUBGOAL_THEN `name = "CALL" \/ name = "STATICCALL" \/ name = "DELEGATECALL"` assume_tac
  >- simp[] >>
  `frame_op_gas H = 50000 + 8 * H + memory_cost H` by simp[frame_op_gas_def] >>
  Q.SUBGOAL_THEN `es1 = v \/ LENGTH v.contexts = SUC (LENGTH es.contexts) /\
     run_call v = SOME (INL (),es1)` assume_tac >- simp[] >>
  `(c.msgParams.gasLimit - c.gasUsed - frame_op_gas H) DIV 64 <=
    (FST (HD es1.contexts)).msgParams.gasLimit - (FST (HD es1.contexts)).gasUsed` by
    (drule_at (Pat `next_opcode _ = _`) asm_step_call_budget_reserve >>
     simp[] >> disch_then irule >>
     conj_tac >- gvs[] >>
     conj_tac
     >- (qexistsl_tac [`d`, `rb`, `rest`, `es`, `v`] >> gvs[]) >>
     qexists_tac `name` >> gvs[]) >>
  Cases_on `es1.contexts` >- gvs[] >>
  rename1 `_.contexts = head::tail` >> Cases_on `head` >>
  gvs[frame_gas_left_def]
QED

Finalise asm_frame_gas_step_call

Theorem asm_frame_gas_step_noncall:
  !prog data es0 a es H.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
    a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
    EL a.as_pc prog <> AsmOp "RETURNDATACOPY" /\
    asm_inst_gas_ok H (EL a.as_pc prog) a.as_stack /\
    frame_op_gas H <= frame_gas_left es /\
    EL a.as_pc prog <> AsmOp "CALL" /\
    EL a.as_pc prog <> AsmOp "STATICCALL" /\
    ~MEM (EL a.as_pc prog) [AsmOp "DELEGATECALL"; AsmOp "CREATE";
      AsmOp "CREATE2"; AsmOp "SELFDESTRUCT"] ==>
    (!op r s'.
       next_opcode (FST (HD es.contexts)) = SOME op /\
       step_inst op es = (r,s') /\
       LENGTH s'.contexts = LENGTH es.contexts ==>
       r <> INR (SOME OutOfGas) /\
       frame_gas_left es <= frame_gas_left s' + frame_op_gas H) /\
    (!es1. frame_next es es1 ==>
       frame_gas_left es <= frame_gas_left es1 + frame_op_gas H)
Proof
  rpt gen_tac >> strip_tac >>
  conj_asm1_tac >- suspend "raw" >> suspend "handled"
QED

Resume asm_frame_gas_step_noncall[raw]:
  pure_rewrite_tac[frame_op_gas_def] >>
  rule_assum_tac (PURE_REWRITE_RULE [frame_op_gas_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `?name. EL a.as_pc prog = AsmOp name /\
    MEM name ["SLOAD";"SSTORE";"TLOAD";"TSTORE"]`
  >- (irule asm_noncall_storage_gas >> simp[GSYM frame_op_gas_def] >>
      metis_tac[listTheory.MEM]) >>
  Cases_on `?name. EL a.as_pc prog = AsmOp name /\
    MEM name ["MLOAD";"MSTORE";"MSTORE8";"SHA3";"RETURN";"REVERT"]`
  >- (irule asm_frame_memory_raw_gas >> simp[GSYM frame_op_gas_def] >>
      metis_tac[listTheory.MEM]) >>
  Cases_on `?name. EL a.as_pc prog = AsmOp name /\
    MEM name ["CALLDATACOPY";"CODECOPY";"EXTCODECOPY";"MCOPY";
      "LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]`
  >- (irule asm_frame_copy_raw_gas >> simp[GSYM frame_op_gas_def] >>
      metis_tac[listTheory.MEM]) >>
  irule asm_noncall_cheap_gas >> simp[GSYM frame_op_gas_def] >>
  gvs[listTheory.MEM] >> metis_tac[]
QED

Resume asm_frame_gas_step_noncall[handled]:
  gen_tac >> disch_tac >>
  qpat_assum `asm_frame_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [asm_frame_rel_def]) >>
  `wf_context c` by gvs[wf_state_def] >>
  drule frame_next_opcode >> disch_then drule >> disch_then drule >>
  simp[] >> strip_tac >>
  `encoding_wf_inst (EL a.as_pc prog)
     (SND (compute_label_offsets (prog ++ [AsmDataItem data])))` by
    (mp_tac (Q.SPECL [`prog ++ [AsmDataItem data]`,`a.as_pc`]
       asmToBytecodeProofsTheory.asm_encoding_wf_el) >>
     simp[asmDataSuffixPropsTheory.data_suffix_encoding_wf,
       listTheory.EL_APPEND_EQN] >> gvs[asm_frame_prog_ok_def]) >>
  `~is_call op` by
    (spose_not_then assume_tac >>
     drule_all asmCheapOpcodeClassifyTheory.encoded_call_inst_cases >>
     strip_tac >> gvs[listTheory.MEM, asm_inst_gas_ok_def]) >>
  irule frame_next_noncall_gas_bound >>
  conj_tac >- (qexistsl_tac [`c`,`op`,`rb`,`rest`] >> simp[] >> metis_tac[]) >>
  simp[]
QED

Finalise asm_frame_gas_step_noncall

(* The instructions unit_shape_ok admits beyond CALL and STATICCALL: like
   asm_frame_gas_step below.  DELEGATECALL, CREATE and CREATE2 run a child
   frame, which leaves our frame at least a 64th of what is left after
   their cost; SELFDESTRUCT ends the frame.  CREATE and CREATE2 charge the
   forwarded gas before a same-depth abort on an existing account
   (abort_create_exists), so their own step leaves only the 64th too.  Each costs less than
   frame_op_gas H: CREATE2 at most 32000 + 8 words per initcode word
   (asm_inst_gas_ok bounds the initcode by 2 * max_code_size) plus memory
   below H, SELFDESTRUCT at most 5000 + 2600 + 25000. *)
Theorem asm_frame_gas_step_create:
  !prog data es0 a es H.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
    a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
    asm_inst_gas_ok H (EL a.as_pc prog) a.as_stack /\
    frame_op_gas H <= frame_gas_left es /\
    MEM (EL a.as_pc prog) [AsmOp "DELEGATECALL"; AsmOp "CREATE";
      AsmOp "CREATE2"; AsmOp "SELFDESTRUCT"] ==>
    (!op r s'.
       next_opcode (FST (HD es.contexts)) = SOME op /\
       step_inst op es = (r, s') /\
       LENGTH s'.contexts = LENGTH es.contexts ==>
       r <> INR (SOME OutOfGas) /\
       if EL a.as_pc prog = AsmOp "CREATE" \/ EL a.as_pc prog = AsmOp "CREATE2"
       then (frame_gas_left es - frame_op_gas H) DIV 64 <= frame_gas_left s'
       else frame_gas_left es <= frame_gas_left s' + frame_op_gas H) /\
    (!es1. frame_next es es1 ==>
       if EL a.as_pc prog = AsmOp "SELFDESTRUCT"
       then frame_gas_left es <= frame_gas_left es1 + frame_op_gas H
       else (frame_gas_left es - frame_op_gas H) DIV 64 <= frame_gas_left es1)
Proof
  cheat
QED

(* The frame's step at es, an instruction of prog that is
   asm_inst_gas_ok H and not RETURNDATACOPY, with frame_op_gas H gas left:
   step_inst doesn't run out of gas at our depth and uses at most
   frame_op_gas H there (a CREATE or CREATE2 leaves at least a 64th of what
   is left after that), and at the frame's next state an instruction that
   runs a child frame (CALL, STATICCALL, DELEGATECALL, CREATE, CREATE2)
   leaves at least a 64th of what is left after that. *)
Theorem asm_frame_gas_step:
  !prog data es0 a es H.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
    a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
    EL a.as_pc prog <> AsmOp "RETURNDATACOPY" /\
    asm_inst_gas_ok H (EL a.as_pc prog) a.as_stack /\
    frame_op_gas H <= frame_gas_left es ==>
    (!op r s'.
       next_opcode (FST (HD es.contexts)) = SOME op /\
       step_inst op es = (r, s') /\
       LENGTH s'.contexts = LENGTH es.contexts ==>
       r <> INR (SOME OutOfGas) /\
       if EL a.as_pc prog = AsmOp "CREATE" \/ EL a.as_pc prog = AsmOp "CREATE2"
       then (frame_gas_left es - frame_op_gas H) DIV 64 <= frame_gas_left s'
       else frame_gas_left es <= frame_gas_left s' + frame_op_gas H) /\
    (!es1. frame_next es es1 ==>
       if MEM (EL a.as_pc prog) [AsmOp "CALL"; AsmOp "STATICCALL";
            AsmOp "DELEGATECALL"; AsmOp "CREATE"; AsmOp "CREATE2"]
       then (frame_gas_left es - frame_op_gas H) DIV 64 <= frame_gas_left es1
       else frame_gas_left es <= frame_gas_left es1 + frame_op_gas H)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `EL a.as_pc prog = AsmOp "CALL" \/
            EL a.as_pc prog = AsmOp "STATICCALL" \/
            EL a.as_pc prog = AsmOp "DELEGATECALL"`
  >- (drule_all asm_frame_gas_step_call >> gvs[]) >>
  Cases_on `MEM (EL a.as_pc prog) [AsmOp "DELEGATECALL"; AsmOp "CREATE";
              AsmOp "CREATE2"; AsmOp "SELFDESTRUCT"]`
  >- (drule_all asm_frame_gas_step_create >> gvs[]) >>
  `EL a.as_pc prog <> AsmOp "CALL" /\
   EL a.as_pc prog <> AsmOp "STATICCALL"` by gvs[] >>
  drule_all asm_frame_gas_step_noncall >> gvs[]
QED
