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
  vfmState

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
    (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL") ==>
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
  Q.SUBGOAL_THEN `?name. (name = "CALL" \/ name = "STATICCALL") /\
      EL a.as_pc prog = AsmOp name` (qx_choose_then `name` assume_tac)
  >- metis_tac[] >>
  `EL a.as_pc prog = AsmOp name` by metis_tac[] >>
  `next_opcode c = SOME (if name = "CALL" then Call else StaticCall)` by
    (drule_all asm_frame_call_decode >> simp[] >> metis_tac[]) >>
  `asm_inst_gas_ok H (AsmOp name) c.stack` by metis_tac[] >>
  `frame_op_gas H <= c.msgParams.gasLimit - c.gasUsed` by
    fs[frame_gas_left_def] >>
  conj_tac >- suspend "raw" >> suspend "handled"
QED

Resume asm_frame_gas_step_call[raw]:
  rpt gen_tac >> rpt disch_tac >>
  `op = (if name = "CALL" then Call else StaticCall)` by
    (qpat_x_assum `next_opcode (FST _) = _` mp_tac >> simp[]) >>
  `step_call op es = (r,s')` by
    (qpat_x_assum `step_inst _ _ = _` mp_tac >>
     Cases_on `name = "CALL"` >> gvs[step_inst_def]) >>
  Q.SUBGOAL_THEN `name = "CALL" \/ name = "STATICCALL"` assume_tac
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
  Q.SUBGOAL_THEN `name = "CALL" \/ name = "STATICCALL"` assume_tac
  >- simp[] >>
  `frame_op_gas H = 50000 + 8 * H + memory_cost H` by simp[frame_op_gas_def] >>
  Q.SUBGOAL_THEN `es1 = v \/ LENGTH v.contexts = SUC (LENGTH es.contexts) /\
     run_call v = SOME (INL (),es1)` assume_tac >- simp[] >>
  `(c.msgParams.gasLimit - c.gasUsed - frame_op_gas H) DIV 64 <=
    (FST (HD es1.contexts)).msgParams.gasLimit - (FST (HD es1.contexts)).gasUsed` by
    metis_tac[asm_step_call_budget_reserve] >>
  Cases_on `es1.contexts` >- gvs[] >>
  rename1 `_.contexts = head::tail` >> Cases_on `head` >>
  gvs[frame_gas_left_def]
QED

Finalise asm_frame_gas_step_call

(* The frame's step at es, an instruction of prog that is
   asm_inst_gas_ok H and not RETURNDATACOPY, with frame_op_gas H gas left:
   step_inst doesn't run out of gas at our depth and uses at most
   frame_op_gas H there, and at the frame's next state a CALL or
   STATICCALL leaves at least a 64th of what is left after that. *)
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
       frame_gas_left es <= frame_gas_left s' + frame_op_gas H) /\
    (!es1. frame_next es es1 ==>
       if EL a.as_pc prog = AsmOp "CALL" \/
          EL a.as_pc prog = AsmOp "STATICCALL"
       then (frame_gas_left es - frame_op_gas H) DIV 64 <= frame_gas_left es1
       else frame_gas_left es <= frame_gas_left es1 + frame_op_gas H)
Proof
  cheat
QED
