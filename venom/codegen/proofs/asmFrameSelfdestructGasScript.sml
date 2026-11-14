(* SELFDESTRUCT has no forwarded gas: all charges total at most 32600. *)
Theory asmFrameSelfdestructGas
Ancestors
  asmFrameRel asmRunBounded frameStep asmFrameLocalStep asmFrameCallStep
  vfmExecution vfmExecutionProp vfmConstants vfmOperation

Theorem step_self_destruct_gas_budget:
  es.contexts = (c,rb)::rest /\ es.msdomain = Collect d /\ wf_context c /\
  32600 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_self_destruct es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >>
  reverse (Cases_on `1 <= LENGTH c.stack`)
  >- gvs[step_self_destruct_def, pop_stack_def, get_current_context_def,
         bind_def, ignore_bind_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  Cases_on `fIN (w2w (HD (TAKE 1 c.stack))) es.rollback.accesses.addresses` >>
  gvs[step_self_destruct_def, pop_stack_def, access_address_def,
      domain_check_def, set_domain_def, get_callee_def, set_return_data_def,
      get_accounts_def, bind_def, ignore_bind_def, get_current_context_def,
      set_current_context_def, return_def, assert_def, fail_def, LET_THM,
      get_static_def, assert_not_static_def, update_accounts_def,
      get_original_def, add_to_delete_def, finish_def,
      consume_gas_def] >>
  gvs[AllCaseEqs(), frame_gas_left_def, zero_warm_def,
      warm_access_cost_def, cold_access_cost_def,
      self_destruct_new_account_cost_def] >>
  Cases_on `account_empty (lookup_account c.msgParams.callee es.originalAccounts)` >>
  gvs[update_accounts_def, add_to_delete_def, bind_def, ignore_bind_def,
      return_def, frame_gas_left_def] >>
  Cases_on `0 < (lookup_account c.msgParams.callee es.rollback.accounts).balance /\
    account_empty (lookup_account (w2w (HD (TAKE 1 c.stack))) es.rollback.accounts)` >>
  gvs[] >> decide_tac
QED

Theorem asm_frame_selfdestruct_gas:
  !prog data es0 a es H.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
    a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
    asm_inst_gas_ok H (EL a.as_pc prog) a.as_stack /\
    50000 + 8 * H + memory_cost H <= frame_gas_left es /\
    EL a.as_pc prog = AsmOp "SELFDESTRUCT" ==>
    (!op r s'.
       next_opcode (FST (HD es.contexts)) = SOME op /\
       step_inst op es = (r,s') /\
       LENGTH s'.contexts = LENGTH es.contexts ==>
       r <> INR (SOME OutOfGas) /\
       frame_gas_left es <= frame_gas_left s' +
         (50000 + 8 * H + memory_cost H)) /\
    (!es1. frame_next es es1 ==>
       frame_gas_left es <= frame_gas_left es1 +
         (50000 + 8 * H + memory_cost H))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `asm_frame_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [asm_frame_rel_def]) >>
  `wf_context c` by gvs[wf_state_def] >>
  `next_opcode (FST (HD es.contexts)) = SOME SelfDestruct` by
    (irule asm_frame_opcode_decode >>
     simp[wf_opname_def] >>
     qexistsl_tac [`a`, `data`, `prog`] >>
     gvs[symbolResolveTheory.encode_inst_def,
         symbolResolveTheory.evm_opcode_byte_def,
         symbolResolveTheory.evm_opcode_table_def, opcode_def]) >>
  `next_opcode c = SOME SelfDestruct` by gvs[] >>
  conj_asm1_tac
  >- (rpt gen_tac >> strip_tac >>
      `op = SelfDestruct` by gvs[] >>
      gvs[step_inst_def] >>
      `50000 + 8 * H + memory_cost H <= c.msgParams.gasLimit - c.gasUsed` by
        gvs[frame_gas_left_def] >>
      `32600 <= 50000 + 8 * H + memory_cost H` by simp[] >>
      drule_all step_self_destruct_gas_budget >> simp[]) >>
  gen_tac >> strip_tac >>
  irule frame_next_noncall_gas_bound >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`c`, `SelfDestruct`, `rb`, `rest`] >>
  simp[is_call_def] >> metis_tac[]
QED
