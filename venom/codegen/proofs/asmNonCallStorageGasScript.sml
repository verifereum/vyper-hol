(* Storage instruction charges, before exception handling. *)
Theory asmNonCallStorageGas
Ancestors
  asmFrameRel asmRunBounded frameStep asmFrameLocalStep asmCallGasArithmetic
  vfmExecution vfmExecutionProp vfmConstants vfmOperation vfmProg

Theorem step_tload_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  100 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_sload T es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >>
  gvs[step_sload_def, pop_stack_def, consume_gas_def,
      push_stack_def, get_callee_def, get_tStorage_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      warm_access_cost_def, wf_context_def, AllCaseEqs()] >>
  gvs[frame_gas_left_def] >> decide_tac
QED

Theorem step_tstore_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  100 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_sstore T es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >>
  gvs[step_sstore_def, pop_stack_def, consume_gas_def,
      get_callee_def, get_tStorage_def, get_static_def, assert_not_static_def,
      write_transient_storage_def, set_tStorage_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      warm_access_cost_def, wf_context_def, AllCaseEqs()] >>
  gvs[frame_gas_left_def] >> decide_tac
QED

Theorem step_sload_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  2100 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_sload F es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >>
  gvs[step_sload_def, pop_stack_def, consume_gas_def,
      push_stack_def, get_callee_def, get_accounts_def,
      access_slot_def, domain_check_def, set_domain_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      warm_access_cost_def, cold_sload_cost_def, wf_context_def,
      AllCaseEqs()] >>
  rpt IF_CASES_TAC >>
  gvs[frame_gas_left_def, bind_def, ignore_bind_def, return_def,
      assert_def, fail_def, set_current_context_def, push_stack_def,
      get_current_context_def] >> decide_tac
QED


Theorem step_sstore_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  22101 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_sstore F es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >>
  gvs[step_sstore_def, step_sstore_gas_consumption_def,
      pop_stack_def, get_gas_left_def,
      get_callee_def, get_accounts_def, get_original_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      call_stipend_def, wf_context_def, AllCaseEqs()] >>
  imp_res_tac write_storage_frame_gas >>
  imp_res_tac update_gas_refund_frame_gas >>
  imp_res_tac assert_not_static_frame_gas >>
  gvs[access_slot_def, domain_check_def, set_domain_def,
      bind_def, ignore_bind_def, return_def, assert_def, fail_def,
      AllCaseEqs()] >>
  fs[frame_gas_left_def, zero_warm_def, warm_access_cost_def,
     cold_sload_cost_def] >>
  qpat_x_assum `consume_gas k st = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `consume_gas charge st` >>
  `charge <= 22100` by
    (simp[Abbr `charge`] >>
     qmatch_goalsub_abbrev_tac `sstore_base_gas ov cv v` >>
     mp_tac sstore_base_gas_le >>
     decide_tac) >>
  strip_tac >>
  drule consume_gas_frame_gas >>
  impl_tac >- (gvs[frame_gas_left_def] >> decide_tac) >>
  strip_tac >> gvs[frame_gas_left_def] >> decide_tac
QED

Theorem asm_noncall_storage_gas:
  !prog data es0 a es H.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
    a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
    EL a.as_pc prog <> AsmOp "RETURNDATACOPY" /\
    asm_inst_gas_ok H (EL a.as_pc prog) a.as_stack /\
    50000 + 8 * H + memory_cost H <= frame_gas_left es /\
    EL a.as_pc prog <> AsmOp "CALL" /\
    EL a.as_pc prog <> AsmOp "STATICCALL" /\
    (?name. EL a.as_pc prog = AsmOp name /\
       MEM name ["SLOAD"; "SSTORE"; "TLOAD"; "TSTORE"]) ==>
    !op r s'.
      next_opcode (FST (HD es.contexts)) = SOME op /\
      step_inst op es = (r,s') /\
      LENGTH s'.contexts = LENGTH es.contexts ==>
      r <> INR (SOME OutOfGas) /\
      frame_gas_left es <= frame_gas_left s' +
        (50000 + 8 * H + memory_cost H)
Proof
  rpt gen_tac >> strip_tac >>
  fs[asm_frame_rel_def] >>
  `wf_context c` by gvs[wf_state_def] >>
  drule frame_next_opcode >>
  disch_then drule >> disch_then drule >>
  simp[] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[listTheory.MEM, symbolResolveTheory.encode_inst_def,
      symbolResolveTheory.evm_opcode_byte_def,
      symbolResolveTheory.evm_opcode_table_def] >>
  all_tac
  >- (`op = SLoad` by
        (irule asmEncodeParseTheory.opcode_wf_inj >>
         simp[wf_opname_def, opcode_def]) >>
      gvs[step_inst_def] >>
      drule step_sload_gas_budget >>
      disch_then (qspecl_then [`s'`,`r`,
        `50000 + 8 * H + memory_cost H`] mp_tac) >>
      gvs[frame_gas_left_def] >> decide_tac)
  >- (`op = SStore` by
        (irule asmEncodeParseTheory.opcode_wf_inj >>
         simp[wf_opname_def, opcode_def]) >>
      gvs[step_inst_def] >>
      drule step_sstore_gas_budget >>
      disch_then (qspecl_then [`s'`,`r`,
        `50000 + 8 * H + memory_cost H`] mp_tac) >>
      gvs[frame_gas_left_def] >> decide_tac)
  >- (`op = TLoad` by
        (irule asmEncodeParseTheory.opcode_wf_inj >>
         simp[wf_opname_def, opcode_def]) >>
      gvs[step_inst_def] >>
      drule step_tload_gas_budget >>
      disch_then (qspecl_then [`s'`,`r`,
        `50000 + 8 * H + memory_cost H`] mp_tac) >>
      gvs[frame_gas_left_def] >> decide_tac) >>
  `op = TStore` by
    (irule asmEncodeParseTheory.opcode_wf_inj >>
     simp[wf_opname_def, opcode_def]) >>
  gvs[step_inst_def] >> drule step_tstore_gas_budget >>
  disch_then (qspecl_then [`s'`,`r`,
    `50000 + 8 * H + memory_cost H`] mp_tac) >>
  gvs[frame_gas_left_def] >> decide_tac
QED
