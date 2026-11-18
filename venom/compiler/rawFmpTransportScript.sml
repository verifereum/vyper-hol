Theory rawFmpTransport
Ancestors
  rawFmpTransportDefs instIdxIndep rawReachableFmp unitShapeDefs venomCallOracleProps
  lowerDloadExternalBackward lowerDloadPtrCreateInterfaces
  concretizeLayoutDelegate deadStoreElimCallSteps deadStoreElimDelegateCallSteps
  readonlyInvokeCopyFwdStepsExternalErrors
  venomExecSemantics venomState venomInst list
  rawFmpExternalCallTransport rawFmpDelegateTransport rawFmpCreateTransport
  rawFmpNonexternalTransport rawFmpRecursiveTransport
Libs
  BasicProvers

Theorem eval_operand_fmp_update[simp]:
  (!op s p. eval_operand op (s with vs_fmp := p) = eval_operand op s) /\
  (!op s i. eval_operand op (s with vs_initial_fmp := i) = eval_operand op s) /\
  (!op s e. eval_operand op (s with vs_call_entry_fmp := e) = eval_operand op s)
Proof
  rpt conj_tac >> Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_phis_fmp_update:
  !insts s p i e.
    eval_phis (s with <|vs_fmp := p; vs_initial_fmp := i;
                       vs_call_entry_fmp := e|>) insts =
    exec_result_map
      (\s. s with <|vs_fmp := p; vs_initial_fmp := i;
                     vs_call_entry_fmp := e|>) (eval_phis s insts)
Proof
  Induct >> rpt gen_tac >> simp[eval_phis_def, exec_result_map_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[exec_result_map_def] >>
  `eval_one_phi (s with <|vs_fmp := p; vs_initial_fmp := i;
                        vs_call_entry_fmp := e|>) h = eval_one_phi s h` by
    simp[eval_one_phi_def, eval_operand_def, lookup_var_def] >>
  gvs[] >> Cases_on `eval_one_phi s h` >> gvs[exec_result_map_def] >>
  PairCases_on `x` >> simp[] >>
  first_x_assum (qspecl_then [`s`, `p`, `i`, `e`] assume_tac) >>
  gvs[] >> Cases_on `eval_phis s insts` >>
  simp[exec_result_map_def, update_var_def]
QED

Theorem step_inst_base_fmp_update:
  !inst s p i e.
    raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA /\
    inst.inst_opcode <> INVOKE ==>
    step_inst_base inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
    exec_result_map
      (\t. t with <|vs_fmp := p; vs_initial_fmp := i;
                    vs_call_entry_fmp := e|>) (step_inst_base inst s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`
  >- (gvs[MEM] >>
      `!ops s p i e. eval_operands ops
          (s with <|vs_fmp := p; vs_initial_fmp := i;
                    vs_call_entry_fmp := e|>) = eval_operands ops s` by
        (rpt gen_tac >> irule eval_operands_agree >> simp[]) >>
      rule_assum_tac (SRULE []) >>
      simp[step_inst_base_opcode_eqs, SRULE [] exec_ext_call_fmp_update,
           SRULE [] exec_delegatecall_fmp_update, SRULE [] exec_create_fmp_update] >>
      rpt (PURE_TOP_CASE_TAC >>
           simp[SRULE [] exec_ext_call_fmp_update, SRULE [] exec_delegatecall_fmp_update,
                SRULE [] exec_create_fmp_update, exec_result_map_def,
                halt_state_def, set_returndata_def])) >>
  irule step_inst_base_nonexternal_fmp_update_under_operand >> simp[]
QED

Theorem run_defs_fmp_update:
  (!fuel ctx inst s. !p i e.
    EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
                              inst.inst_opcode <> DALLOCA) (fn_insts fn))
      ctx.ctx_functions /\
    raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
    raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
      (step_inst fuel ctx inst
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
   (!fuel ctx bb s. !p i e.
    EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
                              inst.inst_opcode <> DALLOCA) (fn_insts fn))
      ctx.ctx_functions /\
    EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
      bb.bb_instructions ==>
    raw_fmp_result_rel p i e (exec_block fuel ctx bb s)
      (exec_block fuel ctx bb
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
   (!fuel ctx fn s. !p i e.
    EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
                              inst.inst_opcode <> DALLOCA) (fn_insts fn))
      ctx.ctx_functions /\
    EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
      (fn_insts fn) ==>
    raw_fmp_result_rel p i e (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)))
Proof
  irule run_defs_fmp_update_under_base >>
  simp[eval_phis_fmp_update, step_inst_base_fmp_update]
QED
