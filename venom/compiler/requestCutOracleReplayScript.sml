Theory requestCutOracleReplay
Ancestors
  instIdxIndep venomCallOracleDefs venomExecSemantics venomState venomInst
  list option pair extCallOracle loweringBudgetFrameOracleTransport
Libs
  BasicProvers

val _ = export_rewrites
  ["loweringBudgetFrameOracleTransport.operand_outcomes_update",
   "loweringBudgetFrameOracleTransport.eval_operands_outcomes_update"]

val outcome_record_ss = pure_ss ++ boolSimps.BOOL_ss ++ rewrites
  [venom_state_accfupds, venom_state_fupdcanon,
   venom_state_fupdfupds, venom_state_fupdfupds_comp,
   combinTheory.K_THM, combinTheory.o_DEF, LET_THM,
   exec_result_map_def, update_var_def, APPEND,
   list_case_def, option_case_def, pair_case_thm, operand_case_def,
   operand_outcomes_update, eval_operands_outcomes_update];

val outcome_envelope_ss = outcome_record_ss ++ rewrites
  [exec_pure1_def, exec_pure2_def, exec_pure3_def,
   exec_read0_def, exec_read1_def, exec_write2_def, exec_gas_def,
   exec_alloca_def];

val outcome_state_ss = outcome_record_ss ++ rewrites
  [write_memory_with_expansion_def, read_memory_def,
   mstore_def, mstore8_def, mload_def, mcopy_def, istore_def,
   sload_def, sstore_def, tload_def, tstore_def,
   contract_storage_def, contract_transient_def,
   jump_to_def, halt_state_def, revert_state_def, set_returndata_def];

val opcode_equations = map (fn th =>
  (rhs (fst (dest_imp (snd (strip_forall (concl th))))), th))
  (CONJUNCTS step_inst_base_opcode_eqs);

fun rewrite_opcode eq =
  let val (_, th) = valOf (List.find
    (fn (opc, _) => aconv opc (rhs (concl eq))) opcode_equations)
  in PURE_ONCE_REWRITE_TAC [MATCH_MP th eq] end;

Theorem pack_dret_dynamic_outcome_suffix[local]:
  !pairs cursor s ptrs final_cursor t tail.
    pack_dret_dynamic cursor pairs s = (ptrs,final_cursor,t) ==>
    t.vs_outcomes = s.vs_outcomes /\
    pack_dret_dynamic cursor pairs (s with vs_outcomes := s.vs_outcomes ++ tail) =
      (ptrs,final_cursor,t with vs_outcomes := t.vs_outcomes ++ tail)
Proof
  Induct >- simp[pack_dret_dynamic_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[Once pack_dret_dynamic_def] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> first_x_assum drule >> disch_then (qspec_then `tail` assume_tac) >>
  simp[Once pack_dret_dynamic_def] >>
  fs[mcopy_def, write_memory_with_expansion_def]
QED

Theorem step_inst_base_nonexternal_outcome_suffix[local]:
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  step_inst_base inst (s with vs_outcomes := s.vs_outcomes ++ tail) =
  exec_result_map (\t. t with vs_outcomes := t.vs_outcomes ++ tail)
    (step_inst_base inst s)
Proof
  Cases_on `inst.inst_opcode` >> simp[] >>
  qpat_assum `inst.inst_opcode = _` rewrite_opcode >>
  asm_simp_tac outcome_envelope_ss [] >>
  rpt (PURE_TOP_CASE_TAC >> asm_simp_tac outcome_envelope_ss []) >>
  asm_simp_tac outcome_state_ss [] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all pack_dret_dynamic_outcome_suffix >>
  disch_then (qspec_then `tail` strip_assume_tac) >>
  gvs[exec_result_map_def]
QED

Theorem take_outcome_suffix[local]:
  FST (take_outcome rq (ohead::(os ++ tail))) = FST (take_outcome rq (ohead::os)) /\
  SND (take_outcome rq (ohead::(os ++ tail))) = SND (take_outcome rq (ohead::os)) ++ tail
Proof
  simp[take_outcome_def] >> rpt CASE_TAC >> gvs[]
QED

Theorem external_outcome_suffix[local]:
  s.vs_outcomes <> [] ==>
  exec_ext_call inst (s with vs_outcomes := s.vs_outcomes ++ tail)
    gas addr value off sz ro rs static =
  exec_result_map (\t. t with vs_outcomes := t.vs_outcomes ++ tail)
    (exec_ext_call inst s gas addr value off sz ro rs static) /\
  exec_delegatecall inst (s with vs_outcomes := s.vs_outcomes ++ tail)
    gas addr off sz ro rs =
  exec_result_map (\t. t with vs_outcomes := t.vs_outcomes ++ tail)
    (exec_delegatecall inst s gas addr off sz ro rs) /\
  exec_create inst (s with vs_outcomes := s.vs_outcomes ++ tail) value off sz salt =
  exec_result_map (\t. t with vs_outcomes := t.vs_outcomes ++ tail)
    (exec_create inst s value off sz salt)
Proof
  Cases_on `s.vs_outcomes` >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
       exec_result_map_def] >> Cases_on `outs` >>
  simp[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
       venom_call_request_def, venom_create_request_def, read_memory_def,
       consume_call_outcome_eq, consume_create_outcome_eq, take_outcome_suffix,
       write_memory_with_expansion_def, update_var_def, halt_state_def,
       set_returndata_def, exec_result_map_def] >>
  rw[exec_result_map_def, halt_state_def, set_returndata_def]
QED

Theorem step_inst_base_outcome_suffix_available[local]:
  (MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
   s.vs_outcomes <> []) ==>
  step_inst_base inst (s with vs_outcomes := s.vs_outcomes ++ tail) =
  exec_result_map (\t. t with vs_outcomes := t.vs_outcomes ++ tail)
    (step_inst_base inst s)
Proof
  disch_tac >>
  Cases_on `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`
  >- (gvs[MEM] >>
      qpat_assum `inst.inst_opcode = _` rewrite_opcode >>
      asm_simp_tac outcome_envelope_ss [] >>
      rpt (PURE_TOP_CASE_TAC >> asm_simp_tac outcome_envelope_ss []) >>
      asm_simp_tac outcome_state_ss [external_outcome_suffix]) >>
  drule step_inst_base_nonexternal_outcome_suffix >> simp[]
QED

Theorem step_inst_base_success_outcome_suffix:
  step_inst_base inst s = r /\
  ((?t. r = OK t) \/ (?t. r = Halt t) \/ (?xs t. r = IntRet xs t)) ==>
  step_inst_base inst (s with vs_outcomes := s.vs_outcomes ++ tail) =
  exec_result_map (\t. t with vs_outcomes := t.vs_outcomes ++ tail) r
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
   s.vs_outcomes <> []` by
    (strip_tac >> strip_tac >> fs[MEM] >> gvs[] >>
     qpat_x_assum `step_inst_base inst s = _` mp_tac >>
     qpat_assum `inst.inst_opcode = _` rewrite_opcode >>
     simp[AllCaseEqs()] >> rpt strip_tac >>
     gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def, AllCaseEqs()]) >>
  qpat_x_assum `step_inst_base inst s = _` (SUBST1_TAC o SYM) >>
  irule step_inst_base_outcome_suffix_available >> simp[]
QED

Theorem step_inst_noninvoke_success_outcome_suffix:
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = r /\
  ((?t. r = OK t) \/ (?t. r = Halt t) \/ (?xs t. r = IntRet xs t)) ==>
  step_inst fuel C inst (s with vs_outcomes := s.vs_outcomes ++ tail) =
  exec_result_map (\t. t with vs_outcomes := t.vs_outcomes ++ tail) r
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  `step_inst_base inst s = r` by metis_tac[step_inst_non_invoke] >>
  simp[step_inst_non_invoke] >> irule step_inst_base_success_outcome_suffix >> simp[] >>
  metis_tac[]
QED

Theorem step_inst_noninvoke_outcome_prefix:
  inst.inst_opcode <> INVOKE /\ s.vs_outcomes = os ++ tail /\
  (MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
   os <> []) ==>
  step_inst fuel C inst s =
  exec_result_map (\t. t with vs_outcomes := t.vs_outcomes ++ tail)
    (step_inst fuel C inst (s with vs_outcomes := os))
Proof
  strip_tac >> simp[step_inst_non_invoke] >>
  `s with vs_outcomes := os ++ tail = s` by
    simp[venom_state_component_equality] >>
  mp_tac (Q.INST [`s` |-> `s with vs_outcomes := os`]
    step_inst_base_outcome_suffix_available) >> simp[]
QED

Theorem external_ok_records_request:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  step_inst fuel C inst s = OK t ==>
  LENGTH t.vs_requests = SUC (LENGTH s.vs_requests)
Proof
  simp[MEM] >> strip_tac >> gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  qpat_assum `inst.inst_opcode = _` rewrite_opcode >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
      consume_call_outcome_eq, consume_create_outcome_eq, update_var_def,
      record_request_def, AllCaseEqs()]
QED

Theorem external_ok_empty_oracle_abort:
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  step_inst fuel C inst s = OK t ==>
  step_inst_base inst (s with vs_outcomes := []) =
    Abort ExHalt_abort (halt_state (set_returndata [] (s with vs_outcomes := [])))
Proof
  simp[MEM] >> strip_tac >> gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  qpat_assum `inst.inst_opcode = _` rewrite_opcode >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def, AllCaseEqs()]
QED

Theorem setup_callee_outcome_update:
  setup_callee fn args (s with vs_outcomes := os) =
    OPTION_MAP (\t. t with vs_outcomes := os) (setup_callee fn args s)
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[]
QED

Theorem bind_outputs_outcome_update:
  bind_outputs outs vals (s with vs_outcomes := os) =
    OPTION_MAP (\t. t with vs_outcomes := os) (bind_outputs outs vals s)
Proof
  `!v w s. update_var v w (s with vs_outcomes := os) =
    update_var v w s with vs_outcomes := os` by simp[update_var_def] >>
  `!xs s.
    FOLDL (\v (out,w). update_var out w v) (s with vs_outcomes := os) xs =
    FOLDL (\v (out,w). update_var out w v) s xs with vs_outcomes := os` by
    (Induct >> simp[] >> Cases_on `h` >> simp[]) >>
  simp[bind_outputs_def] >> IF_CASES_TAC >> simp[]
QED
