Theory algebraicOptMainResidualProofs
Ancestors
  algebraicOptMainCallProofs algebraicOptMainControlProofs
  algebraicOptRelationProofs algebraicOptDefs algebraicOptShapeProofs dretShapeDefs
  venomCallOracleDefs venomExecSemantics venomState venomInst venomWf stateEquiv stateEquivProps stateFrame list

Theorem ao_main_equal_write:
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  ao_main_observations fn V (update_var x w s) (update_var x w r) /\
  (update_var x w s with
    <|vs_vars := (update_var x w r).vs_vars;
      vs_inst_idx := r.vs_inst_idx|>) = update_var x w r
Proof
  strip_tac >> conj_tac
  >- (irule ao_main_observations_update >> simp[]) >>
  gvs[update_var_def, venom_state_component_equality]
QED

Theorem ao_main_parameter_base:
  inst_wf inst /\
  MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM; GETFMP; INITIAL_FMP] /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  ao_resolve_iszero_inst targets inst = inst /\
  ((?e. step_inst_base inst s = Error e) \/
   ?t u. step_inst_base inst s = OK t /\ step_inst_base inst r = OK u /\
     ao_main_observations fn V t u /\
     (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
     t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx)
Proof
  strip_tac >>
  `s.vs_fmp = r.vs_fmp /\ s.vs_initial_fmp = r.vs_initial_fmp /\
   s.vs_params = r.vs_params /\ s.vs_return_pc_token = r.vs_return_pc_token` by
    gvs[venom_state_component_equality] >>
  gvs[MEM] >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  `ao_resolve_iszero_inst targets inst = inst` by
    simp[ao_resolve_iszero_inst_def, ao_resolve_iszero_op_def,
         instruction_component_equality] >>
  simp[step_inst_base_opcode_eqs] >>
  rpt IF_CASES_TAC >> simp[] >>
  irule ao_main_equal_write >> simp[]
QED

Theorem ao_main_read0_transfer:
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  other.inst_outputs = inst.inst_outputs /\ f s = f r /\
  exec_read0 f inst s = OK t ==>
  ?u. exec_read0 f other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  simp[exec_read0_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[] >> irule ao_main_equal_write >> simp[]
QED

Theorem ao_main_read1_transfer:
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  other.inst_outputs = inst.inst_outputs /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  (!w. f w s = f w r) /\ exec_read1 f inst s = OK t ==>
  ?u. exec_read1 f other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  irule ao_main_equal_write >> simp[]
QED

Theorem ao_main_pure2_transfer:
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  other.inst_outputs = inst.inst_outputs /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  exec_pure2 f inst s = OK t ==>
  ?u. exec_pure2 f other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `eval_operand (resolve op1) r = SOME v1 /\
   eval_operand (resolve op2) r = SOME v2` by metis_tac[] >>
  simp[] >> irule ao_main_equal_write >> simp[]
QED

Theorem ao_main_pure3_transfer:
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  other.inst_outputs = inst.inst_outputs /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  exec_pure3 f inst s = OK t ==>
  ?u. exec_pure3 f other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  simp[exec_pure3_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `eval_operand (resolve op1) r = SOME v1 /\
   eval_operand (resolve op2) r = SOME v2 /\
   eval_operand (resolve op3) r = SOME v3` by metis_tac[] >>
  simp[] >> irule ao_main_equal_write >> simp[]
QED

Theorem ao_main_observations_vars:
  ao_main_observations fn V s r /\
  t.vs_vars = s.vs_vars /\ u.vs_vars = r.vs_vars ==>
  ao_main_observations fn V t u
Proof
  simp[ao_main_observations_def, lookup_var_def]
QED

Theorem ao_main_gas_transfer:
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  other.inst_outputs = inst.inst_outputs /\
  exec_gas inst s = OK t ==>
  ?u. exec_gas other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  simp[exec_gas_def, AllCaseEqs()] >> rpt strip_tac >>
  `r.vs_gas_readings = s.vs_gas_readings` by gvs[venom_state_component_equality] >>
  gvs[] >> simp[]
  >- (irule ao_main_equal_write >> simp[]) >>
  conj_tac
  >- (irule ao_main_observations_update >> simp[] >>
      irule ao_main_observations_vars >> qexistsl_tac [`r`, `s`] >> simp[]) >>
  gvs[update_var_def, venom_state_component_equality]
QED

Theorem ao_main_read0_base:
  MEM inst.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; GAS; ORIGIN; GASPRICE; CHAINID;
     COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
     BLOBBASEFEE; SELFBALANCE; CALLDATASIZE; RETURNDATASIZE; MEMTOP; CODESIZE] /\
  other.inst_opcode = inst.inst_opcode /\
  other.inst_outputs = inst.inst_outputs /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >> Cases_on `inst.inst_opcode = GAS`
  >- (gvs[step_inst_base_opcode_eqs] >>
      irule ao_main_gas_transfer >> simp[] >> qexists_tac `inst` >> simp[]) >>
  gvs[MEM] >> gvs[step_inst_base_opcode_eqs] >>
  irule ao_main_read0_transfer >> simp[] >>
  gvs[venom_state_component_equality] >> qexists_tac `inst` >> simp[]
QED

Theorem ao_main_read1_base:
  MEM inst.inst_opcode
    [MLOAD; SLOAD; TLOAD; BLOCKHASH; BLOBHASH; CALLDATALOAD;
     EXTCODEHASH; ILOAD; DLOAD] /\
  other.inst_opcode = inst.inst_opcode /\
  other.inst_outputs = inst.inst_outputs /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >> gvs[MEM] >> gvs[step_inst_base_opcode_eqs] >>
  (irule ao_main_read1_transfer >> simp[] >>
   conj_tac
   >- gvs[venom_state_component_equality, mload_def, sload_def, tload_def,
          contract_storage_def, contract_transient_def] >>
   qexistsl_tac [`inst`, `resolve`] >> simp[])
QED

Theorem ao_main_store_base:
  MEM inst.inst_opcode [MSTORE; MSTORE8; SSTORE; TSTORE; ISTORE] /\
  other.inst_opcode = inst.inst_opcode /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >>
  `r.vs_call_ctx = s.vs_call_ctx` by gvs[venom_state_component_equality] >>
  gvs[MEM] >> gvs[step_inst_base_opcode_eqs] >>
  gvs[exec_write2_def, eval_operands_def, AllCaseEqs()] >>
  rename [`inst.inst_operands = [op1;op2]`,
          `eval_operand op1 s = SOME v1`, `eval_operand op2 s = SOME v2`] >>
  `eval_operand (resolve op1) r = SOME v1 /\
   eval_operand (resolve op2) r = SOME v2` by metis_tac[] >>
  simp[eval_operands_def] >>
  (conj_tac
   >- (irule ao_main_observations_vars >>
       qexistsl_tac [`r`, `s`] >>
       simp[istore_def, mstore_def, mstore8_def, sstore_def, tstore_def]) >>
   gvs[istore_def, mstore_def, mstore8_def, sstore_def, tstore_def,
       venom_state_component_equality])
QED

Theorem ao_main_copy3_base:
  MEM inst.inst_opcode [MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES] /\
  other.inst_opcode = inst.inst_opcode /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >> gvs[MEM] >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rename [`inst.inst_operands = [a;b;c]`,
          `eval_operand a s = SOME x`, `eval_operand b s = SOME y`,
          `eval_operand c s = SOME z`] >>
  `eval_operand (resolve a) r = SOME x /\
   eval_operand (resolve b) r = SOME y /\
   eval_operand (resolve c) r = SOME z` by metis_tac[] >>
  simp[] >>
  (conj_tac
   >- (irule ao_main_observations_vars >>
       qexistsl_tac [`r`, `s`] >>
       simp[mcopy_def, write_memory_with_expansion_def]) >>
   gvs[mcopy_def, write_memory_with_expansion_def,
       venom_state_component_equality])
QED

Theorem ao_main_pure_residual_base:
  MEM inst.inst_opcode [BYTE; OFFSET; ADDMOD; MULMOD] /\
  other.inst_opcode = inst.inst_opcode /\
  other.inst_outputs = inst.inst_outputs /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >> gvs[MEM] >> gvs[step_inst_base_opcode_eqs]
  >- (irule ao_main_pure2_transfer >> simp[] >>
      qexistsl_tac [`inst`, `resolve`] >> simp[])
  >- (irule ao_main_pure2_transfer >> simp[] >>
      qexistsl_tac [`inst`, `resolve`] >> simp[])
  >- (irule ao_main_pure3_transfer >> simp[] >>
      qexistsl_tac [`inst`, `resolve`] >> simp[]) >>
  irule ao_main_pure3_transfer >> simp[] >>
  qexistsl_tac [`inst`, `resolve`] >> simp[]
QED

Theorem ao_main_unary_residual_base:
  MEM inst.inst_opcode [NOT; ASSIGN] /\
  other.inst_opcode = inst.inst_opcode /\
  other.inst_outputs = inst.inst_outputs /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >> gvs[MEM] >> gvs[step_inst_base_opcode_eqs] >>
  gvs[exec_pure1_def, AllCaseEqs()] >> simp[] >>
  irule ao_main_equal_write >> simp[]
QED

Theorem ao_main_sha3_base:
  inst.inst_opcode = SHA3 /\ other.inst_opcode = SHA3 /\
  other.inst_outputs = inst.inst_outputs /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rename [`inst.inst_operands = [a;b]`,
          `eval_operand a s = SOME x`, `eval_operand b s = SOME y`] >>
  `eval_operand (resolve a) r = SOME x /\
   eval_operand (resolve b) r = SOME y` by metis_tac[] >>
  `s.vs_memory = r.vs_memory` by gvs[venom_state_component_equality] >>
  simp[] >> irule ao_main_equal_write >> simp[]
QED

Theorem ao_main_extcodecopy_base:
  inst.inst_opcode = EXTCODECOPY /\ other.inst_opcode = EXTCODECOPY /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rename [`inst.inst_operands = [a;b;c;d]`,
          `eval_operand a s = SOME w`, `eval_operand b s = SOME x`,
          `eval_operand c s = SOME y`, `eval_operand d s = SOME z`] >>
  `eval_operand (resolve a) r = SOME w /\
   eval_operand (resolve b) r = SOME x /\
   eval_operand (resolve c) r = SOME y /\
   eval_operand (resolve d) r = SOME z` by metis_tac[] >>
  simp[] >> conj_tac
  >- (irule ao_main_observations_vars >> qexistsl_tac [`r`, `s`] >>
      simp[write_memory_with_expansion_def]) >>
  gvs[write_memory_with_expansion_def, venom_state_component_equality]
QED

Theorem ao_main_ret_base:
  MEM inst.inst_opcode [RET; RETFMP] /\
  other.inst_opcode = inst.inst_opcode /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  (?e. step_inst_base inst s = Error e) \/
  lift_result R (execution_equiv UNIV) (execution_equiv UNIV)
    (step_inst_base inst s) (step_inst_base other r)
Proof
  strip_tac >> Cases_on `eval_operands inst.inst_operands s`
  >- (gvs[MEM] >> simp[step_inst_base_opcode_eqs]) >>
  `eval_operands other.inst_operands r = SOME x` by
    (gvs[] >> irule ao_main_eval_operands_map >> qexists_tac `s` >> simp[]) >>
  `s.vs_fmp = r.vs_fmp /\ execution_equiv UNIV s r` by
    gvs[execution_equiv_def, execution_frame_def, venom_state_component_equality] >>
  gvs[MEM] >> simp[step_inst_base_opcode_eqs] >>
  Cases_on `x` >> simp[lift_result_def]
QED

Theorem ao_main_stop_base:
  MEM inst.inst_opcode [STOP; SINK] /\ other.inst_opcode = inst.inst_opcode /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  lift_result R (execution_equiv UNIV) (execution_equiv UNIV)
    (step_inst_base inst s) (step_inst_base other r)
Proof
  strip_tac >> gvs[MEM] >>
  simp[step_inst_base_opcode_eqs, lift_result_def, execution_equiv_def,
       execution_frame_def, halt_state_def, venom_state_component_equality] >>
  gvs[venom_state_component_equality]
QED

Theorem ao_main_return_revert_base:
  inst_wf inst /\ MEM inst.inst_opcode [RETURN; REVERT] /\
  other.inst_opcode = inst.inst_opcode /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  (?e. step_inst_base inst s = Error e) \/
  lift_result R (execution_equiv UNIV) (execution_equiv UNIV)
    (step_inst_base inst s) (step_inst_base other r)
Proof
  strip_tac >> gvs[MEM] >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  rename1 `inst.inst_operands = [a;b]` >>
  (Cases_on `eval_operand a s`
   >- simp[step_inst_base_opcode_eqs] >>
   Cases_on `eval_operand b s`
   >- simp[step_inst_base_opcode_eqs] >>
   `eval_operand (resolve a) r = SOME x /\
    eval_operand (resolve b) r = SOME x'` by metis_tac[] >>
   simp[step_inst_base_opcode_eqs, lift_result_def] >>
   gvs[execution_equiv_def, execution_frame_def, halt_state_def,
       revert_state_def, set_returndata_def, venom_state_component_equality])
QED

Theorem ao_main_setfmp_base:
  inst.inst_opcode = SETFMP /\ other.inst_opcode = SETFMP /\
  other.inst_outputs = inst.inst_outputs /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >> simp[] >>
  conj_tac
  >- (irule ao_main_observations_vars >> qexistsl_tac [`r`, `s`] >> simp[]) >>
  gvs[venom_state_component_equality]
QED

Theorem ao_main_dalloca_base:
  inst.inst_opcode = DALLOCA /\ other.inst_opcode = DALLOCA /\
  other.inst_outputs = inst.inst_outputs /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  `s.vs_fmp = r.vs_fmp` by gvs[venom_state_component_equality] >>
  simp[] >> conj_tac
  >- (irule ao_main_observations_update >> simp[] >>
      irule ao_main_observations_vars >> qexistsl_tac [`r`, `s`] >> simp[]) >>
  gvs[update_var_def, venom_state_component_equality]
QED

Theorem ao_main_bump_base:
  inst.inst_opcode = BUMP /\ other.inst_opcode = BUMP /\
  other.inst_outputs = inst.inst_outputs /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rename [`inst.inst_operands = [a;b]`,
          `eval_operand a s = SOME x`, `eval_operand b s = SOME y`] >>
  `eval_operand (resolve a) r = SOME x /\
   eval_operand (resolve b) r = SOME y` by metis_tac[] >>
  simp[] >> conj_tac
  >- (irule ao_main_observations_update >> simp[] >>
      irule ao_main_observations_update >> simp[]) >>
  gvs[update_var_def, venom_state_component_equality]
QED

Theorem ao_main_alloca_base:
  inst_wf inst /\ inst.inst_opcode = ALLOCA /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  ao_resolve_iszero_inst targets inst = inst /\
  ?t u. step_inst_base inst s = OK t /\ step_inst_base inst r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  `ao_resolve_iszero_inst targets inst = inst` by
    simp[ao_resolve_iszero_inst_def, ao_resolve_iszero_op_def,
         instruction_component_equality] >>
  `s.vs_allocas = r.vs_allocas /\ s.vs_alloca_next = r.vs_alloca_next` by
    gvs[venom_state_component_equality] >>
  simp[step_inst_base_opcode_eqs, exec_alloca_def] >>
  Cases_on `FLOOKUP r.vs_allocas inst.inst_id` >> simp[]
  >- (conj_tac
      >- (irule ao_main_observations_update >> simp[] >>
          irule ao_main_observations_vars >> qexistsl_tac [`r`, `s`] >> simp[]) >>
      gvs[update_var_def, venom_state_component_equality]) >>
  PairCases_on `x` >> simp[] >> irule ao_main_equal_write >> simp[]
QED

Theorem ao_main_nop_invalid_base:
  MEM inst.inst_opcode [NOP; INVALID] /\
  other.inst_opcode = inst.inst_opcode /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  lift_result
    (\t u. ao_main_observations fn V t u /\
      (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
      t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx)
    (execution_equiv UNIV) (execution_equiv UNIV)
    (step_inst_base inst s) (step_inst_base other r)
Proof
  strip_tac >> gvs[MEM] >> simp[step_inst_base_opcode_eqs, lift_result_def] >>
  gvs[execution_equiv_def, execution_frame_def, halt_state_def,
      set_returndata_def, venom_state_component_equality]
QED

Theorem ao_main_selfdestruct_base:
  inst_wf inst /\ inst.inst_opcode = SELFDESTRUCT /\
  other.inst_opcode = SELFDESTRUCT /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  (?e. step_inst_base inst s = Error e) \/
  lift_result R (execution_equiv UNIV) (execution_equiv UNIV)
    (step_inst_base inst s) (step_inst_base other r)
Proof
  strip_tac >>
  `r.vs_call_ctx = s.vs_call_ctx` by gvs[venom_state_component_equality] >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  rename1 `inst.inst_operands = [a]` >>
  Cases_on `eval_operand a s`
  >- simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  `eval_operand (resolve a) r = SOME x` by metis_tac[] >>
  simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  disj2_tac >> IF_CASES_TAC >> simp[lift_result_def] >>
  gvs[execution_equiv_def, execution_frame_def, halt_state_def,
      set_returndata_def, venom_state_component_equality]
QED

Theorem ao_main_returndatacopy_base:
  inst_wf inst /\ inst.inst_opcode = RETURNDATACOPY /\
  other.inst_opcode = RETURNDATACOPY /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  (?e. step_inst_base inst s = Error e) \/
  lift_result
    (\t u. ao_main_observations fn V t u /\
      (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
      t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx)
    (execution_equiv UNIV) (execution_equiv UNIV)
    (step_inst_base inst s) (step_inst_base other r)
Proof
  strip_tac >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  rename1 `inst.inst_operands = [a;b;c]` >>
  Cases_on `eval_operand a s`
  >- simp[step_inst_base_opcode_eqs] >>
  Cases_on `eval_operand b s`
  >- simp[step_inst_base_opcode_eqs] >>
  Cases_on `eval_operand c s`
  >- simp[step_inst_base_opcode_eqs] >>
  `eval_operand (resolve a) r = SOME x /\
   eval_operand (resolve b) r = SOME x' /\
   eval_operand (resolve c) r = SOME x''` by metis_tac[] >>
  `s.vs_returndata = r.vs_returndata` by
    gvs[venom_state_component_equality] >>
  simp[step_inst_base_opcode_eqs] >> IF_CASES_TAC >> simp[lift_result_def]
  >- gvs[execution_equiv_def, execution_frame_def, halt_state_def,
         set_returndata_def, venom_state_component_equality] >>
  conj_tac
  >- (irule ao_main_observations_vars >> qexistsl_tac [`r`, `s`] >>
      simp[write_memory_with_expansion_def]) >>
  gvs[write_memory_with_expansion_def, venom_state_component_equality]
QED

Theorem ao_main_jmp_base:
  inst.inst_opcode = JMP /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base (ao_resolve_iszero_inst targets inst) r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = 0 /\ u.vs_inst_idx = 0
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[ao_resolve_iszero_inst_def, ao_resolve_iszero_op_def,
       step_inst_base_opcode_eqs] >> conj_tac
  >- simp[ao_main_control_observations] >>
  gvs[jump_to_def, venom_state_component_equality]
QED

Theorem ao_extract_labels_resolved:
  !ops labels. extract_labels ops = SOME labels ==>
    extract_labels (MAP (ao_resolve_iszero_op targets opc) ops) = SOME labels
Proof
  Induct >> simp[extract_labels_def] >> Cases >>
  simp[extract_labels_def, AllCaseEqs(), ao_resolve_iszero_op_def] >>
  metis_tac[]
QED

Theorem ao_main_djmp_base:
  inst.inst_opcode = DJMP /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (ao_resolve_iszero_op targets DJMP a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base (ao_resolve_iszero_inst targets inst) r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = 0 /\ u.vs_inst_idx = 0
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  `eval_operand (ao_resolve_iszero_op targets DJMP selector_op) r = SOME idx`
    by metis_tac[] >>
  drule ao_extract_labels_resolved >>
  disch_then (qspecl_then [`targets`, `DJMP`] assume_tac) >>
  simp[ao_resolve_iszero_inst_def, step_inst_base_opcode_eqs] >>
  conj_tac
  >- simp[ao_main_control_observations] >>
  gvs[jump_to_def, venom_state_component_equality]
QED

Theorem eval_operands_is_some_every[local]:
  !xs s. IS_SOME (eval_operands xs s) <=> EVERY (\a. IS_SOME (eval_operand a s)) xs
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  first_x_assum (qspec_then `s` (SUBST1_TAC o SYM)) >>
  Cases_on `eval_operand h s` >> Cases_on `eval_operands xs s` >> simp[]
QED

Theorem ao_main_log_base:
  inst.inst_opcode = LOG /\ other.inst_opcode = LOG /\
  inst.inst_operands = Lit tc :: ops /\
  other.inst_operands = Lit tc :: MAP resolve ops /\
  (!a w. MEM a ops /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >>
  `r.vs_call_ctx = s.vs_call_ctx` by gvs[venom_state_component_equality] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  `IS_SOME (eval_operands (Lit tc :: ops) s)` by
    (simp[eval_operands_is_some_every, eval_operand_def] >>
     `EVERY (\a. IS_SOME (eval_operand a s)) (REVERSE ops)` suffices_by simp[] >>
     Cases_on `REVERSE ops` >- gvs[] >> Cases_on `t` >- gvs[] >>
     gvs[] >> simp[GSYM eval_operands_is_some_every]) >>
  gvs[] >>
  `0 < LENGTH (REVERSE ops) /\ 1 < LENGTH (REVERSE ops)` by simp[] >>
  `MEM (EL 0 (REVERSE ops)) ops /\ MEM (EL 1 (REVERSE ops)) ops` by
    metis_tac[MEM_EL, MEM_REVERSE] >>
  `MEM (HD (REVERSE ops)) ops` by
    (qpat_x_assum `MEM (EL 0 _) _` mp_tac >> simp[EL]) >>
  `eval_operand (resolve (HD (REVERSE ops))) r = SOME off /\
   eval_operand (resolve (EL 1 (REVERSE ops))) r = SOME sz` by simp[] >>
  `eval_operands (MAP resolve (DROP 2 (REVERSE ops))) r = SOME topics` by
    (irule ao_main_eval_operands_map >> qexists_tac `s` >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> simp[] >>
     drule rich_listTheory.MEM_DROP_IMP >> simp[]) >>
  `REVERSE ops <> []` by (Cases_on `ops` >> gvs[]) >>
  pure_rewrite_tac[GSYM MAP_REVERSE, GSYM MAP_DROP] >>
  simp[EL_MAP, rich_listTheory.MAP_HD] >> conj_tac
  >- (irule ao_main_observations_vars >> qexistsl_tac [`r`, `s`] >> simp[]) >>
  gvs[venom_state_component_equality]
QED

Theorem ao_main_exec_ext_call:
  other.inst_outputs = inst.inst_outputs /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  exec_ext_call inst s gas addr value ao az ro rz static = OK t ==>
  ?u. exec_ext_call other r gas addr value ao az ro rz static = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >>
  `venom_call_request s addr value ao az static =
   venom_call_request r addr value ao az static` by
    gvs[venom_call_request_def, read_memory_def, venom_state_component_equality] >>
  `s.vs_outcomes = r.vs_outcomes` by gvs[venom_state_component_equality] >>
  gvs[exec_ext_call_def, AllCaseEqs()] >> simp[] >> conj_tac
  >- (irule ao_main_observations_update >> simp[] >>
      irule ao_main_observations_vars >> qexistsl_tac [`r`, `s`] >> simp[]) >>
  gvs[update_var_def, write_memory_with_expansion_def, venom_state_component_equality]
QED

Theorem ao_main_call_base:
  MEM inst.inst_opcode [CALL; STATICCALL] /\
  other.inst_opcode = inst.inst_opcode /\
  other.inst_outputs = inst.inst_outputs /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >> `s.vs_call_ctx = r.vs_call_ctx` by
    gvs[venom_state_component_equality] >>
  Cases_on `r.vs_call_ctx.cc_static` >>
  gvs[MEM] >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  fs[RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[] >> irule ao_main_exec_ext_call >>
  simp[] >> metis_tac[]
QED

Theorem ao_main_exec_create:
  inst.inst_outputs = [out] /\ other.inst_outputs = [out] /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  lift_result
    (\t u. ao_main_observations fn V t u /\
      (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
      t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx)
    (execution_equiv UNIV) (execution_equiv UNIV)
    (exec_create inst s value offset sz salt)
    (exec_create other r value offset sz salt)
Proof
  strip_tac >>
  `venom_create_request s value offset sz salt =
   venom_create_request r value offset sz salt /\ s.vs_outcomes = r.vs_outcomes` by
    gvs[venom_create_request_def, read_memory_def, venom_state_component_equality] >>
  simp[exec_create_def] >> IF_CASES_TAC >> simp[lift_result_def]
  >- gvs[execution_equiv_def, execution_frame_def, halt_state_def,
         set_returndata_def, venom_state_component_equality] >>
  conj_tac
  >- (irule ao_main_observations_update >> simp[] >>
      irule ao_main_observations_vars >> qexistsl_tac [`r`, `s`] >> simp[]) >>
  gvs[update_var_def, venom_state_component_equality]
QED

Theorem ao_main_create_base:
  inst_wf inst /\ MEM inst.inst_opcode [CREATE; CREATE2] /\
  other.inst_opcode = inst.inst_opcode /\
  other.inst_outputs = inst.inst_outputs /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  (?e. step_inst_base inst s = Error e) \/
  lift_result
    (\t u. ao_main_observations fn V t u /\
      (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
      t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx)
    (execution_equiv UNIV) (execution_equiv UNIV)
    (step_inst_base inst s) (step_inst_base other r)
Proof
  strip_tac >>
  `r.vs_call_ctx = s.vs_call_ctx` by gvs[venom_state_component_equality] >>
  gvs[MEM] >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute]
  >- (rename1 `inst.inst_operands = [a;b;c]` >>
      Cases_on `eval_operand a s` >- simp[step_inst_base_opcode_eqs, eval_operands_def] >>
      Cases_on `eval_operand b s` >- simp[step_inst_base_opcode_eqs, eval_operands_def] >>
      Cases_on `eval_operand c s` >- simp[step_inst_base_opcode_eqs, eval_operands_def] >>
      fs[RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM] >>
      simp[step_inst_base_opcode_eqs, eval_operands_def] >> disj2_tac >>
      IF_CASES_TAC
      >- (simp[lift_result_def] >>
          gvs[execution_equiv_def, execution_frame_def, halt_state_def,
              set_returndata_def, venom_state_component_equality]) >>
      simp[] >> irule ao_main_exec_create >> simp[]) >>
  rename1 `inst.inst_operands = [a;b;c;d]` >>
  Cases_on `eval_operand a s` >- simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `eval_operand b s` >- simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `eval_operand c s` >- simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `eval_operand d s` >- simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  fs[RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[step_inst_base_opcode_eqs, eval_operands_def] >> disj2_tac >>
  IF_CASES_TAC
  >- (simp[lift_result_def] >>
      gvs[execution_equiv_def, execution_frame_def, halt_state_def,
          set_returndata_def, venom_state_component_equality]) >>
  simp[] >> irule ao_main_exec_create >> simp[]
QED

Theorem ao_main_exec_delegatecall:
  other.inst_outputs = inst.inst_outputs /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  exec_delegatecall inst s gas addr ao az ro rz = OK t ==>
  ?u. exec_delegatecall other r gas addr ao az ro rz = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >>
  `venom_call_request s addr 0w ao az F =
   venom_call_request r addr 0w ao az F` by
    gvs[venom_call_request_def, read_memory_def, venom_state_component_equality] >>
  `s.vs_outcomes = r.vs_outcomes` by gvs[venom_state_component_equality] >>
  gvs[exec_delegatecall_def, AllCaseEqs()] >> simp[] >> conj_tac
  >- (irule ao_main_observations_update >> simp[] >>
      irule ao_main_observations_vars >> qexistsl_tac [`r`, `s`] >> simp[]) >>
  gvs[update_var_def, write_memory_with_expansion_def, venom_state_component_equality]
QED

Theorem ao_main_delegatecall_base:
  inst.inst_opcode = DELEGATECALL /\ other.inst_opcode = DELEGATECALL /\
  other.inst_outputs = inst.inst_outputs /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base other r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  fs[RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[] >> irule ao_main_exec_delegatecall >> simp[] >> metis_tac[]
QED

Theorem ao_pack_dret_dynamic_vars_index:
  !pairs cursor s ptrs fc t vars idx.
    pack_dret_dynamic cursor pairs s = (ptrs,fc,t) ==>
    pack_dret_dynamic cursor pairs
      (s with <|vs_vars := vars; vs_inst_idx := idx|>) =
    (ptrs,fc,t with <|vs_vars := vars; vs_inst_idx := idx|>)
Proof
  Induct >> simp[pack_dret_dynamic_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[Once pack_dret_dynamic_def] >> pairarg_tac >> gvs[] >>
  strip_tac >> gvs[] >>
  `mcopy (w2n cursor) (w2n h0) (w2n h1)
     (s with <|vs_vars := vars; vs_inst_idx := idx|>) =
   mcopy (w2n cursor) (w2n h0) (w2n h1) s with
     <|vs_vars := vars; vs_inst_idx := idx|>` by
    simp[mcopy_def, write_memory_with_expansion_def,
         venom_state_component_equality] >>
  first_x_assum drule >> disch_then assume_tac >>
  simp[Once pack_dret_dynamic_def]
QED

Theorem ao_main_dret_base:
  inst.inst_opcode = DRET /\ other.inst_opcode = DRET /\
  other.inst_outputs = inst.inst_outputs /\
  parse_dret_shape other = parse_dret_shape inst /\
  other.inst_operands = MAP resolve inst.inst_operands /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (resolve a) r = SOME w) /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = IntRet vals t ==>
  ?u. step_inst_base other r = IntRet vals u /\ execution_equiv UNIV t u
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  `eval_operands other.inst_operands r = SOME vals'` by
    (gvs[] >> irule ao_main_eval_operands_map >> qexists_tac `s` >> simp[]) >>
  `s.vs_call_entry_fmp = r.vs_call_entry_fmp` by
    gvs[venom_state_component_equality] >>
  pairarg_tac >> gvs[] >>
  drule ao_pack_dret_dynamic_vars_index >>
  disch_then (qspecl_then [`r.vs_vars`, `r.vs_inst_idx`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  gvs[execution_equiv_def, execution_frame_def, venom_state_component_equality]
QED

Theorem ao_resolve_dret_shape:
  parse_dret_shape inst = SOME shape ==>
  parse_dret_shape (ao_resolve_iszero_inst targets inst) = SOME shape
Proof
  Cases_on `inst.inst_operands` >>
  simp[parse_dret_shape_def] >>
  Cases_on `h` >> simp[parse_dret_shape_def] >>
  simp[ao_resolve_iszero_inst_def, ao_resolve_iszero_op_def,
       parse_dret_shape_def]
QED


Theorem ao_main_dret_resolved:
  inst_wf inst /\ inst.inst_opcode = DRET /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (ao_resolve_iszero_op targets DRET a) r = SOME w) /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  (?e. step_inst_base inst s = Error e) \/
  lift_result R (execution_equiv UNIV) (execution_equiv UNIV)
    (step_inst_base inst s)
    (step_inst_base (ao_resolve_iszero_inst targets inst) r)
Proof
  strip_tac >>
  `inst.inst_outputs = [] /\ IS_SOME (parse_dret_shape inst)` by gvs[inst_wf_def] >>
  Cases_on `parse_dret_shape inst` >> gvs[] >> PairCases_on `x` >>
  drule ao_resolve_dret_shape >> disch_then (qspec_then `targets` assume_tac) >>
  Cases_on `eval_operands inst.inst_operands s`
  >- simp[step_inst_base_opcode_eqs] >>
  Cases_on `pair_dret_words (TAKE (2 * x1) (DROP (x0 + 1) x))`
  >- simp[step_inst_base_opcode_eqs] >>
  `?vals t. step_inst_base inst s = IntRet vals t` by
    (simp[step_inst_base_opcode_eqs] >> pairarg_tac >> simp[]) >>
  `?u. step_inst_base (ao_resolve_iszero_inst targets inst) r = IntRet vals u /\
       execution_equiv UNIV t u` by
    (irule ao_main_dret_base >> simp[ao_resolve_iszero_inst_def] >>
     qexistsl_tac [`inst`, `ao_resolve_iszero_op targets DRET`, `s`] >> simp[]) >>
  simp[lift_result_def]
QED

Theorem ao_main_read_resolved_OK:
  MEM inst.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; GAS; ORIGIN; GASPRICE; CHAINID;
     COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
     BLOBBASEFEE; SELFBALANCE; CALLDATASIZE; RETURNDATASIZE; MEMTOP; CODESIZE;
     MLOAD; SLOAD; TLOAD; BLOCKHASH; BLOBHASH; CALLDATALOAD;
     EXTCODEHASH; ILOAD; DLOAD] /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (ao_resolve_iszero_op targets inst.inst_opcode a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base (ao_resolve_iszero_inst targets inst) r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >>
  Cases_on `MEM inst.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; GAS; ORIGIN; GASPRICE; CHAINID;
     COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
     BLOBBASEFEE; SELFBALANCE; CALLDATASIZE; RETURNDATASIZE; MEMTOP; CODESIZE]`
  >- (irule ao_main_read0_base >> simp[ao_resolve_iszero_inst_def] >>
      qexists_tac `inst` >> fs[MEM]) >>
  `MEM inst.inst_opcode [MLOAD; SLOAD; TLOAD; BLOCKHASH; BLOBHASH;
    CALLDATALOAD; EXTCODEHASH; ILOAD; DLOAD]` by fs[MEM] >>
  irule ao_main_read1_base >> simp[ao_resolve_iszero_inst_def] >>
  qexistsl_tac [`inst`, `ao_resolve_iszero_op targets inst.inst_opcode`] >> fs[MEM]
QED
