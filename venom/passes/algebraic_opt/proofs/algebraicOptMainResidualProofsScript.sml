Theory algebraicOptMainResidualProofs
Ancestors
  algebraicOptMainCallProofs algebraicOptMainControlProofs
  algebraicOptRelationProofs algebraicOptDefs algebraicOptShapeProofs
  venomExecSemantics venomState venomInst venomWf stateEquiv stateEquivProps list

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
  strip_tac >> gvs[MEM] >> gvs[step_inst_base_opcode_eqs] >>
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

Theorem ao_main_observations_vars:
  ao_main_observations fn V s r /\
  t.vs_vars = s.vs_vars /\ u.vs_vars = r.vs_vars ==>
  ao_main_observations fn V t u
Proof
  simp[ao_main_observations_def, lookup_var_def]
QED

Theorem ao_main_store_base:
  MEM inst.inst_opcode [MSTORE; MSTORE8; SSTORE; TSTORE] /\
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
  strip_tac >> gvs[MEM] >> gvs[step_inst_base_opcode_eqs] >>
  gvs[exec_write2_def, AllCaseEqs()] >>
  rename1 `eval_operand op1 s = SOME v1` >>
  rename1 `eval_operand op2 s = SOME v2` >>
  `eval_operand (resolve op1) r = SOME v1 /\
   eval_operand (resolve op2) r = SOME v2` by metis_tac[] >>
  simp[] >>
  (conj_tac
   >- (irule ao_main_observations_vars >>
       qexistsl_tac [`r`, `s`] >>
       simp[mstore_def, mstore8_def, sstore_def, tstore_def]) >>
   gvs[mstore_def, mstore8_def, sstore_def, tstore_def,
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
