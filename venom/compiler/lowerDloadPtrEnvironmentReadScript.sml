Theory lowerDloadPtrEnvironmentRead
Ancestors lowerDloadPtrScalar lowerDloadPtrOrdinary lowerDloadPtrPhi
  lowerDloadPtrRel lowerDloadPtrAggregate lowerDloadPtrBlockEntry lowerDloadPtrCall
  ptrDiscipline venomExecSemantics venomState venomInst vfmState vfmTypes
  unitShapeDefs codegenRel memLocDefs pointerConfinedDefs finite_map list pred_set

val family = ``[CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
  COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
  CALLDATASIZE; RETURNDATASIZE; BLOCKHASH; BLOBHASH; CALLDATALOAD;
  BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH; CODESIZE; INITIAL_FMP]``;

Theorem dload_shared_store_lookup_account:
  dload_shared_store tn un s t ==>
  !a. (lookup_account a s.vs_accounts with
         storage := (lookup_account a t.vs_accounts).storage) =
       lookup_account a t.vs_accounts
Proof
  simp[dload_shared_store_def, lookup_account_def] >> metis_tac[]
QED

Theorem environment_read_operand_clean[local]:
  MEM i.inst_opcode ^family /\ MEM i (fn_insts f) /\ fn_ptr_ok P f /\
  FDOM G SUBSET fn_pv P f /\ taint_ok f tn i s /\ MEM op i.inst_operands ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  gvs[MEM, ptr_use_ok_def, is_pointer_preserving_op_def,
    mem_read_ops_def, mem_write_ops_def, taint_ok_def] >>
  Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem environment_read_step_transport[local]:
  MEM i.inst_opcode ^family /\ dload_equal_environment s t /\
  dload_shared_store tn un s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst fuel Ct i t = OK t' ==>
  ?out z. i.inst_outputs = [out] /\ t' = update_var out z t /\
    step_inst fuel Cs i s = OK (update_var out z s)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
   s.vs_block_ctx = t.vs_block_ctx /\ s.vs_returndata = t.vs_returndata /\
   s.vs_initial_fmp = t.vs_initial_fmp` by
    (qpat_x_assum `dload_equal_environment _ _` mp_tac >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `s.vs_code = t.vs_code` by metis_tac[dload_equal_environment_code] >>
  `!a. (lookup_account a s.vs_accounts).balance =
          (lookup_account a t.vs_accounts).balance /\
        (lookup_account a s.vs_accounts).nonce =
          (lookup_account a t.vs_accounts).nonce /\
        (lookup_account a s.vs_accounts).code =
          (lookup_account a t.vs_accounts).code` by
    (drule dload_shared_store_lookup_account >> strip_tac >> gen_tac >>
     first_x_assum (qspec_then `a` mp_tac) >>
     simp[account_state_component_equality]) >>
  gvs[MEM] >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_read0_def, exec_read1_def, AllCaseEqs()] >>
  strip_tac >> gvs[MEM, account_empty_def] >> metis_tac[]
QED

Theorem environment_read_ghost_updates[local]:
  MEM i.inst_opcode ^family /\ i.inst_outputs = [out] ==>
  step_prov PG G i (update_var out z s) = set_prov G [out] NONE /\
  step_taint i s (update_var out z s) tn =
    tn with t_var := set_var_taint tn.t_var [out] {}
Proof
  strip_tac >>
  `~MEM i.inst_opcode [MLOAD; ILOAD; SLOAD; TLOAD; ASSIGN; SHL; SHR; SAR] /\
   ~MEM i.inst_opcode [MSTORE; ISTORE; MCOPY]` by gvs[MEM] >>
  `out_taint tn i s = {} /\ written_taint tn i s = {}` by
    metis_tac[out_taint_opcode_exclusion, written_taint_opcode_exclusion] >>
  gvs[MEM] >> simp[step_prov_def, out_prov_def, step_taint_def] >>
  simp[mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, update_var_def] >>
  simp[new_site_bytes_def, step_writes_def, range_bytes_def,
    source_memory_write_ranges_def, FLOOKUP_DEF,
    taint_component_equality, EXTENSION] >> simp[SF CONJ_ss]
QED

Theorem dload_boundary_core_environment_read:
  MEM i.inst_opcode ^family /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t' cs ds /\
    s' = s with vs_vars := s'.vs_vars /\
    t' = t with vs_vars := t'.vs_vars
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `dload_vars_match fs V G H tn un s t` by
    metis_tac[dload_boundary_vars] >>
  `dload_equal_environment s t` by metis_tac[dload_boundary_environment] >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     `op_prov G op = NONE /\ op_taint tn op = {}` by
       (drule_all environment_read_operand_clean >> simp[]) >>
     `!v. op = Var v ==> v IN V` by metis_tac[] >>
     `eval_operand op s = NONE <=> eval_operand op t = NONE` by
       (drule eval_operand_definedness >>
        disch_then (qspec_then `op` mp_tac) >>
        (impl_tac >- metis_tac[]) >> simp[]) >>
     drule_all scalar_operand_equal >> simp[]) >>
  `dload_shared_store tn un s t` by metis_tac[dload_boundary_shared_store] >>
  drule_all environment_read_step_transport >>
  disch_then (qspec_then `Cs` strip_assume_tac) >> gnvs[] >>
  conj_tac >- (rpt strip_tac >>
    irule update_var_definedness >> qexists `U` >> simp[]) >>
  `step_prov PG G i (update_var out z s) = set_prov G [out] NONE /\
   step_taint i s (update_var out z s) tn =
     tn with t_var := set_var_taint tn.t_var [out] {}` by
    (irule environment_read_ghost_updates >> simp[]) >>
  `step_prov PH H i (update_var out z t) = set_prov H [out] NONE /\
   step_taint i t (update_var out z t) un =
     un with t_var := set_var_taint un.t_var [out] {}` by
    (irule environment_read_ghost_updates >> simp[]) >>
  simp[update_var_def] >>
  `dload_vars_match fs V (set_prov G [out] NONE) (set_prov H [out] NONE)
    (tn with t_var := set_var_taint tn.t_var [out] {})
    (un with t_var := set_var_taint un.t_var [out] {})
    (s with <|vs_vars := (update_var out z s).vs_vars; vs_inst_idx := s.vs_inst_idx|>)
    (t with <|vs_vars := (update_var out z t).vs_vars; vs_inst_idx := t.vs_inst_idx|>)` by
    (simp[update_var_def] >> pure_rewrite_tac[GSYM update_var_def] >>
     irule dload_vars_match_write >>
     simp[dload_value_word_def, word_agree_except_def]) >>
  drule_all dload_boundary_core_var_index_update >> simp[update_var_def]
QED

Theorem dload_boundary_core_environment_read_index:
  MEM i.inst_opcode ^family /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==>
      (lookup_var v (s' with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v (t' with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un)
      (s' with vs_inst_idx := SUC s.vs_inst_idx)
      (t' with vs_inst_idx := SUC t.vs_inst_idx) cs ds /\
    s' = s with vs_vars := s'.vs_vars /\
    t' = t with vs_vars := t'.vs_vars
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dload_boundary_core_environment_read >>
  disch_then (qspec_then `Cs` strip_assume_tac) >>
  qexists `s'` >> simp[lookup_var_def] >>
  conj_tac >- gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED
