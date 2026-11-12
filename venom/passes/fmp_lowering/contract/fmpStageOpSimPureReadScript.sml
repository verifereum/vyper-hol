Theory fmpStageOpSimPureRead
Ancestors
  fmpStageOpBase fmpStageRel o1LowerDloadRelocationKernel o1LowerDloadShared
  ptrStaticDiscipline ptrDiscipline o1PassContract contextCodegenRel
  venomExecSemantics venomState venomInst pointerConfinedDefs
  finite_map list pred_set words memLocDefs vfmState

val reads = ``[GAS; CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
  COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
  CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE; BLOCKHASH; BLOBHASH;
  BALANCE; EXTCODESIZE; EXTCODEHASH; CALLDATALOAD; DLOAD]``;

Theorem fmp_read_operand[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode ^reads /\ MEM op inst.inst_operands /\
  eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  drule fmp_stage_prov_support >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  `fn_static_ptr_ok P fn` by metis_tac[EVERY_MEM] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    metis_tac[fn_static_ptr_ok_def] >>
  `op_prov G op = NONE /\ op_taint tn op = {}` by
    (Cases_on `op` >>
     gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF, ptr_use_static_ok_def,
         mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def,
         taint_ok_def, MEM] >> metis_tac[]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt strip_tac >>
     `opaque_use_ok fn` by
       gvs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
     gvs[] >> drule_all unitShapeDefsTheory.opaque_use_ok_retpc_use >>
     gvs[unitShapeDefsTheory.retpc_use_ok_def, MEM]) >>
  `inst.inst_opcode <> PHI` by gvs[MEM] >>
  drule_all fmp_stage_operand >>
  simp[fmp_value_rel_def, ld_value_agree_scalar] >>
  metis_tac[ld_value_agree_clean, ld_value_agree_scalar]
QED

Theorem fmp_read_step[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode ^reads /\ inst.inst_opcode <> GAS /\
  step_inst k C inst s = OK s1 ==>
  ?out x. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst k C' inst t = OK (update_var out x t)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
   s.vs_block_ctx = t.vs_block_ctx /\ s.vs_returndata = t.vs_returndata /\
   s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section` by
    gvs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
       eval_operand op t = SOME x` by metis_tac[fmp_read_operand] >>
  `!a. (lookup_account a s.vs_accounts).balance =
          (lookup_account a t.vs_accounts).balance /\
        (lookup_account a s.vs_accounts).nonce =
          (lookup_account a t.vs_accounts).nonce /\
        (lookup_account a s.vs_accounts).code =
          (lookup_account a t.vs_accounts).code` by
    (fs[fmp_stage_rel_def] >> drule ld_shared_accounts_fields >>
     simp[lookup_account_def] >> strip_tac >> gen_tac >>
     first_x_assum (qspec_then `a` mp_tac) >>
     simp[account_state_component_equality]) >>
  fs[MEM] >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[exec_read0_def, exec_read1_def, AllCaseEqs()] >>
  strip_tac >> gvs[MEM, account_empty_def] >> metis_tac[]
QED

Theorem fmp_read_terminating_result[local]:
  MEM inst.inst_opcode ^reads /\
  step_inst k C inst s = r /\ terminates r ==>
  ?s1. r = OK s1
Proof
  strip_tac >> fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  gvs[exec_read0_def, exec_read1_def, exec_gas_def, AllCaseEqs(),
      passSimulationDefsTheory.terminates_def] >>
  strip_tac >> gvs[passSimulationDefsTheory.terminates_def]
QED

Theorem fmp_read_gas_step[local]:
  ld_shared_agree D A tn s t /\ inst.inst_opcode = GAS /\
  step_inst k C inst s = OK s1 ==>
  ?out x rs. inst.inst_outputs = [out] /\
    s1 = update_var out x (s with vs_gas_readings := rs) /\
    step_inst k C' inst t =
      OK (update_var out x (t with vs_gas_readings := rs))
Proof
  strip_tac >> drule ld_shared_gas_readings >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[exec_gas_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on `s.vs_gas_readings`
  >- (gvs[] >> qexistsl [`0w`,`[]`] >>
      simp[update_var_def, venom_state_component_equality]) >>
  gvs[] >> metis_tac[]
QED

Theorem fmp_read_update_ghosts[local]:
  MEM inst.inst_opcode ^reads /\ inst.inst_outputs = [out] ==>
  step_prov PG G inst (update_var out x (s with vs_gas_readings := rs)) =
    set_prov G [out] NONE /\
  step_taint inst s (update_var out x (s with vs_gas_readings := rs)) tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >>
  `~MEM inst.inst_opcode [MLOAD; ILOAD; SLOAD; TLOAD; ASSIGN; SHL; SHR; SAR] /\
   ~MEM inst.inst_opcode [MSTORE; ISTORE; MCOPY]` by gvs[MEM] >>
  `out_taint tn inst s = {} /\ written_taint tn inst s = {}` by
    (qpat_x_assum `MEM _ _` kall_tac >> fs[MEM] >>
     simp[out_taint_def, written_taint_def] >>
     rpt (CASE_TAC >> simp[])) >>
  conj_tac
  >- (fs[MEM] >> simp[step_prov_def, out_prov_def]) >>
  simp[step_taint_def, set_var_taint_def] >>
  fs[MEM] >>
  simp[mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       update_var_def, new_site_bytes_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, range_bytes_def,
       FLOOKUP_DEF, taint_component_equality, EXTENSION, SF CONJ_ss]
QED

Theorem fmp_read_update_value[local]:
  MEM inst.inst_opcode ^reads /\ inst.inst_outputs = [out] ==>
  (!v. ~MEM v inst.inst_outputs ==>
    FLOOKUP (update_var out x (s with vs_gas_readings := rs)).vs_vars v =
      FLOOKUP s.vs_vars v /\
    FLOOKUP (update_var out x (t with vs_gas_readings := rs)).vs_vars v =
      FLOOKUP t.vs_vars v) /\
  (!v z. MEM v inst.inst_outputs /\
    FLOOKUP (update_var out x (s with vs_gas_readings := rs)).vs_vars v = SOME z ==>
    ?w. FLOOKUP (update_var out x (t with vs_gas_readings := rs)).vs_vars v = SOME w /\
     (~retpc_var fn v ==>
      fmp_value_rel sm
       (FLOOKUP (step_prov PG G inst (update_var out x (s with vs_gas_readings := rs))) v)
       (op_taint (step_taint inst s
         (update_var out x (s with vs_gas_readings := rs)) tn) (Var v)) z w))
Proof
  strip_tac >> drule_all fmp_read_update_ghosts >>
  disch_then assume_tac >>
  simp[update_var_def, FLOOKUP_UPDATE, op_taint_def, set_prov_def,
       FLOOKUP_DRESTRICT, fmp_value_rel_def, ld_value_agree_scalar,
       word_agree_except_def]
QED

Theorem fmp_read_update_post[local]:
  MEM inst.inst_opcode ^reads /\ inst.inst_outputs = [out] /\
  s1 = update_var out x (s with vs_gas_readings := rs) /\
  t1 = update_var out x (t with vs_gas_readings := rs) /\
  ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  s.vs_returndata = t.vs_returndata /\ ~s.vs_halted /\ ~t.vs_halted ==>
  (!v. ~MEM v inst.inst_outputs ==>
    FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
    FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v z. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME z ==>
    ?w. FLOOKUP t1.vs_vars v = SOME w /\
      (~retpc_var fn v ==>
        fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
          (op_taint (step_taint inst s s1 tn) (Var v)) z w)) /\
  ld_memory_agree (fmp_ld_sites sm) eom
    (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1 /\
  s1.vs_returndata = t1.vs_returndata /\ ~s1.vs_halted /\ ~t1.vs_halted /\
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
  s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_params = s.vs_params /\
  s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_tx_ctx = s.vs_tx_ctx /\
  s1.vs_block_ctx = s.vs_block_ctx /\
  s1.vs_data_section = s.vs_data_section /\
  s1.vs_labels = s.vs_labels /\ s1.vs_code = s.vs_code /\
  s1.vs_prev_hashes = s.vs_prev_hashes /\
  s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
  t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
  t1.vs_inst_idx = t.vs_inst_idx /\ t1.vs_params = t.vs_params /\
  t1.vs_call_ctx = t.vs_call_ctx /\ t1.vs_tx_ctx = t.vs_tx_ctx /\
  t1.vs_block_ctx = t.vs_block_ctx /\
  t1.vs_data_section = t.vs_data_section /\
  t1.vs_labels = t.vs_labels /\ t1.vs_code = t.vs_code /\
  t1.vs_prev_hashes = t.vs_prev_hashes /\
  t1.vs_initial_fmp = t.vs_initial_fmp /\ t1.vs_fmp = t.vs_fmp
Proof
  strip_tac >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  qpat_x_assum `t1 = _` SUBST_ALL_TAC >>
  conj_tac >- metis_tac[fmp_read_update_value] >>
  conj_tac >- metis_tac[fmp_read_update_value] >>
  drule_all fmp_read_update_ghosts >>
  disch_then assume_tac >>
  gvs[update_var_def, ld_shared_agree_def]
QED

Theorem fmp_read_step_with_gas[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode ^reads /\ step_inst k C inst s = OK s1 ==>
  ?out x rs. inst.inst_outputs = [out] /\
    s1 = update_var out x (s with vs_gas_readings := rs) /\
    step_inst k C' inst t = OK (update_var out x (t with vs_gas_readings := rs))
Proof
  strip_tac >> Cases_on `inst.inst_opcode = GAS`
  >- (irule fmp_read_gas_step >> fs[fmp_stage_rel_def] >> metis_tac[]) >>
  drule_all fmp_read_step >> strip_tac >>
  qexistsl [`out`,`x`,`s.vs_gas_readings`] >>
  `s.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[fmp_stage_rel_def, ld_shared_gas_readings] >>
  simp[update_var_def, venom_state_component_equality]
QED

Theorem fmp_stage_sim_reads:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode ^reads /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?k' r'. step_inst k' C' inst t = r' /\
    case r of
      OK s1 => ?t1. r' = OK t1 /\
        (!v. ~MEM v inst.inst_outputs ==>
             FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
             FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
        (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
           ?y. FLOOKUP t1.vs_vars v = SOME y /\
               (~retpc_var fn v ==>
                fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
                  (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
        ld_memory_agree (fmp_ld_sites sm) eom
          (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
        ld_shared_agree D s.vs_call_ctx.cc_address
          (step_taint inst s s1 tn) s1 t1 /\
        s1.vs_returndata = t1.vs_returndata /\
        ~s1.vs_halted /\ ~t1.vs_halted /\
        s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
        s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_params = s.vs_params /\
        s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_tx_ctx = s.vs_tx_ctx /\
        s1.vs_block_ctx = s.vs_block_ctx /\
        s1.vs_data_section = s.vs_data_section /\
        s1.vs_labels = s.vs_labels /\ s1.vs_code = s.vs_code /\
        s1.vs_prev_hashes = s.vs_prev_hashes /\
        s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
        t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
        t1.vs_inst_idx = t.vs_inst_idx /\ t1.vs_params = t.vs_params /\
        t1.vs_call_ctx = t.vs_call_ctx /\ t1.vs_tx_ctx = t.vs_tx_ctx /\
        t1.vs_block_ctx = t.vs_block_ctx /\
        t1.vs_data_section = t.vs_data_section /\
        t1.vs_labels = t.vs_labels /\ t1.vs_code = t.vs_code /\
        t1.vs_prev_hashes = t.vs_prev_hashes /\
        t1.vs_initial_fmp = t.vs_initial_fmp /\ t1.vs_fmp = t.vs_fmp
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >> drule_all fmp_read_terminating_result >> strip_tac >>
  qpat_x_assum `r = _` SUBST_ALL_TAC >>
  drule_all fmp_read_step_with_gas >> strip_tac >>
  qabbrev_tac `t1 = update_var out x (t with vs_gas_readings := rs)` >>
  qexistsl [`k`,`OK t1`] >> simp_tac (srw_ss()) [] >>
  conj_tac >- simp[Abbr `t1`] >>
  irule fmp_read_update_post >>
  fs[fmp_stage_rel_def] >> qexistsl [`rs`,`x`] >> simp[Abbr `t1`] >> gvs[]
QED
