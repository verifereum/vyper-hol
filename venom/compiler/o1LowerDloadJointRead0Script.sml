(* Equal-observation read0 operations preserve the whole joint boundary. *)
Theory o1LowerDloadJointRead0
Ancestors
  o1LowerDloadJointScalar o1LowerDloadJointAssign o1LowerDloadJointRelation
  o1LowerDloadShared o1LowerDloadOccurrence o1LowerDloadEnvironment
  ptrDiscipline venomExecSemantics venomState venomInst o1PassContract
  list finite_map vfmState

Theorem ld_out_taint_default:
  ~MEM inst.inst_opcode [MLOAD; ILOAD; SLOAD; TLOAD; ASSIGN; SHL; SHR; SAR] ==>
  out_taint tn inst s = {}
Proof
  strip_tac >> simp[out_taint_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem ld_joint_read0_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  MEM inst.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
     COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
     BLOBBASEFEE; CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE] /\
  step_inst fuel C inst s = OK s1 ==>
  ?out x. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out x t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out x t)
Proof
  strip_tac >>
  `ld_joint_local_fields s t /\ s.vs_returndata = t.vs_returndata /\
   ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
    fs[ld_joint_boundary_def, ld_joint_frame_def] >>
  `ld_env_agree sites fn H tn s t` by metis_tac[ld_joint_environment] >>
  `!addr. (lookup_account addr s.vs_accounts).balance =
           (lookup_account addr t.vs_accounts).balance` by
    (drule ld_shared_accounts_fields >> strip_tac >> gen_tac >>
     simp[lookup_account_def] >>
     qsuff_tac `(s.vs_accounts addr with storage := (t.vs_accounts addr).storage).balance =
                 (t.vs_accounts addr).balance`
     >- simp[] >> AP_TERM_TAC >> simp[]) >>
  fs[ld_joint_local_fields_def, MEM] >>
  (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
   simp[step_inst_non_invoke] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   simp[exec_read0_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
   rename1 `inst.inst_outputs = [out]` >>
   qmatch_goalsub_abbrev_tac `update_var out value s` >>
   qexists_tac `value` >> simp[] >>
   irule ld_env_clean_update >> simp[] >>
   simp[occurrence_out_def, out_prov_def] >>
   irule ld_out_taint_default >> simp[])
QED

Theorem ld_joint_read0_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\
  MEM inst.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
     COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
     BLOBBASEFEE; CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE] /\
  step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  strip_tac >> drule_all ld_joint_read0_step >> strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    gvs[ld_joint_boundary_def] >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by gvs[] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    gvs[is_terminator_def, MEM] >>
  `occ_frame_reachable vs C stk PG (step_prov PG G inst s1)
     (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP
     (occurrence_step a HP H inst s1)` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def] >> gvs[]) >>
  `occurrence_annotation_ok n a U B HP (occurrence_step a HP H inst s1)
     stk PG (step_prov PG G inst s1) (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[occurrence_sites_step_def] >> gvs[]) >>
  qexists_tac `update_var out x t` >> simp[] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  irule ld_joint_var_update_next >> simp[] >>
  conj_tac >- (qexistsl [`out`,`s.vs_gas_readings`,`x`,`x`] >>
    fs[update_var_def, venom_state_component_equality,
       ld_joint_boundary_def, ld_shared_agree_def]) >>
  qexistsl_tac [`G`,`H`,`tn`] >> simp[] >>
  fs[MEM] >>
  simp[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, update_var_def, new_site_bytes_def, written_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss] >>
  rpt (pop_assum kall_tac) >>
  namedCases_on `inst.inst_operands` ["", "h tail"] >> simp[] >>
  namedCases_on `tail` ["", "h2 tail2"] >> simp[] >>
  namedCases_on `tail2` ["", "h3 tail3"] >> simp[] >>
  Cases_on `tail3` >> simp[]
QED

Theorem ld_joint_gas_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ inst.inst_opcode = GAS /\
  step_inst fuel C inst s = OK s1 ==>
  ?out x rs. inst.inst_outputs = [out] /\
    s1 = update_var out x (s with vs_gas_readings := rs) /\
    step_inst fuel C' inst t = OK (update_var out x (t with vs_gas_readings := rs)) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out x (t with vs_gas_readings := rs))
Proof
  strip_tac >>
  `s.vs_gas_readings = t.vs_gas_readings` by
    (fs[ld_joint_boundary_def] >> metis_tac[ld_shared_gas_readings]) >>
  `ld_env_agree sites fn H tn s t` by metis_tac[ld_joint_environment] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_gas_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_gas_def]
  >- (`s with vs_gas_readings := [] = s /\
       t with vs_gas_readings := [] = t` by
        simp[venom_state_component_equality] >>
      qexistsl [`0w`,`[]`] >> simp[] >>
      irule ld_env_clean_update >>
      simp[occurrence_out_def, out_prov_def] >>
      irule ld_out_taint_default >> simp[]) >>
  rename1 `s.vs_gas_readings = reading::rs` >>
  qexistsl [`reading`,`rs`] >> simp[] >>
  `ld_env_agree sites fn H tn (s with vs_gas_readings := rs)
     (t with vs_gas_readings := rs)` by
    gvs[ld_env_agree_def] >>
  `step_taint inst s (update_var out reading (s with vs_gas_readings := rs)) tn =
   step_taint inst (s with vs_gas_readings := rs)
     (update_var out reading (s with vs_gas_readings := rs)) tn` by
    ( `!u. out_taint tn inst u = {}` by
        (gen_tac >> irule ld_out_taint_default >> simp[]) >>
      simp[step_taint_def, mem_taint_def, store_taint_def,
           adopt_reset_def, imm_taint_def, new_site_bytes_def,
           written_taint_def, step_writes_def,
           codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] ) >>
  asm_rewrite_tac[] >> irule ld_env_clean_update >>
  simp[occurrence_out_def, out_prov_def] >>
  irule ld_out_taint_default >> simp[]
QED

Theorem ld_joint_gas_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ inst.inst_opcode = GAS /\
  step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  strip_tac >> drule_all ld_joint_gas_step >> strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    gvs[ld_joint_boundary_def] >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `occ_frame_reachable vs C stk PG (step_prov PG G inst s1)
     (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP
     (occurrence_step a HP H inst s1)` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def]) >>
  `occurrence_annotation_ok n a U B HP (occurrence_step a HP H inst s1)
     stk PG (step_prov PG G inst s1) (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[occurrence_sites_step_def] >> gvs[]) >>
  qexists `update_var out x (t with vs_gas_readings := rs)` >> simp[] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  irule ld_joint_var_update_next >> simp[] >>
  conj_tac >- (qexistsl [`out`,`rs`,`x`,`x`] >> simp[]) >>
  qexistsl [`G`,`H`,`tn`] >> simp[] >>
  simp[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, new_site_bytes_def, written_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, update_var_def, FLOOKUP_DEF, SF CONJ_ss] >>
  rpt (pop_assum kall_tac) >>
  namedCases_on `inst.inst_operands` ["", "h tail"] >> simp[] >>
  namedCases_on `tail` ["", "h2 tail2"] >> simp[] >>
  namedCases_on `tail2` ["", "h3 tail3"] >> simp[] >>
  Cases_on `tail3` >> simp[]
QED
