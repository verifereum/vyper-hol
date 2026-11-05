Theory deadStoreElimStepSimulation
Ancestors
  deadStoreElimOpcodeCoverage deadStoreElimContinuation deadStoreElimJumpSteps
  deadStoreElimPureSteps deadStoreElimFrameReadSteps deadStoreElimReadSteps
  deadStoreElimStoreSteps deadStoreElimCopySteps deadStoreElimExternalCopySteps
  deadStoreElimReturnDataCopySteps deadStoreElimAccountCopySteps
  deadStoreElimRegisterSteps deadStoreElimAllocationSteps
  deadStoreElimFmpSteps deadStoreElimAssertionSteps deadStoreElimAccountSteps
  deadStoreElimMemoryObservers deadStoreElimImmutableSteps
  deadStoreElimBarrierSteps deadStoreElimResidualSimpleSteps
  deadStoreElimCallSteps deadStoreElimDelegateCallSteps deadStoreElimCreateSteps
  deadStoreElimMemoryTerminalSteps deadStoreElimTerminalSteps
  deadStoreElimDefs deadStoreElimLocal deadStoreElimPending deadStoreElimStructure
  deadStoreElimPositional passSharedDefs
  venomExecSemantics venomExecProps venomInst venomState venomWf venomEffects venomMemDefs list

Theorem dse_nonterminator_step:
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
  wf_function fn /\
  all_dead_stores ids (cfg_analyze fn) FEMPTY bp sp fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  dse_local_agrees sp P s t /\
  dse_pending_at (cfg_analyze fn) bp sp fn bb s.vs_inst_idx P s /\
  alloca_inv s /\ bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s1 ==>
  ?P1 t1. step_inst fuel ctx (dse_inst ids sp inst) t = OK t1 /\
    dse_local_agrees sp P1 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at (cfg_analyze fn) bp sp fn bb (SUC s.vs_inst_idx) P1 s1
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  `MEM inst (fn_insts fn)` by
    (`MEM inst bb.bb_instructions` by metis_tac[MEM_EL] >>
     qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
     rewrite_tac[fn_insts_def] >>
     qspec_tac (`fn.fn_blocks`, `bbs`) >>
     Induct >> simp[fn_insts_blocks_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`opc` |-> `inst.inst_opcode`] dse_opcode_coverage) >>
  strip_tac
  >- suspend "pure"
  >- suspend "frame"
  >- suspend "memory"
  >- suspend "register" >>
  suspend "residual"
QED

Resume dse_nonterminator_step[pure]:
  `dse_inst ids sp inst = inst` by
    (fs[dse_pure_opcode_def] >>
     simp[dse_inst_def, is_memory_def_opcode_def, write_effects_def, empty_effects_def]) >>
  drule_all dse_local_agrees_pure_step >> strip_tac >>
  qexistsl_tac [`P`, `t1`] >> simp[]
QED

Resume dse_nonterminator_step[frame]:
  drule_all dse_frame_read_retained >> strip_tac >>
  drule_all dse_local_agrees_frame_read_step >> strip_tac >>
  qexistsl_tac [`P`, `t1`] >> simp[]
QED

Resume dse_nonterminator_step[memory]:
  Cases_on `inst.inst_opcode IN {MLOAD; SLOAD; TLOAD}`
  >- (`dse_inst ids sp inst = inst` by
        (simp[dse_inst_def] >>
         fs[is_memory_def_opcode_def, write_effects_def, empty_effects_def]) >>
      drule_all dse_local_agrees_load_step >> strip_tac >>
      qexistsl_tac [`P`, `t1`] >> simp[]) >>
  Cases_on `inst.inst_id IN ids`
  >- (drule_all all_dead_stores_at >> strip_tac >>
      drule_all all_dead_stores_suffix >> strip_tac >>
      `dse_inst ids sp inst = mk_nop_inst inst` by simp[dse_inst_def] >>
      Cases_on `inst.inst_opcode IN {MSTORE; MSTORE8}`
      >- (`sp = AddrSp_Memory` by
            (qpat_x_assum `inst.inst_opcode IN {MSTORE; MSTORE8}` mp_tac >>
             simp[] >> strip_tac >>
             qpat_x_assum `is_memory_def_opcode _ _` mp_tac >>
             Cases_on `sp` >> simp[is_memory_def_opcode_def, write_effects_def,
               empty_effects_def]) >>
          qpat_x_assum `sp = AddrSp_Memory` SUBST_ALL_TAC >>
          drule_all dse_local_agrees_mstore_deleted_step >> strip_tac >>
          qexistsl_tac [`P1`, `t`] >>
          simp[mk_nop_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
      Cases_on `inst.inst_opcode IN {SSTORE; TSTORE}`
      >- (`(inst.inst_opcode = SSTORE /\ sp = AddrSp_Storage) \/
           (inst.inst_opcode = TSTORE /\ sp = AddrSp_Transient)` by
            (qpat_x_assum `inst.inst_opcode IN {SSTORE; TSTORE}` mp_tac >>
             simp[] >> strip_tac >>
             qpat_x_assum `is_memory_def_opcode _ _` mp_tac >>
             Cases_on `sp` >> simp[is_memory_def_opcode_def, write_effects_def,
               empty_effects_def]) >>
          qpat_x_assum `sp = _` SUBST_ALL_TAC >>
          drule_at (Pat `dse_local_agrees _ _ _ _`)
            dse_local_agrees_key_store_deleted_step >>
          disch_then (drule_at (Pat `dse_pending_at _ _ _ _ _ _ _ _`)) >>
          disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
          simp[] >> strip_tac >>
          qexistsl_tac [`P1`, `t`] >>
          simp[mk_nop_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
      `inst.inst_opcode <> RETURNDATACOPY /\ inst.inst_opcode <> EXTCODECOPY` by
        metis_tac[dse_returndatacopy_not_effects_in_space,
          dse_extcodecopy_not_effects_in_space] >>
      `inst.inst_opcode IN {MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES}` by fs[] >>
      `sp = AddrSp_Memory` by
        (qpat_x_assum `inst.inst_opcode IN {MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES}` mp_tac >>
         simp[] >> strip_tac >>
         qpat_x_assum `is_memory_def_opcode _ _` mp_tac >>
         Cases_on `sp` >> simp[is_memory_def_opcode_def, write_effects_def,
           empty_effects_def]) >>
      qpat_x_assum `sp = AddrSp_Memory` SUBST_ALL_TAC >>
      Cases_on `inst.inst_opcode = MCOPY`
      >- (drule_all dse_local_agrees_mcopy_deleted_step >> strip_tac >>
          qexistsl_tac [`P1`, `t`] >>
          simp[mk_nop_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
      `inst.inst_opcode IN {CALLDATACOPY; CODECOPY; DLOADBYTES}` by fs[] >>
      drule_all dse_local_agrees_external_copy_deleted_step >> strip_tac >>
      qexistsl_tac [`P1`, `t`] >>
      simp[mk_nop_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  `dse_inst ids sp inst = inst` by simp[dse_inst_def] >>
  Cases_on `inst.inst_opcode IN {MSTORE; MSTORE8}`
  >- (drule_all dse_local_agrees_mstore_step >> simp[]) >>
  Cases_on `inst.inst_opcode IN {SSTORE; TSTORE}`
  >- (drule_all dse_local_agrees_key_store_step >> simp[]) >>
  Cases_on `inst.inst_opcode = MCOPY`
  >- (drule_all dse_local_agrees_mcopy_step >> simp[]) >>
  Cases_on `inst.inst_opcode IN {CALLDATACOPY; CODECOPY; DLOADBYTES}`
  >- (drule_all dse_local_agrees_external_copy_step >> simp[]) >>
  Cases_on `inst.inst_opcode = RETURNDATACOPY`
  >- (drule_all dse_local_agrees_returndatacopy_step >> simp[]) >>
  `inst.inst_opcode = EXTCODECOPY` by fs[] >>
  drule_all dse_local_agrees_extcodecopy_step >> simp[]
QED

Resume dse_nonterminator_step[register]:
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (`dse_inst ids sp inst = inst` by (irule dse_alloca_retained >> simp[]) >>
      drule_all dse_local_agrees_alloca_step >> strip_tac >>
      qexistsl_tac [`P`, `t1`] >> simp[]) >>
  `dse_register_opcode inst.inst_opcode` by fs[dse_register_opcode_def] >>
  `dse_inst ids sp inst = inst` by (irule dse_register_retained >> simp[]) >>
  drule_all dse_local_agrees_register_step >> strip_tac >>
  qexistsl_tac [`P`, `t1`] >> simp[]
QED

Resume dse_nonterminator_step[residual]:
  Cases_on `dse_barrier_case sp inst.inst_opcode`
  >- (`dse_inst ids sp inst = inst` by
        (irule dse_barrier_retained >> metis_tac[]) >>
      drule_all dse_barrier_inputs >> strip_tac >>
      qpat_x_assum `s = t` SUBST_ALL_TAC >>
      qexistsl_tac [`[]`, `s1`] >>
      simp[dse_local_agrees_refl, dse_pending_at_empty]) >>
  Cases_on `inst.inst_opcode IN {GETFMP; SETFMP; DALLOCA}`
  >- (`dse_inst ids sp inst = inst` by (irule dse_fmp_retained >> simp[]) >>
      drule_all dse_local_agrees_fmp_step >> strip_tac >>
      qexistsl_tac [`P`, `t1`] >> simp[]) >>
  Cases_on `inst.inst_opcode IN {ASSERT; ASSERT_UNREACHABLE}`
  >- (`inst.inst_opcode IN {ASSERT; ASSERT_UNREACHABLE; INVALID; PHI}` by fs[] >>
      `dse_inst ids sp inst = inst` by (irule dse_assertion_retained >> simp[]) >>
      drule_all dse_local_agrees_assertion_step >> strip_tac >>
      qexistsl_tac [`P`, `t1`] >> simp[]) >>
  Cases_on `inst.inst_opcode IN {BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH}`
  >- (`dse_account_opcode inst.inst_opcode` by fs[dse_account_opcode_def] >>
      `dse_inst ids sp inst = inst` by (irule dse_account_retained >> simp[]) >>
      drule_all dse_local_agrees_account_step >> strip_tac >>
      qexistsl_tac [`P`, `t1`] >> simp[]) >>
  Cases_on `inst.inst_opcode = ISTORE`
  >- (drule_all dse_istore_retained >> strip_tac >>
      drule_all dse_local_agrees_istore_step >> simp[]) >>
  Cases_on `inst.inst_opcode IN {SHA3; LOG}`
  >- (`dse_inst ids sp inst = inst` by (irule dse_observer_retained >> simp[]) >>
      `allocas_non_overlapping s` by fs[alloca_inv_def] >>
      drule_all dse_observer_step >> strip_tac >>
      `s.vs_inst_idx = t.vs_inst_idx` by
        fs[dse_local_agrees_def, dse_operational_agrees_def] >>
      qexistsl_tac [`P`, `t1`] >> simp[dse_local_agrees_inst_idx]) >>
  Cases_on `inst.inst_opcode IN {MEMTOP; ILOAD}`
  >- (`sp IN {AddrSp_Storage; AddrSp_Transient}` by
        (qpat_assum `sp IN _` mp_tac >>
         qpat_assum `inst.inst_opcode IN {MEMTOP; ILOAD}` mp_tac >>
         qpat_assum `~dse_barrier_case _ _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[dse_barrier_case_def] >> metis_tac[]) >>
      `dse_inst ids sp inst = inst` by
        (irule dse_memory_reader_retained >> simp[]) >>
      drule_all dse_key_memory_reader_step >> strip_tac >>
      drule_all dse_key_memory_reader_pending_step >> strip_tac >>
      `s.vs_inst_idx = t.vs_inst_idx` by
        fs[dse_local_agrees_def, dse_operational_agrees_def] >>
      qexistsl_tac [`P`, `t1`] >> simp[dse_local_agrees_inst_idx]) >>
  Cases_on `inst.inst_opcode IN {CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2}`
  >- suspend "external" >>
  `inst.inst_opcode = INVALID \/ inst.inst_opcode = PHI` by
    (qpat_x_assum `inst.inst_opcode IN _` mp_tac >>
     gvs[dse_barrier_case_def] >> strip_tac >> gvs[is_terminator_def]) >>
  fs[] >> imp_res_tac dse_invalid_abort >> imp_res_tac dse_phi_error >> gvs[]
QED

Resume dse_nonterminator_step[external]:
  `sp = AddrSp_Memory` by
    (qpat_assum `sp IN _` mp_tac >>
     qpat_assum `inst.inst_opcode IN {CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2}` mp_tac >>
     qpat_assum `~dse_barrier_case _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[dse_barrier_case_def] >> metis_tac[]) >>
  qpat_x_assum `sp = AddrSp_Memory` SUBST_ALL_TAC >>
  `allocas_non_overlapping s` by fs[alloca_inv_def] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  Cases_on `inst.inst_opcode IN {CREATE; CREATE2}`
  >- (`dse_inst ids AddrSp_Memory inst = inst` by
        (irule dse_create_memory_retained >> simp[]) >>
      drule_all dse_create_memory_step >> strip_tac >>
      qexistsl_tac [`P`, `t1`] >> simp[dse_local_agrees_inst_idx]) >>
  `inst.inst_opcode IN {CALL; STATICCALL; DELEGATECALL}` by fs[] >>
  drule_all dse_external_call_retained >> strip_tac >>
  Cases_on `inst.inst_opcode = DELEGATECALL`
  >- (drule_all dse_delegatecall_memory_step >> strip_tac >>
      qexistsl_tac [`P1`, `t1`] >> simp[dse_local_agrees_inst_idx]) >>
  `inst.inst_opcode IN {CALL; STATICCALL}` by fs[] >>
  drule_all dse_call_memory_step >> strip_tac >>
  qexistsl_tac [`P1`, `t1`] >> simp[dse_local_agrees_inst_idx]
QED

Finalise dse_nonterminator_step
