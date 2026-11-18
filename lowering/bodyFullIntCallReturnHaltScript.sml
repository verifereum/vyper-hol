(* A halting callee inherits the allocation bound of its terminal step. *)
Theory bodyFullIntCallReturnHalt
Ancestors
  fragGasOriginPtr ptrSafeRun ptrDiscipline ptrDisciplineEmptyTaint opcodeClass
  fnFrameBoundaryInvoke venomExecSemantics venomExecProofs venomInstProofs

Theorem noninvoke_halt_initial_fmp[local]:
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = Halt h ==>
  h.vs_initial_fmp = s.vs_initial_fmp
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  drule step_inst_base_halt_opcodes >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = Halt h` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> asm_rewrite_tac[] >>
  simp[] >> strip_tac >>
  gvs[AllCaseEqs(), extract_venom_result_def,
      venomStateTheory.halt_state_def, venomStateTheory.set_returndata_def]
QED

Theorem terminator_ok_not_halted[local]:
  step_inst fuel ctx inst s = OK t /\ is_terminator inst.inst_opcode /\
  ~s.vs_halted ==> ~t.vs_halted
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (strip_tac >> fs[venomInstTheory.is_terminator_def]) >>
  gvs[step_inst_non_invoke] >>
  drule step_inst_base_OK_preserves_halted >> simp[]
QED

Theorem ptr_safe_halt_fmp[local]:
  (!D lo fuel ctx fn PG G tn inst s h.
    ptr_safe_step D lo fuel ctx fn PG G tn inst s /\
    ctx_has_dalloca ctx /\ step_inst fuel ctx inst s = Halt h ==>
    allocas_below_fmp h) /\
  (!D lo fuel ctx fn PG G tn bb s h.
    ptr_safe_block D lo fuel ctx fn PG G tn bb s /\
    ctx_has_dalloca ctx /\ ~s.vs_halted /\
    (exec_block fuel ctx bb s = Halt h \/
     ?u. exec_block fuel ctx bb s = OK u /\ run_blocks fuel ctx fn u = Halt h) ==>
    allocas_below_fmp h) /\
  (!D lo fuel ctx fn PG G tn s h.
    ptr_safe_blocks D lo fuel ctx fn PG G tn s /\
    ctx_has_dalloca ctx /\ ~s.vs_halted /\ run_blocks fuel ctx fn s = Halt h ==>
    allocas_below_fmp h)
Proof
  ho_match_mp_tac ptr_safe_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> gen_tac >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (strip_tac >>
          Cases_on `decode_invoke inst`
          >- (qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
              simp[Once step_inst_def]) >>
          PairCases_on `x` >>
          `inst.inst_operands = Label x0 :: x1` by
            fs[decode_invoke_def, AllCaseEqs()] >>
          drule_all invoke_source_halt >> strip_tac >>
          qpat_x_assum `ptr_safe_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
          simp[Once ptr_safe_step_def] >> strip_tac >>
          rename1 `setup_callee callee args s = SOME setup` >>
          `~setup.vs_halted` by
            (qpat_x_assum `setup_callee _ _ _ = SOME setup`
               (mp_tac o Q.AP_TERM `OPTION_MAP (\s. s.vs_halted)`) >>
             Cases_on `NULL callee.fn_blocks` >> simp[setup_callee_def]) >>
          metis_tac[]) >>
      simp[Once ptr_safe_step_def] >> strip_tac >>
      `allocation_free_opcode inst.inst_opcode` by
        (drule step_inst_halt_opcodes >> strip_tac >>
         simp[allocation_free_opcode_def]) >>
      `h.vs_fmp = s.vs_fmp /\ h.vs_allocas = s.vs_allocas /\
       h.vs_initial_fmp = s.vs_initial_fmp` by
        metis_tac[allocation_free_step_fmp_halt, allocation_free_step_allocas,
                  noninvoke_halt_initial_fmp] >>
      fs[ptr_inst_ok_def, allocas_below_fmp_def] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> gen_tac
  >- (ONCE_REWRITE_TAC [ptr_safe_block_def, exec_block_def] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      Cases_on `step_inst fuel ctx inst s` >> simp[]
      >- (Cases_on `is_terminator inst.inst_opcode` >> simp[]
          >- (rpt strip_tac >> drule_all terminator_ok_not_halted >> strip_tac >>
              gvs[] >> metis_tac[]) >>
          strip_tac >> drule_all step_preserves_halted >> strip_tac >>
          gvs[] >> metis_tac[]) >>
      strip_tac >> metis_tac[]) >>
  Cases_on `fuel` >> simp[Once ptr_safe_blocks_def, Once run_blocks_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  DISJ_CASES_TAC (Q.SPECL [`s`,`bb.bb_instructions`] eval_phis_ok_or_error_defs)
  >- (first_x_assum (qx_choose_then `s_phi` strip_assume_tac) >>
      fs[] >>
      `s_phi.vs_halted = s.vs_halted` by metis_tac[eval_phis_preserves_halted] >>
      Cases_on `exec_block n ctx bb (s_phi with
        vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[]
      >- (strip_tac >> drule exec_block_OK_not_halted >> strip_tac >>
          gvs[] >> metis_tac[]) >>
      strip_tac >> gvs[] >> metis_tac[]) >>
  gvs[]
QED

Theorem gas_origin_ptr_edge_halt_fmp:
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn)
    marks (Halt h,G',tn') /\ ctx_has_dalloca ctx ==>
  allocas_below_fmp h
Proof
  strip_tac >>
  drule gas_origin_ptr_edge_common_fuel >> strip_tac >>
  gvs[] >>
  TRY (drule_all terminator_ok_not_halted >> strip_tac >> gvs[] >> NO_TAC) >>
  drule (cj 1 ptr_safe_halt_fmp) >>
  disch_then (qspec_then `h` match_mp_tac) >> metis_tac[]
QED
