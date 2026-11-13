(* Result inversion for the syntactically discarded revert-forward suffix. *)
Theory o1LowerDloadForwardInversion
Ancestors
  stepWriteFootprintForward venomExecSemantics venomInst contextCodegenRel
  passSimulationDefs

Theorem assign_suffix_no_halt:
  !n s j bb fuel ctx t.
    j = s.vs_inst_idx + n /\
    (?inst. get_instruction bb j = SOME inst /\
            inst.inst_opcode = REVERT) /\
    (!k inst. s.vs_inst_idx <= k /\ k < j /\
              get_instruction bb k = SOME inst ==>
              inst.inst_opcode = ASSIGN) ==>
    exec_block fuel ctx bb s <> Halt t
Proof
  Induct_on `n`
  >- (rpt strip_tac >> gvs[] >>
      qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
      simp[Once exec_block_def] >> simp[step_inst_non_invoke] >>
      asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
      simp[AllCaseEqs()]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once exec_block_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME cur` >>
  `cur.inst_opcode = ASSIGN` by
    (first_x_assum irule >> qexists_tac `s.vs_inst_idx` >> simp[]) >>
  drule step_assign_cases >>
  disch_then (qspecl_then [`s`,`fuel`,`ctx`] strip_assume_tac)
  >- (once_rewrite_tac[exec_block_def] >> simp[is_terminator_def] >>
      first_x_assum irule >> qexists_tac `j` >> simp[] >>
      rpt strip_tac >> first_x_assum irule >>
      qexists_tac `k` >> simp[] >> decide_tac) >>
  once_rewrite_tac[exec_block_def] >> simp[]
QED

Theorem revert_forward_at_no_halt:
  revert_forward_at bb s.vs_inst_idx ==>
  exec_block fuel ctx bb s <> Halt t
Proof
  pure_rewrite_tac[revert_forward_at_def] >> strip_tac
  >- (qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
      pure_rewrite_tac[revert_forward_pair_def] >> strip_tac >>
      drule_all step_forward_copy_cases >>
      disch_then (qspecl_then [`s`,`fuel`,`ctx`] strip_assume_tac)
      >- (once_rewrite_tac[exec_block_def] >> simp[is_terminator_def] >>
          irule assign_suffix_no_halt >>
          qexistsl_tac [`j`,`j - SUC s.vs_inst_idx`] >> simp[] >>
          rpt strip_tac >> first_x_assum irule >>
          qexists_tac `k` >> simp[] >> decide_tac)
      >- (once_rewrite_tac[exec_block_def] >> simp[]) >>
      once_rewrite_tac[exec_block_def] >> simp[]) >>
  qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
  pure_rewrite_tac[revert_forward_pair_def] >> strip_tac >>
  simp[Once exec_block_def] >> simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >> simp[AllCaseEqs()]
QED

Theorem revert_forward_at_terminates_abort:
  revert_forward_at bb s.vs_inst_idx /\
  exec_block fuel ctx bb s = r /\ terminates r ==>
  ?reason se. r = Abort reason se
Proof
  strip_tac >> Cases_on `r` >> gvs[terminates_def] >>
  metis_tac[revert_forward_at_no_normal, revert_forward_at_no_halt]
QED
