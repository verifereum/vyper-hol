(* Revert-forwarding suffixes have no successful normal return. *)
Theory stepWriteFootprintForward
Ancestors
  stepWriteFootprintBase venomExecSemantics venomInst contextCodegenRel

Theorem step_revert_no_normal:
  inst.inst_opcode = REVERT ==>
  step_inst fuel ctx inst s <> OK t /\
  step_inst fuel ctx inst s <> IntRet ret t
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def] >>
  simp[AllCaseEqs()]
QED

Theorem step_assign_cases:
  inst.inst_opcode = ASSIGN ==>
  (?t. step_inst fuel ctx inst s = OK t) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def] >>
  namedCases_on `inst.inst_operands` ["", "op ops"] >> simp[] >>
  Cases_on `ops` >> simp[] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[] >>
  Cases_on `outs` >> simp[] >>
  Cases_on `eval_operand op s` >> simp[]
QED

Theorem assign_suffix_no_normal:
  !n s j bb fuel ctx t ret.
    j = s.vs_inst_idx + n /\
    (?inst. get_instruction bb j = SOME inst /\
            inst.inst_opcode = REVERT) /\
    (!k inst. s.vs_inst_idx <= k /\ k < j /\
              get_instruction bb k = SOME inst ==>
              inst.inst_opcode = ASSIGN) ==>
    exec_block fuel ctx bb s <> OK t /\
    exec_block fuel ctx bb s <> IntRet ret t
Proof
  Induct_on `n`
  >- (rpt strip_tac >> gvs[] >>
      gvs[Once venomExecSemanticsTheory.exec_block_def] >>
      drule step_revert_no_normal >>
      strip_tac >> Cases_on `step_inst fuel ctx inst s` >>
      gvs[] >> metis_tac[])
  >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (conj_tac >> simp[Once venomExecSemanticsTheory.exec_block_def])
  >> rename1 `get_instruction bb s.vs_inst_idx = SOME cur` >>
  `cur.inst_opcode = ASSIGN` by (first_x_assum irule >> qexists_tac `s.vs_inst_idx` >> simp[]) >>
  drule step_assign_cases >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] strip_assume_tac)
  >- (once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >>
      simp[is_terminator_def] >>
      first_x_assum irule >> qexists_tac `j` >> simp[] >>
      rpt strip_tac >> first_x_assum irule >>
      qexists_tac `k` >> simp[] >> decide_tac)
  >> once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >> simp[]
QED

Theorem step_forward_copy_cases:
  inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dst; src; len] ==>
  (?t. step_inst fuel ctx inst s = OK t) \/
  (?a t. step_inst fuel ctx inst s = Abort a t) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  strip_tac >> simp[step_inst_non_invoke] >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  Cases_on `eval_operand dst s` >> simp[] >>
  Cases_on `eval_operand src s` >> simp[] >>
  Cases_on `eval_operand len s` >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem revert_forward_pair_no_normal:
  revert_forward_pair bb s.vs_inst_idx j ==>
  exec_block fuel ctx bb s <> OK t /\
  exec_block fuel ctx bb s <> IntRet ret t
Proof
  pure_rewrite_tac[revert_forward_pair_def] >> strip_tac >>
  drule_all step_forward_copy_cases >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] strip_assume_tac)
  >- (once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >>
      simp[is_terminator_def] >>
      irule assign_suffix_no_normal >>
      qexistsl_tac [`j`, `j - SUC s.vs_inst_idx`] >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> qexists_tac `k` >> simp[] >> decide_tac)
  >- (once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >> simp[])
  >> once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >> simp[]
QED

Theorem revert_forward_at_no_normal:
  revert_forward_at bb s.vs_inst_idx ==>
  exec_block fuel ctx bb s <> OK t /\
  exec_block fuel ctx bb s <> IntRet ret t
Proof
  pure_rewrite_tac[revert_forward_at_def] >> strip_tac
  >- metis_tac[revert_forward_pair_no_normal]
  >> qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
  pure_rewrite_tac[revert_forward_pair_def] >> strip_tac >>
  once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >> simp[] >>
  drule step_revert_no_normal >> strip_tac >>
  Cases_on `step_inst fuel ctx inst2 s` >> gvs[] >> metis_tac[]
QED
