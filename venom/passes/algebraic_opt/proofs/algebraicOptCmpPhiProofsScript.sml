Theory algebraicOptCmpPhiProofs
Ancestors
  algebraicOptCmpSimulationProofs execEquivParamBase venomExecSemantics
  venomState

Theorem ao_cmp_eval_one_phi:
  !ignored flipped s t inst.
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_prev_bb = t.vs_prev_bb /\
    (!v. MEM (Var v) inst.inst_operands ==>
         v NOTIN ignored /\ v NOTIN flipped) ==>
    eval_one_phi s inst = eval_one_phi t inst
Proof
  rpt strip_tac >>
  `!op. MEM op inst.inst_operands ==>
     eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ao_cmp_state_rel_operand >>
     metis_tac[]) >>
  simp[eval_one_phi_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `t.vs_prev_bb` >> simp[] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
  drule resolve_phi_MEM >> strip_tac >> simp[]
QED

Theorem ao_cmp_eval_phis:
  !insts ignored flipped s t.
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_prev_bb = t.vs_prev_bb /\
    s.vs_current_bb = t.vs_current_bb /\
    (!inst. MEM inst insts /\ inst.inst_opcode = PHI ==>
      (!v. MEM (Var v) inst.inst_operands ==>
           v NOTIN ignored /\ v NOTIN flipped) /\
      (!v. MEM v inst.inst_outputs ==> v NOTIN flipped)) ==>
    (?e. eval_phis s insts = Error e /\ eval_phis t insts = Error e) \/
    (?s' t'. eval_phis s insts = OK s' /\ eval_phis t insts = OK t' /\
      ao_cmp_state_rel ignored flipped s' t' /\
      s'.vs_prev_bb = t'.vs_prev_bb /\
      s'.vs_current_bb = t'.vs_current_bb)
Proof
  Induct_on `insts`
  >- (rpt strip_tac >> simp[eval_phis_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- ( `eval_one_phi s h = eval_one_phi t h` by
         (irule ao_cmp_eval_one_phi >> metis_tac[listTheory.MEM]) >>
       Cases_on `eval_one_phi t h`
       >- simp[eval_phis_def] >>
       PairCases_on `x` >>
       `x0 NOTIN flipped` by
         (gvs[eval_one_phi_def, AllCaseEqs()] >> metis_tac[listTheory.MEM]) >>
       first_x_assum (qspecl_then [`ignored`, `flipped`, `s`, `t`] mp_tac) >>
       impl_tac >- metis_tac[listTheory.MEM] >>
       strip_tac
       >- (simp[eval_phis_def] >> metis_tac[]) >>
       simp[eval_phis_def] >>
       conj_tac
       >- (irule ao_cmp_state_rel_write >> simp[]) >>
       simp[update_var_def]) >>
  simp[eval_phis_def] >> metis_tac[]
QED
