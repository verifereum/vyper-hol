Theory lowerDloadMaskBounds
Ancestors
  ptrDiscipline finite_map pred_set list venomInst

Theorem ld_mem_word_taint_bound:
  mem_word_taint M off SUBSET count 32
Proof
  simp[mem_word_taint_def, SUBSET_DEF]
QED

Theorem ld_key_taint_bound:
  key_taint X key SUBSET count 32
Proof
  simp[key_taint_def, SUBSET_DEF]
QED

Theorem ld_shift_taint_bound:
  shift_taint opc k m SUBSET count 32
Proof
  rw[shift_taint_def, SUBSET_DEF] >> simp[]
QED

Theorem ld_op_taint_bound:
  (!v. op_taint tn (Var v) SUBSET count 32) ==>
  op_taint tn op SUBSET count 32
Proof
  Cases_on `op` >> simp[op_taint_def]
QED

Theorem ld_out_taint_bound:
  (!v. op_taint tn (Var v) SUBSET count 32) ==>
  out_taint tn i s SUBSET count 32
Proof
  strip_tac >> simp[out_taint_def] >>
  namedCases_on `i.inst_operands` ["", "a rest"] >> simp[] >>
  namedCases_on `rest` ["", "b tail"] >> simp[]
  >- (Cases_on `eval_operand a s` >> simp[] >>
      rpt IF_CASES_TAC >> simp[ld_mem_word_taint_bound, ld_key_taint_bound] >>
      irule ld_op_taint_bound >> simp[]) >>
  Cases_on `tail` >> simp[] >>
  Cases_on `eval_operand a s` >> simp[] >>
  rpt IF_CASES_TAC >> simp[ld_shift_taint_bound, ld_op_taint_bound]
QED

Theorem ld_set_var_taint_bound:
  (!v n. FLOOKUP tv v = SOME n ==> n SUBSET count 32) /\
  m SUBSET count 32 ==>
  !v n. FLOOKUP (set_var_taint tv outs m) v = SOME n ==> n SUBSET count 32
Proof
  strip_tac >> namedCases_on `outs` ["", "a rest"]
  >- (simp[set_var_taint_def, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  Cases_on `rest` >>
  simp[set_var_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_var_taint_bound_iff:
  (!v. op_taint tn (Var v) SUBSET count 32) <=>
  (!v m. FLOOKUP tn.t_var v = SOME m ==> m SUBSET count 32)
Proof
  simp[op_taint_def] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspec_then `v` mp_tac) >> simp[]) >>
  Cases_on `FLOOKUP tn.t_var v` >> simp[] >> metis_tac[]
QED

Theorem ld_step_taint_bound:
  (!v. op_taint tn (Var v) SUBSET count 32) ==>
  !v. op_taint (step_taint i s s' tn) (Var v) SUBSET count 32
Proof
  strip_tac >> rewrite_tac[ld_var_taint_bound_iff] >>
  `out_taint tn i s SUBSET count 32` by
    (irule ld_out_taint_bound >> simp[]) >>
  fs[ld_var_taint_bound_iff] >> simp[step_taint_def] >>
  metis_tac[ld_set_var_taint_bound]
QED

Theorem ld_phi_taint_bound:
  (!v. op_taint tn (Var v) SUBSET count 32) ==>
  phi_taint prev tn i SUBSET count 32
Proof
  strip_tac >> Cases_on `prev` >> simp[phi_taint_def] >>
  Cases_on `resolve_phi x i.inst_operands` >> simp[] >>
  irule ld_op_taint_bound >> simp[]
QED

Theorem ld_phis_taint_bound:
  (!v. op_taint tn (Var v) SUBSET count 32) ==>
  !v m. FLOOKUP (phis_taint prev tn is) v = SOME m ==> m SUBSET count 32
Proof
  strip_tac >> Induct_on `is`
  >- (fs[phis_taint_def, ld_var_taint_bound_iff] >> metis_tac[]) >>
  qx_gen_tac `i` >>
  `phi_taint prev tn i SUBSET count 32` by
    (irule ld_phi_taint_bound >> simp[]) >>
  simp[phis_taint_def] >> IF_CASES_TAC
  >- (fs[ld_var_taint_bound_iff] >> metis_tac[]) >>
  qpat_x_assum `!v. op_taint tn (Var v) SUBSET count 32` kall_tac >>
  metis_tac[ld_set_var_taint_bound]
QED

Theorem ld_entry_taint_vars_bound:
  (!v. op_taint tn (Var v) SUBSET count 32) ==>
  !v. op_taint (entry_taint_vars fn s tn) (Var v) SUBSET count 32
Proof
  strip_tac >> rewrite_tac[ld_var_taint_bound_iff] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[entry_taint_vars_def] 
  >- (fs[ld_var_taint_bound_iff]) >>
  metis_tac[ld_phis_taint_bound]
QED

Theorem ld_entry_taint_bound:
  !v. op_taint entry_taint (Var v) SUBSET count 32
Proof
  simp[entry_taint_def, op_taint_def]
QED
