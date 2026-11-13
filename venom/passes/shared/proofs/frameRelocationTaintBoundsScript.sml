Theory frameRelocationTaintBounds
Ancestors ptrDiscipline finite_map pred_set list

Definition taint_var_bounded_def:
  taint_var_bounded tv <=>
    !v m. FLOOKUP tv v = SOME m ==> m SUBSET {k:num | k < 32}
End

Theorem taint_var_bounded_empty[simp]:
  taint_var_bounded FEMPTY
Proof
  simp[taint_var_bounded_def]
QED

Theorem taint_var_bounded_restrict:
  taint_var_bounded tv ==> taint_var_bounded (DRESTRICT tv A)
Proof
  simp[taint_var_bounded_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> Cases_on `v IN A` >> gvs[] >> metis_tac[]
QED

Theorem taint_var_bounded_set:
  taint_var_bounded tv /\ m SUBSET {k:num | k < 32} ==>
  taint_var_bounded (set_var_taint tv outs m)
Proof
  strip_tac >> Cases_on `outs`
  >- (simp[set_var_taint_def] >> irule taint_var_bounded_restrict >> simp[]) >>
  Cases_on `t`
  >- (simp[set_var_taint_def, taint_var_bounded_def, FLOOKUP_UPDATE] >>
      rpt gen_tac >> IF_CASES_TAC >> gvs[taint_var_bounded_def] >>
      metis_tac[]) >>
  simp[set_var_taint_def] >> irule taint_var_bounded_restrict >> simp[]
QED

Theorem taint_var_bounded_operand:
  taint_var_bounded tn.t_var ==> op_taint tn op SUBSET {k:num | k < 32}
Proof
  strip_tac >> Cases_on `op` >> simp[op_taint_def] >>
  Cases_on `FLOOKUP tn.t_var s` >> gvs[taint_var_bounded_def] >> metis_tac[]
QED

Theorem out_taint_bounded:
  taint_var_bounded tn.t_var ==> out_taint tn inst s SUBSET {k:num | k < 32}
Proof
  strip_tac >> simp[out_taint_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[]
  >- (Cases_on `eval_operand h s` >> simp[] >>
      rpt IF_CASES_TAC >>
      simp[mem_word_taint_def, key_taint_def, SUBSET_DEF] >>
      drule taint_var_bounded_operand >>
      disch_then (qspec_then `h` mp_tac) >> simp[SUBSET_DEF]) >>
  Cases_on `t'` >> simp[] >>
  Cases_on `inst.inst_opcode = MUL`
  >- (simp[] >> rpt IF_CASES_TAC >>
      simp[taint_var_bounded_operand]) >>
  simp[] >>
  Cases_on `eval_operand h s` >> simp[] >>
  IF_CASES_TAC >> simp[shift_taint_def, SUBSET_DEF] >>
  rpt IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem step_taint_var_bounded:
  taint_var_bounded tn.t_var ==>
  taint_var_bounded (step_taint inst s s' tn).t_var
Proof
  strip_tac >> simp[step_taint_def] >>
  irule taint_var_bounded_set >> simp[out_taint_bounded]
QED

Theorem phi_taint_bounded:
  taint_var_bounded tn.t_var ==>
  phi_taint prev tn inst SUBSET {k:num | k < 32}
Proof
  strip_tac >> Cases_on `prev` >> simp[phi_taint_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >>
  simp[taint_var_bounded_operand]
QED

Theorem phis_taint_bounded:
  taint_var_bounded tn.t_var ==> taint_var_bounded (phis_taint prev tn insts)
Proof
  strip_tac >> Induct_on `insts` >> simp[phis_taint_def] >>
  gen_tac >> IF_CASES_TAC >> simp[] >> irule taint_var_bounded_set >>
  simp[phi_taint_bounded]
QED

Theorem entry_taint_vars_bounded:
  taint_var_bounded tn.t_var ==>
  taint_var_bounded (entry_taint_vars fn s tn).t_var
Proof
  strip_tac >> simp[entry_taint_vars_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[phis_taint_bounded]
QED

Theorem frame_reachable_taint_var_bounded:
  !vs0 ctx stk PG G tn fn inst s.
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  taint_var_bounded tn.t_var /\ EVERY (\f. taint_var_bounded f.cf_tvar) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt strip_tac >>
  gvs[entry_taint_def, step_taint_var_bounded, entry_taint_vars_bounded,
      taint_var_bounded_restrict]
QED

Theorem frame_reachable_operand_taint_bounded:
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  op_taint tn op SUBSET {k:num | k < 32}
Proof
  strip_tac >> irule taint_var_bounded_operand >>
  drule frame_reachable_taint_var_bounded >> simp[]
QED
