Theory bodyPtrIntCallTaintBounds
Ancestors ptrSafeRun ptrDiscipline finite_map pred_set list

Definition intcall_word_taint_bounded_def:
  intcall_word_taint_bounded tn <=>
    !op k. k IN op_taint tn op ==> k < 32
End

Theorem intcall_word_taint_map:
  intcall_word_taint_bounded tn <=>
  !x m k. FLOOKUP tn.t_var x = SOME m /\ k IN m ==> k < 32
Proof
  simp[intcall_word_taint_bounded_def] >> eq_tac
  >- (rpt strip_tac >> first_x_assum (qspecl_then [`Var x`,`k`] mp_tac) >>
      simp[op_taint_def]) >>
  rpt strip_tac >> Cases_on `op` >> gvs[op_taint_def] >>
  Cases_on `FLOOKUP tn.t_var s` >> gvs[] >> metis_tac[]
QED

Theorem intcall_word_taint_empty:
  intcall_word_taint_bounded (tn with t_var := FEMPTY)
Proof
  simp[intcall_word_taint_map]
QED

Theorem intcall_word_taint_restrict:
  intcall_word_taint_bounded tn ==>
  intcall_word_taint_bounded (tn with t_var := DRESTRICT tn.t_var A)
Proof
  simp[intcall_word_taint_map, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem intcall_word_taint_operands:
  intcall_word_taint_bounded tn ==>
  (!op k. MEM op inst.inst_operands /\ k IN op_taint tn op ==> k < 32)
Proof
  simp[intcall_word_taint_bounded_def] >> metis_tac[]
QED

Theorem intcall_set_var_taint_bounded[local]:
  (!x m k. FLOOKUP tv x = SOME m /\ k IN m ==> k < 32) /\
  (!k. k IN n ==> k < 32) ==>
  (!x m k. FLOOKUP (set_var_taint tv outs n) x = SOME m /\ k IN m ==> k < 32)
Proof
  strip_tac >> Cases_on `outs` >> simp[set_var_taint_def, FLOOKUP_DRESTRICT]
  >- metis_tac[] >>
  Cases_on `t` >> simp[set_var_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem intcall_out_taint_bounded[local]:
  intcall_word_taint_bounded tn ==> !k. k IN out_taint tn inst s ==> k < 32
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >- simp[out_taint_def] >>
  rename1 `inst.inst_operands = a::rest` >>
  Cases_on `rest`
  >- (simp[out_taint_def] >> Cases_on `eval_operand a s` >> simp[] >>
      rpt IF_CASES_TAC >>
      simp[mem_word_taint_def, key_taint_def, intcall_word_taint_bounded_def] >>
      fs[intcall_word_taint_bounded_def] >> metis_tac[]) >>
  rename1 `inst.inst_operands = a::v::rest` >>
  Cases_on `rest`
  >- (simp[out_taint_def] >> Cases_on `eval_operand a s` >> simp[] >>
      rpt IF_CASES_TAC >> simp[shift_taint_def] >>
      Cases_on `0 IN op_taint tn v` >> simp[] >> rpt strip_tac >> gvs[] >>
      fs[intcall_word_taint_bounded_def] >> metis_tac[]) >>
  simp[out_taint_def]
QED

Theorem intcall_word_taint_step:
  intcall_word_taint_bounded tn ==>
  intcall_word_taint_bounded (step_taint inst s s' tn)
Proof
  strip_tac >> drule intcall_out_taint_bounded >> strip_tac >>
  simp[intcall_word_taint_map, step_taint_def] >>
  match_mp_tac intcall_set_var_taint_bounded >>
  fs[intcall_word_taint_map] >> metis_tac[]
QED

Theorem intcall_phi_taint_bounded[local]:
  intcall_word_taint_bounded tn ==>
  !k. k IN phi_taint prev tn inst ==> k < 32
Proof
  strip_tac >> Cases_on `prev` >> simp[phi_taint_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
  fs[intcall_word_taint_bounded_def] >> metis_tac[]
QED

Theorem intcall_phis_taint_bounded[local]:
  !insts. intcall_word_taint_bounded tn ==>
  !x m k. FLOOKUP (phis_taint prev tn insts) x = SOME m /\ k IN m ==> k < 32
Proof
  Induct >- simp[phis_taint_def, GSYM intcall_word_taint_map] >>
  strip_tac >> simp[phis_taint_def] >> IF_CASES_TAC
  >- simp[intcall_word_taint_map] >>
  strip_tac >> match_mp_tac intcall_set_var_taint_bounded >>
  conj_tac >- metis_tac[] >>
  match_mp_tac intcall_phi_taint_bounded >> simp[]
QED

Theorem intcall_word_taint_entry:
  intcall_word_taint_bounded tn ==>
  intcall_word_taint_bounded (entry_taint_vars fn s tn)
Proof
  strip_tac >> simp[entry_taint_vars_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  simp[intcall_word_taint_map] >> match_mp_tac intcall_phis_taint_bounded >> simp[]
QED

Theorem intcall_word_taint_same_vars:
  tn'.t_var = tn.t_var /\ intcall_word_taint_bounded tn ==>
  intcall_word_taint_bounded tn'
Proof
  simp[intcall_word_taint_map] >> metis_tac[]
QED

Theorem intcall_word_taint_ghost_step:
  intcall_word_taint_bounded tn ==>
  intcall_word_taint_bounded (SND (ghost_step fuel ctx PG G tn inst s))
Proof
  strip_tac >> simp[Once ghost_step_def] >> IF_CASES_TAC
  >- (Cases_on `decode_invoke inst` >> simp[] >>
      PairCases_on `x` >> simp[] >>
      Cases_on `lookup_function x0 ctx.ctx_functions` >> simp[] >>
      Cases_on `eval_operands x1 s` >> simp[] >>
      Cases_on `setup_callee x x' s` >> simp[] >>
      irule intcall_word_taint_same_vars >>
      qexists_tac `tn with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs))` >>
      simp[intcall_word_taint_restrict]) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[intcall_word_taint_step]
QED
