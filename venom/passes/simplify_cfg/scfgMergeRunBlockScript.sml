(*
 * Simplify-CFG Merge Run-Block Helpers
 *
 * run_block/step_in_block lemmas for label replacement.
 *)

Theory scfgMergeRunBlock
Ancestors
  scfgMergeHelpers scfgPhiLemmas scfgEquiv scfgDefs scfgStateOps
  venomSem venomSemProps venomInst venomState list
Libs
  scfgDefsTheory scfgEquivTheory scfgStateOpsTheory venomSemTheory
  venomSemPropsTheory venomInstTheory venomStateTheory listTheory

(* ===== replace_label_block preserves execution ===== *)

(* CHEATED - run_block API changed from 3 args to 2 args *)
Theorem step_in_block_replace_label:
  !bb s1 s2 old new preds res is_term fn.
    step_in_block bb s1 = (res, is_term) /\
    state_equiv_cfg s1 s2 /\
    s1.vs_prev_bb = SOME old /\
    s2.vs_prev_bb = SOME new /\
    old <> new /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    preds = pred_labels fn bb.bb_label /\
    MEM old preds /\
    ~MEM new preds /\
    phi_block_wf preds bb
  ==>
    ?res'. step_in_block (replace_label_block old new bb) s2 = (res', is_term) /\
           result_equiv_cfg res' res
Proof
  rpt strip_tac >> simp[step_in_block_def, replace_label_block_def] >>
  qpat_x_assum `step_in_block _ _ = _` mp_tac >> simp[step_in_block_def] >>
  Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[get_instruction_def]
  >- simp[result_equiv_cfg_def]
  >- (
    simp[EL_MAP, replace_label_inst_def] >>
    qabbrev_tac `inst = bb.bb_instructions❲s2.vs_inst_idx❳` >>
    Cases_on `inst.inst_opcode = PHI`
    >- (
      `MEM inst bb.bb_instructions` by (simp[Abbr `inst`, MEM_EL] >>
        qexists_tac `s2.vs_inst_idx` >> simp[]) >>
      `phi_inst_wf (pred_labels fn bb.bb_label) inst` by metis_tac[phi_block_wf_inst] >>
      drule_all step_inst_replace_label_phi >>
      simp[replace_label_inst_def] >> strip_tac >> strip_tac >>
      simp[is_terminator_def] >>
      Cases_on `step_inst inst s1` >> gvs[is_terminator_def, result_equiv_cfg_def]
      >- (
        Cases_on `step_inst (inst with inst_operands :=
          MAP (replace_label_operand old new) inst.inst_operands) s2` >>
        gvs[result_equiv_cfg_def] >>
        irule next_inst_state_equiv_cfg >> simp[] >>
        irule state_equiv_cfg_sym >> simp[])
      >- (
        gvs[result_equiv_cfg_def] >>
        Cases_on `step_inst (inst with inst_operands :=
          MAP (replace_label_operand old new) inst.inst_operands) s2` >>
        gvs[result_equiv_cfg_def]
        >- (gvs[] >> fs[result_equiv_cfg_def] >> metis_tac[result_equiv_cfg_def])
        >- gvs[result_equiv_cfg_sym]
        >- metis_tac[result_equiv_cfg_def]
        >- metis_tac[result_equiv_cfg_def])
      >- (
        gvs[result_equiv_cfg_def] >>
        Cases_on `step_inst (inst with inst_operands :=
          MAP (replace_label_operand old new) inst.inst_operands) s2` >>
        gvs[result_equiv_cfg_def, result_equiv_cfg_sym] >>
        metis_tac[result_equiv_cfg_def])
      >- (
        gvs[result_equiv_cfg_def] >>
        Cases_on `step_inst (inst with inst_operands :=
          MAP (replace_label_operand old new) inst.inst_operands) s2` >>
        gvs[result_equiv_cfg_def, result_equiv_cfg_sym] >>
        metis_tac[result_equiv_cfg_def]))
    >- (
      strip_tac >> drule_all step_inst_replace_label_non_phi >>
      simp[replace_label_inst_def] >> strip_tac >>
      Cases_on `step_inst inst s1` >> gvs[result_equiv_cfg_def]
      >- (
        Cases_on `step_inst (inst with inst_operands :=
          MAP (replace_label_operand old new) inst.inst_operands) s2` >>
        gvs[result_equiv_cfg_def]
        >- (
          IF_CASES_TAC >> gvs[] >> simp[result_equiv_cfg_def, state_equiv_cfg_sym, next_inst_state_equiv_cfg]
          >- (first_x_assum (qspecl_then [`old`, `new`] mp_tac) >>
              gvs[result_equiv_cfg_def, result_equiv_cfg_sym])
          >- (irule next_inst_state_equiv_cfg >> irule state_equiv_cfg_sym >> simp[] >>
              first_x_assum (qspecl_then [`old`, `new`] mp_tac) >> gvs[result_equiv_cfg_def]))
        >- (first_x_assum (qspecl_then [`old`, `new`] mp_tac) >> gvs[result_equiv_cfg_def])
        >- (first_x_assum (qspecl_then [`old`, `new`] mp_tac) >> gvs[result_equiv_cfg_def])
        >- (first_x_assum (qspecl_then [`old`, `new`] mp_tac) >> gvs[result_equiv_cfg_def]))
      >- (
        first_x_assum (qspecl_then [`old`, `new`] mp_tac) >>
        gvs[result_equiv_cfg_def] >>
        Cases_on `step_inst (inst with inst_operands :=
          MAP (replace_label_operand old new) inst.inst_operands) s2` >>
        gvs[result_equiv_cfg_def, result_equiv_cfg_sym] >>
        gvs[result_equiv_cfg_def] >> simp[result_equiv_cfg_def] >>
        strip_tac >> gvs[result_equiv_cfg_def] >>
        qpat_x_assum `Halt _ = _` (SUBST_ALL_TAC o SYM) >> gvs[result_equiv_cfg_def])
      >- (
        first_x_assum (qspecl_then [`old`, `new`] mp_tac) >>
        qpat_x_assum `Revert _ = _` (SUBST_ALL_TAC o SYM) >>
        Cases_on `step_inst (inst with inst_operands :=
          MAP (replace_label_operand old new) inst.inst_operands) s2` >>
        gvs[result_equiv_cfg_def] >> metis_tac[state_equiv_cfg_sym])
      >- (
        first_x_assum (qspecl_then [`old`, `new`] mp_tac) >>
        qpat_x_assum `Error _ = _` (SUBST_ALL_TAC o SYM) >>
        Cases_on `step_inst (inst with inst_operands :=
          MAP (replace_label_operand old new) inst.inst_operands) s2` >>
        gvs[result_equiv_cfg_def])))
QED

(* CHEATED - run_block API changed from 3 args to 2 args *)
Theorem run_block_replace_label:
  !bb s1 s2 old new preds fn.
    state_equiv_cfg s1 s2 /\
    s1.vs_prev_bb = SOME old /\
    s2.vs_prev_bb = SOME new /\
    old <> new /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    preds = pred_labels fn bb.bb_label /\
    MEM old preds /\
    ~MEM new preds /\
    phi_block_wf preds bb
  ==>
    result_equiv_cfg (run_block bb s1)
                     (run_block (replace_label_block old new bb) s2)
Proof
  recInduct run_block_ind >> rpt strip_tac >>
  Cases_on `step_in_block bb s` >>
  rename1 `step_in_block bb s = (res1, is_term)` >>
  drule_all step_in_block_replace_label >> strip_tac >>
  rename1 `step_in_block _ s2 = (res2, _)` >>
  once_rewrite_tac[run_block_def] >> gvs[] >>
  Cases_on `res1` >> Cases_on `res2` >> gvs[result_equiv_cfg_def]
  >- (
    IF_CASES_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_def]
    >- fs[stateEquivTheory.var_equiv_def]
    >- (
      IF_CASES_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_def,
        stateEquivTheory.var_equiv_def] >>
      drule step_in_block_preserves_prev_bb >> simp[] >> strip_tac >>
      `v.vs_prev_bb = SOME old` by metis_tac[step_in_block_preserves_prev_bb] >>
      `v.vs_inst_idx = v'.vs_inst_idx` by (imp_res_tac step_in_block_inst_idx_succ >> simp[]) >>
      first_x_assum (qspecl_then [`v'`, `old`, `new`, `fn`] mp_tac) >> simp[]))
  >- simp[state_equiv_cfg_sym]
  >- simp[state_equiv_cfg_sym]
QED

(* Helper: step_in_block with no PHI instructions *)
Theorem step_in_block_replace_label_no_phi:
  !bb s1 s2 old new res is_term.
    step_in_block bb s1 = (res, is_term) /\
    state_equiv_cfg s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    block_has_no_phi bb
  ==>
    ?res'. step_in_block (replace_label_block old new bb) s2 = (res', is_term) /\
           result_equiv_cfg res res'
Proof
  rpt strip_tac >> simp[step_in_block_def, replace_label_block_def] >>
  qpat_x_assum `step_in_block _ _ = _` mp_tac >> simp[step_in_block_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >> gvs[get_instruction_def]
  >- simp[result_equiv_cfg_def]
  >- (
    strip_tac >>
    `s2.vs_inst_idx < LENGTH bb.bb_instructions` by gvs[get_instruction_def] >>
    simp[get_instruction_def, EL_MAP] >>
    qabbrev_tac `inst = EL s2.vs_inst_idx bb.bb_instructions` >>
    `MEM inst bb.bb_instructions` by (simp[Abbr `inst`, MEM_EL] >>
      qexists_tac `s2.vs_inst_idx` >> simp[]) >>
    `inst.inst_opcode <> PHI` by metis_tac[block_has_no_phi_inst] >>
    `get_instruction bb s2.vs_inst_idx = SOME inst` by
      gvs[get_instruction_def, Abbr `inst`] >>
    gvs[] >>
    drule_all step_inst_replace_label_non_phi >> strip_tac >>
    first_x_assum (qspecl_then [`old`, `new`] mp_tac) >>
    simp[replace_label_inst_def] >>
    Cases_on `step_inst inst s1` >> gvs[result_equiv_cfg_def]
    >- (
      Cases_on `step_inst (inst with inst_operands :=
        MAP (replace_label_operand old new) inst.inst_operands) s2` >>
      gvs[result_equiv_cfg_def] >>
      strip_tac >> IF_CASES_TAC >> gvs[result_equiv_cfg_def]
      >- (
        qpat_x_assum `OK _ = _` (SUBST_ALL_TAC o SYM) >>
        simp[result_equiv_cfg_def, state_equiv_cfg_sym])
      >- (irule next_inst_state_equiv_cfg >> simp[]))
    >- (
      strip_tac >>
      Cases_on `step_inst (inst with inst_operands :=
        MAP (replace_label_operand old new) inst.inst_operands) s2` >>
      gvs[result_equiv_cfg_def] >>
      qpat_x_assum `Halt _ = _` (SUBST_ALL_TAC o SYM) >>
      fs[result_equiv_cfg_def])
    >- (
      strip_tac >> qpat_x_assum `Revert _ = _` (SUBST_ALL_TAC o SYM) >>
      Cases_on `step_inst (inst with inst_operands :=
        MAP (replace_label_operand old new) inst.inst_operands) s2` >>
      gvs[result_equiv_cfg_def])
    >- (
      strip_tac >> qpat_x_assum `Error _ = _` (SUBST_ALL_TAC o SYM) >>
      Cases_on `step_inst (inst with inst_operands :=
        MAP (replace_label_operand old new) inst.inst_operands) s2` >>
      gvs[result_equiv_cfg_def]))
QED

(* run_block with no PHI - uses simpler block_has_no_phi precondition *)
Theorem run_block_replace_label_no_phi:
  !bb s1 s2 old new.
    state_equiv_cfg s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    block_has_no_phi bb
  ==>
    result_equiv_cfg (run_block bb s1)
                     (run_block (replace_label_block old new bb) s2)
Proof
  recInduct run_block_ind >> rpt strip_tac >>
  Cases_on `step_in_block bb s` >>
  rename1 `step_in_block bb s = (res1, is_term)` >>
  drule_all step_in_block_replace_label_no_phi >> strip_tac >>
  first_x_assum (qspecl_then [`old`, `new`] strip_assume_tac) >>
  once_rewrite_tac[run_block_def] >> gvs[] >>
  Cases_on `res1` >> Cases_on `res'` >> gvs[result_equiv_cfg_def] >>
  IF_CASES_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_def] >>
  IF_CASES_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_def,
    stateEquivTheory.var_equiv_def] >>
  `v.vs_inst_idx = v'.vs_inst_idx` by
    (imp_res_tac step_in_block_inst_idx_succ >> simp[]) >>
  first_x_assum (qspecl_then [`v'`, `old`, `new`] mp_tac) >> simp[]
QED

(* Keep old theorem name for backwards compatibility *)
Theorem run_block_replace_label_no_phi_old:
  !bb s1 s2 old new.
    state_equiv_cfg s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    block_has_no_phi bb
  ==>
    result_equiv_cfg (run_block bb s1)
                     (run_block (replace_label_block old new bb) s2)
Proof
  metis_tac[run_block_replace_label_no_phi]
QED

(* Helper: step_in_block preserves equivalence when prev <> old and prev <> new *)
Theorem step_in_block_replace_label_prev_diff:
  !bb s old new preds prev fn res is_term.
    step_in_block bb s = (res, is_term) /\
    s.vs_prev_bb = SOME prev /\ prev <> old /\ prev <> new /\
    preds = pred_labels fn bb.bb_label /\
    MEM prev preds /\
    phi_block_wf preds bb ==>
    ?res'. step_in_block (replace_label_block old new bb) s = (res', is_term) /\
           result_equiv_cfg res' res
Proof
  rpt strip_tac >> simp[step_in_block_def, replace_label_block_def] >>
  qpat_x_assum `step_in_block _ _ = _` mp_tac >> simp[step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[get_instruction_def]
  >- simp[result_equiv_cfg_def]
  >- (
    simp[EL_MAP] >> qabbrev_tac `inst = EL s.vs_inst_idx bb.bb_instructions` >>
    simp[replace_label_inst_def] >> strip_tac >> Cases_on `inst.inst_opcode = PHI`
    >- (
      `MEM inst bb.bb_instructions` by (simp[Abbr `inst`, MEM_EL] >>
        qexists_tac `s.vs_inst_idx` >> simp[]) >>
      `phi_inst_wf (pred_labels fn bb.bb_label) inst` by
        metis_tac[phi_block_wf_inst] >>
      qspecl_then [`old`, `new`, `pred_labels fn bb.bb_label`, `inst`, `s`,
        `prev`] mp_tac step_inst_replace_label_phi_prev_diff >>
      simp[replace_label_inst_def] >> strip_tac >>
      simp[is_terminator_def] >>
      Cases_on `step_inst inst s` >> gvs[is_terminator_def, result_equiv_cfg_def]
      >- (
        Cases_on `step_inst (inst with inst_operands :=
          MAP (replace_label_operand old new) inst.inst_operands) s` >>
        gvs[result_equiv_cfg_def] >>
        irule next_inst_state_equiv_cfg >> simp[state_equiv_cfg_sym])
      >- (
        qpat_x_assum `Halt _ = _` (SUBST_ALL_TAC o SYM) >>
        Cases_on `step_inst (inst with inst_operands :=
          MAP (replace_label_operand old new) inst.inst_operands) s` >>
        gvs[result_equiv_cfg_def, state_equiv_cfg_sym])
      >- (
        qpat_x_assum `Revert _ = _` (SUBST_ALL_TAC o SYM) >>
        Cases_on `step_inst (inst with inst_operands :=
          MAP (replace_label_operand old new) inst.inst_operands) s` >>
        gvs[result_equiv_cfg_def, state_equiv_cfg_sym])
      >- (
        qpat_x_assum `Error _ = _` (SUBST_ALL_TAC o SYM) >>
        Cases_on `step_inst (inst with inst_operands :=
          MAP (replace_label_operand old new) inst.inst_operands) s` >>
        gvs[result_equiv_cfg_def]))
    >- (
      `state_equiv_cfg s s` by simp[state_equiv_cfg_refl] >>
      drule_all step_inst_replace_label_non_phi >>
      simp[replace_label_inst_def] >> strip_tac >>
      first_x_assum (qspecl_then [`old`, `new`] mp_tac) >>
      Cases_on `step_inst inst s` >>
      Cases_on `step_inst (inst with inst_operands :=
        MAP (replace_label_operand old new) inst.inst_operands) s` >>
      gvs[result_equiv_cfg_def]
      >- (
        strip_tac >> IF_CASES_TAC >> gvs[result_equiv_cfg_def,
          state_equiv_cfg_sym, next_inst_state_equiv_cfg] >>
        gvs[result_equiv_cfg_def, state_equiv_cfg_sym] >>
        qpat_x_assum `OK _ = _` (SUBST_ALL_TAC o SYM) >>
        gvs[result_equiv_cfg_def, state_equiv_cfg_sym])
      >- (
        qpat_x_assum `Halt _ = _` (SUBST_ALL_TAC o SYM) >>
        gvs[result_equiv_cfg_def, state_equiv_cfg_sym])
      >- (
        qpat_x_assum `Revert _ = _` (SUBST_ALL_TAC o SYM) >>
        gvs[result_equiv_cfg_def, state_equiv_cfg_sym])
      >- (
        qpat_x_assum `Error _ = _` (SUBST_ALL_TAC o SYM) >>
        gvs[result_equiv_cfg_def])))
QED

Theorem run_block_replace_label_prev_diff:
  !bb s old new preds prev fn.
    s.vs_prev_bb = SOME prev /\
    prev <> old /\ prev <> new /\
    preds = pred_labels fn bb.bb_label /\
    MEM prev preds /\
    phi_block_wf preds bb
  ==>
    result_equiv_cfg (run_block bb s)
                     (run_block (replace_label_block old new bb) s)
Proof
  recInduct run_block_ind >> rpt strip_tac >>
  Cases_on `step_in_block bb s` >>
  rename1 `step_in_block bb s = (res, is_term)` >>
  qspecl_then [`bb`, `s`, `old`, `new`, `preds`, `prev`, `fn`, `res`,
    `is_term`] mp_tac step_in_block_replace_label_prev_diff >> simp[] >>
  strip_tac >>
  once_rewrite_tac[run_block_def] >> gvs[] >>
  Cases_on `res` >> gvs[result_equiv_cfg_def]
  >- (
    Cases_on `res'` >> gvs[result_equiv_cfg_def] >>
    IF_CASES_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_sym]
    >- (
      `v'.vs_halted` by gvs[state_equiv_cfg_def] >>
      simp[result_equiv_cfg_def, state_equiv_cfg_sym])
    >- (
      `~v'.vs_halted` by gvs[state_equiv_cfg_def] >>
      simp[] >>
      IF_CASES_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_sym] >>
      irule result_equiv_cfg_trans >>
      qexists_tac `run_block (replace_label_block old new bb) v` >>
      sg `v.vs_prev_bb = s.vs_prev_bb`
      >- (
        qspecl_then [`bb`, `s`, `v`] mp_tac
          venomSemPropsTheory.step_in_block_preserves_prev_bb >> simp[])
      >- (
        conj_tac
        >- (
          first_x_assum (qspecl_then [`old`, `new`, `prev`, `fn`] mp_tac) >>
          simp[])
        >- (
          irule run_block_state_equiv_cfg >>
          rpt conj_tac
          >- (
            qspecl_then [`bb`, `s`, `v`] mp_tac step_in_block_inst_idx_succ >>
            simp[] >>
            qspecl_then [`replace_label_block old new bb`, `s`, `v'`] mp_tac
              step_in_block_inst_idx_succ >> simp[])
          >- (
            qspecl_then [`replace_label_block old new bb`, `s`, `v'`] mp_tac
              venomSemPropsTheory.step_in_block_preserves_prev_bb >> simp[])
          >- simp[state_equiv_cfg_sym]))))
  >- (Cases_on `res'` >> gvs[result_equiv_cfg_def, state_equiv_cfg_sym])
  >- (Cases_on `res'` >> gvs[result_equiv_cfg_def, state_equiv_cfg_sym])
  >- (Cases_on `res'` >> gvs[result_equiv_cfg_def, state_equiv_cfg_sym])
QED

(* Helper: step_in_block with prev_bb = NONE - PHIs always error *)
Theorem step_in_block_replace_label_prev_bb_none:
  !bb s1 s2 old new res is_term.
    step_in_block bb s1 = (res, is_term) /\
    state_equiv_cfg s1 s2 /\
    s1.vs_prev_bb = NONE /\ s2.vs_prev_bb = NONE /\
    s1.vs_inst_idx = s2.vs_inst_idx ==>
    ?res'. step_in_block (replace_label_block old new bb) s2 = (res', is_term) /\
           result_equiv_cfg res res'
Proof
  rpt strip_tac >> simp[step_in_block_def, replace_label_block_def] >>
  qpat_x_assum `step_in_block _ _ = _` mp_tac >> simp[step_in_block_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >> gvs[get_instruction_def]
  >- simp[result_equiv_cfg_def]
  >- (
    strip_tac >>
    `s2.vs_inst_idx < LENGTH bb.bb_instructions` by gvs[get_instruction_def] >>
    simp[get_instruction_def, EL_MAP] >>
    qabbrev_tac `inst = EL s2.vs_inst_idx bb.bb_instructions` >>
    `get_instruction bb s2.vs_inst_idx = SOME inst` by
      gvs[get_instruction_def, Abbr `inst`] >>
    gvs[] >>
    drule_all step_inst_replace_label_prev_bb_none >> strip_tac >>
    first_x_assum (qspecl_then [`inst`, `old`, `new`] mp_tac) >>
    simp[replace_label_inst_def] >>
    Cases_on `step_inst inst s1` >> gvs[result_equiv_cfg_def]
    >- (
      Cases_on `step_inst (inst with inst_operands :=
        MAP (replace_label_operand old new) inst.inst_operands) s2` >>
      gvs[result_equiv_cfg_def] >>
      strip_tac >> IF_CASES_TAC >> gvs[result_equiv_cfg_def]
      >- (
        qpat_x_assum `OK _ = _` (SUBST_ALL_TAC o SYM) >>
        simp[result_equiv_cfg_def])
      >- (irule next_inst_state_equiv_cfg >> simp[]))
    >- (
      strip_tac >>
      Cases_on `step_inst (inst with inst_operands :=
        MAP (replace_label_operand old new) inst.inst_operands) s2` >>
      gvs[result_equiv_cfg_def] >>
      qpat_x_assum `Halt _ = _` (SUBST_ALL_TAC o SYM) >>
      fs[result_equiv_cfg_def])
    >- (
      strip_tac >> qpat_x_assum `Revert _ = _` (SUBST_ALL_TAC o SYM) >>
      Cases_on `step_inst (inst with inst_operands :=
        MAP (replace_label_operand old new) inst.inst_operands) s2` >>
      gvs[result_equiv_cfg_def])
    >- (
      strip_tac >> qpat_x_assum `Error _ = _` (SUBST_ALL_TAC o SYM) >>
      Cases_on `step_inst (inst with inst_operands :=
        MAP (replace_label_operand old new) inst.inst_operands) s2` >>
      gvs[result_equiv_cfg_def]))
QED

(* run_block with prev_bb = NONE - uses simpler condition since PHIs always error *)
Theorem run_block_replace_label_prev_bb_none:
  !bb s1 s2 old new.
    state_equiv_cfg s1 s2 /\
    s1.vs_prev_bb = NONE /\ s2.vs_prev_bb = NONE /\
    s1.vs_inst_idx = s2.vs_inst_idx ==>
    result_equiv_cfg (run_block bb s1)
                     (run_block (replace_label_block old new bb) s2)
Proof
  recInduct run_block_ind >> rpt strip_tac >>
  Cases_on `step_in_block bb s` >>
  rename1 `step_in_block bb s = (res1, is_term)` >>
  drule_all step_in_block_replace_label_prev_bb_none >> strip_tac >>
  first_x_assum (qspecl_then [`old`, `new`] strip_assume_tac) >>
  once_rewrite_tac[run_block_def] >> gvs[] >>
  Cases_on `res1` >> Cases_on `res'` >> gvs[result_equiv_cfg_def] >>
  IF_CASES_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_def] >>
  IF_CASES_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_def,
    stateEquivTheory.var_equiv_def] >>
  `v.vs_inst_idx = v'.vs_inst_idx` by
    (imp_res_tac step_in_block_inst_idx_succ >> simp[]) >>
  `v.vs_prev_bb = s.vs_prev_bb` by
    metis_tac[venomSemPropsTheory.step_in_block_preserves_prev_bb] >>
  `v'.vs_prev_bb = s.vs_prev_bb` by
    metis_tac[venomSemPropsTheory.step_in_block_preserves_prev_bb] >>
  first_x_assum (qspecl_then [`v'`, `old`, `new`] mp_tac) >> simp[]
QED

(* Helper: terminators (except halting ones) preserve vs_current_bb through replace_label *)
Theorem step_inst_terminator_same_current_bb:
  !inst old new s1 s2 v1 v2.
    state_equiv_cfg s1 s2 /\
    is_terminator inst.inst_opcode /\
    ~MEM old (get_successors inst) /\
    step_inst inst s1 = OK v1 /\
    step_inst (replace_label_inst old new inst) s2 = OK v2 /\
    ~v1.vs_halted /\ ~v2.vs_halted
  ==>
    v1.vs_current_bb = v2.vs_current_bb
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
  >- (
    gvs[step_inst_def, replace_label_inst_def, get_successors_def,
        is_terminator_def] >>
    Cases_on `inst.inst_operands` >> gvs[] >>
    Cases_on `h` >> gvs[] >> Cases_on `t` >>
    gvs[replace_label_operand_def, get_label_def, jump_to_def])
  >- (
    gvs[step_inst_def, replace_label_inst_def, get_successors_def,
        is_terminator_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >>
         gvs[replace_label_operand_def, get_label_def, jump_to_def])
    >- (imp_res_tac eval_operand_state_equiv_cfg >>
        Cases_on `h'` >> gvs[replace_label_operand_def, get_label_def])
    >- (Cases_on `h'` >>
        gvs[replace_label_operand_def, get_label_def, eval_operand_def] >>
        gvs[state_equiv_cfg_def, stateEquivTheory.var_equiv_def])
    >- (Cases_on `h'` >> gvs[get_label_def, eval_operand_def])
    >- (Cases_on `h'` >>
        gvs[get_label_def, replace_label_operand_def, eval_operand_state_equiv_cfg]
        >- gvs[eval_operand_def]
        >- (imp_res_tac eval_operand_state_equiv_cfg >> gvs[])))
  >- gvs[step_inst_def, replace_label_inst_def]
  >- gvs[step_inst_def, replace_label_inst_def]
  >- gvs[step_inst_def, replace_label_inst_def]
  >- gvs[step_inst_def, replace_label_inst_def]
  >- gvs[step_inst_def, replace_label_inst_def]
  >- gvs[step_inst_def, replace_label_inst_def]
QED

(* Key lemma: when old is not in block_successors and PHIs don't reference old,
   run_block preserves vs_current_bb.
   This is needed for the IH in run_function_merge_blocks_equiv_fwd. *)
Theorem run_block_replace_label_current_bb:
  !bb s1 s2 old new v v'.
    state_equiv_cfg s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    block_terminator_last bb /\
    ~MEM old (block_successors bb) /\
    (* PHIs in block don't reference old label *)
    (!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
            ~MEM (Label old) inst.inst_operands) /\
    run_block bb s1 = OK v /\
    run_block (replace_label_block old new bb) s2 = OK v' /\
    ~v.vs_halted ==>
    v.vs_current_bb = v'.vs_current_bb
Proof
  completeInduct_on `LENGTH bb.bb_instructions - s1.vs_inst_idx` >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `run_block bb s1 = _` mp_tac >> simp[Once run_block_def] >>
  qpat_x_assum `run_block (replace_label_block _ _ _) _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block bb s1` >> Cases_on `q` >> gvs[] >>
  Cases_on `step_in_block (replace_label_block old new bb) s2` >> Cases_on `q` >>
  gvs[] >> rpt strip_tac >> rpt (IF_CASES_TAC >> gvs[]) >>
  Cases_on `v.vs_halted` >> gvs[] >> Cases_on `r` >> gvs[]
  >- (
    Cases_on `v'³'.vs_halted` >> Cases_on `r'` >> gvs[]
    >- (
      gvs[step_in_block_def, replace_label_block_def] >>
      Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[get_instruction_def] >>
      gvs[EL_MAP, replace_label_inst_def] >>
      Cases_on `step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s1` >> gvs[] >>
      Cases_on `is_terminator bb.bb_instructions❲s2.vs_inst_idx❳.inst_opcode` >> gvs[] >>
      Cases_on `step_inst (bb.bb_instructions❲s2.vs_inst_idx❳ with
        inst_operands := MAP (replace_label_operand old new)
        bb.bb_instructions❲s2.vs_inst_idx❳.inst_operands) s2` >> gvs[] >>
      `s2.vs_inst_idx = LENGTH bb.bb_instructions - 1` by
        (fs[block_terminator_last_def, get_instruction_def] >>
         first_x_assum irule >> simp[]) >>
      sg `~MEM old (get_successors bb.bb_instructions❲s2.vs_inst_idx❳)`
      >- (gvs[block_successors_def, block_last_inst_def] >> gvs[GSYM LAST_EL] >>
          gvs[NULL_EQ, LAST_EL] >> gvs[arithmeticTheory.PRE_SUB1] >>
          `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >> fs[]) >>
      irule step_inst_terminator_same_current_bb >> simp[replace_label_inst_def] >>
      qexists_tac `bb.bb_instructions❲s2.vs_inst_idx❳` >> simp[] >>
      qexistsl_tac [`new`, `old`, `s1`, `s2`] >> simp[] >> gvs[])
    >- (
      gvs[step_in_block_def, replace_label_block_def] >>
      Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[get_instruction_def] >>
      gvs[EL_MAP, replace_label_inst_def] >>
      Cases_on `step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s1` >> gvs[] >>
      Cases_on `is_terminator bb.bb_instructions❲s2.vs_inst_idx❳.inst_opcode` >> gvs[] >>
      Cases_on `step_inst (bb.bb_instructions❲s2.vs_inst_idx❳ with
        inst_operands := MAP (replace_label_operand old new)
        bb.bb_instructions❲s2.vs_inst_idx❳.inst_operands) s2` >> gvs[]))
  >- (
    gvs[step_in_block_def, replace_label_block_def] >>
    Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[get_instruction_def] >>
    gvs[EL_MAP, replace_label_inst_def] >>
    Cases_on `step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s1` >> gvs[] >>
    Cases_on `is_terminator bb.bb_instructions❲s2.vs_inst_idx❳.inst_opcode` >> gvs[] >>
    Cases_on `step_inst (bb.bb_instructions❲s2.vs_inst_idx❳ with
      inst_operands := MAP (replace_label_operand old new)
      bb.bb_instructions❲s2.vs_inst_idx❳.inst_operands) s2` >> gvs[] >>
    Cases_on `(next_inst v).vs_halted` >> gvs[] >>
    first_x_assum irule >> simp[] >>
    qexistsl_tac [`bb`, `new`, `old`, `next_inst v'⁴'`, `next_inst v`] >> simp[] >>
    `v'⁴'.vs_inst_idx = s1.vs_inst_idx` by (imp_res_tac step_inst_preserves_inst_idx >> gvs[]) >>
    `v.vs_inst_idx = s2.vs_inst_idx` by (imp_res_tac step_inst_preserves_inst_idx >>
      gvs[replace_label_inst_def]) >>
    `v'⁴'.vs_prev_bb = s1.vs_prev_bb` by (imp_res_tac step_inst_preserves_prev_bb >> gvs[]) >>
    `v.vs_prev_bb = s2.vs_prev_bb` by (imp_res_tac step_inst_preserves_prev_bb >>
      gvs[replace_label_inst_def]) >>
    simp[next_inst_def] >>
    sg `state_equiv_cfg v'⁴' v`
    >- (
      `result_equiv_cfg (step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s1)
        (step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s2)` by
        (irule step_inst_state_equiv_cfg >> simp[]) >>
      Cases_on `step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s2`
      >- (
        gvs[result_equiv_cfg_def] >> gvs[] >>
        TRY (fs[result_equiv_cfg_def] >> NO_TAC) >>
        `result_equiv_cfg (step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s2)
          (step_inst (replace_label_inst old new bb.bb_instructions❲s2.vs_inst_idx❳) s2)` by
          (irule step_inst_replace_label_no_phi_old >> rw[] >>
           first_x_assum irule >> simp[EL_MEM]) >>
        gvs[replace_label_inst_def, result_equiv_cfg_def] >>
        irule state_equiv_cfg_trans >> qexists_tac `v'³'` >> simp[])
      >- gvs[result_equiv_cfg_def]
      >- gvs[result_equiv_cfg_def]
      >- gvs[result_equiv_cfg_def])
    >- (
      drule state_equiv_cfg_inst_idx >>
      disch_then (qspec_then `s2.vs_inst_idx + 1` assume_tac) >>
      qpat_x_assum `state_equiv_cfg (_ with vs_inst_idx := _) v` mp_tac >>
      simp[Once state_equiv_cfg_sym] >>
      disch_then (fn th => assume_tac (MATCH_MP state_equiv_cfg_inst_idx th)) >>
      pop_assum (qspec_then `s2.vs_inst_idx + 1` assume_tac) >>
      gvs[state_equiv_cfg_sym] >>
      gvs[state_equiv_cfg_def] >>
      gvs[stateEquivTheory.var_equiv_def, lookup_var_def]))
QED

(* When prev_bb = NONE for both states, vs_current_bb is preserved through replace_label.
   No PHI condition needed because when prev_bb = NONE, PHI would error if executed,
   so if run_block succeeds, the PHI wasn't reached (and thus label operands don't matter). *)
Theorem run_block_replace_label_current_bb_prev_none:
  !bb s1 s2 old new v v'.
    state_equiv_cfg s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = NONE /\ s2.vs_prev_bb = NONE /\
    block_terminator_last bb /\
    ~MEM old (block_successors bb) /\
    run_block bb s1 = OK v /\
    run_block (replace_label_block old new bb) s2 = OK v' /\
    ~v.vs_halted ==>
    v.vs_current_bb = v'.vs_current_bb
Proof
  completeInduct_on `LENGTH bb.bb_instructions - s1.vs_inst_idx` >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `run_block bb s1 = _` mp_tac >> simp[Once run_block_def] >>
  qpat_x_assum `run_block (replace_label_block _ _ _) _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block bb s1` >> Cases_on `q` >> gvs[] >>
  Cases_on `step_in_block (replace_label_block old new bb) s2` >>
  Cases_on `q` >> gvs[] >>
  rpt strip_tac >> rpt (IF_CASES_TAC >> gvs[]) >>
  Cases_on `v.vs_halted` >> Cases_on `r` >> gvs[]
  >- (
    Cases_on `v'³'.vs_halted` >> Cases_on `r'` >> gvs[]
    >- (
      (* Terminator case T,T - use step_inst_terminator_same_current_bb *)
      gvs[step_in_block_def, replace_label_block_def] >>
      Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[get_instruction_def] >>
      gvs[listTheory.EL_MAP, replace_label_inst_def] >>
      Cases_on `step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s1` >> gvs[] >>
      Cases_on `is_terminator bb.bb_instructions❲s2.vs_inst_idx❳.inst_opcode` >> gvs[] >>
      Cases_on `step_inst (bb.bb_instructions❲s2.vs_inst_idx❳ with
        inst_operands := MAP (replace_label_operand old new)
          bb.bb_instructions❲s2.vs_inst_idx❳.inst_operands) s2` >> gvs[] >>
      sg `~MEM old (get_successors bb.bb_instructions❲s2.vs_inst_idx❳)`
      >- (
        gvs[block_successors_def, block_last_inst_def] >>
        fs[block_terminator_last_def] >>
        `s2.vs_inst_idx = LENGTH bb.bb_instructions - 1` by
          (first_x_assum (qspecl_then [`s2.vs_inst_idx`,
            `bb.bb_instructions❲s2.vs_inst_idx❳`] mp_tac) >>
           simp[get_instruction_def]) >>
        sg `bb.bb_instructions❲s2.vs_inst_idx❳ = LAST bb.bb_instructions`
        >- (
          `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
          gvs[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1])
        >- (
          gvs[listTheory.NULL_EQ] >>
          qpat_x_assum `~MEM old (case _ of NONE => _ | SOME _ => _)` mp_tac >>
          `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
          simp[]))
      >- (
        irule step_inst_terminator_same_current_bb >> simp[replace_label_inst_def] >>
        qexists_tac `bb.bb_instructions❲s2.vs_inst_idx❳` >>
        qexists_tac `new` >> qexists_tac `old` >>
        qexists_tac `s1` >> qexists_tac `s2` >> simp[]))
    >- (
      (* T,F contradiction *)
      gvs[step_in_block_def, replace_label_block_def] >>
      Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[get_instruction_def] >>
      gvs[listTheory.EL_MAP, replace_label_inst_def] >>
      Cases_on `step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s1` >> gvs[] >>
      Cases_on `is_terminator bb.bb_instructions❲s2.vs_inst_idx❳.inst_opcode` >> gvs[] >>
      Cases_on `step_inst (bb.bb_instructions❲s2.vs_inst_idx❳ with
        inst_operands := MAP (replace_label_operand old new)
          bb.bb_instructions❲s2.vs_inst_idx❳.inst_operands) s2` >> gvs[]))
  >- (
    Cases_on `v'³'.vs_halted` >> Cases_on `r'` >> gvs[]
    >- (
      (* F,T contradiction *)
      gvs[step_in_block_def, replace_label_block_def] >>
      Cases_on `get_instruction bb s2.vs_inst_idx` >>
      gvs[get_instruction_def, listTheory.EL_MAP, replace_label_inst_def] >>
      Cases_on `step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s1` >> gvs[] >>
      Cases_on `is_terminator bb.bb_instructions❲s2.vs_inst_idx❳.inst_opcode` >> gvs[] >>
      Cases_on `step_inst (bb.bb_instructions❲s2.vs_inst_idx❳ with
        inst_operands := MAP (replace_label_operand old new)
          bb.bb_instructions❲s2.vs_inst_idx❳.inst_operands) s2` >> gvs[])
    >- (
      (* F,F recursive case *)
      gvs[step_in_block_def, replace_label_block_def] >>
      Cases_on `get_instruction bb s2.vs_inst_idx` >>
      gvs[get_instruction_def, listTheory.EL_MAP, replace_label_inst_def] >>
      Cases_on `step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s1` >> gvs[] >>
      Cases_on `is_terminator bb.bb_instructions❲s2.vs_inst_idx❳.inst_opcode` >> gvs[] >>
      Cases_on `step_inst (bb.bb_instructions❲s2.vs_inst_idx❳ with
        inst_operands := MAP (replace_label_operand old new)
          bb.bb_instructions❲s2.vs_inst_idx❳.inst_operands) s2` >> gvs[] >>
      sg `state_equiv_cfg v'⁴' v`
      >- (
        `result_equiv_cfg (step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s1)
          (step_inst (replace_label_inst old new bb.bb_instructions❲s2.vs_inst_idx❳) s2)`
          by (irule step_inst_replace_label_prev_bb_none >> simp[]) >>
        gvs[result_equiv_cfg_def, replace_label_inst_def])
      >- (
        first_x_assum irule >> simp[] >>
        qexists_tac `bb` >> qexists_tac `new` >> qexists_tac `old` >>
        qexistsl_tac [`next_inst v'⁴'`, `next_inst v`] >> simp[] >>
        `v'⁴'.vs_inst_idx = s1.vs_inst_idx` by
          (drule_all step_inst_preserves_inst_idx >> simp[]) >>
        `v.vs_inst_idx = s2.vs_inst_idx` by
          (irule step_inst_preserves_inst_idx >>
           qexists_tac `bb.bb_instructions❲s2.vs_inst_idx❳ with
             inst_operands := MAP (replace_label_operand old new)
               bb.bb_instructions❲s2.vs_inst_idx❳.inst_operands` >> simp[]) >>
        simp[next_inst_def] >>
        `v'⁴'.vs_prev_bb = s1.vs_prev_bb` by
          (imp_res_tac step_inst_preserves_prev_bb >> gvs[]) >> gvs[] >>
        `v.vs_prev_bb = s2.vs_prev_bb` by
          (irule step_inst_preserves_prev_bb >>
           qexists_tac `bb.bb_instructions❲s2.vs_inst_idx❳ with
             inst_operands := MAP (replace_label_operand old new)
               bb.bb_instructions❲s2.vs_inst_idx❳.inst_operands` >> simp[]) >> gvs[] >>
        drule state_equiv_cfg_inst_idx >>
        disch_then (qspec_then `s2.vs_inst_idx + 1` assume_tac) >>
        simp[state_equiv_cfg_def, stateEquivTheory.var_equiv_def,
             venomStateTheory.lookup_var_def] >>
        gvs[state_equiv_cfg_def, stateEquivTheory.var_equiv_def,
            venomStateTheory.lookup_var_def])))
QED

(* Variant of run_block_replace_label_current_bb for no-PHI blocks.
   This version doesn't require prev_bb equality since PHIs are the only
   instructions that use prev_bb, and no-PHI blocks have none. *)
Theorem run_block_replace_label_no_phi_current_bb:
  !bb s1 s2 old new v v'.
    state_equiv_cfg s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    block_terminator_last bb /\
    block_has_no_phi bb /\
    ~MEM old (block_successors bb) /\
    run_block bb s1 = OK v /\
    run_block (replace_label_block old new bb) s2 = OK v' /\
    ~v.vs_halted ==>
    v.vs_current_bb = v'.vs_current_bb
Proof
  completeInduct_on `LENGTH bb.bb_instructions - s1.vs_inst_idx` >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `run_block bb s1 = _` mp_tac >> simp[Once run_block_def] >>
  qpat_x_assum `run_block (replace_label_block _ _ _) _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block bb s1` >> Cases_on `q` >> gvs[] >>
  Cases_on `step_in_block (replace_label_block old new bb) s2` >> Cases_on `q` >> gvs[] >>
  rpt strip_tac >> rpt (IF_CASES_TAC >> gvs[]) >>
  Cases_on `v.vs_halted` >> Cases_on `r` >> gvs[]
  >- ((* terminator, halted case *)
    Cases_on `v'³'.vs_halted` >> Cases_on `r'` >> gvs[]
    >- ((* both terminators *)
      gvs[step_in_block_def, replace_label_block_def] >>
      Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[get_instruction_def] >>
      gvs[EL_MAP, replace_label_inst_def] >>
      Cases_on `step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s1` >> gvs[] >>
      Cases_on `is_terminator bb.bb_instructions❲s2.vs_inst_idx❳.inst_opcode` >> gvs[] >>
      Cases_on `step_inst (bb.bb_instructions❲s2.vs_inst_idx❳ with
        inst_operands := MAP (replace_label_operand old new)
          bb.bb_instructions❲s2.vs_inst_idx❳.inst_operands) s2` >> gvs[] >>
      sg `~MEM old (get_successors bb.bb_instructions❲s2.vs_inst_idx❳)`
      >- (
        gvs[block_successors_def, block_last_inst_def] >>
        fs[block_terminator_last_def] >>
        `s2.vs_inst_idx = LENGTH bb.bb_instructions - 1` by (
          first_x_assum (qspecl_then [`s2.vs_inst_idx`,
            `bb.bb_instructions❲s2.vs_inst_idx❳`] mp_tac) >>
          simp[get_instruction_def]) >>
        sg `bb.bb_instructions❲s2.vs_inst_idx❳ = LAST bb.bb_instructions`
        >- (
          gvs[GSYM LAST_EL] >>
          `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
          simp[LAST_EL] >> simp[arithmeticTheory.PRE_SUB1])
        >- (
          gvs[NULL_EQ] >> gvs[] >>
          `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
          fs[]))
      >- (
        irule step_inst_terminator_same_current_bb >>
        simp[replace_label_inst_def] >>
        qexists_tac `bb.bb_instructions❲s2.vs_inst_idx❳` >> simp[] >>
        qexistsl_tac [`new`, `old`, `s1`, `s2`] >> simp[]))
    >- ((* terminator T vs F contradiction *)
      gvs[step_in_block_def, replace_label_block_def] >>
      Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[get_instruction_def] >>
      gvs[EL_MAP, replace_label_inst_def] >>
      Cases_on `step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s1` >> gvs[] >>
      Cases_on `is_terminator bb.bb_instructions❲s2.vs_inst_idx❳.inst_opcode` >> gvs[] >>
      Cases_on `step_inst (bb.bb_instructions❲s2.vs_inst_idx❳ with
        inst_operands := MAP (replace_label_operand old new)
          bb.bb_instructions❲s2.vs_inst_idx❳.inst_operands) s2` >> gvs[]))
  >- ((* recursive case: non-terminator *)
    gvs[step_in_block_def, replace_label_block_def] >>
    Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[get_instruction_def] >>
    gvs[EL_MAP, replace_label_inst_def] >>
    Cases_on `step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s1` >> gvs[] >>
    Cases_on `is_terminator bb.bb_instructions❲s2.vs_inst_idx❳.inst_opcode` >> gvs[] >>
    Cases_on `step_inst (bb.bb_instructions❲s2.vs_inst_idx❳ with
      inst_operands := MAP (replace_label_operand old new)
        bb.bb_instructions❲s2.vs_inst_idx❳.inst_operands) s2` >> gvs[] >>
    Cases_on `(next_inst v).vs_halted` >> gvs[] >>
    sg `bb.bb_instructions❲s2.vs_inst_idx❳.inst_opcode <> PHI`
    >- (
      fs[block_has_no_phi_def, block_has_phi_def] >> CCONTR_TAC >> fs[] >>
      first_x_assum (qspec_then `bb.bb_instructions❲s2.vs_inst_idx❳` mp_tac) >>
      simp[MEM_EL] >> qexists_tac `s2.vs_inst_idx` >> simp[])
    >- (
      sg `state_equiv_cfg v'⁴' v`
      >- (
        `result_equiv_cfg (step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s1)
          (step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s2)` by (
          irule step_inst_state_equiv_cfg >> simp[]) >>
        Cases_on `step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s2`
        >- (
          gvs[result_equiv_cfg_def] >>
          TRY (gvs[result_equiv_cfg_def] >> NO_TAC) >>
          sg `result_equiv_cfg (step_inst bb.bb_instructions❲s2.vs_inst_idx❳ s2)
            (step_inst (replace_label_inst old new bb.bb_instructions❲s2.vs_inst_idx❳) s2)`
          >- (irule step_inst_replace_label_no_phi_old >> simp[])
          >- (
            gvs[result_equiv_cfg_def, replace_label_inst_def] >>
            irule state_equiv_cfg_trans >> qexists_tac `v'³'` >> simp[]))
        >- gvs[result_equiv_cfg_def]
        >- gvs[result_equiv_cfg_def]
        >- gvs[result_equiv_cfg_def])
      >- (
        first_x_assum irule >> simp[] >>
        qexists_tac `bb` >>
        qexists_tac `new` >> qexists_tac `old` >>
        qexists_tac `next_inst v'⁴'` >> qexists_tac `next_inst v` >>
        simp[] >>
        conj_tac >- (
          simp[next_inst_def] >>
          `v'⁴'.vs_inst_idx = s1.vs_inst_idx` by (
            drule_all step_inst_preserves_inst_idx >> simp[]) >>
          simp[]) >>
        simp[next_inst_def] >>
        conj_tac
        >- (
          `v'⁴'.vs_inst_idx = s1.vs_inst_idx` by (
            drule_all step_inst_preserves_inst_idx >> simp[]) >>
          `v.vs_inst_idx = s2.vs_inst_idx` by (
            irule step_inst_preserves_inst_idx >>
            qexists_tac `bb.bb_instructions❲s2.vs_inst_idx❳ with
              inst_operands := MAP (replace_label_operand old new)
                bb.bb_instructions❲s2.vs_inst_idx❳.inst_operands` >>
            simp[]) >>
          simp[])
        >- (
          simp[GSYM next_inst_def] >>
          irule next_inst_state_equiv_cfg >> simp[]))))
QED

(* Helper: Running block b from any index is equivalent to running merged from corresponding index
   when merged.bb_instructions = prefix ++ b.bb_instructions and b has no PHI.
   The key invariant: s2.vs_inst_idx = s1.vs_inst_idx + LENGTH prefix *)
Theorem run_block_suffix_no_phi:
  !n b prefix s1 s2 merged.
    n = LENGTH b.bb_instructions - s1.vs_inst_idx /\
    merged.bb_instructions = prefix ++ b.bb_instructions /\
    state_equiv_cfg s1 s2 /\
    s2.vs_inst_idx = s1.vs_inst_idx + LENGTH prefix /\
    block_has_no_phi b
  ==>
    result_equiv_cfg (run_block b s1) (run_block merged s2)
Proof
  completeInduct_on `n` >> rpt strip_tac >> gvs[] >>
  simp[Once run_block_def] >> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  `get_instruction merged s2.vs_inst_idx = get_instruction b s1.vs_inst_idx` by (
    simp[get_instruction_def] >>
    Cases_on `s1.vs_inst_idx < LENGTH b.bb_instructions` >>
    simp[rich_listTheory.EL_APPEND2]) >>
  Cases_on `step_in_block b s1` >> qpat_x_assum `step_in_block b s1 = _` mp_tac >>
  simp[step_in_block_def] >>
  Cases_on `get_instruction b s1.vs_inst_idx` >> simp[result_equiv_cfg_def] >>
  (* SOME x case *)
  `x.inst_opcode <> PHI` by (
    fs[block_has_no_phi_def, block_has_phi_def, get_instruction_def] >>
    CCONTR_TAC >> fs[] >> first_x_assum (qspec_then `x` mp_tac) >>
    simp[MEM_EL] >> qexists_tac `s1.vs_inst_idx` >> simp[]) >>
  `result_equiv_cfg (step_inst x s1) (step_inst x s2)` by (
    irule step_inst_state_equiv_cfg >> simp[]) >>
  Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[result_equiv_cfg_def]
  >- (
    (* OK case *)
    IF_CASES_TAC >> gvs[] >> strip_tac >> gvs[]
    >- (
      (* terminator case *)
      qpat_x_assum `OK v = _` (fn th => simp[GSYM th]) >>
      IF_CASES_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_def])
    >- (
      (* non-terminator case - IH *)
      IF_CASES_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_def, next_inst_def]
      >- fs[stateEquivTheory.var_equiv_def, lookup_var_def]
      >- (
        first_x_assum irule >> simp[] >>
        `v.vs_inst_idx = s1.vs_inst_idx` by (imp_res_tac step_inst_preserves_inst_idx >> gvs[]) >>
        `v'.vs_inst_idx = s2.vs_inst_idx` by (imp_res_tac step_inst_preserves_inst_idx >> gvs[]) >>
        `s1.vs_inst_idx < LENGTH b.bb_instructions` by (
          fs[get_instruction_def] >> Cases_on `s1.vs_inst_idx < LENGTH b.bb_instructions` >> fs[]) >>
        gvs[stateEquivTheory.var_equiv_def, lookup_var_def])))
  >- (
    (* Halt case *)
    strip_tac >> gvs[result_equiv_cfg_def, state_equiv_cfg_def] >>
    gvs[result_equiv_cfg_def, state_equiv_cfg_def] >>
    qpat_x_assum `Halt _ = step_inst _ _` (SUBST1_TAC o GSYM) >>
    simp[result_equiv_cfg_def, state_equiv_cfg_def])
  >- (
    (* Revert case *)
    strip_tac >> gvs[] >> qpat_x_assum `Revert _ = step_inst _ _` (SUBST1_TAC o GSYM) >>
    simp[result_equiv_cfg_def, state_equiv_cfg_def])
  >- (
    (* Error case *)
    strip_tac >> gvs[] >> qpat_x_assum `Error _ = step_inst _ _` (SUBST1_TAC o GSYM) >>
    simp[result_equiv_cfg_def])
QED

Theorem run_block_merge_blocks_equiv:
  !fn a b s b_lbl.
    block_last_jmp_to b_lbl a /\
    block_terminator_last a /\
    block_has_no_phi b /\
    ~s.vs_halted /\
    s.vs_inst_idx <= LENGTH (BUTLAST a.bb_instructions)
  ==>
    result_equiv_cfg
      (case run_block a s of
         OK s' => if s'.vs_halted then Halt s' else run_block b s'
       | other => other)
      (run_block (a with bb_instructions := BUTLAST a.bb_instructions ++ b.bb_instructions) s)
Proof
  rpt strip_tac >>
  completeInduct_on `LENGTH a.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >> gvs[] >>
  Cases_on `s.vs_inst_idx < LENGTH (FRONT a.bb_instructions)`
  (* Case 1: Not at the JMP yet - execute same instruction on both sides *)
  >- (
    simp[Once run_block_def] >> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
    `a.bb_instructions <> []` by
      (fs[block_last_jmp_to_def, block_last_inst_def] >> Cases_on `a.bb_instructions` >> fs[]) >>
    qabbrev_tac `merged = a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions` >>
    `get_instruction merged s.vs_inst_idx = get_instruction a s.vs_inst_idx` by (
      simp[get_instruction_def, Abbr `merged`] >>
      conj_tac >- (fs[rich_listTheory.LENGTH_FRONT] >> decide_tac) >>
      simp[rich_listTheory.EL_APPEND1, rich_listTheory.FRONT_EL]) >>
    `step_in_block merged s = step_in_block a s` by simp[step_in_block_def] >>
    gvs[] >> Cases_on `step_in_block a s` >> Cases_on `q` >> gvs[result_equiv_cfg_def]
    >- (
      IF_CASES_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_refl] >>
      IF_CASES_TAC >> gvs[result_equiv_cfg_def]
      >- (
        (* is_term = T but not at last instruction - contradiction *)
        qpat_x_assum `step_in_block a s = _` mp_tac >> simp[step_in_block_def] >>
        `s.vs_inst_idx < LENGTH a.bb_instructions` by (fs[rich_listTheory.LENGTH_FRONT] >> decide_tac) >>
        simp[get_instruction_def] >>
        qabbrev_tac `inst = a.bb_instructions❲s.vs_inst_idx❳` >>
        `~is_terminator inst.inst_opcode` by (
          CCONTR_TAC >> fs[block_terminator_last_def] >>
          first_x_assum (qspecl_then [`s.vs_inst_idx`, `inst`] mp_tac) >>
          simp[get_instruction_def, Abbr `inst`] >> fs[rich_listTheory.LENGTH_FRONT]) >>
        Cases_on `step_inst inst s` >> gvs[])
      >- (
        (* Non-terminator - use IH *)
        `v.vs_inst_idx = s.vs_inst_idx + 1` by (imp_res_tac step_in_block_inst_idx_succ >> fs[]) >>
        first_x_assum (qspec_then `LENGTH a.bb_instructions - v.vs_inst_idx` mp_tac) >>
        impl_tac >- (fs[rich_listTheory.LENGTH_FRONT] >> decide_tac) >> strip_tac >>
        first_x_assum (qspecl_then [`a`, `v`] mp_tac) >> simp[]))
    >- simp[state_equiv_cfg_refl]
    >- simp[state_equiv_cfg_refl])
  (* Case 2: At the JMP instruction - boundary case *)
  >- (
    `s.vs_inst_idx = LENGTH (FRONT a.bb_instructions)` by decide_tac >>
    `a.bb_instructions <> []` by
      (fs[block_last_jmp_to_def, block_last_inst_def] >> Cases_on `a.bb_instructions` >> fs[]) >>
    qabbrev_tac `merged = a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions` >>
    simp[Once run_block_def] >>
    `get_instruction a s.vs_inst_idx = SOME (LAST a.bb_instructions)` by (
      simp[get_instruction_def, rich_listTheory.LENGTH_FRONT, LAST_EL] >>
      Cases_on `a.bb_instructions` >> fs[]) >>
    fs[block_last_jmp_to_def, block_last_inst_def] >>
    qabbrev_tac `jmp_inst = LAST a.bb_instructions` >>
    `step_in_block a s = (OK (jump_to b_lbl s), T)` by (
      simp[step_in_block_def, is_terminator_def] >>
      `step_inst jmp_inst s = OK (jump_to b_lbl s)` by (simp[step_inst_def] >> CASE_TAC >> fs[Abbr `jmp_inst`]) >>
      simp[]) >>
    gvs[jump_to_def] >>
    qabbrev_tac `s' = s with <|vs_prev_bb := SOME s.vs_current_bb;
                               vs_current_bb := b_lbl; vs_inst_idx := 0|>` >>
    irule run_block_suffix_no_phi >>
    rpt conj_tac
    >- simp[]
    >- simp[]
    >- (qexists_tac `FRONT a.bb_instructions` >> simp[Abbr `merged`, Abbr `s'`])
    >- simp[Abbr `s'`, state_equiv_cfg_def, stateEquivTheory.var_equiv_def, lookup_var_def])
QED

(* ===== Helper lemmas for merge correctness ===== *)

(* If block_terminator_last and instruction at idx is a terminator, it's the last instruction *)
Theorem block_last_inst_terminator:
  !bb idx inst.
    block_terminator_last bb /\
    get_instruction bb idx = SOME inst /\
    is_terminator inst.inst_opcode ==>
    block_last_inst bb = SOME inst
Proof
  rw[block_terminator_last_def, get_instruction_def, block_last_inst_def]
  >- gvs[NULL_EQ, NOT_NIL_EQ_LENGTH_NOT_0]
  >- (first_x_assum (qspec_then `idx` mp_tac) >> simp[] >>
      strip_tac >> simp[LAST_EL, NOT_NIL_EQ_LENGTH_NOT_0, arithmeticTheory.PRE_SUB1])
QED

(* After run_block succeeds without halting, current_bb is a successor of the block *)
Theorem run_block_ok_successor:
  !fn bb s s'.
    cfg_wf fn /\
    MEM bb fn.fn_blocks /\
    run_block bb s = OK s' /\
    ~s'.vs_halted ==>
    MEM s'.vs_current_bb (block_successors bb)
Proof
  rpt gen_tac >> strip_tac >>
  `block_terminator_last bb` by gvs[cfg_wf_def] >>
  pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >>
  qid_spec_tac `s'` >> qid_spec_tac `s` >> qid_spec_tac `bb` >>
  ho_match_mp_tac venomSemTheory.run_block_ind >> rpt strip_tac >>
  rename [`run_block bb s = OK s'`, `block_terminator_last bb`] >>
  qpat_x_assum `run_block _ _ = _` mp_tac >>
  simp[Once venomSemTheory.run_block_def] >>
  Cases_on `step_in_block bb s` >> Cases_on `q` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[] >> Cases_on `r` >> simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `step_in_block _ _ = _` mp_tac >>
  simp[venomSemTheory.step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  Cases_on `step_inst x s` >> simp[] >>
  Cases_on `is_terminator x.inst_opcode` >> simp[] >>
  strip_tac >> gvs[] >>
  drule_all block_last_inst_terminator >> strip_tac >>
  drule_all venomSemPropsTheory.step_inst_terminator_successor >> strip_tac >>
  gvs[block_successors_def]
QED

(* After run_block succeeds without halting, the block's label is a predecessor of current_bb *)
Theorem run_block_ok_pred_labels:
  !fn bb s s'.
    cfg_wf fn /\ MEM bb fn.fn_blocks /\
    run_block bb s = OK s' /\ ~s'.vs_halted ==>
    MEM bb.bb_label (pred_labels fn s'.vs_current_bb)
Proof
  rpt strip_tac >>
  drule_all run_block_ok_successor >> strip_tac >>
  simp[pred_labels_def, MEM_MAP, MEM_FILTER] >>
  qexists_tac `bb` >> simp[]
QED

(* If a label is not in its own pred_labels, it's not in any of its successors *)
Theorem pred_labels_not_self_loop:
  !fn bb lbl preds.
    MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\
    pred_labels fn lbl = preds /\ ~MEM lbl preds ==>
    ~MEM lbl (block_successors bb)
Proof
  rpt strip_tac >> spose_not_then assume_tac >> gvs[] >>
  sg `MEM bb.bb_label (pred_labels fn bb.bb_label)` >- (
    qpat_x_assum `~MEM _ _` mp_tac >>
    simp[pred_labels_def, listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
    strip_tac >> qexists_tac `bb` >> simp[]) >>
  gvs[]
QED

(* When prev_bb ≠ old and terminator unchanged, current_bb is preserved.
   This is a weaker version of run_block_replace_label_current_bb that doesn't
   require PHIs to not reference old - instead it relies on prev_bb ≠ old
   meaning the PHI resolution won't select the old branch anyway. *)
Theorem run_block_replace_label_current_bb_prev_diff:
  !bb s old new v v' prev preds.
    s.vs_prev_bb = SOME prev /\
    prev <> old /\ prev <> new /\
    MEM prev preds /\
    phi_block_wf preds bb /\
    block_terminator_last bb /\
    ~MEM old (block_successors bb) /\
    run_block bb s = OK v /\
    run_block (replace_label_block old new bb) s = OK v' /\
    ~v.vs_halted ==>
    v.vs_current_bb = v'.vs_current_bb
Proof
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `run_block bb s = _` mp_tac >> simp[Once run_block_def] >>
  qpat_x_assum `run_block (replace_label_block _ _ _) _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block bb s` >> Cases_on `q` >> gvs[] >>
  Cases_on `step_in_block (replace_label_block old new bb) s` >> Cases_on `q` >> gvs[] >>
  rpt strip_tac >> rpt (IF_CASES_TAC >> gvs[]) >>
  Cases_on `v.vs_halted` >> gvs[] >>
  Cases_on `v'³'.vs_halted` >> gvs[] >>
  Cases_on `r` >> gvs[]
  >- ((* Terminator case *)
    gvs[step_in_block_def, replace_label_block_def, get_instruction_def] >>
    Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >> gvs[EL_MAP] >>
    qabbrev_tac `inst = bb.bb_instructions❲s.vs_inst_idx❳` >>
    Cases_on `step_inst inst s` >> gvs[] >>
    Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
    `(replace_label_inst old new inst).inst_opcode = inst.inst_opcode`
      by simp[replace_label_inst_def] >>
    Cases_on `step_inst (replace_label_inst old new inst) s` >> gvs[] >>
    `state_equiv_cfg s s` by simp[state_equiv_cfg_refl] >>
    `s.vs_inst_idx = LENGTH bb.bb_instructions - 1` by (
      gvs[block_terminator_last_def] >>
      first_x_assum (qspecl_then [`s.vs_inst_idx`, `inst`] mp_tac) >>
      simp[get_instruction_def, markerTheory.Abbrev_def]) >>
    `~MEM old (get_successors inst)` by (
      gvs[block_successors_def, block_last_inst_def] >>
      Cases_on `bb.bb_instructions` >> gvs[LAST_EL, markerTheory.Abbrev_def]) >>
    Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
    >- (gvs[step_inst_def, replace_label_inst_def, get_successors_def, is_terminator_def] >>
        Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `h` >> gvs[] >>
        Cases_on `t` >> gvs[] >>
        gvs[replace_label_operand_def, get_label_def, jump_to_def])
    >- (gvs[step_inst_def, replace_label_inst_def] >>
        rpt (BasicProvers.FULL_CASE_TAC >>
             gvs[replace_label_operand_def, get_label_def, jump_to_def,
                 get_successors_def, is_terminator_def]) >>
        gvs[scfgMergeHelpersTheory.eval_operand_replace_label])
    >- gvs[step_inst_def, replace_label_inst_def]
    >- fs[step_inst_def, replace_label_inst_def]
    >- fs[step_inst_def, replace_label_inst_def]
    >- fs[step_inst_def, replace_label_inst_def]
    >- fs[step_inst_def, replace_label_inst_def]
    >- fs[step_inst_def, replace_label_inst_def])
  >- ((* Non-terminator case *)
    Cases_on `r':bool`
    >- ((* r' = T contradiction *)
      gvs[step_in_block_def, replace_label_block_def, get_instruction_def,
          EL_MAP, LENGTH_MAP] >>
      gvs[replace_label_inst_def] >>
      Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >> gvs[] >>
      Cases_on `step_inst bb.bb_instructions❲s.vs_inst_idx❳ s` >> gvs[AllCaseEqs()])
    >- ((* r' = F, inductive case *)
      gvs[] >>
      gvs[step_in_block_def, replace_label_block_def, get_instruction_def] >>
      Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >> gvs[EL_MAP, LENGTH_MAP] >>
      qabbrev_tac `inst = bb.bb_instructions❲s.vs_inst_idx❳` >>
      gvs[replace_label_inst_def] >>
      Cases_on `step_inst inst s` >> gvs[AllCaseEqs()] >>
      Cases_on `inst.inst_opcode = PHI`
      >- ((* PHI case *)
        gvs[step_inst_def] >> rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
        `MEM inst bb.bb_instructions` by (
          gvs[MEM_EL, markerTheory.Abbrev_def] >>
          qexists_tac `s.vs_inst_idx` >> simp[]) >>
        drule_all phi_block_wf_inst >> strip_tac >>
        drule_all scfgPhiLemmasTheory.phi_inst_wf_props >> strip_tac >>
        drule_all scfgPhiLemmasTheory.resolve_phi_replace_label_other >> strip_tac >> gvs[] >>
        fs[scfgPhiLemmasTheory.resolve_phi_replace_label_other] >>
        `x'' = x` by (
          qpat_x_assum `resolve_phi prev (MAP _ _) = SOME x''` mp_tac >>
          simp[scfgPhiLemmasTheory.resolve_phi_replace_label_other]) >>
        gvs[] >>
        first_x_assum (qspecl_then
          [`LENGTH bb.bb_instructions - (next_inst (update_var h x' s)).vs_inst_idx`] mp_tac) >>
        impl_tac >- simp[next_inst_def, update_var_def] >>
        disch_then (qspecl_then [`bb`, `next_inst (update_var h x' s)`] mp_tac) >> simp[] >>
        disch_then (qspecl_then [`old`, `new`, `v''`, `prev`, `preds`] mp_tac) >>
        simp[next_inst_def, update_var_def])
      >- ((* Non-PHI case *)
        drule_all scfgMergeHelpersTheory.step_inst_replace_label_non_phi_eq >> strip_tac >>
        `v'⁴' = s'` by (
          first_x_assum (qspecl_then [`s`, `old`, `new`] mp_tac) >>
          gvs[replace_label_inst_def]) >>
        gvs[] >>
        first_x_assum (qspecl_then
          [`LENGTH bb.bb_instructions - (next_inst s').vs_inst_idx`] mp_tac) >>
        impl_tac >- (drule_all venomSemTheory.step_inst_preserves_inst_idx >> simp[next_inst_def]) >>
        disch_then (qspecl_then [`bb`, `next_inst s'`] mp_tac) >> simp[] >>
        disch_then (qspecl_then [`old`, `new`, `v''`, `prev`, `preds`] mp_tac) >>
        impl_tac >- (drule_all venomSemPropsTheory.step_inst_preserves_prev_bb >> simp[next_inst_def]) >>
        simp[])))
QED

(* Helper: replace_label_operand is identity if old label not in operand list *)
Theorem map_replace_label_operand_id:
  !ops old new. ~MEM old (MAP THE (FILTER IS_SOME (MAP get_label ops))) ==>
    MAP (replace_label_operand old new) ops = ops
Proof
  Induct_on `ops` >> simp[] >>
  rpt strip_tac >> Cases_on `h` >> gvs[get_label_def, replace_label_operand_def]
QED

(* Helper: replace_label_inst is identity if old not in successors *)
Theorem replace_label_inst_id_not_in_successors:
  !inst old new. is_terminator inst.inst_opcode /\ ~MEM old (get_successors inst) ==>
    replace_label_inst old new inst = inst
Proof
  rpt strip_tac >> simp[replace_label_inst_def, instruction_component_equality] >>
  irule map_replace_label_operand_id >> gvs[get_successors_def]
QED

(* Helper: Same terminator from state_equiv_cfg states gives same vs_current_bb *)
Theorem step_inst_terminator_same_current_bb_simple:
  !inst s1 s2 v1 v2. state_equiv_cfg s1 s2 /\ is_terminator inst.inst_opcode /\
    step_inst inst s1 = OK v1 /\ step_inst inst s2 = OK v2 /\
    ~v1.vs_halted /\ ~v2.vs_halted ==>
    v1.vs_current_bb = v2.vs_current_bb
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
  >- (gvs[step_inst_def] >> rpt (BasicProvers.FULL_CASE_TAC >> gvs[jump_to_def]))
  >- (gvs[step_inst_def] >> rpt (BasicProvers.FULL_CASE_TAC >> gvs[jump_to_def])
      >- (imp_res_tac scfgEquivTheory.eval_operand_state_equiv_cfg >> gvs[])
      >- (drule_all scfgEquivTheory.eval_operand_state_equiv_cfg >> simp[] >>
          strip_tac >> first_x_assum (qspec_then `h` mp_tac) >> gvs[]))
  >- gvs[step_inst_def]
  >- (gvs[step_inst_def] >> rpt (BasicProvers.FULL_CASE_TAC >> gvs[]))
  >- gvs[step_inst_def, exec_result_distinct]
  >- gvs[step_inst_def, exec_result_distinct]
  >- gvs[step_inst_def, exec_result_distinct]
  >- gvs[step_inst_def, exec_result_distinct]
QED

(* Running the same block on state_equiv_cfg states gives the same current_bb.
   Key insight: current_bb is determined by the terminator instruction,
   and with var_equiv the terminator condition evaluates the same way. *)
Theorem run_block_ok_same_current_bb:
  !bb s1 s2 v1 v2.
    state_equiv_cfg s1 s2 /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    block_terminator_last bb /\
    run_block bb s1 = OK v1 /\ ~v1.vs_halted /\
    run_block bb s2 = OK v2 /\ ~v2.vs_halted ==>
    v1.vs_current_bb = v2.vs_current_bb
Proof
  completeInduct_on `LENGTH bb.bb_instructions - s1.vs_inst_idx` >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `run_block _ s1 = _` mp_tac >> simp[Once run_block_def] >>
  qpat_x_assum `run_block _ s2 = _` mp_tac >> simp[Once run_block_def] >>
  Cases_on `step_in_block bb s1` >> Cases_on `step_in_block bb s2` >>
  Cases_on `q` >> Cases_on `q'` >> gvs[] >>
  (* Both must be OK since run_block returned OK *)
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[] >>
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[]
  >- (
    (* Both terminate - use step_inst_terminator_same_current_bb_simple *)
    rpt strip_tac >> gvs[] >>
    qpat_x_assum `step_in_block bb s1 = _` mp_tac >>
    qpat_x_assum `step_in_block bb s2 = _` mp_tac >>
    simp[step_in_block_def] >>
    `get_instruction bb s1.vs_inst_idx = get_instruction bb s2.vs_inst_idx` by gvs[] >>
    Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[] >>
    Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
    IF_CASES_TAC >> gvs[] >>
    rpt strip_tac >> gvs[] >>
    irule step_inst_terminator_same_current_bb_simple >>
    simp[] >> qexistsl_tac [`x`, `s1`, `s2`] >> simp[])
  >- (
    (* s1 terminates but s2 doesn't - contradiction from same inst *)
    rpt strip_tac >>
    qpat_x_assum `step_in_block bb s1 = _` mp_tac >>
    qpat_x_assum `step_in_block bb s2 = _` mp_tac >>
    simp[step_in_block_def] >>
    `get_instruction bb s1.vs_inst_idx = get_instruction bb s2.vs_inst_idx` by gvs[] >>
    Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[] >>
    Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
    IF_CASES_TAC >> gvs[])
  >- (
    (* s1 doesn't terminate but s2 does - contradiction *)
    rpt strip_tac >>
    qpat_x_assum `step_in_block bb s1 = _` mp_tac >>
    qpat_x_assum `step_in_block bb s2 = _` mp_tac >>
    simp[step_in_block_def] >>
    `get_instruction bb s1.vs_inst_idx = get_instruction bb s2.vs_inst_idx` by gvs[] >>
    Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[] >>
    Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
    IF_CASES_TAC >> gvs[])
  >- (
    (* Neither terminates - use IH *)
    rpt strip_tac >>
    first_x_assum (qspec_then `LENGTH bb.bb_instructions - v.vs_inst_idx` mp_tac) >>
    impl_tac
    >- (
      `v.vs_inst_idx = s1.vs_inst_idx + 1` by
        (imp_res_tac scfgEquivTheory.step_in_block_inst_idx_succ >> simp[]) >>
      `s1.vs_inst_idx < LENGTH bb.bb_instructions` by (
        qpat_x_assum `step_in_block bb s1 = _` mp_tac >>
        simp[venomSemTheory.step_in_block_def, AllCaseEqs(),
             venomInstTheory.get_instruction_def]) >>
      simp[])
    >- (
      strip_tac >> first_x_assum irule >> simp[] >>
      qexistsl_tac [`bb`, `v`, `v'`] >> simp[] >>
      `v.vs_inst_idx = s1.vs_inst_idx + 1` by
        (imp_res_tac scfgEquivTheory.step_in_block_inst_idx_succ >> simp[]) >>
      `v'.vs_inst_idx = s2.vs_inst_idx + 1` by
        (imp_res_tac scfgEquivTheory.step_in_block_inst_idx_succ >> simp[]) >>
      `v.vs_prev_bb = s1.vs_prev_bb` by
        (imp_res_tac venomSemPropsTheory.step_in_block_preserves_prev_bb >> simp[]) >>
      `v'.vs_prev_bb = s2.vs_prev_bb` by
        (imp_res_tac venomSemPropsTheory.step_in_block_preserves_prev_bb >> simp[]) >>
      gvs[] >>
      qpat_x_assum `step_in_block bb s1 = _` mp_tac >>
      qpat_x_assum `step_in_block bb s2 = _` mp_tac >>
      simp[venomSemTheory.step_in_block_def] >>
      Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[] >>
      Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
      rpt strip_tac >> gvs[] >>
      BasicProvers.FULL_CASE_TAC >> gvs[] >>
      irule scfgStateOpsTheory.next_inst_state_equiv_cfg >>
      `result_equiv_cfg (step_inst x s1) (step_inst x s2)` by
        (irule scfgEquivTheory.step_inst_state_equiv_cfg >> simp[]) >>
      gvs[scfgDefsTheory.result_equiv_cfg_def]))
QED

(* Helper: run_block OK ~halted implies the last instruction is a terminator *)
Theorem run_block_ok_last_terminator:
  !bb s s'.
    run_block bb s = OK s' /\ ~s'.vs_halted /\ ~s.vs_halted /\
    block_terminator_last bb /\ bb.bb_instructions <> [] ==>
    is_terminator (LAST bb.bb_instructions).inst_opcode
Proof
  ho_match_mp_tac venomSemTheory.run_block_ind >> rpt strip_tac >>
  qpat_x_assum `run_block _ _ = _` mp_tac >>
  simp[Once venomSemTheory.run_block_def] >>
  Cases_on `step_in_block bb s` >> Cases_on `q` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[] >>
  Cases_on `r` >> simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `step_in_block _ _ = _` mp_tac >>
  simp[venomSemTheory.step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  Cases_on `step_inst x s` >> simp[] >>
  Cases_on `is_terminator x.inst_opcode` >> simp[] >>
  strip_tac >> gvs[] >>
  drule_all block_last_inst_terminator >>
  simp[scfgDefsTheory.block_last_inst_def]
QED

(* Helper: When running suffix from state_equiv_cfg states with offset, vs_current_bb matches *)
Theorem run_block_suffix_no_phi_current_bb:
  !b prefix s1 s2 merged v1 v2.
    merged.bb_instructions = prefix ++ b.bb_instructions /\
    state_equiv_cfg s1 s2 /\
    s2.vs_inst_idx = s1.vs_inst_idx + LENGTH prefix /\
    block_has_no_phi b /\
    block_terminator_last b /\
    b.bb_instructions <> [] /\
    run_block b s1 = OK v1 /\ ~v1.vs_halted /\
    run_block merged s2 = OK v2 /\ ~v2.vs_halted ==>
    v1.vs_current_bb = v2.vs_current_bb
Proof
  completeInduct_on `LENGTH b.bb_instructions - s1.vs_inst_idx` >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `run_block b _ = _` mp_tac >> simp[Once run_block_def] >>
  qpat_x_assum `run_block merged _ = _` mp_tac >> simp[Once run_block_def] >>
  `get_instruction merged s2.vs_inst_idx = get_instruction b s1.vs_inst_idx` by
    (simp[get_instruction_def] >> gvs[rich_listTheory.EL_APPEND2]) >>
  Cases_on `step_in_block b s1` >> Cases_on `q` >> gvs[] >>
  gvs[step_in_block_def] >>
  Cases_on `get_instruction b s1.vs_inst_idx` >> gvs[] >>
  `x.inst_opcode <> PHI` by (irule block_has_no_phi_inst >> qexists_tac `b` >>
    gvs[get_instruction_def, MEM_EL] >> qexists_tac `s1.vs_inst_idx` >> gvs[]) >>
  `result_equiv_cfg (step_inst x s1) (step_inst x s2)` by
    (irule step_inst_state_equiv_cfg >> gvs[]) >>
  Cases_on `step_inst x s1` >> gvs[result_equiv_cfg_def] >>
  Cases_on `step_inst x s2` >> gvs[result_equiv_cfg_def] >>
  Cases_on `is_terminator x.inst_opcode` >> gvs[]
  >- (
    rpt strip_tac >> gvs[] >> fs[] >>
    `v1 = v` by (Cases_on `v.vs_halted` >> gvs[]) >>
    `v2 = v''` by (Cases_on `v''.vs_halted` >> gvs[]) >> gvs[] >>
    irule step_inst_terminator_same_current_bb_simple >> gvs[] >>
    qexistsl_tac [`x`, `s1`, `s2`] >> gvs[])
  >- (
    rpt strip_tac >> gvs[next_inst_def] >>
    `~v'.vs_halted` by (Cases_on `v'.vs_halted` >> gvs[]) >>
    gvs[state_equiv_cfg_def] >>
    `v'.vs_inst_idx = s1.vs_inst_idx` by
      (irule step_inst_preserves_inst_idx >> qexists_tac `x` >> gvs[]) >>
    `v''.vs_inst_idx = s2.vs_inst_idx` by
      (irule step_inst_preserves_inst_idx >> qexists_tac `x` >> gvs[]) >>
    first_x_assum (qspec_then `LENGTH b.bb_instructions - (s1.vs_inst_idx + 1)` mp_tac) >>
    impl_tac >- (gvs[get_instruction_def] >> simp[]) >> strip_tac >>
    first_x_assum (qspecl_then [`b`, `v' with vs_inst_idx := v'.vs_inst_idx + 1`] mp_tac) >>
    impl_tac >- gvs[] >>
    disch_then (qspecl_then [`prefix`, `v'' with vs_inst_idx := v''.vs_inst_idx + 1`,
                             `merged`, `v1`, `v2`] mp_tac) >>
    simp[] >> impl_tac
    >- (gvs[stateEquivTheory.var_equiv_def] >>
        simp[venomStateTheory.lookup_var_def] >>
        fs[stateEquivTheory.var_equiv_def, venomStateTheory.lookup_var_def])
    >- simp[])
QED

(* Key lemma for merge_blocks correctness: vs_current_bb equality.
   When running a then b vs running merged (FRONT(a) ++ b), both end with
   b's terminator which produces the same vs_current_bb on state_equiv_cfg states. *)
Theorem run_block_merge_blocks_current_bb:
  !a b s v v' v_mid b_lbl.
    block_last_jmp_to b_lbl a /\
    block_terminator_last a /\
    block_terminator_last b /\
    block_has_no_phi b /\
    ~MEM b_lbl (block_successors b) /\
    ~s.vs_halted /\
    s.vs_inst_idx = 0 /\
    run_block a s = OK v /\ ~v.vs_halted /\
    run_block b v = OK v' /\ ~v'.vs_halted /\
    run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s = OK v_mid /\
    ~v_mid.vs_halted
  ==>
    v'.vs_current_bb = v_mid.vs_current_bb
Proof
  rpt strip_tac >>
  (* Generalize the statement for induction - need inst_idx <= LENGTH (FRONT a) *)
  `!n a s. n = LENGTH a.bb_instructions - s.vs_inst_idx ==>
   block_last_jmp_to b_lbl a ==> block_terminator_last a ==> ~s.vs_halted ==>
   s.vs_inst_idx <= LENGTH (FRONT a.bb_instructions) ==>
   run_block a s = OK v ==>
   run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s = OK v_mid ==>
   v'.vs_current_bb = v_mid.vs_current_bb` suffices_by
    (disch_then (qspecl_then [`LENGTH a.bb_instructions`, `a`, `s`] mp_tac) >> simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >> gvs[] >>
  Cases_on `s'.vs_inst_idx = LENGTH (FRONT a'.bb_instructions)`
  >- (
    (* Case 1: at JMP instruction - use run_block_suffix_no_phi_current_bb *)
    irule run_block_suffix_no_phi_current_bb >> simp[] >>
    qexistsl_tac [`b`, `a' with bb_instructions := FRONT a'.bb_instructions ++ b.bb_instructions`,
                  `FRONT a'.bb_instructions`, `v`, `s'`] >> simp[] >>
    rpt conj_tac
    >- (CCONTR_TAC >> gvs[] >> qpat_x_assum `run_block b _ = _` mp_tac >>
        simp[Once run_block_def, step_in_block_def, get_instruction_def])
    >- imp_res_tac run_block_ok_inst_idx >> gvs[]
    >- (sg `get_instruction a' s'.vs_inst_idx = SOME (LAST a'.bb_instructions)`
        >- (simp[get_instruction_def] >> fs[block_last_jmp_to_def, block_last_inst_def] >>
            `a'.bb_instructions <> []` by (Cases_on `a'.bb_instructions` >> gvs[]) >>
            simp[rich_listTheory.LENGTH_FRONT, listTheory.LAST_EL] >>
            Cases_on `a'.bb_instructions` >> gvs[])
        >- (gvs[block_last_jmp_to_def, block_last_inst_def, is_terminator_def] >>
            qpat_x_assum `run_block a' s' = _` mp_tac >>
            simp[Once run_block_def, step_in_block_def, is_terminator_def, step_inst_def, jump_to_def] >>
            strip_tac >> gvs[state_equiv_cfg_def, stateEquivTheory.var_equiv_def, lookup_var_def])))
  >- (
    (* Case 2: before JMP - apply IH *)
    qabbrev_tac `merged = a' with bb_instructions := FRONT a'.bb_instructions ++ b.bb_instructions` >>
    `s'.vs_inst_idx < LENGTH (FRONT a'.bb_instructions)` by gvs[] >>
    sg `get_instruction merged s'.vs_inst_idx = get_instruction a' s'.vs_inst_idx`
    >- (simp[get_instruction_def, Abbr `merged`] >>
        `a'.bb_instructions <> []` by (fs[block_last_jmp_to_def, block_last_inst_def] >>
                                       Cases_on `a'.bb_instructions` >> gvs[]) >>
        simp[rich_listTheory.LENGTH_FRONT] >>
        conj_tac >- (fs[rich_listTheory.LENGTH_FRONT] >> decide_tac) >>
        simp[rich_listTheory.EL_APPEND1, rich_listTheory.FRONT_EL])
    >- (qpat_x_assum `run_block a' s' = _` mp_tac >> simp[Once run_block_def] >>
        qpat_x_assum `run_block merged s' = _` mp_tac >> simp[Once run_block_def] >>
        `step_in_block merged s' = step_in_block a' s'` by simp[step_in_block_def] >>
        gvs[] >> Cases_on `step_in_block a' s'` >> Cases_on `q` >> gvs[] >>
        rpt strip_tac >>
        sg `~r`
        >- (fs[step_in_block_def] >>
            Cases_on `get_instruction a' s'.vs_inst_idx` >> gvs[] >>
            Cases_on `step_inst x s'` >> gvs[] >>
            Cases_on `is_terminator x.inst_opcode` >> gvs[] >>
            fs[block_terminator_last_def] >>
            first_x_assum (qspecl_then [`s'.vs_inst_idx`, `x`] mp_tac) >> simp[] >>
            `a'.bb_instructions <> []` by (fs[block_last_jmp_to_def, block_last_inst_def] >>
                                           Cases_on `a'.bb_instructions` >> gvs[]) >>
            gvs[rich_listTheory.LENGTH_FRONT])
        >- (gvs[] >> Cases_on `v''.vs_halted` >> gvs[] >>
            first_x_assum (qspec_then `LENGTH a'.bb_instructions - v''.vs_inst_idx` mp_tac) >>
            impl_tac
            >- (imp_res_tac step_in_block_inst_idx_succ >> gvs[] >>
                `a'.bb_instructions <> []` by (fs[block_last_jmp_to_def, block_last_inst_def] >>
                                               Cases_on `a'.bb_instructions` >> gvs[]) >>
                gvs[rich_listTheory.LENGTH_FRONT])
            >- (disch_then (qspecl_then [`a'`, `v''`] mp_tac) >>
                impl_tac >> simp[] >>
                impl_tac >- (imp_res_tac step_in_block_inst_idx_succ >> gvs[]) >>
                simp[]))))
QED

(* When s1.vs_prev_bb = SOME old and s2.vs_prev_bb = SOME new, and we have
   the conditions for run_block_replace_label, the current_bb is preserved.
   This handles the case where execution came from the merged predecessor. *)
Theorem run_block_replace_label_current_bb_diff_states:
  !bb s1 s2 old new v1 v2 preds fn.
    state_equiv_cfg s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = SOME old /\
    s2.vs_prev_bb = SOME new /\
    old <> new /\
    preds = pred_labels fn bb.bb_label /\
    MEM old preds /\ ~MEM new preds /\
    phi_block_wf preds bb /\
    block_terminator_last bb /\
    ~MEM old (block_successors bb) /\
    run_block bb s1 = OK v1 /\
    run_block (replace_label_block old new bb) s2 = OK v2 /\
    ~v1.vs_halted ==>
    v1.vs_current_bb = v2.vs_current_bb
Proof
  completeInduct_on `LENGTH bb.bb_instructions - s1.vs_inst_idx` >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `run_block bb s1 = _` mp_tac >> simp[Once run_block_def] >>
  qpat_x_assum `run_block (replace_label_block _ _ _) _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block bb s1` >> Cases_on `q` >> gvs[] >>
  Cases_on `step_in_block (replace_label_block old new bb) s2` >>
  Cases_on `q` >> gvs[] >>
  rpt strip_tac >> rpt (IF_CASES_TAC >> gvs[]) >>
  `r' = r /\ result_equiv_cfg (OK v') (OK v)` by (
    qspecl_then [`bb`, `s1`, `s2`, `old`, `new`, `pred_labels fn bb.bb_label`,
                 `OK v`, `r`, `fn`] mp_tac step_in_block_replace_label >>
    simp[] >> strip_tac >> gvs[]) >>
  Cases_on `v.vs_halted` >> gvs[] >>
  Cases_on `r` >> gvs[]
  >- ((* terminator case *)
    Cases_on `v'.vs_halted` >> gvs[] >>
    gvs[step_in_block_def, replace_label_block_def] >>
    Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[] >>
    gvs[get_instruction_def] >>
    qabbrev_tac `inst = bb.bb_instructions❲s2.vs_inst_idx❳` >>
    `(MAP (replace_label_inst old new) bb.bb_instructions)❲s2.vs_inst_idx❳ =
     replace_label_inst old new inst` by simp[EL_MAP, Abbr `inst`] >>
    gvs[] >>
    Cases_on `step_inst inst s1` >> gvs[] >>
    Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
    Cases_on `step_inst (replace_label_inst old new inst) s2` >> gvs[] >>
    gvs[replace_label_inst_def] >>
    irule step_inst_terminator_same_current_bb >>
    simp[replace_label_inst_def] >>
    qexistsl_tac [`inst`, `new`, `old`, `s1`, `s2`] >> simp[] >>
    gvs[block_successors_def, block_last_inst_def] >>
    sg `inst = LAST bb.bb_instructions`
    >- (
      fs[block_terminator_last_def, get_instruction_def, Abbr `inst`] >>
      simp[GSYM LAST_EL] >>
      `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
      simp[LAST_EL, arithmeticTheory.PRE_SUB1])
    >- (`~NULL bb.bb_instructions` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
        gvs[]))
  >- ((* non-terminator case - use IH *)
    Cases_on `v'.vs_halted` >> gvs[] >>
    first_x_assum irule >> gvs[] >>
    qexistsl_tac [`bb`, `fn`, `new`, `old`, `v`, `v'`] >> simp[] >>
    rpt conj_tac
    >- (imp_res_tac step_in_block_inst_idx_succ >> simp[])
    >- gvs[step_in_block_def, get_instruction_def, AllCaseEqs()]
    >- (imp_res_tac step_in_block_inst_idx_succ >> simp[])
    >- (imp_res_tac step_in_block_preserves_prev_bb >> gvs[])
    >- (imp_res_tac step_in_block_preserves_prev_bb >> gvs[])
    >- gvs[result_equiv_cfg_def, state_equiv_cfg_sym])
QED

(* Helper: Chain run_block_ok_same_current_bb with run_block_replace_label_current_bb_prev_diff
   for the case where we have state_equiv_cfg states with same prev_bb = SOME prev. *)
Theorem run_block_replace_label_current_bb_same_prev:
  !bb s1 s2 old new v v' prev preds.
    state_equiv_cfg s1 s2 /\ s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_prev_bb = SOME prev /\ s1.vs_inst_idx = s2.vs_inst_idx /\
    prev <> old /\ prev <> new /\
    MEM prev preds /\ phi_block_wf preds bb /\ block_terminator_last bb /\
    ~MEM old (block_successors bb) /\
    run_block bb s1 = OK v /\
    run_block (replace_label_block old new bb) s2 = OK v' /\ ~v.vs_halted ==>
    v.vs_current_bb = v'.vs_current_bb
Proof
  rpt strip_tac \\
  `result_equiv_cfg (run_block bb s1) (run_block bb s2)` by
    (irule run_block_state_equiv_cfg >> gvs[]) \\
  Cases_on `run_block bb s2` >> gvs[result_equiv_cfg_def] \\
  rename1 `run_block bb s2 = OK v_mid` \\
  `~v_mid.vs_halted` by gvs[state_equiv_cfg_def] \\
  `v.vs_current_bb = v_mid.vs_current_bb` by
    metis_tac[run_block_ok_same_current_bb] \\
  `v_mid.vs_current_bb = v'.vs_current_bb` by
    metis_tac[run_block_replace_label_current_bb_prev_diff] \\
  simp[]
QED

(* Helper: block_successors of merged block equals block_successors of b *)
Theorem block_successors_merged:
  !a b. b.bb_instructions <> [] ==>
        block_successors (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) =
        block_successors b
Proof
  rw[block_successors_def, block_last_inst_def] >>
  simp[rich_listTheory.LAST_APPEND_NOT_NIL] >>
  gvs[] >> fs[listTheory.NULL_EQ]
QED

(* Helper: current_bb preserved for merged block with replace_label and no_phi *)
Theorem run_block_merged_no_phi_current_bb:
  !a b s1 s2 old new v v'.
    state_equiv_cfg s1 s2 /\ s1.vs_inst_idx = s2.vs_inst_idx /\
    block_terminator_last a /\ block_terminator_last b /\
    a.bb_instructions <> [] /\ b.bb_instructions <> [] /\
    block_has_no_phi (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) /\
    ~MEM old (block_successors b) /\
    run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1 = OK v /\
    run_block (replace_label_block old new
      (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2 = OK v' /\
    ~v.vs_halted ==>
    v.vs_current_bb = v'.vs_current_bb
Proof
  rpt strip_tac >>
  irule run_block_replace_label_no_phi_current_bb >> simp[] >>
  qexists_tac `a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions` >>
  qexistsl_tac [`new`, `old`, `s1`, `s2`] >>
  simp[block_successors_merged] >>
  simp[block_terminator_last_def] >>
  rpt strip_tac >> simp[get_instruction_def] >>
  qpat_x_assum `get_instruction _ _ = _` mp_tac >> simp[get_instruction_def] >>
  strip_tac >> Cases_on `idx < LENGTH (FRONT a.bb_instructions)`
  >- (gvs[rich_listTheory.EL_APPEND1] >>
      `(FRONT a.bb_instructions)❲idx❳ = a.bb_instructions❲idx❳` by
        (irule rich_listTheory.EL_FRONT >> simp[NULL_EQ]) >>
      qpat_x_assum `block_terminator_last a` mp_tac >>
      simp[block_terminator_last_def, get_instruction_def] >>
      strip_tac >> first_x_assum (qspec_then `idx` mp_tac) >> simp[rich_listTheory.LENGTH_FRONT] >>
      gvs[] >> `idx < LENGTH a.bb_instructions` by
        (fs[rich_listTheory.LENGTH_FRONT] >> Cases_on `a.bb_instructions` >> gvs[]) >>
      strip_tac >> gvs[rich_listTheory.LENGTH_FRONT])
  >- (gvs[rich_listTheory.EL_APPEND2] >>
      qpat_x_assum `block_terminator_last b` mp_tac >>
      simp[block_terminator_last_def, get_instruction_def] >>
      strip_tac >> first_x_assum (qspec_then `idx - LENGTH (FRONT a.bb_instructions)` mp_tac) >>
      gvs[])
QED

(* Helper: block_terminator_last of merged block when both a and b have terminators last *)
Theorem block_terminator_last_merged:
  !a b. block_terminator_last a /\ block_terminator_last b /\
        a.bb_instructions <> [] /\ b.bb_instructions <> [] ==>
        block_terminator_last (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)
Proof
  rw[block_terminator_last_def, get_instruction_def] >>
  Cases_on `idx < LENGTH (FRONT a.bb_instructions)`
  >- (
    (* idx in FRONT a - contradiction since FRONT removes the terminator *)
    `(FRONT a.bb_instructions ++ b.bb_instructions)❲idx❳ = (FRONT a.bb_instructions)❲idx❳`
      by simp[rich_listTheory.EL_APPEND1] >>
    `(FRONT a.bb_instructions)❲idx❳ = a.bb_instructions❲idx❳`
      by (irule rich_listTheory.FRONT_EL >> simp[]) >>
    `LENGTH (FRONT a.bb_instructions) = PRE (LENGTH a.bb_instructions)`
      by simp[rich_listTheory.LENGTH_FRONT] >>
    `idx < LENGTH a.bb_instructions` by (Cases_on `a.bb_instructions` >> gvs[]) >>
    `is_terminator a.bb_instructions❲idx❳.inst_opcode` by gvs[] >>
    `idx = LENGTH a.bb_instructions - 1` by (first_x_assum drule >> simp[]) >>
    gvs[])
  >- (
    (* idx in b part - use b's terminator property *)
    `(FRONT a.bb_instructions ++ b.bb_instructions)❲idx❳ =
     b.bb_instructions❲idx - LENGTH (FRONT a.bb_instructions)❳`
      by simp[rich_listTheory.EL_APPEND2] >>
    first_x_assum (qspec_then `idx - LENGTH (FRONT a.bb_instructions)` mp_tac) >>
    simp[] >> gvs[])
QED

(* Helper: current_bb preserved for merged block with replace_label and PHI with prev_bb = NONE
   This combines run_block_merge_blocks_current_bb with run_block_replace_label_current_bb_prev_none *)
Theorem run_block_merged_phi_prev_none_current_bb:
  !a b s v v' v_merged v'' s2 old new.
    (* Block structure preconditions *)
    block_last_jmp_to old a /\
    block_terminator_last a /\ block_terminator_last b /\
    block_has_no_phi b /\
    ~MEM old (block_successors b) /\
    a.bb_instructions <> [] /\ b.bb_instructions <> [] /\
    (* State preconditions *)
    ~s.vs_halted /\ s.vs_inst_idx = 0 /\
    state_equiv_cfg s s2 /\
    s.vs_prev_bb = NONE /\ s2.vs_prev_bb = NONE /\
    s.vs_inst_idx = s2.vs_inst_idx /\
    (* Execution results *)
    run_block a s = OK v /\ ~v.vs_halted /\
    run_block b v = OK v' /\ ~v'.vs_halted /\
    run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s = OK v_merged /\
    run_block (replace_label_block old new
               (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2 = OK v'' /\
    ~v_merged.vs_halted
  ==>
    v'.vs_current_bb = v''.vs_current_bb
Proof
  rpt strip_tac >>
  (* Step 1: v'.vs_current_bb = v_merged.vs_current_bb *)
  `v'.vs_current_bb = v_merged.vs_current_bb` by metis_tac[run_block_merge_blocks_current_bb] >>
  (* Step 2: v_merged.vs_current_bb = v''.vs_current_bb *)
  qspecl_then [`a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions`,
               `s`, `s2`, `old`, `new`, `v_merged`, `v''`]
    mp_tac run_block_replace_label_current_bb_prev_none >>
  impl_tac
  >- (simp[block_successors_merged] >> rpt conj_tac >> gvs[] >>
      rw[block_terminator_last_def, get_instruction_def] >>
      Cases_on `idx < LENGTH (FRONT a.bb_instructions)`
      >- ((* idx in FRONT a case - contradiction *)
          `(FRONT a.bb_instructions ++ b.bb_instructions)❲idx❳ =
           (FRONT a.bb_instructions)❲idx❳` by simp[rich_listTheory.EL_APPEND1] >>
          `(FRONT a.bb_instructions)❲idx❳ = a.bb_instructions❲idx❳`
            by (irule rich_listTheory.FRONT_EL >> simp[]) >>
          qpat_x_assum `block_terminator_last a` mp_tac >>
          simp[block_terminator_last_def, get_instruction_def] >> strip_tac >>
          `idx < LENGTH a.bb_instructions`
            by (Cases_on `a.bb_instructions` >> gvs[rich_listTheory.LENGTH_FRONT]) >>
          `idx = LENGTH a.bb_instructions - 1` by (first_x_assum irule >> gvs[]) >>
          gvs[rich_listTheory.LENGTH_FRONT])
      >- ((* idx in b part *)
          `(FRONT a.bb_instructions ++ b.bb_instructions)❲idx❳ =
           b.bb_instructions❲idx - LENGTH (FRONT a.bb_instructions)❳`
            by simp[rich_listTheory.EL_APPEND2] >>
          qpat_x_assum `block_terminator_last b` mp_tac >>
          simp[block_terminator_last_def, get_instruction_def] >> strip_tac >>
          `idx - LENGTH (FRONT a.bb_instructions) = LENGTH b.bb_instructions - 1`
            by (first_x_assum irule >> gvs[]) >>
          gvs[]))
  >- simp[]
QED

(* Wrapper with variable names matching scfgMergeCorrectScript proof context *)
Theorem run_block_merged_prev_none_current_bb_wrapper:
  !bb s1 s2 old new v_merged v''.
    state_equiv_cfg s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = NONE /\ s2.vs_prev_bb = NONE /\
    block_terminator_last bb /\
    ~MEM old (block_successors bb) /\
    run_block bb s1 = OK v_merged /\
    run_block (replace_label_block old new bb) s2 = OK v'' /\
    ~v_merged.vs_halted
  ==>
    v_merged.vs_current_bb = v''.vs_current_bb
Proof
  rpt strip_tac >>
  drule_all run_block_replace_label_current_bb_prev_none >> simp[]
QED

(* ===== Jump Threading Helpers ===== *)

(* Key: MEM in block_successors implies last instruction is terminator *)
Theorem block_successors_mem_is_terminator:
  !bb lbl.
    MEM lbl (block_successors bb) ==>
    ?inst. block_last_inst bb = SOME inst /\ is_terminator inst.inst_opcode
Proof
  rpt strip_tac >> gvs[block_successors_def, AllCaseEqs()] >>
  Cases_on `block_last_inst bb` >> gvs[] >>
  CCONTR_TAC >> gvs[get_successors_def]
QED

(* Corollary: block with successors must have non-empty instructions *)
Theorem block_successors_implies_nonempty:
  !bb lbl. MEM lbl (block_successors bb) ==> bb.bb_instructions <> []
Proof
  rpt strip_tac >>
  drule block_successors_mem_is_terminator >> strip_tac >>
  gvs[block_last_inst_def, AllCaseEqs()]
QED

(* LAST of FRONT is second-to-last element *)
Theorem LAST_FRONT_EL:
  !l. LENGTH l >= 2 ==> LAST (FRONT l) = EL (LENGTH l - 2) l
Proof
  rpt strip_tac >> simp[LAST_EL, rich_listTheory.LENGTH_FRONT] >>
  `l <> []` by (Cases_on `l` >> gvs[]) >>
  `~NULL (FRONT l)` by (Cases_on `l` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  simp[LAST_EL, rich_listTheory.LENGTH_FRONT, NULL_EQ] >>
  `FRONT l <> []` by gvs[NULL_EQ] >>
  `LAST (FRONT l) = (FRONT l)❲PRE (LENGTH (FRONT l))❳` by (irule LAST_EL >> gvs[]) >>
  simp[rich_listTheory.LENGTH_FRONT] >>
  `PRE (PRE (LENGTH l)) = LENGTH l - 2` by simp[] >>
  simp[rich_listTheory.EL_FRONT] >>
  `LENGTH l - 2 < LENGTH l - 1` by simp[] >>
  irule rich_listTheory.EL_FRONT >> simp[rich_listTheory.LENGTH_FRONT] >>
  gvs[NULL_EQ] >> Cases_on `LENGTH l` >> gvs[]
QED

(* Helper: step_inst on terminator with label replacement gives state_equiv_cfg results.
   Key insight: state_equiv_cfg ignores vs_current_bb, vs_prev_bb, vs_inst_idx *)
Theorem step_inst_terminator_replace_label_equiv:
  !inst old_lbl new_lbl s.
    is_terminator inst.inst_opcode ==>
    let inst' = replace_label_inst old_lbl new_lbl inst in
    result_equiv_cfg (step_inst inst s) (step_inst inst' s)
Proof
  rpt strip_tac >> gvs[venomInstTheory.is_terminator_def] >>
  Cases_on `inst.inst_opcode` >> gvs[venomInstTheory.is_terminator_def]
  (* JMP *)
  >- (simp[step_inst_def, replace_label_inst_def] >>
      Cases_on `inst.inst_operands` >> simp[result_equiv_cfg_def, replace_label_operand_def] >>
      Cases_on `h` >> simp[result_equiv_cfg_def, replace_label_operand_def] >>
      Cases_on `t` >> simp[result_equiv_cfg_def]
      >- (IF_CASES_TAC >> simp[result_equiv_cfg_def] >>
          irule scfgStateOpsTheory.jump_to_state_equiv_cfg >> simp[state_equiv_cfg_refl])
      >- (IF_CASES_TAC >> simp[result_equiv_cfg_def]))
  (* JNZ - case analysis on 3 operands *)
  >- (simp[step_inst_def, replace_label_inst_def] >>
      Cases_on `inst.inst_operands` >> simp[result_equiv_cfg_def, replace_label_operand_def] >>
      Cases_on `t` >> simp[result_equiv_cfg_def, replace_label_operand_def] >>
      Cases_on `h'` >> simp[result_equiv_cfg_def, replace_label_operand_def] >>
      Cases_on `t'` >> simp[result_equiv_cfg_def, replace_label_operand_def]
      >- (IF_CASES_TAC >> simp[result_equiv_cfg_def])
      >- (Cases_on `h'` >> simp[result_equiv_cfg_def, replace_label_operand_def]
          >- (IF_CASES_TAC >> simp[result_equiv_cfg_def])
          >- (IF_CASES_TAC >> simp[result_equiv_cfg_def])
          >- (Cases_on `t` >> simp[result_equiv_cfg_def, replace_label_operand_def]
              >- (IF_CASES_TAC >> simp[result_equiv_cfg_def]
                  >- (IF_CASES_TAC >> simp[result_equiv_cfg_def]
                      >- (simp[scfgMergeHelpersTheory.eval_operand_replace_label] >>
                          Cases_on `eval_operand h s` >> simp[result_equiv_cfg_def] >>
                          irule scfgStateOpsTheory.jump_to_state_equiv_cfg >> simp[state_equiv_cfg_refl])
                      >- (simp[scfgMergeHelpersTheory.eval_operand_replace_label] >>
                          Cases_on `eval_operand h s` >> simp[result_equiv_cfg_def] >>
                          IF_CASES_TAC >> simp[result_equiv_cfg_def] >>
                          TRY (irule scfgStateOpsTheory.jump_to_state_equiv_cfg >> simp[state_equiv_cfg_refl])))
                  >- (IF_CASES_TAC >> simp[scfgMergeHelpersTheory.eval_operand_replace_label, result_equiv_cfg_def]
                      >- (Cases_on `eval_operand h s` >> simp[result_equiv_cfg_def] >>
                          IF_CASES_TAC >> simp[result_equiv_cfg_def, state_equiv_cfg_refl] >>
                          irule scfgStateOpsTheory.jump_to_state_equiv_cfg >> simp[state_equiv_cfg_refl])
                      >- simp[result_equiv_cfg_refl]))
              >- (IF_CASES_TAC >> simp[result_equiv_cfg_def] >>
                  IF_CASES_TAC >> simp[result_equiv_cfg_def]))))
  (* DJMP - unimplemented *)
  >- simp[step_inst_def, replace_label_inst_def, result_equiv_cfg_def]
  (* RET - unimplemented *)
  >- simp[step_inst_def, replace_label_inst_def, result_equiv_cfg_def]
  (* RETURN *)
  >- simp[step_inst_def, replace_label_inst_def, result_equiv_cfg_def,
          state_equiv_cfg_def, stateEquivTheory.var_equiv_def, venomStateTheory.halt_state_def]
  (* REVERT *)
  >- simp[step_inst_def, replace_label_inst_def, result_equiv_cfg_def,
          state_equiv_cfg_def, stateEquivTheory.var_equiv_def, venomStateTheory.revert_state_def]
  (* STOP *)
  >- simp[step_inst_def, replace_label_inst_def, result_equiv_cfg_def,
          state_equiv_cfg_def, stateEquivTheory.var_equiv_def, venomStateTheory.halt_state_def]
  (* SINK *)
  >- simp[step_inst_def, replace_label_inst_def, result_equiv_cfg_def,
          state_equiv_cfg_def, stateEquivTheory.var_equiv_def, venomStateTheory.halt_state_def]
QED

(* For merge_jump: running a then b (jump-only) is equivalent to running a'
   where a' is a with the last instruction's target changed from b_lbl to c_lbl *)
Theorem run_block_merge_jump_equiv:
  !a b b_lbl c_lbl s.
    block_terminator_last a /\
    jump_only_target b = SOME c_lbl /\
    MEM b_lbl (block_successors a) /\
    ~s.vs_halted /\
    s.vs_inst_idx <= LENGTH (BUTLAST a.bb_instructions)
  ==>
    let a' = a with bb_instructions :=
      update_last_inst (replace_label_inst b_lbl c_lbl) a.bb_instructions in
    result_equiv_cfg
      (case run_block a s of
         OK v => if v.vs_halted then Halt v else run_block b v
       | Halt v => Halt v
       | Revert v => Revert v
       | Error e => Error e)
      (run_block a' s)
Proof
  completeInduct_on `LENGTH a.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >> gvs[] >>
  Cases_on `s.vs_inst_idx < LENGTH (FRONT a.bb_instructions)`
  (* Not at terminator - same instruction on both sides *)
  >- (
    simp[Once run_block_def] >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
    qabbrev_tac `a' = a with bb_instructions :=
      update_last_inst (replace_label_inst b_lbl c_lbl) a.bb_instructions` >>
    sg `get_instruction a' s.vs_inst_idx = get_instruction a s.vs_inst_idx`
    >- (simp[get_instruction_def, Abbr `a'`, scfgMergeHelpersTheory.update_last_inst_length] >>
        `a.bb_instructions <> []` by
          (fs[block_successors_def, block_last_inst_def] >>
           Cases_on `a.bb_instructions` >> gvs[]) >>
        IF_CASES_TAC >> simp[] >>
        `s.vs_inst_idx < LENGTH a.bb_instructions - 1` by fs[rich_listTheory.LENGTH_FRONT] >>
        drule_all scfgMergeHelpersTheory.update_last_inst_el_unchanged >> simp[])
    >- (`step_in_block a' s = step_in_block a s` by simp[step_in_block_def] >>
        gvs[] >> Cases_on `step_in_block a s` >> Cases_on `q` >> gvs[result_equiv_cfg_def]
        >- (IF_CASES_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_refl] >>
            IF_CASES_TAC >> gvs[result_equiv_cfg_def]
            >- ((* is_term=T at non-last position - contradiction *)
                qpat_x_assum `step_in_block a s = _` mp_tac >> simp[step_in_block_def] >>
                strip_tac >> gvs[AllCaseEqs()] >> fs[block_terminator_last_def] >>
                `s.vs_inst_idx = LENGTH a.bb_instructions - 1` by (first_x_assum irule >> simp[]) >>
                fs[rich_listTheory.LENGTH_FRONT] >>
                `a.bb_instructions <> []` by
                  (fs[block_successors_def, block_last_inst_def] >>
                   Cases_on `a.bb_instructions` >> gvs[]) >>
                gvs[rich_listTheory.LENGTH_FRONT])
            >- ((* use IH *)
                `v.vs_inst_idx = s.vs_inst_idx + 1` by (imp_res_tac step_in_block_inst_idx_succ >> fs[]) >>
                first_x_assum (qspec_then `LENGTH a.bb_instructions - v.vs_inst_idx` mp_tac) >>
                impl_tac
                >- (`a.bb_instructions <> []` by
                      (fs[block_successors_def, block_last_inst_def] >>
                       Cases_on `a.bb_instructions` >> gvs[]) >>
                    fs[rich_listTheory.LENGTH_FRONT] >> decide_tac)
                >- (strip_tac >> first_x_assum (qspecl_then [`a`, `v`] mp_tac) >> simp[] >>
                    strip_tac >> first_x_assum (qspecl_then [`b`, `b_lbl`, `c_lbl`] mp_tac) >> simp[])))
        >- simp[state_equiv_cfg_refl]
        >- simp[state_equiv_cfg_refl]))
  (* At terminator - boundary case *)
  >- (`s.vs_inst_idx = LENGTH (FRONT a.bb_instructions)` by decide_tac >>
      `a.bb_instructions <> []` by
        (fs[block_successors_def, block_last_inst_def] >> Cases_on `a.bb_instructions` >> gvs[]) >>
      simp[Once run_block_def] >>
      CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
      qabbrev_tac `a' = a with bb_instructions :=
        update_last_inst (replace_label_inst b_lbl c_lbl) a.bb_instructions` >>
      drule_all block_successors_mem_is_terminator >> strip_tac >>
      sg `get_instruction a s.vs_inst_idx = SOME inst`
      >- (simp[get_instruction_def, rich_listTheory.LENGTH_FRONT] >>
          gvs[block_last_inst_def, AllCaseEqs()] >> simp[listTheory.LAST_EL] >>
          Cases_on `a.bb_instructions` >> gvs[])
      >- (sg `get_instruction a' s.vs_inst_idx = SOME (replace_label_inst b_lbl c_lbl inst)`
          >- (simp[get_instruction_def, Abbr `a'`,
                   scfgMergeHelpersTheory.update_last_inst_length,
                   rich_listTheory.LENGTH_FRONT] >>
              gvs[block_last_inst_def, AllCaseEqs()] >>
              simp[scfgMergeHelpersTheory.update_last_inst_el_last] >>
              Cases_on `a.bb_instructions` >> gvs[])
          >- (simp[step_in_block_def] >>
              `is_terminator (replace_label_inst b_lbl c_lbl inst).inst_opcode` by
                simp[scfgDefsTheory.replace_label_inst_def] >>
              simp[] >>
              `result_equiv_cfg (step_inst inst s)
                 (step_inst (replace_label_inst b_lbl c_lbl inst) s)` by
                (qspecl_then [`inst`, `b_lbl`, `c_lbl`, `s`] mp_tac
                   step_inst_terminator_replace_label_equiv >> simp[]) >>
              Cases_on `step_inst inst s` >> gvs[result_equiv_cfg_def]
              >- (Cases_on `step_inst (replace_label_inst b_lbl c_lbl inst) s` >>
                  gvs[result_equiv_cfg_def] >>
                  IF_CASES_TAC >> gvs[result_equiv_cfg_def]
                  >- (`v'.vs_halted` by gvs[state_equiv_cfg_def] >>
                      simp[result_equiv_cfg_def])
                  >- (`~v'.vs_halted` by gvs[state_equiv_cfg_def] >> simp[] >>
                      (* v.vs_inst_idx = 0 from terminator OK result *)
                      `v.vs_inst_idx = 0` by
                        metis_tac[venomSemPropsTheory.step_inst_terminator_ok_inst_idx_zero] >>
                      (* Expand jump_only_target to get b's structure *)
                      gvs[jump_only_target_def, AllCaseEqs()] >>
                      simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
                      simp[EVAL ``is_terminator JMP``, step_inst_def] >>
                      `~(jump_to c_lbl v).vs_halted` by simp[jump_to_def] >>
                      simp[result_equiv_cfg_def] >>
                      irule scfgStateOpsTheory.state_equiv_cfg_jump_to_left >> simp[]))
              >- (Cases_on `step_inst (replace_label_inst b_lbl c_lbl inst) s` >>
                  gvs[result_equiv_cfg_def])
              >- (Cases_on `step_inst (replace_label_inst b_lbl c_lbl inst) s` >>
                  gvs[result_equiv_cfg_def])
              >- (Cases_on `step_inst (replace_label_inst b_lbl c_lbl inst) s` >>
                  gvs[result_equiv_cfg_def]))))
QED

(* Helper for IH applications in merge proofs: if block successors are disjoint from a list,
   the resulting current_bb is not in that list *)
Theorem run_block_ok_vs_current_bb_not_in_list:
  !fn bb s s' lbls.
    cfg_wf fn /\ MEM bb fn.fn_blocks /\
    run_block bb s = OK s' /\ ~s'.vs_halted /\
    DISJOINT (set (block_successors bb)) (set lbls) ==>
    ~MEM s'.vs_current_bb lbls
Proof
  rpt strip_tac >>
  drule_all run_block_ok_successor >> strip_tac >>
  fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION, pred_setTheory.IN_INTER] >>
  first_x_assum (qspec_then `s'.vs_current_bb` mp_tac) >> simp[]
QED

(* If a block has exactly one predecessor different from itself, it doesn't jump to itself *)
Theorem block_no_self_successor:
  !fn bb lbl p.
    MEM bb fn.fn_blocks /\
    bb.bb_label = lbl /\
    pred_labels fn lbl = [p] /\
    p <> lbl ==>
    ~MEM lbl (block_successors bb)
Proof
  rpt strip_tac >>
  gvs[scfgDefsTheory.pred_labels_def, listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  `MEM bb (FILTER (\bb'. MEM bb.bb_label (block_successors bb')) fn.fn_blocks)` by
    simp[listTheory.MEM_FILTER] >>
  gvs[]
QED

(* ===== replace_phi_in_block when prev_bb <> SOME old ===== *)

(* For non-PHI instructions, replace_label_in_phi is identity *)
Theorem replace_label_in_phi_non_phi:
  !inst old new. inst.inst_opcode <> PHI ==> replace_label_in_phi old new inst = inst
Proof
  rpt strip_tac >> simp[scfgDefsTheory.replace_label_in_phi_def]
QED

(* step_in_block helper for replace_phi_in_block when prev <> old and prev <> new *)
Theorem step_in_block_replace_phi_in_block_prev_diff:
  !bb s old new preds res is_term.
    step_in_block bb s = (res, is_term) /\
    s.vs_prev_bb <> SOME old /\
    s.vs_prev_bb <> SOME new /\
    phi_block_wf preds bb ==>
    ?res'. step_in_block (replace_phi_in_block old new bb) s = (res', is_term) /\
           result_equiv_cfg res res'
Proof
  rpt strip_tac >> simp[step_in_block_def, replace_phi_in_block_def] >>
  qpat_x_assum `step_in_block _ _ = _` mp_tac >> simp[step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[get_instruction_def]
  >- simp[result_equiv_cfg_def]
  >- (
    qabbrev_tac `inst = EL s.vs_inst_idx bb.bb_instructions` >>
    `(MAP (replace_label_in_phi old new) bb.bb_instructions)❲s.vs_inst_idx❳ =
     replace_label_in_phi old new inst` by simp[Abbr `inst`, EL_MAP] >>
    simp[] >>
    Cases_on `inst.inst_opcode = PHI`
    >- ((* PHI case: use resolve_phi_replace_label_other *)
      REVERSE (simp[replace_label_in_phi_def] >> strip_tac >>
        qexists_tac `res` >> simp[result_equiv_cfg_refl]) >>
      simp[step_inst_def, is_terminator_def] >>
      Cases_on `s.vs_prev_bb` >> gvs[]
      >- gvs[step_inst_def, is_terminator_def]
      >- (
        `MEM inst bb.bb_instructions` by (simp[Abbr `inst`, MEM_EL] >>
          qexists_tac `s.vs_inst_idx` >> simp[]) >>
        `phi_inst_wf preds inst` by metis_tac[phi_block_wf_inst] >>
        gvs[phi_inst_wf_def] >>
        `resolve_phi x (MAP (replace_label_operand old new) inst.inst_operands) =
         resolve_phi x inst.inst_operands` by
          (irule scfgPhiLemmasTheory.resolve_phi_replace_label_other >> simp[]) >>
        simp[] >> gvs[step_inst_def, is_terminator_def]))
    >- ((* Non-PHI case: replace_label_in_phi is identity *)
      simp[replace_label_in_phi_def] >> simp[result_equiv_cfg_refl]))
QED

(* When we didn't arrive from old OR new, replacing old->new in PHIs doesn't change semantics *)
Theorem run_block_replace_phi_in_block_prev_not_old:
  !bb s old new preds.
    s.vs_prev_bb <> SOME old /\
    s.vs_prev_bb <> SOME new /\
    phi_block_wf preds bb /\
    ~MEM old (block_successors bb) ==>
    result_equiv_cfg (run_block bb s)
                     (run_block (replace_phi_in_block old new bb) s)
Proof
  recInduct run_block_ind >> rpt strip_tac >>
  Cases_on `step_in_block bb s` >>
  rename1 `step_in_block bb s = (res, is_term)` >>
  (* Apply step_in_block helper - need to handle variable naming carefully *)
  `?res'. step_in_block (replace_phi_in_block old new bb) s = (res', is_term) /\
          result_equiv_cfg res res'` by (
    irule step_in_block_replace_phi_in_block_prev_diff >> simp[] >>
    qexists_tac `preds` >> simp[]) >>
  once_rewrite_tac[run_block_def] >> gvs[] >>
  Cases_on `res` >> Cases_on `res'` >> gvs[result_equiv_cfg_def] >>
  (* OK case: handle halted and terminator checks *)
  IF_CASES_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_def] >>
  IF_CASES_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_def] >>
  (* Use transitivity *)
  irule result_equiv_cfg_trans >>
  qexists_tac `run_block (replace_phi_in_block old new bb) v` >> conj_tac
  >- (first_x_assum irule >> simp[] >>
      `v.vs_prev_bb = s.vs_prev_bb` by metis_tac[venomSemPropsTheory.step_in_block_preserves_prev_bb] >>
      gvs[] >> qexists_tac `preds` >> simp[])
  >- (irule scfgEquivTheory.run_block_state_equiv_cfg >> simp[state_equiv_cfg_def] >>
      conj_tac >- metis_tac[scfgEquivTheory.step_in_block_inst_idx_succ] >>
      metis_tac[venomSemPropsTheory.step_in_block_preserves_prev_bb])
QED

(* Helper: replace_phi_in_block preserves vs_current_bb since terminator is unchanged *)
Theorem run_block_replace_phi_vs_current_bb:
  !bb s old new v v' preds.
    run_block bb s = OK v /\
    run_block (replace_phi_in_block old new bb) s = OK v' /\
    s.vs_prev_bb <> SOME old /\
    s.vs_prev_bb <> SOME new /\
    phi_block_wf preds bb /\
    ~MEM old (block_successors bb) /\
    ~v.vs_halted /\ ~v'.vs_halted ==>
    v.vs_current_bb = v'.vs_current_bb
Proof
  (* Key insight: replace_phi_in_block only changes PHI operands, not terminators.
     The terminator determines vs_current_bb, so it must be unchanged. *)
  recInduct run_block_ind >> rpt strip_tac >>
  Cases_on `step_in_block bb s` >>
  rename1 `step_in_block bb s = (res, is_term)` >>
  Cases_on `step_in_block (replace_phi_in_block old new bb) s` >>
  rename1 `step_in_block (replace_phi_in_block old new bb) s = (res', is_term')` >>
  (* Establish key facts: same termination and result_equiv_cfg *)
  sg `is_term' = is_term /\ result_equiv_cfg res res'`
  >- (qspecl_then [`bb`, `s`, `old`, `new`, `preds`, `res`, `is_term`]
        mp_tac step_in_block_replace_phi_in_block_prev_diff >>
      simp[] >> strip_tac >> gvs[])
  >- (Cases_on `is_term`
      (* Terminating case: same terminator instruction gives same vs_current_bb *)
      >- (gvs[Once run_block_def] >>
          Cases_on `res` >> gvs[result_equiv_cfg_def] >>
          gvs[AllCaseEqs()] >>
          qpat_x_assum `run_block (replace_phi_in_block _ _ _) _ = _` mp_tac >>
          simp[Once run_block_def] >> strip_tac >>
          Cases_on `res'` >> gvs[result_equiv_cfg_def, AllCaseEqs()] >>
          gvs[step_in_block_def] >>
          Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[] >>
          `get_instruction (replace_phi_in_block old new bb) s.vs_inst_idx =
           SOME (replace_label_in_phi old new x)` by
            (gvs[get_instruction_def, replace_phi_in_block_def] >>
             simp[listTheory.EL_MAP]) >>
          Cases_on `step_inst x s` >> gvs[AllCaseEqs()] >>
          `x.inst_opcode <> PHI` by (CCONTR_TAC >> gvs[is_terminator_def]) >>
          `replace_label_in_phi old new x = x` by simp[replace_label_in_phi_def] >>
          gvs[])
      (* Non-terminating case: use IH *)
      >- (gvs[step_in_block_def] >>
          Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[] >>
          `get_instruction (replace_phi_in_block old new bb) s.vs_inst_idx =
           SOME (replace_label_in_phi old new x)` by
            (gvs[get_instruction_def, replace_phi_in_block_def] >>
             simp[listTheory.EL_MAP]) >>
          Cases_on `step_inst x s` >> gvs[AllCaseEqs()] >>
          Cases_on `x.inst_opcode = PHI`
          (* PHI case: need to show PHI evaluation same when prev_bb ≠ old/new *)
          >- cheat
          (* Non-PHI case: instruction unchanged, so intermediate states equal *)
          >- (`replace_label_in_phi old new x = x` by simp[replace_label_in_phi_def] >>
              gvs[] >>
              qpat_x_assum `run_block bb s = OK v` mp_tac >>
              simp[Once run_block_def] >> strip_tac >>
              gvs[step_in_block_def, AllCaseEqs()] >>
              qpat_x_assum `run_block (replace_phi_in_block _ _ _) s = OK v'` mp_tac >>
              simp[Once run_block_def, step_in_block_def] >> strip_tac >>
              gvs[AllCaseEqs()] >>
              first_x_assum (qspecl_then [`old`, `new`, `v'`, `preds`] mp_tac) >>
              simp[] >> impl_tac
              >- (conj_tac >> simp[next_inst_def] >>
                  metis_tac[venomSemPropsTheory.step_inst_preserves_prev_bb])
              >- simp[])))
QED

val _ = export_theory();
