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

val _ = export_theory();
