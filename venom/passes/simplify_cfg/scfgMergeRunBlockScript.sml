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

(* Helper: Running block b from any index is equivalent to running merged from corresponding index
   when merged.bb_instructions = prefix ++ b.bb_instructions and b has no PHI.
   The key invariant: s2.vs_inst_idx = s1.vs_inst_idx + LENGTH prefix *)
Theorem run_block_suffix_no_phi:
  !b prefix s1 s2 merged.
    merged.bb_instructions = prefix ++ b.bb_instructions /\
    state_equiv_cfg s1 s2 /\
    s2.vs_inst_idx = s1.vs_inst_idx + LENGTH prefix /\
    block_has_no_phi b
  ==>
    result_equiv_cfg (run_block b s1) (run_block merged s2)
Proof
  cheat
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
    >- (qexists_tac `FRONT a.bb_instructions` >> simp[Abbr `merged`, Abbr `s'`])
    >- simp[Abbr `s'`, state_equiv_cfg_def, stateEquivTheory.var_equiv_def, lookup_var_def])
QED

val _ = export_theory();
