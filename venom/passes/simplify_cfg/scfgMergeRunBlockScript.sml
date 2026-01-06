(* 
 * Simplify-CFG Merge Run-Block Helpers
 *
 * run_block/step_in_block lemmas for label replacement.
 *)

Theory scfgMergeRunBlock
Ancestors
  scfgMergeHelpers

(* ===== replace_label_block preserves execution ===== *)

Theorem step_in_block_replace_label:
  !bb s1 s2 old new preds res is_term.
    step_in_block fn bb s1 = (res, is_term) /\
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
    ?res'. step_in_block fn (replace_label_block old new bb) s2 = (res', is_term) /\
           result_equiv_cfg res' res
Proof
  rpt strip_tac >>
  simp[step_in_block_def, replace_label_block_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >> simp[]
  >- (
    qexists_tac `Error "block not terminated"` >>
    qpat_x_assum `step_in_block fn bb s1 = _` mp_tac >>
    qpat_x_assum `get_instruction bb s1.vs_inst_idx = NONE` mp_tac >>
    simp[step_in_block_def, get_instruction_def, LENGTH_MAP, result_equiv_cfg_def]
  )
  >- (
    rename1 `get_instruction bb _ = SOME inst` >>
    qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
    simp[get_instruction_def] >> strip_tac >>
    `MEM inst bb.bb_instructions` by metis_tac[MEM_EL] >>
    `get_instruction (bb with bb_instructions := MAP (replace_label_inst old new) bb.bb_instructions)
                     s2.vs_inst_idx = SOME (replace_label_inst old new inst)` by
      (rw[get_instruction_def] >> simp[EL_MAP]) >>
    simp[] >>
    Cases_on `inst.inst_opcode = PHI`
    >- (
      `result_equiv_cfg (step_inst inst s1)
                        (step_inst (replace_label_inst old new inst) s2)` by
        (irule step_inst_replace_label_phi >> simp[] >>
         drule_all phi_block_wf_inst >> simp[]) >>
      Cases_on `step_inst inst s1` >>
      Cases_on `step_inst (replace_label_inst old new inst) s2` >>
      gvs[result_equiv_cfg_def] >>
      rename1 `step_inst inst s1 = OK v1` >>
      rename1 `step_inst (replace_label_inst old new inst) s2 = OK v2` >>
      Cases_on `is_terminator inst.inst_opcode` >>
      qexists_tac `OK v2` >>
      simp[result_equiv_cfg_def]
    )
    >- (
      `result_equiv_cfg (step_inst inst s1)
                        (step_inst (replace_label_inst old new inst) s2)` by
        (irule step_inst_replace_label_non_phi >> simp[]) >>
      Cases_on `step_inst inst s1` >>
      Cases_on `step_inst (replace_label_inst old new inst) s2` >>
      gvs[result_equiv_cfg_def] >>
      rename1 `step_inst inst s1 = OK v1` >>
      rename1 `step_inst (replace_label_inst old new inst) s2 = OK v2` >>
      Cases_on `is_terminator inst.inst_opcode` >>
      qexists_tac `OK v2` >>
      simp[result_equiv_cfg_def]
    )
  )
QED

Theorem run_block_replace_label:
  !bb s1 s2 old new preds.
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
    result_equiv_cfg (run_block fn bb s1)
                     (run_block fn (replace_label_block old new bb) s2)
Proof
  ho_match_mp_tac run_block_ind >>
  rpt gen_tac >> strip_tac >>
  rpt strip_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s1` >> Cases_on `q` >> simp[] >>
  strip_tac >>
  drule_all step_in_block_replace_label >> strip_tac >>
  gvs[] >>
  Cases_on `res'` >> gvs[result_equiv_cfg_def]
  >- (qexists_tac `Halt v'` >> gvs[result_equiv_cfg_def])
  >- (qexists_tac `Revert v'` >> gvs[result_equiv_cfg_def])
  >- (qexists_tac `Error e'` >> gvs[result_equiv_cfg_def])
  >- (
    rename1 `res' = OK v'` >>
    Cases_on `v'.vs_halted` >> gvs[]
    >- (qexists_tac `Halt v'` >> gvs[result_equiv_cfg_def])
    >- (
      Cases_on `r` >> gvs[]
      >- (
        qexists_tac `OK v'` >>
        gvs[result_equiv_cfg_def]
      )
      >- (
        `v.vs_prev_bb = s1.vs_prev_bb` by (
          qpat_x_assum `step_in_block fn bb s1 = (OK v,F)` mp_tac >>
          simp[step_in_block_def] >>
          Cases_on `get_instruction bb s1.vs_inst_idx` >> simp[] >>
          Cases_on `step_inst x s1` >> gvs[] >>
          gvs[next_inst_def] >>
          drule_all step_inst_preserves_prev_bb >> simp[]
        ) >>
        `v.vs_current_bb = s1.vs_current_bb` by (
          qpat_x_assum `step_in_block fn bb s1 = (OK v,F)` mp_tac >>
          simp[step_in_block_def] >>
          Cases_on `get_instruction bb s1.vs_inst_idx` >> simp[] >>
          Cases_on `step_inst x s1` >> gvs[] >>
          gvs[next_inst_def] >>
          drule_all step_inst_preserves_current_bb >> simp[]
        ) >>
        `v.vs_inst_idx = s1.vs_inst_idx + 1` by (
          qpat_x_assum `step_in_block fn bb s1 = (OK v,F)` mp_tac >>
          simp[step_in_block_def] >>
          Cases_on `get_instruction bb s1.vs_inst_idx` >> simp[] >>
          Cases_on `step_inst x s1` >> gvs[] >>
          gvs[next_inst_def] >>
          drule_all step_inst_preserves_inst_idx >> simp[]
        ) >>
        `v'.vs_prev_bb = s2.vs_prev_bb` by (
          qpat_x_assum
            `step_in_block fn (replace_label_block old new bb) s2 = (OK v',F)` mp_tac >>
          simp[step_in_block_def, replace_label_block_def] >>
          Cases_on `get_instruction bb s2.vs_inst_idx` >> simp[] >>
          rename1 `get_instruction bb _ = SOME inst` >>
          qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
          simp[get_instruction_def] >> strip_tac >>
          `get_instruction (bb with bb_instructions := MAP (replace_label_inst old new) bb.bb_instructions)
                           s2.vs_inst_idx = SOME (replace_label_inst old new inst)` by
            (rw[get_instruction_def] >> simp[EL_MAP]) >>
          simp[] >>
          Cases_on `step_inst (replace_label_inst old new inst) s2` >> gvs[] >>
          gvs[next_inst_def] >>
          drule_all step_inst_preserves_prev_bb >> simp[]
        ) >>
        `v'.vs_current_bb = s2.vs_current_bb` by (
          qpat_x_assum
            `step_in_block fn (replace_label_block old new bb) s2 = (OK v',F)` mp_tac >>
          simp[step_in_block_def, replace_label_block_def] >>
          Cases_on `get_instruction bb s2.vs_inst_idx` >> simp[] >>
          rename1 `get_instruction bb _ = SOME inst` >>
          qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
          simp[get_instruction_def] >> strip_tac >>
          `get_instruction (bb with bb_instructions := MAP (replace_label_inst old new) bb.bb_instructions)
                           s2.vs_inst_idx = SOME (replace_label_inst old new inst)` by
            (rw[get_instruction_def] >> simp[EL_MAP]) >>
          simp[] >>
          Cases_on `step_inst (replace_label_inst old new inst) s2` >> gvs[] >>
          gvs[next_inst_def] >>
          drule_all step_inst_preserves_current_bb >> simp[]
        ) >>
        `v'.vs_inst_idx = s2.vs_inst_idx + 1` by (
          qpat_x_assum
            `step_in_block fn (replace_label_block old new bb) s2 = (OK v',F)` mp_tac >>
          simp[step_in_block_def, replace_label_block_def] >>
          Cases_on `get_instruction bb s2.vs_inst_idx` >> simp[] >>
          rename1 `get_instruction bb _ = SOME inst` >>
          qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
          simp[get_instruction_def] >> strip_tac >>
          `get_instruction (bb with bb_instructions := MAP (replace_label_inst old new) bb.bb_instructions)
                           s2.vs_inst_idx = SOME (replace_label_inst old new inst)` by
            (rw[get_instruction_def] >> simp[EL_MAP]) >>
          simp[] >>
          Cases_on `step_inst (replace_label_inst old new inst) s2` >> gvs[] >>
          gvs[next_inst_def] >>
          drule_all step_inst_preserves_inst_idx >> simp[]
        ) >>
        `state_equiv_cfg v v'` by
          (gvs[result_equiv_cfg_def]) >>
        `v' = v` by (irule state_equiv_cfg_ctrl_eq >> simp[]) >>
        first_x_assum (qspec_then `v` mp_tac) >> simp[]
      )
    )
  )
QED

Theorem run_block_replace_label_no_phi_old:
  !bb s1 s2 old new.
    state_equiv_cfg s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
            ~MEM (Label old) inst.inst_operands)
  ==>
    result_equiv_cfg (run_block fn bb s1)
                     (run_block fn (replace_label_block old new bb) s2)
Proof
  ho_match_mp_tac run_block_ind >>
  rpt gen_tac >> strip_tac >>
  rpt strip_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s1` >> Cases_on `q` >> simp[] >>
  strip_tac >>
  qpat_x_assum `step_in_block fn bb s1 = (OK v,r)` mp_tac >>
  simp[step_in_block_def, replace_label_block_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >> simp[]
  >- (
    qexists_tac `Error "block not terminated"` >>
    qpat_x_assum `get_instruction bb s1.vs_inst_idx = NONE` mp_tac >>
    simp[step_in_block_def, get_instruction_def, LENGTH_MAP,
         result_equiv_cfg_def]
  )
  >- (
    rename1 `get_instruction bb _ = SOME inst` >>
    qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
    simp[get_instruction_def] >> strip_tac >>
    `MEM inst bb.bb_instructions` by metis_tac[MEM_EL] >>
    `get_instruction (bb with bb_instructions := MAP (replace_label_inst old new) bb.bb_instructions)
                     s2.vs_inst_idx = SOME (replace_label_inst old new inst)` by
      (rw[get_instruction_def] >> simp[EL_MAP]) >>
    simp[] >>
    `result_equiv_cfg (step_inst inst s1)
                      (step_inst (replace_label_inst old new inst) s2)` by
      (irule step_inst_replace_label_no_phi_old >> simp[]) >>
    Cases_on `step_inst inst s1` >>
    Cases_on `step_inst (replace_label_inst old new inst) s2` >>
    gvs[result_equiv_cfg_def] >>
    rename1 `step_inst inst s1 = OK v1` >>
    rename1 `step_inst (replace_label_inst old new inst) s2 = OK v2` >>
    Cases_on `is_terminator inst.inst_opcode` >>
    gvs[result_equiv_cfg_def]
    >- (
      qexists_tac `OK v2` >>
      simp[result_equiv_cfg_def]
    )
    >- (
      `state_equiv_cfg (next_inst v1) (next_inst v2)` by
        (irule next_inst_state_equiv_cfg >> simp[result_equiv_cfg_def]) >>
      `v1.vs_inst_idx = s1.vs_inst_idx` by
        (drule_all step_inst_preserves_inst_idx >> simp[]) >>
      `v2.vs_inst_idx = s2.vs_inst_idx` by
        (drule_all step_inst_preserves_inst_idx >> simp[]) >>
      first_x_assum (qspecl_then [`next_inst v1`, `next_inst v2`] mp_tac) >>
      simp[next_inst_def]
    )
  )
QED

Theorem run_block_replace_label_prev_diff:
  !bb s old new preds prev.
    s.vs_prev_bb = SOME prev /\
    prev <> old /\
    preds = pred_labels fn bb.bb_label /\
    MEM prev preds /\
    phi_block_wf preds bb
  ==>
    result_equiv_cfg (run_block fn bb s)
                     (run_block fn (replace_label_block old new bb) s)
Proof
  ho_match_mp_tac run_block_ind >>
  rpt gen_tac >> strip_tac >>
  rpt strip_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s` >> Cases_on `q` >> simp[] >>
  strip_tac >>
  qpat_x_assum `step_in_block fn bb s = (OK v,r)` mp_tac >>
  simp[step_in_block_def, replace_label_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[]
  >- (
    qexists_tac `Error "block not terminated"` >>
    qpat_x_assum `get_instruction bb s.vs_inst_idx = NONE` mp_tac >>
    simp[step_in_block_def, get_instruction_def, LENGTH_MAP,
         result_equiv_cfg_def]
  )
  >- (
    rename1 `get_instruction bb _ = SOME inst` >>
    qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
    simp[get_instruction_def] >> strip_tac >>
    `MEM inst bb.bb_instructions` by metis_tac[MEM_EL] >>
    `get_instruction (bb with bb_instructions := MAP (replace_label_inst old new) bb.bb_instructions)
                     s.vs_inst_idx = SOME (replace_label_inst old new inst)` by
      (rw[get_instruction_def] >> simp[EL_MAP]) >>
    simp[] >>
    Cases_on `inst.inst_opcode = PHI`
    >- (
      `result_equiv_cfg (step_inst inst s)
                        (step_inst (replace_label_inst old new inst) s)` by
        (irule step_inst_replace_label_phi_prev_diff >> simp[] >>
         drule_all phi_block_wf_inst >> simp[]) >>
      Cases_on `step_inst inst s` >>
      Cases_on `step_inst (replace_label_inst old new inst) s` >>
      gvs[result_equiv_cfg_def] >>
      rename1 `step_inst inst s = OK v1` >>
      rename1 `step_inst (replace_label_inst old new inst) s = OK v2` >>
      Cases_on `is_terminator inst.inst_opcode` >>
      gvs[result_equiv_cfg_def]
      >- (
        qexists_tac `OK v2` >>
        simp[result_equiv_cfg_def]
      )
      >- (
        `state_equiv_cfg (next_inst v1) (next_inst v2)` by
          (irule next_inst_state_equiv_cfg >> simp[result_equiv_cfg_def]) >>
        `v1.vs_prev_bb = s.vs_prev_bb` by
          (drule_all step_inst_preserves_prev_bb >> simp[]) >>
        `v2.vs_prev_bb = s.vs_prev_bb` by
          (drule_all step_inst_preserves_prev_bb >> simp[]) >>
        first_x_assum (qspec_then `next_inst v1` mp_tac) >>
        simp[next_inst_def]
      )
    )
    >- (
      `result_equiv_cfg (step_inst inst s)
                        (step_inst (replace_label_inst old new inst) s)` by
        (irule step_inst_replace_label_non_phi >> simp[state_equiv_cfg_refl]) >>
      Cases_on `step_inst inst s` >>
      Cases_on `step_inst (replace_label_inst old new inst) s` >>
      gvs[result_equiv_cfg_def] >>
      rename1 `step_inst inst s = OK v1` >>
      rename1 `step_inst (replace_label_inst old new inst) s = OK v2` >>
      Cases_on `is_terminator inst.inst_opcode` >>
      gvs[result_equiv_cfg_def]
      >- (
        qexists_tac `OK v2` >>
        simp[result_equiv_cfg_def]
      )
      >- (
        `state_equiv_cfg (next_inst v1) (next_inst v2)` by
          (irule next_inst_state_equiv_cfg >> simp[result_equiv_cfg_def]) >>
        `v1.vs_prev_bb = s.vs_prev_bb` by
          (drule_all step_inst_preserves_prev_bb >> simp[]) >>
        `v2.vs_prev_bb = s.vs_prev_bb` by
          (drule_all step_inst_preserves_prev_bb >> simp[]) >>
        first_x_assum (qspec_then `next_inst v1` mp_tac) >>
        simp[next_inst_def]
      )
    )
  )
QED

Theorem run_block_merge_blocks_equiv:
  !fn a b s b_lbl.
    block_last_jmp_to b_lbl a /\
    block_terminator_last a /\
    block_has_no_phi b /\
    s.vs_inst_idx <= LENGTH (BUTLAST a.bb_instructions)
  ==>
    result_equiv_cfg
      (case run_block fn a s of
         OK s' => if s'.vs_halted then Halt s' else run_block fn b s'
       | other => other)
      (run_block fn (a with bb_instructions := BUTLAST a.bb_instructions ++ b.bb_instructions) s)
Proof
  completeInduct_on `LENGTH (BUTLAST a.bb_instructions) - s.vs_inst_idx` >>
  rpt strip_tac >>
  Cases_on `s.vs_inst_idx = LENGTH (BUTLAST a.bb_instructions)`
  >- (
    qpat_x_assum `block_last_jmp_to b_lbl a` mp_tac >>
    simp[block_last_jmp_to_def] >> strip_tac >>
    `a.bb_instructions <> []` by
      (fs[block_last_inst_def] >> Cases_on `a.bb_instructions` >> fs[]) >>
    `inst = LAST a.bb_instructions` by
      (fs[block_last_inst_def] >>
       metis_tac[optionTheory.SOME_11]) >>
    `get_instruction a s.vs_inst_idx = SOME inst` by (
      simp[get_instruction_def] >>
      `s.vs_inst_idx = LENGTH a.bb_instructions - 1` by (
        fs[LENGTH_BUTLAST] >>
        Cases_on `a.bb_instructions` >> fs[]
      ) >>
      simp[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1]
    ) >>
    simp[Once run_block_def, step_in_block_def] >>
    simp[Once run_block_def, step_in_block_def] >>
    simp[step_inst_def] >>
    gvs[AllCaseEqs(), jump_to_def] >>
    Cases_on `b.bb_instructions`
    >- (
      simp[get_instruction_def, result_equiv_cfg_def] >>
      qexists_tac `Error "block not terminated"` >>
      simp[]
    )
    >- (
      simp[get_instruction_def, LENGTH_APPEND, listTheory.EL_APPEND2] >>
      simp[result_equiv_cfg_def]
    ) >>
    (* relate merged block to running b directly *)
    `result_equiv_cfg
       (run_block fn (a with bb_instructions := BUTLAST a.bb_instructions ++ b.bb_instructions) s)
       (run_block fn b (s with vs_inst_idx := 0))` by (
      irule run_block_drop_equiv_cfg >>
      simp[]
    ) >>
    `state_equiv_cfg (s with vs_inst_idx := 0) (jump_to b_lbl s)` by
      simp[state_equiv_cfg_def, var_equiv_def, jump_to_def, lookup_var_def] >>
    `result_equiv_cfg (run_block fn b (s with vs_inst_idx := 0))
                      (run_block fn b (jump_to b_lbl s))` by
      (irule run_block_no_phi_equiv_cfg >> simp[]) >>
    irule result_equiv_cfg_trans >>
    qexists_tac `run_block fn b (s with vs_inst_idx := 0)` >>
    simp[] >>
    Cases_on `run_block fn b (jump_to b_lbl s)` >>
    gvs[result_equiv_cfg_def]
  )
  >- (
    `s.vs_inst_idx < LENGTH (BUTLAST a.bb_instructions)` by simp[] >>
    `get_instruction a s.vs_inst_idx = SOME inst` by
      (simp[get_instruction_def] >> simp[LENGTH_BUTLAST]) >>
    `~is_terminator inst.inst_opcode` by (
      CCONTR_TAC >>
      fs[block_terminator_last_def] >>
      first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >>
      simp[]
    ) >>
    simp[Once run_block_def, step_in_block_def] >>
    simp[Once run_block_def, step_in_block_def] >>
    Cases_on `step_inst inst s` >> gvs[] >>
    rename1 `step_inst inst s = OK s1` >>
    `s1.vs_inst_idx = s.vs_inst_idx` by
      (drule_all step_inst_preserves_inst_idx >> simp[]) >>
    first_x_assum (qspec_then `next_inst s1` mp_tac) >>
    simp[arithmeticTheory.ADD1, next_inst_def, LENGTH_BUTLAST] >>
    disch_then irule >>
    simp[arithmeticTheory.ADD1]
  )
QED

val _ = export_theory();
