(*
 * Simplify-CFG Correctness
 *
 * Pass-level correctness theorems for simplify-cfg.
 * NOTE: Many helper proofs are cheated pending full stabilization.
 *)

Theory scfgCorrect
Ancestors
  scfgMergeCorrect scfgTransform venomInst list relation
Libs
  scfgDefsTheory scfgEquivTheory scfgStateOpsTheory scfgPhiLemmasTheory
  scfgPhiRunBlockTheory scfgPhiStepTheory venomSemTheory venomSemPropsTheory
  venomInstTheory venomStateTheory listTheory relationTheory arithmeticTheory

(* ===== CFG/Lookup Helpers ===== *)

Theorem lookup_block_label:
  !lbl blocks bb.
    lookup_block lbl blocks = SOME bb ==> bb.bb_label = lbl
Proof
  Induct_on `blocks`
  >- simp[lookup_block_def]
  >- (rw[lookup_block_def] >> rpt strip_tac >> COND_CASES_TAC >> gvs[])
QED

Theorem lookup_block_MEM:
  !lbl blocks bb.
    lookup_block lbl blocks = SOME bb ==> MEM bb blocks
Proof
  Induct_on `blocks`
  >- simp[lookup_block_def]
  >- (rw[lookup_block_def] >> rpt strip_tac >> metis_tac[])
QED

Theorem lookup_block_at_hd:
  !lbl blocks bb.
    blocks <> [] /\
    lbl = (HD blocks).bb_label /\
    lookup_block lbl blocks = SOME bb ==>
    bb = HD blocks
Proof
  Cases_on `blocks` >> simp[lookup_block_def]
QED

Theorem lookup_block_filter:
  !P lbl blocks bb.
    lookup_block lbl blocks = SOME bb /\ P bb ==>
    lookup_block lbl (FILTER P blocks) = SOME bb
Proof
  Induct_on `blocks`
  >- simp[lookup_block_def]
  >- (rw[lookup_block_def, FILTER] >> rpt strip_tac >> gvs[])
QED

Theorem lookup_block_filter_none:
  !P lbl blocks.
    lookup_block lbl blocks = NONE ==> lookup_block lbl (FILTER P blocks) = NONE
Proof
  Induct_on `blocks` >> simp[lookup_block_def, FILTER] >> rw[] >> gvs[] >>
  simp[lookup_block_def]
QED

Theorem lookup_block_simplify_phi_block:
  !lbl blocks fn' bb.
    lookup_block lbl blocks = SOME bb ==>
    lookup_block lbl
      (MAP (\bb. simplify_phi_block (pred_labels fn' bb.bb_label) bb) blocks) =
    SOME (simplify_phi_block (pred_labels fn' lbl) bb)
Proof
  Induct_on `blocks`
  >- simp[lookup_block_def]
  >- rw[lookup_block_def, MAP, scfgPhiStepTheory.simplify_phi_block_label]
QED

Theorem lookup_block_simplify_phi_block_none:
  !lbl blocks fn'.
    lookup_block lbl blocks = NONE ==>
    lookup_block lbl
      (MAP (\bb. simplify_phi_block (pred_labels fn' bb.bb_label) bb) blocks) = NONE
Proof
  Induct_on `blocks` >> simp[lookup_block_def, MAP,
    scfgPhiStepTheory.simplify_phi_block_label] >> rw[]
QED

Theorem pred_labels_mem_from_edge:
  !fn bb lbl.
    MEM bb fn.fn_blocks /\ MEM lbl (block_successors bb) ==>
    MEM bb.bb_label (pred_labels fn lbl)
Proof
  rw[pred_labels_def, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem pred_labels_subset:
  !fn fn' lbl pred.
    (!bb. MEM bb fn'.fn_blocks ==> MEM bb fn.fn_blocks) /\
    MEM pred (pred_labels fn' lbl) ==>
    MEM pred (pred_labels fn lbl)
Proof
  rw[pred_labels_def, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem pred_labels_keep_reachable:
  !fn entry lbl prev keep.
    keep = FILTER (\bb. reachable_label fn entry bb.bb_label) fn.fn_blocks /\
    MEM prev (pred_labels fn lbl) /\
    reachable_label fn entry prev ==>
    MEM prev (pred_labels (fn with fn_blocks := keep) lbl)
Proof
  rw[pred_labels_def, MEM_MAP, MEM_FILTER] >> rpt strip_tac >> gvs[] >>
  qexists_tac `bb` >> simp[]
QED

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

Theorem reachable_label_step:
  !fn entry src dst.
    reachable_label fn entry src /\ cfg_edge fn src dst ==>
    reachable_label fn entry dst
Proof
  rw[reachable_label_def] >> metis_tac[relationTheory.RTC_RULES_RIGHT1]
QED

Theorem run_function_remove_unreachable_equiv:
  !fuel fn s.
    cfg_wf fn /\
    phi_fn_wf fn /\
    reachable_label fn (entry_label fn) s.vs_current_bb /\
    (s.vs_prev_bb = NONE ==> s.vs_current_bb = entry_label fn) /\
    (!prev. s.vs_prev_bb = SOME prev ==> MEM prev (pred_labels fn s.vs_current_bb)) /\
    (!prev. s.vs_prev_bb = SOME prev ==> reachable_label fn (entry_label fn) prev)
  ==>
    result_equiv_cfg (run_function fuel fn s)
                     (run_function fuel (remove_unreachable_blocks fn) s)
Proof
  Induct_on `fuel`
  >- (simp[Once run_function_def, result_equiv_cfg_def] >>
      simp[Once run_function_def] >> simp[result_equiv_cfg_def])
  >- (
    rpt gen_tac >> strip_tac >> simp[Once run_function_def] >>
    Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
    >- (
      simp[] >> simp[Once run_function_def] >>
      Cases_on `fn.fn_blocks = []`
      >- gvs[cfg_wf_def]
      >- (
        sg `lookup_block s.vs_current_bb (remove_unreachable_blocks fn).fn_blocks = NONE`
        >- (simp[remove_unreachable_blocks_def] >>
            drule lookup_block_filter_none >> strip_tac >>
            first_x_assum (qspec_then `\bb. reachable_label fn (HD fn.fn_blocks).bb_label bb.bb_label` assume_tac) >>
            drule lookup_block_simplify_phi_block_none >> simp[])
        >- gvs[result_equiv_cfg_def]))
    >- (
      simp[] >>
      `x.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
      `fn.fn_blocks <> []` by gvs[cfg_wf_def] >>
      sg `lookup_block s.vs_current_bb (FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks) = SOME x`
      >- (irule lookup_block_filter >> simp[])
      >- (
        drule lookup_block_simplify_phi_block >> strip_tac >>
        first_x_assum (qspec_then `fn with fn_blocks := FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks` assume_tac) >>
        sg `(remove_unreachable_blocks fn).fn_blocks = MAP (\bb. simplify_phi_block (pred_labels (fn with fn_blocks := FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks) bb.bb_label) bb) (FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks)`
        >- gvs[remove_unreachable_blocks_def, entry_label_def]
        >- (
          CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >> simp[] >>
          Cases_on `s.vs_prev_bb`
          >- ( (* Entry block case *)
            gvs[] >>
            sg `x = HD fn.fn_blocks`
            >- (irule lookup_block_at_hd >> simp[entry_label_def] >> gvs[entry_label_def])
            >- (
              `block_has_no_phi x` by gvs[phi_fn_wf_def] >>
              `simplify_phi_block (pred_labels (fn with fn_blocks := FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks) (entry_label fn)) x = x` by (irule simplify_phi_block_no_phi >> simp[]) >>
              gvs[] >>
              Cases_on `run_block (HD fn.fn_blocks) s` >> gvs[result_equiv_cfg_def]
              >- (
                Cases_on `v.vs_halted` >> gvs[result_equiv_cfg_def, state_equiv_cfg_refl] >>
                `v.vs_prev_bb = SOME (entry_label fn)` by (drule_all run_block_ok_prev_bb >> gvs[]) >>
                sg `MEM v.vs_current_bb (block_successors (HD fn.fn_blocks))`
                >- (`MEM (HD fn.fn_blocks) fn.fn_blocks` by simp[rich_listTheory.HEAD_MEM] >> drule_all run_block_ok_successor >> simp[])
                >- (
                  sg `reachable_label fn (entry_label fn) v.vs_current_bb`
                  >- (irule reachable_label_step >> qexists_tac `entry_label fn` >> simp[cfg_edge_def] >>
                      qexists_tac `HD fn.fn_blocks` >> simp[rich_listTheory.HEAD_MEM] >> gvs[entry_label_def])
                  >- (
                    sg `MEM (entry_label fn) (pred_labels fn v.vs_current_bb)`
                    >- (`MEM (HD fn.fn_blocks) fn.fn_blocks` by simp[rich_listTheory.HEAD_MEM] >>
                        drule pred_labels_mem_from_edge >> disch_then (qspec_then `v.vs_current_bb` mp_tac) >> simp[])
                    >- (first_x_assum irule >> simp[]))))
              >- simp[state_equiv_cfg_refl]
              >- simp[state_equiv_cfg_refl]))
          >- ( (* Non-entry block case *)
            `MEM x' (pred_labels fn s.vs_current_bb)` by (first_x_assum (qspec_then `x'` mp_tac) >> simp[]) >>
            `reachable_label fn (entry_label fn) x'` by (first_x_assum (qspec_then `x'` mp_tac) >> simp[]) >>
            sg `result_equiv_cfg (run_block (simplify_phi_block (pred_labels (fn with fn_blocks := FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks) s.vs_current_bb) x) s) (run_block x s)`
            >- (
              irule scfgPhiRunBlockTheory.run_block_simplify_phi >> rpt conj_tac
              >- (qexists_tac `fn with fn_blocks := FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks` >> gvs[])
              >- (qexists_tac `x'` >> simp[] >> irule pred_labels_keep_reachable >> simp[] >> qexists_tac `entry_label fn` >> simp[])
              >- (qexists_tac `pred_labels fn s.vs_current_bb` >> conj_tac
                  >- (rpt strip_tac >> irule pred_labels_subset >>
                      qexists_tac `fn with fn_blocks := FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks` >> simp[listTheory.MEM_FILTER])
                  >- (`MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >> drule_all scfgPhiLemmasTheory.phi_fn_wf_block >> gvs[])))
            >- (
              Cases_on `run_block x s`
              >- ( (* OK case *)
                gvs[result_equiv_cfg_def] >> simp[] >>
                Cases_on `run_block (simplify_phi_block (pred_labels (fn with fn_blocks := FILTER (λbb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks) s.vs_current_bb) x) s`
                >- (
                  gvs[result_equiv_cfg_def] >>
                  Cases_on `v.vs_halted` >> gvs[result_equiv_cfg_def]
                  >- (gvs[state_equiv_cfg_def] >> simp[result_equiv_cfg_def] >> irule state_equiv_cfg_sym >> simp[] >> simp[state_equiv_cfg_def])
                  >- (
                    Cases_on `v'.vs_halted` >> gvs[state_equiv_cfg_def] >>
                    sg `MEM x' (pred_labels (fn with fn_blocks := FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks) s.vs_current_bb)`
                    >- (irule pred_labels_keep_reachable >> simp[] >> qexists_tac `entry_label fn` >> simp[])
                    >- (
                      sg `run_block (simplify_phi_block (pred_labels (fn with fn_blocks := FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks) s.vs_current_bb) x) s = OK v`
                      >- (
                        irule scfgPhiRunBlockTheory.run_block_simplify_phi_ok >> simp[] >> rpt conj_tac
                        >- (qexists_tac `fn with fn_blocks := FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks` >> simp[])
                        >- (qexists_tac `pred_labels fn s.vs_current_bb` >> conj_tac
                            >- (rpt strip_tac >> qspecl_then [`fn`, `fn with fn_blocks := FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks`, `s.vs_current_bb`, `lbl`] mp_tac pred_labels_subset >> simp[listTheory.MEM_FILTER])
                            >- (`MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
                                `phi_block_wf (pred_labels fn x.bb_label) x` by (drule_all scfgPhiLemmasTheory.phi_fn_wf_block >> simp[]) >> gvs[])))
                      >- (
                        `v = v'` by gvs[] >> gvs[] >>
                        first_x_assum irule >> simp[] >>
                        `v.vs_prev_bb = SOME s.vs_current_bb` by (drule_all venomSemPropsTheory.run_block_ok_prev_bb >> simp[]) >>
                        simp[] >> rpt conj_tac
                        >- (`MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
                            `MEM v.vs_current_bb (block_successors x)` by (drule_all run_block_ok_successor >> simp[]) >>
                            drule_all pred_labels_mem_from_edge >> gvs[])
                        >- (irule reachable_label_step >> qexists_tac `s.vs_current_bb` >> simp[scfgDefsTheory.cfg_edge_def] >>
                            qexists_tac `x` >> simp[] >> gvs[] >>
                            `MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >> conj_tac >- simp[] >>
                            drule_all run_block_ok_successor >> simp[])))))
                >- gvs[result_equiv_cfg_def]
                >- gvs[result_equiv_cfg_def]
                >- gvs[result_equiv_cfg_def])
              >- (simp[] >> Cases_on `run_block (simplify_phi_block (pred_labels (fn with fn_blocks := FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks) s.vs_current_bb) x) s` >> gvs[result_equiv_cfg_def, state_equiv_cfg_refl] >> irule state_equiv_cfg_sym >> simp[])
              >- (simp[] >> Cases_on `run_block (simplify_phi_block (pred_labels (fn with fn_blocks := FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks) s.vs_current_bb) x) s` >> gvs[result_equiv_cfg_def, state_equiv_cfg_refl] >> irule state_equiv_cfg_sym >> simp[])
              >- (simp[] >> Cases_on `run_block (simplify_phi_block (pred_labels (fn with fn_blocks := FILTER (\bb. reachable_label fn (entry_label fn) bb.bb_label) fn.fn_blocks) s.vs_current_bb) x) s` >> gvs[result_equiv_cfg_def])))))))
QED

Theorem remove_unreachable_blocks_correct:
  !fn s.
    cfg_wf fn /\
    phi_fn_wf fn /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE ==>
    run_function_equiv_cfg fn (remove_unreachable_blocks fn) s
Proof
  rpt gen_tac >> strip_tac >> simp[run_function_equiv_cfg_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> qexists_tac `fuel` >>
      sg `result_equiv_cfg (run_function fuel fn s)
            (run_function fuel (remove_unreachable_blocks fn) s)`
      >- (irule run_function_remove_unreachable_equiv >>
          simp[reachable_label_def])
      >- (Cases_on `run_function fuel fn s` >>
          Cases_on `run_function fuel (remove_unreachable_blocks fn) s` >>
          gvs[result_equiv_cfg_def, terminates_def]))
  >- (rpt gen_tac >> strip_tac >> qexists_tac `fuel'` >>
      sg `result_equiv_cfg (run_function fuel' fn s)
            (run_function fuel' (remove_unreachable_blocks fn) s)`
      >- (irule run_function_remove_unreachable_equiv >>
          simp[reachable_label_def])
      >- (Cases_on `run_function fuel' fn s` >>
          Cases_on `run_function fuel' (remove_unreachable_blocks fn) s` >>
          gvs[result_equiv_cfg_def, terminates_def]))
QED

(* ===== Simplify-CFG Step Correctness (Skeletons) ===== *)

Theorem simplify_cfg_step_correct:
  !fn fn' s.
    simplify_cfg_step fn fn' /\
    cfg_wf fn /\
    phi_fn_wf fn /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE /\
    s.vs_inst_idx = 0 ==>
    run_function_equiv_cfg fn fn' s
Proof
  rpt gen_tac >> strip_tac >> gvs[simplify_cfg_step_def]
  >- (irule remove_unreachable_blocks_correct >> simp[])
  >- (irule scfgMergeCorrectTheory.merge_blocks_correct >> simp[])
  >- (irule scfgMergeCorrectTheory.merge_jump_correct >> simp[])
QED

Theorem simplify_cfg_correct:
  !fn fn' s.
    simplify_cfg fn fn' /\
    cfg_wf fn /\
    phi_fn_wf fn /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE /\
    s.vs_inst_idx = 0 ==>
    run_function_equiv_cfg fn fn' s
Proof
  cheat
QED

val _ = export_theory();
