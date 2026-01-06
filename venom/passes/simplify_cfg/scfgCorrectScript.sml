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
  cheat
QED

Theorem remove_unreachable_blocks_correct:
  !fn s.
    cfg_wf fn /\
    phi_fn_wf fn /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE ==>
    run_function_equiv_cfg fn (remove_unreachable_blocks fn) s
Proof
  cheat
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
  cheat
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
