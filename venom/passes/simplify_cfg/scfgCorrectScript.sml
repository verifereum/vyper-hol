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

(* Helper: MEM in remove_block gives a block with different label from original list *)
Theorem MEM_remove_block:
  !lbl blocks bb.
    MEM bb (remove_block lbl blocks) ==>
    bb.bb_label <> lbl /\ MEM bb blocks
Proof
  Induct_on `blocks` >> simp[remove_block_def] >>
  rpt strip_tac >> Cases_on `h.bb_label = lbl` >> gvs[] >> metis_tac[]
QED

(* Helper: ALL_DISTINCT preserved by remove_block *)
Theorem ALL_DISTINCT_remove_block:
  !lbl blocks.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) blocks) ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (remove_block lbl blocks))
Proof
  Induct_on `blocks` >> simp[remove_block_def] >> rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[MEM_MAP] >>
  rpt strip_tac >> drule MEM_remove_block >> strip_tac >> metis_tac[]
QED

(* Helper: MEM in replace_block gives either the new block or an old block with different label *)
Theorem MEM_replace_block:
  !bb' blocks bb.
    ALL_DISTINCT (MAP (\b. b.bb_label) blocks) /\
    MEM bb (replace_block bb' blocks) ==>
    bb = bb' \/ (bb.bb_label <> bb'.bb_label /\ MEM bb blocks)
Proof
  Induct_on `blocks` >> simp[replace_block_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `h.bb_label = bb'.bb_label` >> gvs[]
  >- (strip_tac >> gvs[MEM_MAP] >> metis_tac[])
  >- (first_x_assum (qspecl_then [`bb'`, `bb`] mp_tac) >> simp[] >> metis_tac[])
QED

(* Converse: block stays in remove_block if label differs *)
Theorem MEM_remove_block_intro:
  !lbl blocks bb.
    bb.bb_label <> lbl /\ MEM bb blocks ==>
    MEM bb (remove_block lbl blocks)
Proof
  Induct_on `blocks` >> simp[remove_block_def] >>
  rpt strip_tac >> Cases_on `h.bb_label = lbl` >> gvs[]
QED

(* If a block with new_bb's label exists, new_bb is in replace_block result *)
Theorem MEM_replace_block_intro:
  !bb' blocks.
    (?old_bb. MEM old_bb blocks /\ old_bb.bb_label = bb'.bb_label) ==>
    MEM bb' (replace_block bb' blocks)
Proof
  Induct_on `blocks` >> simp[replace_block_def] >>
  rpt strip_tac >> Cases_on `h.bb_label = bb'.bb_label` >> gvs[] >> metis_tac[]
QED

(* Block with different label stays in replace_block result *)
Theorem MEM_replace_block_other:
  !bb' blocks bb.
    MEM bb blocks /\ bb.bb_label <> bb'.bb_label ==>
    MEM bb (replace_block bb' blocks)
Proof
  Induct_on `blocks` >> simp[replace_block_def] >>
  rpt strip_tac >> Cases_on `h.bb_label = bb'.bb_label` >> gvs[] >> metis_tac[]
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

(* Helper: ALL_DISTINCT (MAP f l) implies ALL_DISTINCT (MAP f (FILTER P l)) *)
Theorem all_distinct_map_filter:
  !f P l. ALL_DISTINCT (MAP f l) ==> ALL_DISTINCT (MAP f (FILTER P l))
Proof
  gen_tac >> gen_tac >> Induct >> simp[] >> rw[] >> gvs[MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

(* Helper: simplify_phi_block preserves block_terminator_last *)
Theorem simplify_phi_block_terminator_last:
  !preds bb.
    block_terminator_last bb ==>
    block_terminator_last (simplify_phi_block preds bb)
Proof
  rw[block_terminator_last_def, scfgDefsTheory.simplify_phi_block_def,
     get_instruction_def, LENGTH_MAP] >>
  first_x_assum irule >> simp[EL_MAP] >> gvs[EL_MAP] >>
  qabbrev_tac `inst = bb.bb_instructions❲idx❳` >>
  Cases_on `inst.inst_opcode = PHI` >>
  gvs[scfgDefsTheory.simplify_phi_inst_def, is_terminator_def] >>
  qpat_x_assum `is_terminator _` mp_tac >> simp[is_terminator_def] >>
  rpt COND_CASES_TAC >> simp[is_terminator_def]
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

(* ===== Pred-Labels Algebra Lemmas ===== *)
(* These lemmas describe how pred_labels changes under function transformations.
   They are essential for proving phi_block_wf preservation in merge_blocks/merge_jump. *)

(* How pred_labels changes after removing a block *)
Theorem pred_labels_remove_block:
  !fn b_lbl lbl.
    pred_labels (fn with fn_blocks := remove_block b_lbl fn.fn_blocks) lbl =
    FILTER (\p. p <> b_lbl) (pred_labels fn lbl)
Proof
  simp[pred_labels_def] >>
  rpt gen_tac >> Induct_on `fn.fn_blocks` >- simp[scfgDefsTheory.remove_block_def] >>
  rpt strip_tac >> gvs[scfgDefsTheory.remove_block_def] >>
  qpat_x_assum `h::v = _` (fn th => SUBST_ALL_TAC (SYM th)) >>
  simp[scfgDefsTheory.remove_block_def] >>
  Cases_on `h.bb_label = b_lbl` >> simp[]
  >- (first_x_assum (qspec_then `fn with fn_blocks := v` mp_tac) >> simp[] >>
      Cases_on `MEM lbl (block_successors h)` >> gvs[])
  >- (Cases_on `MEM lbl (block_successors h)` >> gvs[] >>
      first_x_assum (qspec_then `<| fn_blocks := v |>` mp_tac) >> simp[])
QED

(* Helper: block_successors transformation under replace_label_block *)
Theorem block_successors_replace_label_block:
  !old new bb.
    block_successors (replace_label_block old new bb) =
    MAP (\lbl. if lbl = old then new else lbl) (block_successors bb)
Proof
  rw[block_successors_def, replace_label_block_def, block_last_inst_def] >>
  gvs[NULL_EQ, LAST_MAP] >>
  simp[get_successors_def, replace_label_inst_def] >>
  Cases_on `is_terminator (LAST bb.bb_instructions).inst_opcode` >> simp[] >>
  Induct_on `(LAST bb.bb_instructions).inst_operands` >- simp[] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `h::v = _` (SUBST_ALL_TAC o SYM) >> simp[] >>
  Cases_on `h` >> simp[get_label_def, replace_label_operand_def]
  >- (first_x_assum (qspec_then `bb with bb_instructions := [(LAST bb.bb_instructions) with inst_operands := v]` mp_tac) >> simp[])
  >- (first_x_assum (qspec_then `bb with bb_instructions := [(LAST bb.bb_instructions) with inst_operands := v]` mp_tac) >> simp[])
  >- (simp[get_label_def] >> Cases_on `s = old` >> simp[get_label_def] >>
      first_x_assum (qspec_then `bb with bb_instructions := [(LAST bb.bb_instructions) with inst_operands := v]` mp_tac) >> simp[])
QED

(* How pred_labels changes after replace_label_fn (as set equality) *)
Theorem pred_labels_replace_label_fn_set:
  !fn old new lbl.
    lbl <> old ==>
    set (pred_labels (replace_label_fn old new fn) lbl) =
    if lbl = new then
      set (pred_labels fn lbl) UNION set (pred_labels fn old)
    else set (pred_labels fn lbl)
Proof
  rpt strip_tac >> simp[pred_labels_def, replace_label_fn_def] >>
  simp[pred_setTheory.EXTENSION, MEM_MAP, MEM_FILTER] >>
  rpt strip_tac >> eq_tac
  >- (
    rpt strip_tac >> gvs[block_successors_replace_label_block,
      replace_label_block_def, MEM_MAP] >>
    CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM replace_label_block_def))) >>
    qpat_x_assum `MEM lbl (block_successors _)` (mp_tac o REWRITE_RULE
      [GSYM replace_label_block_def]) >>
    simp[block_successors_replace_label_block, MEM_MAP] >>
    rpt strip_tac >> Cases_on `lbl' = old` >> gvs[]
    >- (DISJ2_TAC >> simp[MEM_MAP, MEM_FILTER] >> metis_tac[])
    >- (COND_CASES_TAC >> simp[MEM_MAP, MEM_FILTER] >> metis_tac[]))
  >- (
    COND_CASES_TAC >> simp[MEM_MAP, MEM_FILTER] >> rpt strip_tac >> gvs[]
    >- (
      qexists_tac `replace_label_block old lbl bb` >>
      simp[replace_label_block_def, block_successors_replace_label_block,
        MEM_MAP] >> metis_tac[])
    >- (
      qexists_tac `replace_label_block old lbl bb` >>
      simp[replace_label_block_def, block_successors_replace_label_block,
        MEM_MAP] >> metis_tac[])
    >- (
      qexists_tac `replace_label_block old new bb` >>
      simp[replace_label_block_def, block_successors_replace_label_block,
        MEM_MAP] >> metis_tac[]))
QED

(* MEM-based corollary of pred_labels_replace_label_fn_set *)
Theorem MEM_pred_labels_replace_label_fn:
  !fn old new lbl x.
    lbl <> old ==>
    (MEM x (pred_labels (replace_label_fn old new fn) lbl) <=>
     if lbl = new then MEM x (pred_labels fn lbl) \/ MEM x (pred_labels fn old)
     else MEM x (pred_labels fn lbl))
Proof
  rpt strip_tac >>
  `set (pred_labels (replace_label_fn old new fn) lbl) =
   if lbl = new then set (pred_labels fn lbl) UNION set (pred_labels fn old)
   else set (pred_labels fn lbl)` by (irule pred_labels_replace_label_fn_set >> simp[]) >>
  simp[pred_setTheory.EXTENSION] >> COND_CASES_TAC >> gvs[]
QED

(* Helper: if bb has lbl as successor, then bb.bb_label is in pred_labels of lbl *)
Theorem block_successors_pred_labels:
  !fn bb lbl.
    MEM bb fn.fn_blocks /\ MEM lbl (block_successors bb) ==>
    MEM bb.bb_label (pred_labels fn lbl)
Proof
  rpt strip_tac >>
  simp[scfgDefsTheory.pred_labels_def, MEM_MAP, MEM_FILTER] >>
  qexists_tac `bb` >> simp[]
QED

(* Helper: block_successors depends only on LAST instruction *)
Theorem block_successors_append_last:
  !insts1 insts2 bb.
    insts2 <> [] ==>
    block_successors (bb with bb_instructions := insts1 ++ insts2) =
    block_successors (bb with bb_instructions := insts2)
Proof
  rpt strip_tac >>
  simp[scfgDefsTheory.block_successors_def, scfgDefsTheory.block_last_inst_def] >>
  gvs[rich_listTheory.LAST_APPEND_NOT_NIL, NULL_EQ]
QED

(* Helper: characterize pred_labels after replace_block + remove_block *)
Theorem MEM_pred_labels_replace_block_remove:
  !fn new_bb removed_lbl lbl x.
    ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
    new_bb.bb_label <> removed_lbl /\
    (?old_bb. MEM old_bb fn.fn_blocks /\ old_bb.bb_label = new_bb.bb_label) ==>
    (MEM x (pred_labels (fn with fn_blocks :=
       replace_block new_bb (remove_block removed_lbl fn.fn_blocks)) lbl) <=>
     (if x = new_bb.bb_label then MEM lbl (block_successors new_bb)
      else x <> removed_lbl /\ MEM x (pred_labels fn lbl)))
Proof
  rpt strip_tac >> simp[scfgDefsTheory.pred_labels_def, MEM_MAP, MEM_FILTER] >>
  EQ_TAC >> strip_tac
  >- (`ALL_DISTINCT (MAP (\b. b.bb_label) (remove_block removed_lbl fn.fn_blocks))`
        by (irule ALL_DISTINCT_remove_block >> simp[]) >>
      drule_all MEM_replace_block >> strip_tac >> gvs[] >>
      drule MEM_remove_block >> strip_tac >> simp[] >> qexists_tac `bb` >> simp[])
  >- (Cases_on `x = new_bb.bb_label` >> gvs[]
      >- (qexists_tac `new_bb` >> simp[] >> irule MEM_replace_block_intro >>
          qexists_tac `old_bb` >> simp[] >> irule MEM_remove_block_intro >> gvs[])
      >- (qexists_tac `bb` >> simp[] >> irule MEM_replace_block_other >> simp[] >>
          irule MEM_remove_block_intro >> gvs[]))
QED

(* End-to-end pred_labels characterization for merge_blocks result *)
Theorem pred_labels_merge_blocks_result:
  !fn a b lbl x.
    merge_blocks_cond fn a b /\ cfg_wf fn /\ lbl <> b ==>
    (MEM x (pred_labels (merge_blocks fn a b) lbl) <=>
     if lbl = a then MEM x (pred_labels fn a) \/ MEM x (FILTER (\p. p <> b) (pred_labels fn b))
     else MEM x (FILTER (\p. p <> b) (pred_labels fn lbl)))
Proof
  rpt gen_tac >> strip_tac >>
  simp[scfgTransformTheory.merge_blocks_def] >>
  gvs[scfgTransformTheory.merge_blocks_cond_def] >>
  qabbrev_tac `fn1 = fn with fn_blocks :=
    replace_block (a' with bb_instructions :=
      FRONT a'.bb_instructions ++ b'.bb_instructions)
    (remove_block b fn.fn_blocks)` >>
  simp[MEM_pred_labels_replace_label_fn] >>
  (* b was removed from fn1, so pred_labels fn1 b = [] *)
  sg `pred_labels fn1 b = []`
  >- (simp[scfgDefsTheory.pred_labels_def, Abbr`fn1`, FILTER_EQ_NIL, EVERY_MEM] >>
      rpt strip_tac >>
      `ALL_DISTINCT (MAP (\b. b.bb_label) (remove_block b fn.fn_blocks))`
        by (irule ALL_DISTINCT_remove_block >> gvs[cfg_wf_def]) >>
      drule_all MEM_replace_block >> strip_tac >> gvs[]
      >- ((* merged block case: use block_successors_pred_labels for contradiction *)
          `MEM b' fn.fn_blocks` by (irule lookup_block_MEM >> qexists_tac `b` >> simp[]) >>
          `b'.bb_label = b` by (irule lookup_block_label >> qexists_tac `fn.fn_blocks` >> simp[]) >>
          `b'.bb_instructions <> []` by cheat >>
          `block_successors (a' with bb_instructions := FRONT a'.bb_instructions ++ b'.bb_instructions) =
           block_successors b'` by (irule scfgMergeCorrectTheory.block_successors_merged >> simp[]) >>
          gvs[] >>
          drule_all block_successors_pred_labels >> gvs[])
      >- ((* other block case: use block_successors_pred_labels for contradiction *)
          drule MEM_remove_block >> strip_tac >>
          `a'.bb_label = a` by (irule lookup_block_label >> qexists_tac `fn.fn_blocks` >> simp[]) >>
          drule_all block_successors_pred_labels >> gvs[]))
  >- (simp[] >> Cases_on `lbl = a` >> simp[]
      >- cheat (* lbl = a: pred_labels fn1 a ~ pred_labels fn a + {a} *)
      >- cheat) (* lbl != a: pred_labels fn1 lbl ~ FILTER (neq b) (pred_labels fn lbl) *)
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
    s.vs_inst_idx = 0 /\
    ~s.vs_halted ==>
    run_function_equiv_cfg fn fn' s
Proof
  rpt gen_tac >> strip_tac >> gvs[simplify_cfg_step_def]
  >- (irule remove_unreachable_blocks_correct >> simp[])
  >- (irule scfgMergeCorrectTheory.merge_blocks_correct >> simp[])
  >- (irule scfgMergeCorrectTheory.merge_jump_correct >> simp[])
QED

(* Helper: entry_label preserved by simplify_cfg_step *)
Theorem entry_label_simplify_cfg_step:
  !fn fn'.
    simplify_cfg_step fn fn' /\ cfg_wf fn /\ phi_fn_wf fn ==>
    entry_label fn' = entry_label fn
Proof
  rpt strip_tac >> gvs[simplify_cfg_step_def]
  (* Case 1: remove_unreachable_blocks *)
  >- (simp[entry_label_def, scfgTransformTheory.remove_unreachable_blocks_def] >>
      Cases_on `fn.fn_blocks = []` >> gvs[cfg_wf_def] >>
      sg `FILTER (\bb. reachable_label fn (HD fn.fn_blocks).bb_label bb.bb_label)
                 fn.fn_blocks =
          HD fn.fn_blocks ::
          FILTER (\bb. reachable_label fn (HD fn.fn_blocks).bb_label bb.bb_label)
                 (TL fn.fn_blocks)`
      >- (Cases_on `fn.fn_blocks` >> gvs[] >> simp[reachable_label_def]) >>
      gvs[scfgPhiStepTheory.simplify_phi_block_label])
  (* Case 2: merge_blocks *)
  >- (gvs[scfgTransformTheory.merge_blocks_cond_def,
          scfgTransformTheory.merge_blocks_def] >>
      simp[entry_label_def, scfgDefsTheory.replace_label_fn_def] >>
      Cases_on `fn.fn_blocks` >> gvs[cfg_wf_def] >>
      `b <> h.bb_label` by gvs[entry_label_def] >>
      simp[scfgDefsTheory.remove_block_def] >>
      Cases_on `a = h.bb_label` >> gvs[scfgDefsTheory.replace_block_def]
      >- (`a' = h` by gvs[lookup_block_def] >> gvs[] >>
          simp[scfgDefsTheory.replace_label_block_def])
      >- (sg `a'.bb_label = a`
          >- (irule lookup_block_label >> simp[] >> qexists_tac `h::t` >> simp[])
          >- (gvs[] >> simp[scfgDefsTheory.replace_label_block_def])))
  (* Case 3: merge_jump *)
  >- (gvs[scfgTransformTheory.merge_jump_cond_def,
          scfgTransformTheory.merge_jump_def] >>
      simp[entry_label_def, scfgDefsTheory.replace_label_fn_def] >>
      Cases_on `fn.fn_blocks` >> gvs[cfg_wf_def] >>
      `b <> h.bb_label` by gvs[entry_label_def] >>
      Cases_on `a = h.bb_label`
      >- (`a' = h` by gvs[venomInstTheory.lookup_block_def] >> gvs[] >>
          simp[scfgDefsTheory.replace_block_def] >>
          simp[scfgDefsTheory.remove_block_def] >>
          simp[scfgDefsTheory.replace_label_block_def,
               scfgDefsTheory.replace_phi_in_block_def] >>
          simp[] >> rw[])
      >- (simp[scfgDefsTheory.replace_block_def] >>
          `a'.bb_label = a` by
            (irule lookup_block_label >> qexists_tac `h::t` >> simp[]) >>
          gvs[] >>
          simp[scfgDefsTheory.remove_block_def] >>
          simp[scfgDefsTheory.replace_label_block_def,
               scfgDefsTheory.replace_phi_in_block_def] >>
          rw[]))
QED

(* Helper: update_last_inst preserves length *)
Theorem update_last_inst_length:
  !f l. LENGTH (update_last_inst f l) = LENGTH l
Proof
  gen_tac >> Induct >> rw[scfgDefsTheory.update_last_inst_def] >>
  Cases_on `l` >> gvs[scfgDefsTheory.update_last_inst_def]
QED

(* Helper: update_last_inst preserves elements before last *)
Theorem update_last_inst_el_unchanged:
  !f l idx.
    l <> [] /\ idx < LENGTH l - 1 ==>
    EL idx (update_last_inst f l) = EL idx l
Proof
  gen_tac >> Induct >> rw[scfgDefsTheory.update_last_inst_def] >>
  Cases_on `l` >> gvs[scfgDefsTheory.update_last_inst_def] >>
  Cases_on `idx` >> gvs[]
QED

(* Helper: replace_label_inst preserves opcode *)
Theorem replace_label_inst_opcode:
  !old new inst.
    (replace_label_inst old new inst).inst_opcode = inst.inst_opcode
Proof
  simp[scfgDefsTheory.replace_label_inst_def]
QED

(* Helper: non-PHI instructions trivially satisfy phi_inst_wf *)
Theorem phi_inst_wf_non_phi:
  !preds old new inst.
    inst.inst_opcode <> PHI ==>
    phi_inst_wf preds (replace_label_inst old new inst)
Proof
  rw[phi_inst_wf_def, replace_label_inst_opcode]
QED

(* Helper: phi_inst_wf preserved when old label is not a predecessor *)
Theorem phi_inst_wf_not_mem_pred:
  !old new preds inst.
    phi_inst_wf preds inst /\ ~MEM old preds ==>
    phi_inst_wf preds (replace_label_inst old new inst)
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- (
    simp[phi_inst_wf_def, replace_label_inst_def, replace_label_inst_opcode] >>
    drule_all phi_inst_wf_props >> strip_tac >>
    qexists_tac `out` >> simp[] >>
    sg `MAP (replace_label_operand old new) inst.inst_operands =
        inst.inst_operands`
    >- (
      `~MEM (Label old) inst.inst_operands` by
        (drule_all phi_ops_all_preds_no_label >> simp[]) >>
      irule listTheory.LIST_EQ >>
      simp[listTheory.EL_MAP] >>
      rpt strip_tac >> Cases_on `inst.inst_operands❲x❳` >>
      simp[replace_label_operand_def] >>
      `s <> old` by (CCONTR_TAC >> gvs[listTheory.MEM_EL] >> metis_tac[]) >>
      simp[])
    >- gvs[])
  >- (irule phi_inst_wf_non_phi >> simp[])
QED

(* Helper: phi_inst_wf preserved under label replacement *)
Theorem phi_inst_wf_replace_label:
  !old new preds (inst:instruction).
    phi_inst_wf preds inst /\
    MEM old preds /\ ~MEM new preds ==>
    phi_inst_wf (MAP (\lbl. if lbl = old then new else lbl) preds)
                (replace_label_inst old new inst)
Proof
  rpt strip_tac >>
  gvs[phi_inst_wf_def] >>
  simp[replace_label_inst_opcode, replace_label_inst_def,
       venomInstTheory.instruction_accfupds] >>
  strip_tac >> gvs[] >>
  rpt conj_tac
  >- (
    simp[phi_ops_all_preds_def, listTheory.MEM_MAP] >>
    rpt strip_tac >> Cases_on `y` >> gvs[replace_label_operand_def] >>
    Cases_on `s = old` >> gvs[]
    >- (qexists_tac `old` >> simp[])
    >- (qexists_tac `lbl` >> simp[] >> gvs[phi_ops_all_preds_def]))
  >- (
    simp[phi_ops_complete_def, listTheory.MEM_MAP] >>
    rpt strip_tac >> Cases_on `lbl = new`
    >- (
      gvs[] >> Cases_on `lbl' = old` >> gvs[] >>
      drule_all scfgPhiLemmasTheory.phi_ops_complete_MEM >> strip_tac >>
      irule_at Any scfgMergeHelpersTheory.resolve_phi_replace_label_id >> simp[] >>
      drule_all scfgPhiLemmasTheory.phi_ops_all_preds_no_label >> simp[] >> metis_tac[])
    >- (
      Cases_on `lbl' = old` >> gvs[] >>
      `lbl <> old /\ lbl <> new` by simp[] >>
      drule scfgPhiLemmasTheory.resolve_phi_replace_label_other >>
      disch_then (qspecl_then [`new`, `inst.inst_operands`] mp_tac) >>
      simp[] >> strip_tac >>
      drule_all scfgPhiLemmasTheory.phi_ops_complete_MEM >> simp[]))
  >- (irule scfgPhiLemmasTheory.phi_vals_not_label_replace_label >> simp[])
QED

(* Helper: phi_inst_wf when both old and new are in preds - old gets removed *)
Theorem phi_inst_wf_replace_label_both_mem:
  !old new preds inst.
    phi_inst_wf preds inst /\ MEM old preds /\ MEM new preds /\ old <> new ==>
    phi_inst_wf (FILTER (\l. l <> old) preds) (replace_label_inst old new inst)
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- (
    simp[phi_inst_wf_def, replace_label_inst_def, replace_label_inst_opcode] >>
    drule_all phi_inst_wf_props >> strip_tac >> qexists_tac `out` >> simp[] >>
    rpt conj_tac
    >- (
      simp[phi_ops_all_preds_def, MEM_MAP, MEM_FILTER] >>
      rpt strip_tac >> Cases_on `y` >> gvs[replace_label_operand_def]
      >- (gvs[] >> Cases_on `s = lbl` >> gvs[])
      >- (Cases_on `s = old` >> gvs[] >> gvs[phi_ops_all_preds_def]))
    >- (
      simp[phi_ops_complete_def, MEM_FILTER] >>
      rpt strip_tac >> Cases_on `lbl = new`
      >- (gvs[] >> irule resolve_phi_replace_label_exists >> simp[] >>
          gvs[phi_ops_complete_def])
      >- (simp[resolve_phi_replace_label_other] >> gvs[phi_ops_complete_def]))
    >- (irule phi_vals_not_label_replace_label >> simp[]))
  >- simp[phi_inst_wf_def, replace_label_inst_def]
QED

(* Helper: block_terminator_last for update_last_inst *)
Theorem block_terminator_last_update_last_inst:
  !f bb.
    block_terminator_last bb /\
    (!inst. is_terminator inst.inst_opcode ==> is_terminator (f inst).inst_opcode) ==>
    block_terminator_last (bb with bb_instructions := update_last_inst f bb.bb_instructions)
Proof
  rw[block_terminator_last_def, get_instruction_def, update_last_inst_length] >>
  Cases_on `idx = LENGTH bb.bb_instructions - 1`
  >- (gvs[] >>
      Cases_on `bb.bb_instructions = []` >> gvs[] >>
      `EL (LENGTH bb.bb_instructions - 1) (update_last_inst f bb.bb_instructions) =
       f (LAST bb.bb_instructions)` by (
        qspec_tac (`bb.bb_instructions`, `l`) >> Induct >>
        rw[scfgDefsTheory.update_last_inst_def] >>
        Cases_on `l` >> gvs[scfgDefsTheory.update_last_inst_def]) >>
      gvs[] >> first_x_assum irule >>
      gvs[block_terminator_last_def, get_instruction_def] >>
      first_x_assum (qspec_then `LENGTH bb.bb_instructions - 1` mp_tac) >>
      simp[LAST_EL])
  >- (`idx < LENGTH bb.bb_instructions - 1` by gvs[] >>
      `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
      `EL idx (update_last_inst f bb.bb_instructions) = EL idx bb.bb_instructions`
        by (irule update_last_inst_el_unchanged >> simp[]) >>
      gvs[block_terminator_last_def, get_instruction_def])
QED

(* Helper: PHI instructions in update_last_inst come from original list
   when f preserves opcodes *)
Theorem update_last_inst_phi_mem:
  !f l inst.
    (!x. (f x).inst_opcode = x.inst_opcode) /\
    MEM inst (update_last_inst f l) /\ inst.inst_opcode = PHI ==>
    ?inst'. MEM inst' l /\ inst'.inst_opcode = PHI
Proof
  ho_match_mp_tac update_last_inst_ind >> rpt strip_tac >>
  gvs[update_last_inst_def]
  >- (qexists_tac `inst` >> simp[])
  >- (first_x_assum drule_all >> strip_tac >> qexists_tac `inst''` >> gvs[])
QED

(* Helper: phi_block_wf preserved by replace_label_block when pred list transforms *)
Theorem phi_block_wf_replace_label_block:
  !old new preds bb.
    phi_block_wf preds bb /\ MEM old preds /\ ~MEM new preds ==>
    phi_block_wf (MAP (\lbl. if lbl = old then new else lbl) preds)
                 (replace_label_block old new bb)
Proof
  rpt strip_tac >>
  simp[scfgDefsTheory.phi_block_wf_def, scfgDefsTheory.replace_label_block_def,
       MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  irule phi_inst_wf_replace_label >> simp[] >>
  gvs[scfgDefsTheory.phi_block_wf_def]
QED

(* Helper: phi_block_wf when both old and new are in preds - old gets filtered out *)
Theorem phi_block_wf_replace_label_both_mem:
  !old new preds bb.
    phi_block_wf preds bb /\ MEM old preds /\ MEM new preds /\ old <> new ==>
    phi_block_wf (FILTER (\l. l <> old) preds) (replace_label_block old new bb)
Proof
  rpt strip_tac >>
  simp[scfgDefsTheory.phi_block_wf_def, scfgDefsTheory.replace_label_block_def,
       MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  irule phi_inst_wf_replace_label_both_mem >> simp[] >>
  gvs[scfgDefsTheory.phi_block_wf_def]
QED

(* Helper: ALL_DISTINCT on mapped list implies injectivity *)
Theorem ALL_DISTINCT_MAP_EQ:
  !f x y ls. ALL_DISTINCT (MAP f ls) /\ MEM x ls /\ MEM y ls /\ f x = f y ==> x = y
Proof
  gen_tac >> gen_tac >> gen_tac >> Induct_on `ls` >-
  simp[] >-
  (rpt strip_tac >> gvs[] >-
   (CCONTR_TAC >> gvs[listTheory.MEM_MAP]) >-
   (CCONTR_TAC >> gvs[listTheory.MEM_MAP]))
QED

(* Specialized version for bb_label - avoids lambda witness in qexists_tac *)
Theorem ALL_DISTINCT_bb_labels_EQ:
  !x y blocks.
    ALL_DISTINCT (MAP (\b. b.bb_label) blocks) /\
    MEM x blocks /\ MEM y blocks /\ x.bb_label = y.bb_label ==> x = y
Proof
  rpt gen_tac >> Induct_on `blocks` >> simp[] >> rpt strip_tac >> gvs[] >>
  CCONTR_TAC >> gvs[listTheory.MEM_MAP]
QED

(* Helper: FILTER unchanged when removed block doesn't pass predicate *)
Theorem FILTER_remove_block_unchanged:
  !P lbl blocks.
    (!bb. MEM bb blocks /\ bb.bb_label = lbl ==> ~P bb) ==>
    FILTER P (remove_block lbl blocks) = FILTER P blocks
Proof
  gen_tac >> gen_tac >> Induct_on `blocks` >-
  simp[scfgDefsTheory.remove_block_def] >-
  (rpt strip_tac >> simp[scfgDefsTheory.remove_block_def] >>
   Cases_on `h.bb_label = lbl` >> gvs[])
QED

(* Helper: FILTER unchanged when replaced block doesn't pass predicate *)
Theorem FILTER_replace_block_unchanged:
  !P new_bb blocks.
    ~P new_bb /\
    (!bb. MEM bb blocks /\ bb.bb_label = new_bb.bb_label ==> ~P bb) ==>
    FILTER P (replace_block new_bb blocks) = FILTER P blocks
Proof
  gen_tac >> gen_tac >> Induct_on `blocks` >-
  simp[scfgDefsTheory.replace_block_def] >-
  (rpt strip_tac >> simp[scfgDefsTheory.replace_block_def] >>
   Cases_on `h.bb_label = new_bb.bb_label` >> gvs[])
QED

(* Helper: FILTER unchanged when replaced/removed blocks don't pass predicate *)
Theorem FILTER_replace_block_remove_unchanged:
  !P new_bb removed_lbl blocks old_bb removed_bb.
    ALL_DISTINCT (MAP (\b. b.bb_label) blocks) /\
    ~P new_bb /\
    MEM old_bb blocks /\ old_bb.bb_label = new_bb.bb_label /\ ~P old_bb /\
    MEM removed_bb blocks /\ removed_bb.bb_label = removed_lbl /\ ~P removed_bb /\
    new_bb.bb_label <> removed_lbl ==>
    FILTER P (replace_block new_bb (remove_block removed_lbl blocks)) =
    FILTER P blocks
Proof
  (* TODO: debug drule_all ALL_DISTINCT_bb_labels_EQ pattern *)
  cheat
QED

(* Helper: pred_labels preserved for non-merged blocks when b not a predecessor *)
Theorem pred_labels_merge_blocks_other:
  !fn a b lbl.
    merge_blocks_cond fn a b /\ cfg_wf fn /\
    lbl <> a /\ lbl <> b /\ ~MEM b (pred_labels fn lbl) ==>
    pred_labels (merge_blocks fn a b) lbl = pred_labels fn lbl
Proof
  rpt strip_tac >>
  gvs[scfgTransformTheory.merge_blocks_cond_def] >>
  simp[scfgTransformTheory.merge_blocks_def] >>
  qabbrev_tac `merged = a' with bb_instructions := FRONT a'.bb_instructions ++ b'.bb_instructions` >>
  qabbrev_tac `fn1 = fn with fn_blocks := replace_block merged (remove_block b fn.fn_blocks)` >>
  `set (pred_labels (replace_label_fn b a fn1) lbl) = set (pred_labels fn1 lbl)` by (drule_all pred_labels_replace_label_fn_set >> gvs[]) >>
  `merged.bb_label = a'.bb_label` by simp[Abbr`merged`] >>
  `a'.bb_label = a` by (imp_res_tac lookup_block_label >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by gvs[cfg_wf_def] >>
  `MEM a' fn.fn_blocks` by (imp_res_tac lookup_block_MEM >> simp[]) >>
  `b'.bb_label = b` by (imp_res_tac lookup_block_label >> simp[]) >>
  `MEM b' fn.fn_blocks` by (imp_res_tac lookup_block_MEM >> simp[]) >>
  `~MEM lbl (block_successors b')` by (CCONTR_TAC >> gvs[] >> drule_all block_successors_pred_labels >> gvs[]) >>
  Cases_on `b'.bb_instructions = []`
  >- cheat (* empty instructions edge case *)
  >- (
    `block_successors merged = block_successors (a' with bb_instructions := b'.bb_instructions)` by (simp[Abbr`merged`] >> irule block_successors_append_last >> simp[]) >>
    `block_successors (a' with bb_instructions := b'.bb_instructions) = block_successors b'` by simp[scfgDefsTheory.block_successors_def, scfgDefsTheory.block_last_inst_def] >>
    `~MEM lbl (block_successors merged)` by gvs[] >>
    `block_successors a' = [b]` by (irule scfgMergeHelpersTheory.block_last_jmp_to_successors >> simp[]) >>
    sg `~MEM a (pred_labels fn lbl)`
    >- (simp[scfgDefsTheory.pred_labels_def, MEM_MAP, MEM_FILTER] >> rpt strip_tac >>
        Cases_on `MEM bb fn.fn_blocks`
        >- (DISJ1_TAC >> `bb = a'` suffices_by gvs[] >>
            irule scfgMergeHelpersTheory.lookup_block_unique >> simp[] >>
            qexists_tac `fn.fn_blocks` >> gvs[])
        >- (DISJ2_TAC >> simp[]))
    >- (sg `pred_labels fn1 lbl = pred_labels fn lbl`
        >- (simp[Abbr`fn1`, scfgDefsTheory.pred_labels_def] >>
            `FILTER (\bb. MEM lbl (block_successors bb)) (replace_block merged (remove_block b fn.fn_blocks)) = FILTER (\bb. MEM lbl (block_successors bb)) fn.fn_blocks` suffices_by simp[] >>
            `~MEM lbl (block_successors a')` by gvs[] >>
            irule FILTER_replace_block_remove_unchanged >> simp[] >>
            conj_tac >- (qexists_tac `a'` >> simp[]) >>
            qexists_tac `b'` >> simp[])
        >- (gvs[] >> cheat))) (* list vs set equality *)
QED

(* Helper: phi_block_wf preserved when old label is not a predecessor *)
Theorem phi_block_wf_not_mem_pred:
  !old new preds bb.
    phi_block_wf preds bb /\ ~MEM old preds ==>
    phi_block_wf preds (replace_label_block old new bb)
Proof
  rpt strip_tac >>
  simp[scfgDefsTheory.phi_block_wf_def, scfgDefsTheory.replace_label_block_def,
       MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  irule phi_inst_wf_not_mem_pred >> simp[] >>
  gvs[scfgDefsTheory.phi_block_wf_def]
QED

(* Helper: cfg_wf and phi_fn_wf preserved by simplify_cfg_step *)
Theorem wf_simplify_cfg_step:
  !fn fn'.
    simplify_cfg_step fn fn' /\ cfg_wf fn /\ phi_fn_wf fn ==>
    cfg_wf fn' /\ phi_fn_wf fn'
Proof
  rpt strip_tac >> gvs[simplify_cfg_step_def]
  >- ( (* cfg_wf remove_unreachable_blocks *)
    simp[scfgTransformTheory.remove_unreachable_blocks_def, cfg_wf_def] >>
    gvs[cfg_wf_def] >> Cases_on `fn.fn_blocks` >> gvs[] >>
    simp[scfgDefsTheory.reachable_label_def] >> simp[MAP_MAP_o,
    combinTheory.o_DEF, scfgPhiStepTheory.simplify_phi_block_label] >> rpt conj_tac
    >- (strip_tac >> gvs[MEM_MAP, MEM_FILTER])
    >- (irule all_distinct_map_filter >> simp[])
    >- (rw[MEM_MAP, MEM_FILTER] >> rpt strip_tac >> gvs[] >> irule
        simplify_phi_block_terminator_last >> first_x_assum irule >> simp[]))
  >- ( (* cfg_wf merge_blocks *)
    simp[scfgTransformTheory.merge_blocks_def,
         scfgTransformTheory.merge_blocks_cond_def] >> rpt strip_tac >>
    gvs[scfgTransformTheory.merge_blocks_cond_def] \\
    simp[cfg_wf_def, scfgDefsTheory.replace_label_fn_def, MAP_MAP_o,
         combinTheory.o_DEF] \\
    `!old new bb. (replace_label_block old new bb).bb_label = bb.bb_label`
      by simp[scfgDefsTheory.replace_label_block_def] \\ simp[] \\
    `!a' blocks. MAP (\bb. bb.bb_label) (replace_block a' blocks) = MAP
     (\bb. bb.bb_label) blocks` by (gen_tac >> Induct >>
     simp[scfgDefsTheory.replace_block_def] >> rw[]) \\
    `!lbl blocks. MAP (\bb. bb.bb_label) (remove_block lbl blocks) =
     FILTER (\l. l <> lbl) (MAP (\bb. bb.bb_label) blocks)` by (gen_tac
     >> Induct >> simp[scfgDefsTheory.remove_block_def] >> rw[]) \\
    simp[] >> rpt conj_tac
    >- (gvs[cfg_wf_def] >> Cases_on `fn.fn_blocks` >>
        gvs[scfgDefsTheory.entry_label_def] >>
        simp[scfgDefsTheory.remove_block_def,
             scfgDefsTheory.replace_block_def] >> COND_CASES_TAC >> simp[])
    >- (irule FILTER_ALL_DISTINCT >> gvs[cfg_wf_def])
    >- (rw[MEM_MAP] >> rpt strip_tac >> gvs[] \\
        sg `block_terminator_last y`
        >- (`!bb' blocks y. MEM y (replace_block bb' blocks) ==> (y = bb' /\
             MEM bb'.bb_label (MAP (\b. b.bb_label) blocks)) \/ MEM y
             blocks` by (gen_tac >> Induct >>
             simp[scfgDefsTheory.replace_block_def] >> rw[] >> gvs[] >>
             metis_tac[]) \\
            `!lbl blocks y. MEM y (remove_block lbl blocks) ==> MEM y
             blocks` by (gen_tac >> Induct >>
             simp[scfgDefsTheory.remove_block_def] >> rw[] >> gvs[]) \\
            first_x_assum drule >> strip_tac >> gvs[]
            >- (simp[block_terminator_last_def, get_instruction_def] >> rpt
                strip_tac >> Cases_on `idx < LENGTH (FRONT a'.bb_instructions)`
                >- (gvs[EL_APPEND_EQN] >> `block_terminator_last a'` by
                    (gvs[cfg_wf_def] >> first_x_assum irule >> irule
                     lookup_block_MEM >> metis_tac[]) \\
                    `a'.bb_instructions <> []` by (fs[block_last_jmp_to_def,
                     block_last_inst_def] >> Cases_on `a'.bb_instructions` >>
                     fs[]) \\
                    `EL idx (FRONT a'.bb_instructions) = EL idx
                     a'.bb_instructions` by simp[rich_listTheory.FRONT_EL] \\
                    gvs[block_terminator_last_def, get_instruction_def] >>
                    `idx = LENGTH a'.bb_instructions - 1` by (first_x_assum
                     irule >> gvs[rich_listTheory.LENGTH_FRONT]) \\
                    gvs[rich_listTheory.LENGTH_FRONT])
                >- (gvs[EL_APPEND_EQN] >> `block_terminator_last b'` by
                    (gvs[cfg_wf_def] >> first_x_assum irule >> irule
                     lookup_block_MEM >> metis_tac[]) \\
                    gvs[block_terminator_last_def, get_instruction_def] >> `idx
                     - LENGTH (FRONT a'.bb_instructions) = LENGTH
                     b'.bb_instructions - 1` by (first_x_assum irule >> gvs[]) \\
                    gvs[]))
            >- (`MEM y fn.fn_blocks` by metis_tac[] >> gvs[cfg_wf_def]))
        >- (simp[block_terminator_last_def, get_instruction_def,
                 scfgDefsTheory.replace_label_block_def, LENGTH_MAP, EL_MAP] >>
            rpt strip_tac >> `(replace_label_inst b a (EL idx
            y.bb_instructions)).inst_opcode = (EL idx
            y.bb_instructions).inst_opcode` by
            simp[scfgDefsTheory.replace_label_inst_def] >>
            gvs[block_terminator_last_def, get_instruction_def])))
  >- ( (* cfg_wf merge_jump *)
    simp[scfgTransformTheory.merge_jump_def,
         scfgTransformTheory.merge_jump_cond_def] >> rpt strip_tac >>
    gvs[scfgTransformTheory.merge_jump_cond_def] \\
    simp[cfg_wf_def, scfgDefsTheory.replace_label_fn_def, MAP_MAP_o,
         combinTheory.o_DEF] \\
    `!old new bb. (replace_label_block old new bb).bb_label = bb.bb_label`
      by simp[scfgDefsTheory.replace_label_block_def] \\
    `!old new bb. (replace_phi_in_block old new bb).bb_label =
     bb.bb_label` by simp[scfgDefsTheory.replace_phi_in_block_def] \\
    `!P x. (if P then replace_phi_in_block b a x else x).bb_label =
     x.bb_label` by (rw[] >> simp[scfgDefsTheory.replace_phi_in_block_def]) \\
    simp[] \\
    `!a' blocks. MAP (\bb. bb.bb_label) (replace_block a' blocks) = MAP
     (\bb. bb.bb_label) blocks` by (gen_tac >> Induct >>
     simp[scfgDefsTheory.replace_block_def] >> rw[]) \\
    `!lbl blocks. MAP (\bb. bb.bb_label) (remove_block lbl blocks) =
     FILTER (\l. l <> lbl) (MAP (\bb. bb.bb_label) blocks)` by
     (gen_tac >> Induct >> simp[scfgDefsTheory.remove_block_def] >> rw[]) \\
    simp[] >> rpt conj_tac
    >- (gvs[cfg_wf_def] >> Cases_on `fn.fn_blocks` >>
        gvs[scfgDefsTheory.entry_label_def] >>
        simp[scfgDefsTheory.remove_block_def,
             scfgDefsTheory.replace_block_def] \\
        COND_CASES_TAC >> simp[scfgDefsTheory.remove_block_def] \\
        `a'.bb_label <> b` by gvs[] >> simp[])
    >- (irule FILTER_ALL_DISTINCT >> gvs[cfg_wf_def])
    >- (rw[MEM_MAP] >> rpt strip_tac >> gvs[] \\
        sg `block_terminator_last bb'`
        >- (`!bb' blocks y. MEM y (replace_block bb' blocks) ==> (y = bb'
             /\ MEM bb'.bb_label (MAP (\b. b.bb_label) blocks)) \/ MEM y
             blocks` by (gen_tac >> Induct >>
             simp[scfgDefsTheory.replace_block_def] >> rw[] >> gvs[] >>
             metis_tac[]) \\
            `!lbl blocks y. MEM y (remove_block lbl blocks) ==> MEM y
             blocks` by (gen_tac >> Induct >>
             simp[scfgDefsTheory.remove_block_def] >> rw[] >> gvs[]) \\
            `MEM bb' (replace_block (a' with bb_instructions :=
             update_last_inst (replace_label_inst b c_lbl)
             a'.bb_instructions) fn.fn_blocks)` by (first_x_assum drule
             >> simp[]) \\
            first_x_assum drule >> strip_tac >> gvs[] \\
            first_assum (qspec_then `(a' with bb_instructions :=
             update_last_inst (replace_label_inst b c_lbl)
             a'.bb_instructions)` mp_tac) \\
            strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
            >- (irule block_terminator_last_update_last_inst >> conj_tac
                >- simp[replace_label_inst_opcode]
                >- (gvs[cfg_wf_def] >> first_x_assum irule >> irule
                    lookup_block_MEM >> metis_tac[]))
            >- gvs[cfg_wf_def])
        >- (simp[block_terminator_last_def,
                 venomInstTheory.get_instruction_def,
                 scfgDefsTheory.replace_label_block_def,
                 scfgDefsTheory.replace_phi_in_block_def, LENGTH_MAP, EL_MAP] \\
            rpt strip_tac >> COND_CASES_TAC >> gvs[LENGTH_MAP, EL_MAP]
            >- (sg `!old new inst. (replace_label_in_phi old new
                 inst).inst_opcode = inst.inst_opcode`
                >- (simp[scfgDefsTheory.replace_label_in_phi_def] \\ rw[])
                >- gvs[replace_label_inst_opcode, block_terminator_last_def,
                       venomInstTheory.get_instruction_def])
            >- gvs[replace_label_inst_opcode, block_terminator_last_def,
                   venomInstTheory.get_instruction_def])))
  >- ( (* phi_fn_wf remove_unreachable_blocks *)
    rpt strip_tac >>
    simp[scfgTransformTheory.remove_unreachable_blocks_def,
         scfgDefsTheory.phi_fn_wf_def] >>
    Cases_on `fn.fn_blocks` >> gvs[scfgDefsTheory.phi_fn_wf_def] >>
    simp[scfgDefsTheory.reachable_label_def, relationTheory.RTC_REFL] \\
    qabbrev_tac `keep = h::FILTER (\bb. (cfg_edge fn)^* h.bb_label bb.bb_label) t` >>
    qabbrev_tac `fn' = fn with fn_blocks := keep` \\
    qabbrev_tac `fix = simplify_phi_block (pred_labels fn' h.bb_label) h ::
      MAP (\bb'. simplify_phi_block (pred_labels fn' bb'.bb_label) bb')
      (FILTER (\bb'. (cfg_edge fn)^* h.bb_label bb'.bb_label) t)` >>
    qabbrev_tac `fn'' = fn with fn_blocks := fix` \\
    rpt conj_tac
    >- (
      rpt strip_tac
      >- (
        `block_has_no_phi bb` by (gvs[] >>
          irule scfgPhiLemmasTheory.simplify_phi_block_no_phi >> simp[]) \\
        simp[scfgDefsTheory.phi_block_wf_def, scfgDefsTheory.phi_inst_wf_def] >>
        rpt strip_tac >>
        gvs[scfgDefsTheory.block_has_no_phi_def, scfgDefsTheory.block_has_phi_def] >>
        metis_tac[])
      >- (
        gvs[listTheory.MEM_MAP, listTheory.MEM_FILTER] \\
        simp[scfgDefsTheory.simplify_phi_block_def] \\
        sg `pred_labels fn'' bb'.bb_label = pred_labels fn' bb'.bb_label`
        >- (
          simp[scfgDefsTheory.pred_labels_def] \\
          simp[Abbr`fn''`, Abbr`fn'`, Abbr`fix`, Abbr`keep`] \\
          simp[scfgPhiLemmasTheory.simplify_phi_block_successors] \\
          simp[scfgDefsTheory.simplify_phi_block_def] \\
          simp[venomInstTheory.basic_block_accfupds] \\
          COND_CASES_TAC
          >- (
            simp[] \\
            simp[rich_listTheory.FILTER_MAP] \\
            simp[combinTheory.o_DEF, scfgDefsTheory.simplify_phi_block_def,
                 scfgPhiLemmasTheory.simplify_phi_block_successors,
                 venomInstTheory.basic_block_accfupds] \\
            CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM scfgDefsTheory.simplify_phi_block_def))) \\
            simp[scfgPhiLemmasTheory.simplify_phi_block_successors] \\
            simp[listTheory.MAP_MAP_o, combinTheory.o_DEF,
                 scfgDefsTheory.simplify_phi_block_def,
                 venomInstTheory.basic_block_accfupds])
          >- (
            simp[] \\
            simp[rich_listTheory.FILTER_MAP] >>
            CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM scfgDefsTheory.simplify_phi_block_def))) >>
            simp[scfgPhiLemmasTheory.simplify_phi_block_successors,
                 listTheory.MAP_MAP_o, combinTheory.o_DEF,
                 scfgDefsTheory.simplify_phi_block_def,
                 venomInstTheory.basic_block_accfupds]))
        >- (
          gvs[] \\
          simp[GSYM scfgDefsTheory.simplify_phi_block_def] >>
          irule scfgPhiLemmasTheory.simplify_phi_block_wf \\
          qexists_tac `pred_labels fn bb'.bb_label` \\
          conj_tac
          >- (
            rpt strip_tac >>
            irule pred_labels_subset >>
            qexists_tac `fn'` >>
            simp[Abbr`fn'`, Abbr`keep`, listTheory.MEM_FILTER] \\
            metis_tac[])
          >- (first_x_assum (qspec_then `bb'` mp_tac) >> simp[]))))
    >- (irule scfgPhiLemmasTheory.simplify_phi_block_no_phi >> simp[]))
  >- ( (* phi_fn_wf merge_blocks *)
    rpt strip_tac >>
    simp[scfgTransformTheory.merge_blocks_def,
         scfgTransformTheory.merge_blocks_cond_def] >>
    rpt strip_tac >> gvs[scfgTransformTheory.merge_blocks_cond_def] >>
    simp[scfgDefsTheory.phi_fn_wf_def, scfgDefsTheory.replace_label_fn_def,
         listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
    qabbrev_tac `merged = a' with bb_instructions :=
      FRONT a'.bb_instructions ++ b'.bb_instructions` >>
    qabbrev_tac `blocks1 = remove_block b fn.fn_blocks` >>
    qabbrev_tac `blocks2 = replace_block merged blocks1` >>
    qabbrev_tac `blocks3 = MAP (replace_label_block b a) blocks2` >>
    qabbrev_tac `fn' = fn with fn_blocks := blocks3` >>
    rpt conj_tac
    >- ( (* blocks3 ≠ [] *)
      gvs[Abbr`blocks2`] >> Cases_on `blocks1` >>
      gvs[scfgDefsTheory.replace_block_def]
      >- (gvs[scfgDefsTheory.phi_fn_wf_def] >> Cases_on `fn.fn_blocks` >>
          gvs[scfgDefsTheory.remove_block_def, scfgDefsTheory.entry_label_def])
      >- (COND_CASES_TAC >> simp[]))
    >- ( (* phi_block_wf for all blocks *)
      rpt strip_tac >> gvs[Abbr`blocks3`, MEM_MAP] >>
      rpt strip_tac >> gvs[Abbr`blocks2`] >>
      `ALL_DISTINCT (MAP (\bb. bb.bb_label) blocks1)` by
        (gvs[cfg_wf_def, Abbr`blocks1`] >> irule ALL_DISTINCT_remove_block >> simp[]) >>
      drule_all MEM_replace_block >> strip_tac >> gvs[]
      >- ( (* y = merged case *)
        simp[scfgDefsTheory.replace_label_block_def, Abbr`merged`] >>
        (* First establish phi_block_wf for merged block *)
        sg `phi_block_wf (pred_labels fn a)
              (a' with bb_instructions := FRONT a'.bb_instructions ++ b'.bb_instructions)`
        >- (irule scfgMergeCorrectTheory.phi_block_wf_merged >> simp[] >>
            rpt conj_tac
            >- (gvs[scfgDefsTheory.block_last_jmp_to_def,
                    scfgDefsTheory.block_last_inst_def] >>
                Cases_on `a'.bb_instructions` >> gvs[])
            >- (gvs[scfgDefsTheory.phi_fn_wf_def] >>
                `a'.bb_label = a` by (irule lookup_block_label >> metis_tac[]) >>
                gvs[] >> first_x_assum irule >> irule lookup_block_MEM >> metis_tac[]))
        >- ( (* Now transform pred_labels - case split on MEM b *)
          Cases_on `MEM b (pred_labels fn a)`
          >- ( (* MEM b (pred_labels fn a) case *)
            cheat)
          >- ( (* ~MEM b (pred_labels fn a) case *)
            `a'.bb_label = a` by (irule lookup_block_label >> metis_tac[]) >>
            simp[scfgDefsTheory.phi_block_wf_def, MEM_MAP, MEM_APPEND] >>
            rpt strip_tac >> gvs[]
            >- ( (* y from FRONT a'.bb_instructions *)
              `phi_inst_wf (pred_labels fn a'.bb_label) y` by
                (gvs[scfgDefsTheory.phi_block_wf_def] >> first_x_assum irule >>
                 simp[listTheory.MEM_APPEND] >> DISJ1_TAC >>
                 irule rich_listTheory.MEM_FRONT_NOT_NIL >>
                 gvs[scfgDefsTheory.block_last_jmp_to_def,
                     scfgDefsTheory.block_last_inst_def] >>
                 Cases_on `a'.bb_instructions` >> gvs[]) >>
              Cases_on `y.inst_opcode = PHI`
              >- cheat (* PHI case needs pred_labels fn' ~ pred_labels fn *)
              >- gvs[scfgDefsTheory.phi_inst_wf_def,
                     scfgDefsTheory.replace_label_inst_def])
            >- ( (* y from b'.bb_instructions - no PHIs *)
              gvs[scfgDefsTheory.phi_inst_wf_def,
                  scfgDefsTheory.replace_label_inst_def,
                  scfgDefsTheory.block_has_no_phi_def,
                  scfgDefsTheory.block_has_phi_def] >> metis_tac[]))))
      >- ( (* y from original blocks case *)
        simp[scfgDefsTheory.replace_label_block_def] >> cheat))
    >- ( (* block_has_no_phi (HD blocks3) *)
      gvs[Abbr`blocks3`, Abbr`blocks2`, Abbr`blocks1`] >>
      Cases_on `fn.fn_blocks` >> gvs[scfgDefsTheory.phi_fn_wf_def,
        scfgDefsTheory.remove_block_def] >>
      COND_CASES_TAC >> gvs[scfgDefsTheory.entry_label_def] >>
      simp[scfgDefsTheory.replace_block_def] >>
      COND_CASES_TAC >> gvs[]
      >- (
        simp[scfgDefsTheory.replace_label_block_def,
             scfgDefsTheory.block_has_no_phi_def,
             scfgDefsTheory.block_has_phi_def, listTheory.EXISTS_MAP] >>
        rpt strip_tac >> gvs[listTheory.MEM_MAP] >>
        gvs[scfgDefsTheory.replace_label_inst_def, Abbr`merged`,
            listTheory.MEM_APPEND]
        >- (
          gvs[scfgDefsTheory.block_has_no_phi_def,
              scfgDefsTheory.block_has_phi_def] >>
          sg `a' = h`
          >- (
            gvs[venomInstTheory.lookup_block_def] >>
            Cases_on `a'.bb_label = a` >> gvs[] >>
            qpat_x_assum `lookup_block a t = SOME a'` mp_tac >>
            qpat_x_assum `a'.bb_label ≠ a` mp_tac >>
            rpt (pop_assum kall_tac) >>
            MAP_EVERY qid_spec_tac [`a'`, `t`] >>
            Induct >> simp[venomInstTheory.lookup_block_def] >> rw[] >> gvs[])
          >- (
            qpat_x_assum `a' = h` (fn th => SUBST_ALL_TAC th) >>
            qpat_x_assum `MEM y (FRONT h.bb_instructions)` mp_tac >>
            qpat_x_assum `y.inst_opcode = PHI` mp_tac >>
            qpat_x_assum `block_last_jmp_to b h` mp_tac >>
            first_x_assum (qspec_then `y` mp_tac) >>
            rpt (pop_assum kall_tac) >> rpt strip_tac >>
            rw[] >>
            `h.bb_instructions <> []` by (
              fs[scfgDefsTheory.block_last_jmp_to_def,
                 scfgDefsTheory.block_last_inst_def] >>
              Cases_on `h.bb_instructions` >> fs[]) >>
            drule_all rich_listTheory.MEM_FRONT_NOT_NIL >> rw[]))
        >- gvs[scfgDefsTheory.block_has_no_phi_def,
               scfgDefsTheory.block_has_phi_def])
      >- (
        fs[scfgDefsTheory.block_has_no_phi_def,
           scfgDefsTheory.block_has_phi_def,
           scfgDefsTheory.replace_label_block_def, listTheory.EXISTS_MAP] >>
        rpt strip_tac >> gvs[scfgDefsTheory.replace_label_inst_def] >>
        gvs[listTheory.MEM_MAP] >>
        first_x_assum (qspec_then `y` mp_tac) >>
        gvs[scfgDefsTheory.replace_label_inst_def])))
  >- ( (* phi_fn_wf merge_jump *)
    rpt strip_tac >>
    simp[scfgTransformTheory.merge_jump_def,
         scfgTransformTheory.merge_jump_cond_def] >>
    gvs[scfgTransformTheory.merge_jump_cond_def] \\
    simp[scfgDefsTheory.phi_fn_wf_def, scfgDefsTheory.replace_label_fn_def,
         listTheory.MAP_MAP_o, combinTheory.o_DEF] \\
    qabbrev_tac `a_new = a' with bb_instructions :=
      update_last_inst (replace_label_inst b c_lbl) a'.bb_instructions` >>
    qabbrev_tac `blocks1 = replace_block a_new fn.fn_blocks` >>
    qabbrev_tac `blocks2 = remove_block b blocks1` >>
    qabbrev_tac `succs = block_successors a_new` >>
    qabbrev_tac `blocks3 = MAP (\bb. if MEM bb.bb_label succs
      then replace_phi_in_block b a bb else bb) blocks2` >>
    qabbrev_tac `blocks4 = MAP (replace_label_block b c_lbl) blocks3` >>
    qabbrev_tac `fn' = fn with fn_blocks := blocks4` \\
    rpt conj_tac
    >- ( (* blocks4 ≠ [] *)
      gvs[Abbr`blocks2`, Abbr`blocks1`] >>
      Cases_on `fn.fn_blocks` >>
      gvs[scfgDefsTheory.phi_fn_wf_def, scfgDefsTheory.replace_block_def,
          scfgDefsTheory.remove_block_def] >>
      COND_CASES_TAC >>
      gvs[scfgDefsTheory.entry_label_def, scfgDefsTheory.remove_block_def] >>
      `a'.bb_label <> b` by gvs[] >> simp[])
    >- ( (* phi_block_wf for all blocks in merge_jump *)
      rpt strip_tac >> gvs[Abbr`blocks4`, MEM_MAP] >>
      rpt strip_tac >> gvs[Abbr`blocks3`, MEM_MAP] >>
      rpt strip_tac >> gvs[Abbr`blocks2`] >>
      `ALL_DISTINCT (MAP (\bb. bb.bb_label) blocks1)` by
        (gvs[cfg_wf_def, Abbr`blocks1`] >>
         `!a' blocks. MAP (\bb. bb.bb_label) (replace_block a' blocks) =
          MAP (\bb. bb.bb_label) blocks` by
           (gen_tac >> Induct >> simp[scfgDefsTheory.replace_block_def] >> rw[]) >>
         simp[]) >>
      drule MEM_remove_block >> strip_tac >> gvs[] >>
      (* Now y' is from blocks1, case split on whether it's a_new or original *)
      cheat)
    >- ( (* block_has_no_phi (HD blocks4) *)
      gvs[Abbr`blocks2`, Abbr`blocks1`] >>
      Cases_on `fn.fn_blocks` >>
      gvs[scfgDefsTheory.phi_fn_wf_def, scfgDefsTheory.replace_block_def,
          scfgDefsTheory.remove_block_def] \\
      COND_CASES_TAC >>
      gvs[scfgDefsTheory.entry_label_def, scfgDefsTheory.remove_block_def]
      >- ( (* h.bb_label = a_new.bb_label case *)
        COND_CASES_TAC >>
        gvs[scfgDefsTheory.replace_label_block_def,
            scfgDefsTheory.replace_phi_in_block_def,
            scfgDefsTheory.block_has_no_phi_def,
            scfgDefsTheory.block_has_phi_def, listTheory.EXISTS_MAP]
        >- ( (* MEM h.bb_label succs *)
          rpt strip_tac >> gvs[listTheory.MEM_MAP] \\
          sg `y'.inst_opcode = PHI`
          >- (gvs[scfgDefsTheory.replace_label_inst_def,
                  scfgDefsTheory.replace_label_in_phi_def] >>
              Cases_on `y'.inst_opcode` >> gvs[])
          >- (gvs[Abbr`a_new`] \\
              `?inst'. MEM inst' a'.bb_instructions /\ inst'.inst_opcode = PHI`
                by (irule update_last_inst_phi_mem >>
                    qexists_tac `replace_label_inst b c_lbl` >>
                    qexists_tac `y'` >>
                    simp[replace_label_inst_opcode]) \\
              sg `a' = h`
              >- (gvs[venomInstTheory.lookup_block_def] \\
                  Cases_on `a'.bb_label = a` >> gvs[] \\
                  drule lookup_block_label >> gvs[] \\
                  strip_tac >>
                  qpat_x_assum `lookup_block a t = SOME a'`
                    (mp_tac o MATCH_MP lookup_block_label) >> gvs[])
              >- (first_x_assum (qspec_then `inst'` mp_tac) >> simp[] \\
                  qpat_x_assum `a' = h` (fn th => SUBST_ALL_TAC th) >>
                  first_x_assum ACCEPT_TAC)))
        >- ( (* ~MEM h.bb_label succs *)
          rpt strip_tac >> gvs[listTheory.MEM_MAP, Abbr`a_new`] >>
          `y.inst_opcode = PHI` by gvs[scfgDefsTheory.replace_label_inst_def] \\
          `?inst'. MEM inst' a'.bb_instructions /\ inst'.inst_opcode = PHI`
            by (irule update_last_inst_phi_mem >>
                qexists_tac `replace_label_inst b c_lbl` >>
                qexists_tac `y` >>
                simp[replace_label_inst_opcode]) \\
          sg `a' = h`
          >- (gvs[venomInstTheory.lookup_block_def] >>
              Cases_on `h.bb_label = a` >> gvs[] >>
              qpat_x_assum `lookup_block a t = SOME a'`
                (mp_tac o MATCH_MP lookup_block_label) >> gvs[]) \\
          first_x_assum (qspec_then `inst'` mp_tac) >> simp[] >>
          qpat_x_assum `a' = h` (fn th => SUBST_ALL_TAC th) >>
          first_x_assum ACCEPT_TAC))
      >- ( (* h.bb_label ≠ a_new.bb_label case *)
        COND_CASES_TAC >>
        gvs[scfgDefsTheory.replace_label_block_def,
            scfgDefsTheory.replace_phi_in_block_def,
            scfgDefsTheory.block_has_no_phi_def,
            scfgDefsTheory.block_has_phi_def, listTheory.EXISTS_MAP]
        >- ( (* MEM h.bb_label succs *)
          rpt strip_tac >> gvs[listTheory.MEM_MAP] \\
          gvs[scfgDefsTheory.replace_label_inst_def] \\
          gvs[scfgDefsTheory.replace_label_in_phi_def] \\
          Cases_on `y'.inst_opcode = PHI` >> gvs[])
        >- ( (* ~MEM h.bb_label succs *)
          rpt strip_tac >> gvs[listTheory.MEM_MAP,
                               scfgDefsTheory.replace_label_inst_def]))))
QED

(* Main theorem: RTC of simplify_cfg_step preserves equivalence *)
Theorem simplify_cfg_correct:
  !fn fn' s.
    simplify_cfg fn fn' /\
    cfg_wf fn /\
    phi_fn_wf fn /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE /\
    s.vs_inst_idx = 0 /\
    ~s.vs_halted ==>
    run_function_equiv_cfg fn fn' s
Proof
  rpt strip_tac >> gvs[scfgTransformTheory.simplify_cfg_def] >>
  `!fn fn'. simplify_cfg_step^* fn fn' ==>
   !s. cfg_wf fn /\ phi_fn_wf fn /\ s.vs_current_bb = entry_label fn /\
       s.vs_prev_bb = NONE /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
       run_function_equiv_cfg fn fn' s` suffices_by metis_tac[] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >> rpt strip_tac
  >- simp[scfgEquivTheory.run_function_equiv_cfg_refl]
  >- (irule scfgEquivTheory.run_function_equiv_cfg_trans >>
      qexists_tac `fn'³'` >> conj_tac
      >- (irule simplify_cfg_step_correct >> gvs[])
      >- (first_x_assum irule >>
          drule_all wf_simplify_cfg_step >> strip_tac >>
          drule_all entry_label_simplify_cfg_step >> strip_tac >>
          gvs[]))
QED

val _ = export_theory();
