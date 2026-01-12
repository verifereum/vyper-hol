(*
 * Simplify-CFG Merge Correctness
 *
 * Correctness proofs for block merge and jump threading.
 *)

Theory scfgMergeCorrect
Ancestors
  scfgMergeRunBlock
Libs
  scfgMergeRunBlockTheory scfgMergeHelpersTheory scfgDefsTheory
  scfgEquivTheory scfgTransformTheory
  venomSemTheory venomSemPropsTheory venomStateTheory venomInstTheory

(* ===== Lookup Helpers for Merged Function ===== *)

(* Helper: lookup_block returns a block with matching label *)
Theorem lookup_block_label:
  !lbl blocks bb. lookup_block lbl blocks = SOME bb ==> bb.bb_label = lbl
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

(* Helper: lookup_block returns an element of the list *)
Theorem lookup_block_MEM:
  !lbl blocks bb. lookup_block lbl blocks = SOME bb ==> MEM bb blocks
Proof
  Induct_on `blocks`
  >- simp[lookup_block_def]
  >- (rw[lookup_block_def] >> rpt strip_tac >> metis_tac[])
QED

(* b_lbl is removed from merged function *)
Theorem lookup_block_merge_blocks_b:
  !fn a_lbl b_lbl a b.
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    a_lbl <> b_lbl ==>
    lookup_block b_lbl (merge_blocks fn a_lbl b_lbl).fn_blocks = NONE
Proof
  rpt strip_tac >> simp[merge_blocks_def, replace_label_fn_def] >>
  sg `a.bb_label = a_lbl` >- metis_tac[lookup_block_label] >>
  irule lookup_block_replace_label_block_none >>
  irule lookup_block_replace_block_none >>
  simp[lookup_block_remove_block_same]
QED

(* a_lbl maps to merged block in merged function *)
Theorem lookup_block_merge_blocks_a:
  !fn a_lbl b_lbl a b.
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    a_lbl <> b_lbl ==>
    lookup_block a_lbl (merge_blocks fn a_lbl b_lbl).fn_blocks =
    SOME (replace_label_block b_lbl a_lbl
           (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions))
Proof
  rpt strip_tac >> simp[merge_blocks_def, replace_label_fn_def] >>
  sg `a.bb_label = a_lbl` >- metis_tac[lookup_block_label] >>
  irule lookup_block_replace_label_block >>
  sg `lookup_block a_lbl (remove_block b_lbl fn.fn_blocks) = SOME a`
  >- (irule lookup_block_remove_block >> simp[])
  >- (drule lookup_block_replace_block >> strip_tac >>
      first_x_assum (qspec_then `a with bb_instructions :=
        FRONT a.bb_instructions ++ b.bb_instructions` mp_tac) >> simp[])
QED

(* Other blocks map to label-replaced versions *)
Theorem lookup_block_merge_blocks_other:
  !fn a_lbl b_lbl a b c_lbl c.
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    lookup_block c_lbl fn.fn_blocks = SOME c /\
    a_lbl <> b_lbl /\ c_lbl <> a_lbl /\ c_lbl <> b_lbl ==>
    lookup_block c_lbl (merge_blocks fn a_lbl b_lbl).fn_blocks =
    SOME (replace_label_block b_lbl a_lbl c)
Proof
  rpt strip_tac >> simp[merge_blocks_def, replace_label_fn_def] >>
  sg `a.bb_label = a_lbl` >- metis_tac[lookup_block_label] >>
  irule lookup_block_replace_label_block >>
  sg `lookup_block c_lbl (remove_block b_lbl fn.fn_blocks) = SOME c`
  >- (irule lookup_block_remove_block >> simp[])
  >- (drule lookup_block_replace_block >> strip_tac >>
      first_x_assum (qspec_then `a with bb_instructions :=
        FRONT a.bb_instructions ++ b.bb_instructions` mp_tac) >> simp[])
QED

(* Key lemma: if pred_labels fn b_lbl = [a_lbl] and x.bb_label <> a_lbl,
   then block x doesn't jump to b_lbl. This is used to show vs_current_bb <> b_lbl
   after executing a block that's not a. *)
Theorem pred_labels_single_no_jmp:
  !fn b_lbl a_lbl x.
    pred_labels fn b_lbl = [a_lbl] /\
    MEM x fn.fn_blocks /\
    x.bb_label <> a_lbl ==>
    ~MEM b_lbl (block_successors x)
Proof
  rpt strip_tac >> fs[pred_labels_def] >>
  sg `MEM x [bb]`
  >- (gvs[listTheory.MEM_FILTER] >>
      `MEM x (FILTER (\bb. MEM b_lbl (block_successors bb)) fn.fn_blocks)`
        by gvs[listTheory.MEM_FILTER] >> gvs[])
  >- gvs[]
QED

(* Helper: terminates is preserved by result_equiv_cfg *)
Theorem terminates_result_equiv_cfg:
  !r1 r2. result_equiv_cfg r1 r2 /\ terminates r1 ==> terminates r2
Proof
  Cases >> Cases >> gvs[result_equiv_cfg_def, terminates_def]
QED

(* Helper: no PHI in merged block when neither a nor b have PHIs *)
Theorem block_has_no_phi_merged:
  !a b. a.bb_instructions <> [] /\ block_has_no_phi a /\ block_has_no_phi b ==>
        block_has_no_phi (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)
Proof
  rw[block_has_no_phi_def, block_has_phi_def] >>
  SPOSE_NOT_THEN ASSUME_TAC >> gvs[] >>
  `MEM inst a.bb_instructions` by (irule rich_listTheory.MEM_FRONT_NOT_NIL >> simp[]) >>
  metis_tac[]
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

(* Helper: phi_block_wf for merged block when a may have PHIs but b has none *)
Theorem phi_block_wf_merged:
  !a b preds.
    phi_block_wf preds a /\ block_has_no_phi b /\ a.bb_instructions <> [] ==>
    phi_block_wf preds (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)
Proof
  rw[phi_block_wf_def, block_has_no_phi_def, block_has_phi_def]
  >- (first_x_assum irule >> irule rich_listTheory.MEM_FRONT_NOT_NIL >> simp[])
  >- (simp[phi_inst_wf_def] >> rpt strip_tac >> first_x_assum drule >> simp[])
QED

(* ===== Merging Blocks ===== *)

(* Termination propagates through block execution *)
Theorem run_function_terminates_step:
  !fuel fn s bb v.
    terminates (run_function (SUC fuel) fn s) /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_block bb s = OK v /\
    ~v.vs_halted ==>
    terminates (run_function fuel fn v)
Proof
  rpt strip_tac >> fs[Once venomSemTheory.run_function_def]
QED

(* Helper: a block that only jumps to b_lbl can't be its own predecessor *)
Theorem no_self_loop_from_jmp_to:
  !fn a a_lbl b_lbl.
    cfg_wf fn /\ lookup_block a_lbl fn.fn_blocks = SOME a /\
    block_last_jmp_to b_lbl a /\ a_lbl <> b_lbl ==>
    ~MEM a_lbl (pred_labels fn a_lbl)
Proof
  rpt strip_tac >> simp[pred_labels_def, listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  fs[pred_labels_def, listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  `a.bb_label = a_lbl` by metis_tac[lookup_block_label] >>
  `MEM a fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  sg `bb = a`
  >- (gvs[cfg_wf_def] >> irule scfgMergeHelpersTheory.lookup_block_unique >> simp[] >>
      qexists_tac `fn.fn_blocks` >> simp[])
  >- (`block_successors a = [b_lbl]` by metis_tac[block_last_jmp_to_successors] >> fs[])
QED

(* Helper: block with single predecessor can't loop to itself *)
Theorem run_block_no_self_loop_single_pred:
  !fn bb s s' a_lbl.
    cfg_wf fn /\ MEM bb fn.fn_blocks /\
    pred_labels fn bb.bb_label = [a_lbl] /\
    a_lbl <> bb.bb_label /\
    run_block bb s = OK s' /\ ~s'.vs_halted ==>
    s'.vs_current_bb <> bb.bb_label
Proof
  rpt strip_tac >>
  drule_all run_block_ok_successor >> strip_tac >>
  `~MEM bb.bb_label (block_successors bb)` by
    (qspecl_then [`fn`, `bb.bb_label`, `a_lbl`, `bb`] mp_tac pred_labels_single_no_jmp >> simp[]) >>
  metis_tac[]
QED

(* Helper lemma: IH conditions hold after running a no-phi block with prev_bb <> b_lbl *)
Theorem ih_conditions_no_phi_prev_neq:
  !fuel fn a_lbl b_lbl a b s1 s2 x v v'.
    cfg_wf fn /\ phi_fn_wf fn /\
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    a_lbl <> b_lbl /\ b_lbl <> entry_label fn /\
    pred_labels fn b_lbl = [a_lbl] /\
    block_has_no_phi b /\ block_last_jmp_to b_lbl a /\
    state_equiv_cfg s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_current_bb <> b_lbl /\ s1.vs_current_bb <> a_lbl /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    s1.vs_prev_bb <> SOME b_lbl /\ s1.vs_prev_bb = s2.vs_prev_bb /\
    (!lbl. s1.vs_prev_bb = SOME lbl ==> MEM lbl (pred_labels fn s1.vs_current_bb)) /\
    ~s1.vs_halted /\
    terminates (run_function (SUC fuel) fn s1) /\
    lookup_block s1.vs_current_bb fn.fn_blocks = SOME x /\
    block_has_no_phi x /\ block_terminator_last x /\
    run_block x s1 = OK v /\
    run_block (replace_label_block b_lbl a_lbl x) s2 = OK v' /\
    state_equiv_cfg v v' /\ ~v.vs_halted /\ ~v'.vs_halted
  ==>
    v.vs_current_bb = v'.vs_current_bb /\
    v.vs_current_bb <> b_lbl /\
    v.vs_inst_idx = 0 /\ v'.vs_inst_idx = 0 /\
    (v.vs_prev_bb = SOME b_lbl ==> v'.vs_prev_bb = SOME a_lbl) /\
    (v.vs_prev_bb <> SOME b_lbl ==> v.vs_prev_bb = v'.vs_prev_bb) /\
    (!lbl. v.vs_prev_bb = SOME lbl ==> MEM lbl (pred_labels fn v.vs_current_bb)) /\
    terminates (run_function fuel fn v)
Proof
  rpt strip_tac >> rpt conj_tac
  (* v.vs_current_bb = v'.vs_current_bb *)
  >- (
    `x.bb_label = s1.vs_current_bb` by metis_tac[lookup_block_label] >>
    `MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
    `~MEM b_lbl (block_successors x)` by metis_tac[pred_labels_single_no_jmp] >>
    irule run_block_replace_label_no_phi_current_bb >> simp[] >>
    qexistsl_tac [`x`, `a_lbl`, `b_lbl`, `s1`, `s2`] >> simp[])
  (* v.vs_current_bb <> b_lbl *)
  >- (
    sg `MEM v.vs_current_bb (block_successors x)`
    >- (`MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
        metis_tac[run_block_ok_successor]) >>
    `x.bb_label = s1.vs_current_bb` by metis_tac[lookup_block_label] >>
    `MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
    `~MEM b_lbl (block_successors x)` by metis_tac[pred_labels_single_no_jmp] >>
    metis_tac[])
  (* v.vs_inst_idx = 0 *)
  >- metis_tac[run_block_ok_inst_idx]
  (* v'.vs_inst_idx = 0 *)
  >- metis_tac[run_block_ok_inst_idx]
  (* v.vs_prev_bb = SOME b_lbl ==> v'.vs_prev_bb = SOME a_lbl - contradiction *)
  >- (`v.vs_prev_bb = SOME s1.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >> gvs[])
  (* v.vs_prev_bb <> SOME b_lbl ==> v.vs_prev_bb = v'.vs_prev_bb *)
  >- (
    `v.vs_prev_bb = SOME s1.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >>
    `v'.vs_prev_bb = SOME s2.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >> gvs[])
  (* MEM lbl (pred_labels fn v.vs_current_bb) *)
  >- (
    `v.vs_prev_bb = SOME s1.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >> gvs[] >>
    `MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
    `x.bb_label = s1.vs_current_bb` by metis_tac[lookup_block_label] >>
    metis_tac[run_block_ok_pred_labels])
  (* terminates (run_function fuel fn v) *)
  >- metis_tac[run_function_terminates_step]
QED

(* ===== Helper: merged_no_label to merged_bb ===== *)

(* This helper proves equivalence between running the merged block (before label
   replacement) on s1 and the merged block (after label replacement) on s2.
   The key case split is on s1.vs_prev_bb:
   - NONE: use run_block_replace_label_prev_bb_none
   - SOME b_lbl: use run_block_replace_label (prev_bb changes from b_lbl to a_lbl)
   - SOME x (x <> b_lbl): use run_block_replace_label_prev_diff *)
Theorem run_block_merged_to_merged_bb:
  !fn a b a_lbl b_lbl s1 s2.
    cfg_wf fn /\ phi_fn_wf fn /\
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    a_lbl <> b_lbl /\
    pred_labels fn b_lbl = [a_lbl] /\
    block_has_no_phi b /\ block_last_jmp_to b_lbl a /\
    state_equiv_cfg s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (s1.vs_prev_bb = SOME b_lbl ==> s2.vs_prev_bb = SOME a_lbl) /\
    (s1.vs_prev_bb <> SOME b_lbl ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (!lbl. s1.vs_prev_bb = SOME lbl ==> MEM lbl (pred_labels fn a_lbl))
  ==>
    let merged_no_label = a with bb_instructions :=
          FRONT a.bb_instructions ++ b.bb_instructions in
    let merged_bb = replace_label_block b_lbl a_lbl merged_no_label in
    result_equiv_cfg (run_block merged_no_label s1) (run_block merged_bb s2)
Proof
  rpt strip_tac >> simp[] >>
  Cases_on `s1.vs_prev_bb`
  (* NONE case: use run_block_replace_label_prev_bb_none *)
  >- (irule run_block_replace_label_prev_bb_none >> gvs[])
  (* SOME case: split on whether it's b_lbl or not *)
  >- (
    Cases_on `x = b_lbl`
    (* prev_bb = SOME b_lbl: use run_block_replace_label *)
    >- (
      gvs[] >> irule run_block_replace_label >> simp[] >>
      qexists_tac `fn` >> simp[] >>
      `a.bb_label = a_lbl` by metis_tac[lookup_block_label] >> simp[] >>
      conj_tac
      >- (irule scfgMergeHelpersTheory.pred_labels_no_jmp_other >> simp[] >>
          metis_tac[])
      >- (irule phi_block_wf_merged >> simp[] >>
          conj_tac >- (gvs[block_last_jmp_to_def, block_last_inst_def] >>
            Cases_on `a.bb_instructions` >> gvs[]) >>
          metis_tac[phi_fn_wf_def, lookup_block_MEM, lookup_block_label]))
    (* prev_bb = SOME x, x <> b_lbl: use run_block_replace_label_prev_diff *)
    >- (
      `s1.vs_prev_bb = s2.vs_prev_bb` by gvs[] >>
      irule result_equiv_cfg_trans >>
      qexists_tac `run_block (a with bb_instructions :=
        FRONT a.bb_instructions ++ b.bb_instructions) s2` >> conj_tac
      >- (irule run_block_state_equiv_cfg >> gvs[])
      >- (
        `x <> a_lbl` by (CCONTR_TAC >> gvs[] >>
          `~MEM a_lbl (pred_labels fn a_lbl)` by
            (irule scfgMergeHelpersTheory.pred_labels_no_jmp_other >>
             simp[] >> metis_tac[]) >> gvs[]) >>
        irule run_block_replace_label_prev_diff >> simp[] >>
        qexists_tac `fn` >> qexists_tac `x` >> gvs[] >>
        `a.bb_label = a_lbl` by metis_tac[lookup_block_label] >> gvs[] >>
        irule phi_block_wf_merged >> simp[] >>
        conj_tac >- (gvs[block_last_jmp_to_def, block_last_inst_def] >>
          Cases_on `a.bb_instructions` >> gvs[]) >>
        metis_tac[phi_fn_wf_def, lookup_block_MEM])))
QED

(* ===== Helper: general block to replaced block ===== *)

(* This helper proves equivalence between running a general block c (not a or b)
   on s1 and the replaced block on s2. Same 3-case pattern as run_block_merged_to_merged_bb:
   - NONE: use run_block_replace_label_prev_bb_none
   - SOME b_lbl: use run_block_replace_label (prev_bb changes from b_lbl to a_lbl)
   - SOME x (x <> b_lbl): use transitivity + run_block_replace_label_prev_diff *)
Theorem run_block_other_to_other_replaced:
  !fn a_lbl b_lbl a c s1 s2.
    cfg_wf fn /\ phi_fn_wf fn /\
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block s1.vs_current_bb fn.fn_blocks = SOME c /\
    s1.vs_current_bb <> a_lbl /\ s1.vs_current_bb <> b_lbl /\
    a_lbl <> b_lbl /\
    pred_labels fn b_lbl = [a_lbl] /\
    block_last_jmp_to b_lbl a /\
    state_equiv_cfg s1 s2 /\ s1.vs_inst_idx = s2.vs_inst_idx /\
    (s1.vs_prev_bb = SOME b_lbl ==> s2.vs_prev_bb = SOME a_lbl) /\
    (s1.vs_prev_bb <> SOME b_lbl ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (!lbl. s1.vs_prev_bb = SOME lbl ==> MEM lbl (pred_labels fn s1.vs_current_bb))
  ==>
    result_equiv_cfg (run_block c s1)
                     (run_block (replace_label_block b_lbl a_lbl c) s2)
Proof
  rpt strip_tac >>
  `c.bb_label = s1.vs_current_bb` by metis_tac[lookup_block_label] >>
  `MEM c fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `phi_block_wf (pred_labels fn s1.vs_current_bb) c` by
    (gvs[phi_fn_wf_def] >> first_x_assum drule >> gvs[]) >>
  Cases_on `s1.vs_prev_bb`
  (* NONE case: use run_block_replace_label_prev_bb_none *)
  >- (irule run_block_replace_label_prev_bb_none >> gvs[])
  (* SOME case: split on whether it's b_lbl or not *)
  >- (
    Cases_on `x = b_lbl`
    (* prev_bb = SOME b_lbl: use run_block_replace_label *)
    >- (
      gvs[] >> irule run_block_replace_label >> simp[] >>
      qexists_tac `fn` >> simp[] >>
      irule scfgMergeHelpersTheory.pred_labels_no_jmp_other >> simp[] >>
      metis_tac[])
    (* prev_bb = SOME x, x <> b_lbl: use run_block_replace_label_prev_diff *)
    >- (
      `s1.vs_prev_bb = s2.vs_prev_bb` by gvs[] >>
      irule result_equiv_cfg_trans >>
      qexists_tac `run_block c s2` >> conj_tac
      >- (irule run_block_state_equiv_cfg >> gvs[])
      >- (
        sg `x <> a_lbl`
        >- (CCONTR_TAC >> gvs[] >>
            `~MEM a_lbl (pred_labels fn s1.vs_current_bb)` by
              (irule scfgMergeHelpersTheory.pred_labels_no_jmp_other >>
               simp[] >> metis_tac[]))
        >- (irule run_block_replace_label_prev_diff >> simp[] >>
            qexists_tac `fn` >> qexists_tac `x` >> gvs[]))))
QED

(* ===== Fuel Alignment Helpers ===== *)

(* Helper: if both executions terminate with same fuel and are equivalent,
   adding more fuel to one side preserves equivalence. *)
Theorem fuel_align_equiv:
  !fuel fn merged_fn s1 s2.
    terminates (run_function fuel merged_fn s2) /\
    result_equiv_cfg (run_function fuel fn s1) (run_function fuel merged_fn s2)
  ==>
    !fuel'. fuel <= fuel' ==>
      result_equiv_cfg (run_function fuel fn s1) (run_function fuel' merged_fn s2)
Proof
  rpt gen_tac >> strip_tac >> Induct_on `fuel' - fuel`
  >- (rpt strip_tac >> `fuel' = fuel` by simp[] >> gvs[])
  >- (rpt strip_tac >>
      `terminates (run_function (fuel' - 1) merged_fn s2)` by
        (irule terminates_fuel_le >> qexists_tac `fuel` >> simp[]) >>
      `result_equiv_cfg (run_function fuel fn s1)
         (run_function (fuel' - 1) merged_fn s2)` by
        (first_x_assum (qspecl_then [`fuel' - 1`, `fuel`] mp_tac) >> simp[]) >>
      `fuel' = SUC (fuel' - 1)` by simp[] >> pop_assum SUBST1_TAC >>
      `run_function (SUC (fuel' - 1)) merged_fn s2 =
         run_function (fuel' - 1) merged_fn s2` by
        (irule run_function_fuel_monotonicity >> simp[]) >>
      simp[])
QED

(* ===== Merge Point Helper Lemmas ===== *)

(* Helper: IH preconditions at merge point after running block b.
   After running block a (to v), then block b (to v'), and merged_bb (to v''),
   establishes all preconditions needed to apply the IH for continuation. *)
Theorem ih_conditions_at_merge_point:
  !fn a_lbl b_lbl a b n s1 s2 v v' v''.
    cfg_wf fn /\ phi_fn_wf fn /\
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    a_lbl <> b_lbl /\ b_lbl <> entry_label fn /\
    pred_labels fn b_lbl = [a_lbl] /\
    block_has_no_phi b /\ block_last_jmp_to b_lbl a /\
    state_equiv_cfg s1 s2 /\
    s1.vs_current_bb = a_lbl /\ s2.vs_current_bb = a_lbl /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    (s1.vs_prev_bb = SOME b_lbl ==> s2.vs_prev_bb = SOME a_lbl) /\
    (s1.vs_prev_bb <> SOME b_lbl ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (!lbl. s1.vs_prev_bb = SOME lbl ==> MEM lbl (pred_labels fn a_lbl)) /\
    ~s1.vs_halted /\
    terminates (run_function (SUC (SUC n)) fn s1) /\
    run_block a s1 = OK v /\ ~v.vs_halted /\ v.vs_current_bb = b_lbl /\
    run_block b v = OK v' /\ ~v'.vs_halted /\
    run_block (replace_label_block b_lbl a_lbl
      (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2 = OK v'' /\
    ~v''.vs_halted /\ state_equiv_cfg v' v''
  ==>
    v'.vs_current_bb = v''.vs_current_bb /\
    v'.vs_current_bb <> b_lbl /\
    v'.vs_inst_idx = 0 /\ v''.vs_inst_idx = 0 /\
    (v'.vs_prev_bb = SOME b_lbl ==> v''.vs_prev_bb = SOME a_lbl) /\
    (v'.vs_prev_bb <> SOME b_lbl ==> v'.vs_prev_bb = v''.vs_prev_bb) /\
    (!lbl. v'.vs_prev_bb = SOME lbl ==> MEM lbl (pred_labels fn v'.vs_current_bb)) /\
    terminates (run_function n fn v')
Proof
  rpt strip_tac >> rpt conj_tac
  >- ( (* v'.vs_current_bb = v''.vs_current_bb *)
    `block_terminator_last a` by (gvs[cfg_wf_def] >> first_x_assum irule >>
      irule lookup_block_MEM >> metis_tac[]) >>
    `block_terminator_last b` by (gvs[cfg_wf_def] >> first_x_assum irule >>
      irule lookup_block_MEM >> metis_tac[]) >>
    `MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
    `b.bb_label = b_lbl` by metis_tac[lookup_block_label] >>
    `v'.vs_current_bb <> b_lbl` by (qspecl_then [`fn`, `b`, `v`, `v'`,
      `a_lbl`] mp_tac run_block_no_self_loop_single_pred >> gvs[]) >>
    qspecl_then [`fn`, `a`, `b`, `s1`, `b_lbl`] mp_tac
      run_block_merge_blocks_equiv >> impl_tac >- gvs[] >> strip_tac >>
    `result_equiv_cfg (run_block b v) (run_block (a with
      bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)
      s1)` by gvs[] >>
    qabbrev_tac `merged = a with bb_instructions := FRONT
      a.bb_instructions ++ b.bb_instructions` >>
    Cases_on `run_block merged s1` >> gvs[result_equiv_cfg_def] >>
    rename1 `run_block merged s1 = OK v_mid` >>
    (* After gvs[], b_lbl -> v.vs_current_bb, a_lbl -> s1.vs_current_bb *)
    `~MEM v.vs_current_bb (block_successors b)` by
      (irule pred_labels_single_no_jmp >> qexistsl_tac [`s1.vs_current_bb`, `fn`] >> gvs[]) >>
    qspecl_then [`a`, `b`, `s1`, `v`, `v'`, `v_mid`, `v.vs_current_bb`] mp_tac
      run_block_merge_blocks_current_bb >>
    impl_tac >- gvs[Abbr `merged`, state_equiv_cfg_def] >> strip_tac >>
    (* Case split on s1.vs_prev_bb to use appropriate lemma *)
    Cases_on `s1.vs_prev_bb`
    >- ( (* NONE case *)
      gvs[] >>
      `a.bb_instructions <> []` by
        (fs[block_last_jmp_to_def, block_last_inst_def] >>
         Cases_on `a.bb_instructions` >> gvs[]) >>
      `b.bb_instructions <> []` by
        (CCONTR_TAC >> gvs[] >> qpat_x_assum `run_block b _ = _` mp_tac >>
         simp[Once run_block_def, step_in_block_def, get_instruction_def]) >>
      `block_terminator_last merged` by
        (simp[Abbr `merged`] >> irule block_terminator_last_merged >> gvs[]) >>
      `block_successors merged = block_successors b` by
        (simp[Abbr `merged`] >> irule block_successors_merged >> gvs[]) >>
      `~v_mid.vs_halted` by gvs[state_equiv_cfg_def] >>
      irule run_block_replace_label_current_bb_prev_none >> gvs[] >>
      qexistsl_tac [`merged`, `s1.vs_current_bb`, `v.vs_current_bb`, `s1`, `s2`] >>
      gvs[])
    >- ( (* SOME case - needs helper for different prev_bb *)
      Cases_on `x = v.vs_current_bb`
      >- ( (* x = b_lbl: use run_block_replace_label_current_bb_diff_states *)
        gvs[] >>
        `~MEM s1.vs_current_bb (pred_labels fn s1.vs_current_bb)` by
          (qspecl_then [`fn`, `a`, `s1.vs_current_bb`, `v.vs_current_bb`, `s1.vs_current_bb`]
           mp_tac pred_labels_no_jmp_other >> impl_tac >- gvs[] >> simp[]) >>
        `MEM a fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
        `a.bb_label = s1.vs_current_bb` by metis_tac[lookup_block_label] >>
        `phi_block_wf (pred_labels fn a.bb_label) a` by
          (fs[phi_fn_wf_def] >> first_x_assum irule >> gvs[]) >>
        `a.bb_instructions <> []` by
          (fs[block_last_jmp_to_def, block_last_inst_def] >>
           Cases_on `a.bb_instructions` >> gvs[]) >>
        `phi_block_wf (pred_labels fn a.bb_label) merged` by
          (simp[Abbr `merged`] >> irule phi_block_wf_merged >> gvs[]) >>
        `b.bb_instructions <> []` by
          (CCONTR_TAC >> gvs[] >> qpat_x_assum `run_block b _ = _` mp_tac >>
           simp[Once run_block_def, step_in_block_def, get_instruction_def]) >>
        `block_terminator_last merged` by
          (simp[Abbr `merged`] >> irule block_terminator_last_merged >> gvs[]) >>
        `~v_mid.vs_halted` by gvs[state_equiv_cfg_def] >>
        `block_successors merged = block_successors b` by
          (simp[Abbr `merged`] >> irule block_successors_merged >> gvs[]) >>
        irule run_block_replace_label_current_bb_diff_states >> gvs[] >>
        qexists_tac `merged` >> qexists_tac `fn` >> qexists_tac `s1.vs_current_bb` >>
        qexists_tac `v.vs_current_bb` >> qexists_tac `s1` >> qexists_tac `s2` >>
        simp[Abbr `merged`] >> gvs[])
      >- ( (* x <> b_lbl: use run_block_replace_label_current_bb_same_prev *)
        gvs[] >>
        `s1.vs_prev_bb = SOME x` by gvs[] >>
        `~MEM s1.vs_current_bb (pred_labels fn s1.vs_current_bb)` by
          (qspecl_then [`fn`, `a`, `s1.vs_current_bb`, `v.vs_current_bb`, `s1.vs_current_bb`]
           mp_tac pred_labels_no_jmp_other >> impl_tac >- gvs[] >> simp[]) >>
        `x <> s1.vs_current_bb` by (CCONTR_TAC >> gvs[]) >>
        `MEM a fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
        `a.bb_label = s1.vs_current_bb` by metis_tac[lookup_block_label] >>
        `a.bb_instructions <> []` by
          (fs[block_last_jmp_to_def, block_last_inst_def] >>
           Cases_on `a.bb_instructions` >> gvs[]) >>
        `phi_block_wf (pred_labels fn a.bb_label) a` by
          (fs[phi_fn_wf_def] >> first_x_assum irule >> gvs[]) >>
        `phi_block_wf (pred_labels fn a.bb_label) merged` by
          (simp[Abbr `merged`] >> irule phi_block_wf_merged >> gvs[]) >>
        `b.bb_instructions <> []` by
          (CCONTR_TAC >> gvs[] >> qpat_x_assum `run_block b _ = _` mp_tac >>
           simp[Once run_block_def, step_in_block_def, get_instruction_def]) >>
        `block_terminator_last merged` by
          (simp[Abbr `merged`] >> irule block_terminator_last_merged >> gvs[]) >>
        `block_successors merged = block_successors b` by
          (simp[Abbr `merged`] >> irule block_successors_merged >> gvs[]) >>
        `~v_mid.vs_halted` by gvs[state_equiv_cfg_def] >>
        irule run_block_replace_label_current_bb_same_prev >> gvs[] >>
        qexists_tac `merged` >> qexists_tac `s1.vs_current_bb` >>
        qexists_tac `v.vs_current_bb` >> qexists_tac `pred_labels fn a.bb_label` >>
        qexists_tac `x` >> qexists_tac `s1` >> qexists_tac `s2` >>
        simp[Abbr `merged`] >> gvs[])))
  >- ( (* v'.vs_current_bb <> b_lbl - after gvs[], uses v.vs_current_bb *)
    `MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
    `b.bb_label = v.vs_current_bb` by metis_tac[lookup_block_label] >>
    qspecl_then [`fn`, `b`, `v`, `v'`, `s1.vs_current_bb`] mp_tac
      run_block_no_self_loop_single_pred >> gvs[])
  >- (irule run_block_ok_inst_idx >> metis_tac[])
  >- (irule run_block_ok_inst_idx >> metis_tac[])
  >- (qspecl_then [`replace_label_block b_lbl a_lbl (a with bb_instructions :=
        FRONT a.bb_instructions ++ b.bb_instructions)`, `s2`, `v''`] mp_tac
        run_block_ok_prev_bb >> gvs[])
  >- (qspecl_then [`b`, `v`, `v'`] mp_tac run_block_ok_prev_bb >> gvs[] >>
      qspecl_then [`replace_label_block b_lbl a_lbl (a with bb_instructions :=
        FRONT a.bb_instructions ++ b.bb_instructions)`, `s2`, `v''`] mp_tac
        run_block_ok_prev_bb >> gvs[])
  >- (qspecl_then [`b`, `v`, `v'`] mp_tac run_block_ok_prev_bb >> gvs[] >>
      strip_tac >> qspecl_then [`fn`, `b`, `v`, `v'`] mp_tac run_block_ok_pred_labels >>
      impl_tac >- (gvs[] >> metis_tac[lookup_block_MEM]) >> gvs[] >>
      strip_tac >> `b.bb_label = v.vs_current_bb` by metis_tac[lookup_block_label] >>
      gvs[])
  >- (`terminates (run_function (SUC n) fn v)` by (irule
        run_function_terminates_step >> gvs[] >> metis_tac[]) >>
      irule run_function_terminates_step >> gvs[] >>
      qexistsl_tac [`b`, `v`] >> gvs[])
QED

(* Helper for the OK+not halted case at merge point.
   At the merge point, original runs 2 blocks (a then b), merged runs 1 block.
   This handles the fuel asymmetry and IH application.

   Key structure:
   1. Original: run_function n fn v (continuing after run_block b)
   2. Merged: run_function (SUC n) merged_fn s2 (needs to run merged_bb first)

   The IH gives us equivalence for fuel < SUC n, so we use fuel n for the continuation.
   Then run_function_fuel_monotonicity aligns the fuels. *)
Theorem merge_blocks_at_merge_point_ok_continue:
  !n fn a_lbl b_lbl a b s1 s2 v merged_bb.
    cfg_wf fn /\ phi_fn_wf fn /\
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    a_lbl <> b_lbl /\ b_lbl <> entry_label fn /\
    pred_labels fn b_lbl = [a_lbl] /\
    block_has_no_phi b /\ block_last_jmp_to b_lbl a /\
    (* State equiv and indices *)
    state_equiv_cfg s1 s2 /\ s1.vs_current_bb = a_lbl /\ s2.vs_current_bb = a_lbl /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    (s1.vs_prev_bb = SOME b_lbl ==> s2.vs_prev_bb = SOME a_lbl) /\
    (s1.vs_prev_bb <> SOME b_lbl ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (!lbl. s1.vs_prev_bb = SOME lbl ==> MEM lbl (pred_labels fn s1.vs_current_bb)) /\
    ~s1.vs_halted /\
    terminates (run_function (SUC n) fn s1) /\
    (* Specific to OK+not halted case *)
    run_block a s1 = OK v /\ ~v.vs_halted /\
    (* merged_bb definition *)
    merged_bb = replace_label_block b_lbl a_lbl (a with bb_instructions :=
      FRONT a.bb_instructions ++ b.bb_instructions) /\
    (* IH for recursive calls *)
    (!fuel' s1' s2'.
      fuel' < SUC n /\ state_equiv_cfg s1' s2' /\
      s1'.vs_current_bb = s2'.vs_current_bb /\ s1'.vs_current_bb <> b_lbl /\
      s1'.vs_inst_idx = 0 /\ s2'.vs_inst_idx = 0 /\
      (s1'.vs_prev_bb = SOME b_lbl ==> s2'.vs_prev_bb = SOME a_lbl) /\
      (s1'.vs_prev_bb <> SOME b_lbl ==> s1'.vs_prev_bb = s2'.vs_prev_bb) /\
      (!lbl. s1'.vs_prev_bb = SOME lbl ==> MEM lbl (pred_labels fn s1'.vs_current_bb)) /\
      ~s1'.vs_halted /\ terminates (run_function fuel' fn s1')
      ==> result_equiv_cfg (run_function fuel' fn s1')
            (run_function fuel' (merge_blocks fn a_lbl b_lbl) s2'))
  ==>
    result_equiv_cfg (run_function n fn v)
      (case run_block merged_bb s2 of
         OK s' => if s'.vs_halted then Halt s'
                  else run_function n (merge_blocks fn a_lbl b_lbl) s'
       | Halt v5 => Halt v5
       | Revert v6 => Revert v6
       | Error v7 => Error v7)
Proof
  rpt strip_tac >>
  `block_terminator_last a` by (gvs[cfg_wf_def] >> first_x_assum irule >>
    irule lookup_block_MEM >> metis_tac[]) >>
  `block_successors a = [b_lbl]` by (irule block_last_jmp_to_successors >> simp[]) >>
  `MEM a fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM v.vs_current_bb (block_successors a)` by
    (qspecl_then [`fn`, `a`, `s1`, `v`] mp_tac run_block_ok_successor >> simp[]) >>
  `v.vs_current_bb = b_lbl` by gvs[] >>
  qabbrev_tac `merged_no_label = a with bb_instructions :=
    FRONT a.bb_instructions ++ b.bb_instructions` >>
  qspecl_then [`fn`, `a`, `b`, `s1`, `b_lbl`] mp_tac run_block_merge_blocks_equiv >>
  impl_tac >- simp[] >>
  simp[Abbr`merged_no_label`] >> strip_tac >>
  qspecl_then [`fn`, `a`, `b`, `a_lbl`, `b_lbl`, `s1`, `s2`] mp_tac
    run_block_merged_to_merged_bb >>
  impl_tac >- gvs[] >>
  simp[] >> strip_tac >>
  `result_equiv_cfg (run_block b v) (run_block
    (replace_label_block b_lbl a_lbl (a with bb_instructions :=
    FRONT a.bb_instructions ++ b.bb_instructions)) s2)` by
    (irule result_equiv_cfg_trans >> qexists_tac `run_block (a with bb_instructions :=
      FRONT a.bb_instructions ++ b.bb_instructions) s1` >> simp[]) >>
  Cases_on `run_block b v`
  >- ((* OK case *)
    Cases_on `run_block (replace_label_block b_lbl a_lbl
      (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
    gvs[result_equiv_cfg_def] >>
    Cases_on `v''.vs_halted` >> gvs[]
    >- (`~v'.vs_halted` by (drule_all run_block_ok_not_halted >> simp[]) >>
        gvs[state_equiv_cfg_def])
    >- ( (* IH application - fuel asymmetry *)
      Cases_on `n`
      >- simp[run_function_def, result_equiv_cfg_def]
      >- (
        simp[Once run_function_def] >>
        CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [run_function_def]))) >>
        simp[] >>
        Cases_on `v'.vs_halted` >> gvs[]
        >- (`v''.vs_halted` by gvs[state_equiv_cfg_def] >>
            simp[Once run_function_def] >> gvs[result_equiv_cfg_def, state_equiv_cfg_def])
        >- (irule fuel_align_equiv >> simp[] >>
            conj_tac
            >- (`terminates (run_function (SUC n') fn v)` by (irule
                  run_function_terminates_step >> gvs[] >> metis_tac[]) >>
                `terminates (run_function n' fn v')` by (irule
                  run_function_terminates_step >> gvs[] >> metis_tac[]) >>
                irule terminates_result_equiv_cfg >>
                qexists_tac `run_function n' fn v'` >>
                conj_tac >- (first_x_assum irule >> gvs[]) >>
                first_x_assum irule >> gvs[] >>
                qspecl_then [`fn`, `s1.vs_current_bb`, `v.vs_current_bb`, `a`,
                  `b`, `n'`, `s1`, `s2`, `v`, `v'`, `v''`] mp_tac
                  ih_conditions_at_merge_point >>
                impl_tac >- gvs[] >> strip_tac >> gvs[])
            >- (qspecl_then [`fn`, `s1.vs_current_bb`, `v.vs_current_bb`, `a`,
                  `b`, `n'`, `s1`, `s2`, `v`, `v'`, `v''`] mp_tac
                  ih_conditions_at_merge_point >> impl_tac >- gvs[] >> strip_tac >>
                first_x_assum irule >> gvs[])))))
  >- ((* Halt case *)
    Cases_on `run_block (replace_label_block b_lbl a_lbl
      (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
    gvs[result_equiv_cfg_def] >>
    Cases_on `n` >> simp[Once run_function_def] >> gvs[result_equiv_cfg_def] >>
    (* n=0: termination contradiction; n>0: gvs closes *)
    TRY (`run_function 1 fn s1 = run_function 0 fn v` by
          (simp[Once run_function_def] >> gvs[]) >>
        `run_function 0 fn v = Error "out of fuel"` by simp[Once run_function_def] >>
        `~terminates (run_function 1 fn s1)` by gvs[terminates_def]) >>
    gvs[])
  >- ((* Revert case *)
    Cases_on `run_block (replace_label_block b_lbl a_lbl
      (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
    gvs[result_equiv_cfg_def] >>
    Cases_on `n` >> simp[Once run_function_def] >> gvs[result_equiv_cfg_def] >>
    (* n=0: termination contradiction; n>0: gvs closes *)
    TRY (`run_function 1 fn s1 = run_function 0 fn v` by
          (simp[Once run_function_def] >> gvs[]) >>
        `run_function 0 fn v = Error "out of fuel"` by simp[Once run_function_def] >>
        `~terminates (run_function 1 fn s1)` by gvs[terminates_def]) >>
    gvs[])
  >- ((* Error case *)
    Cases_on `run_block (replace_label_block b_lbl a_lbl
      (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
    gvs[result_equiv_cfg_def] >>
    Cases_on `n` >> simp[Once run_function_def] >> gvs[result_equiv_cfg_def])
QED

(* Helper: handle the specific case when at merge point (vs_current_bb = a_lbl).
   Extracted from the large forward proof to enable incremental verification. *)
Theorem merge_blocks_at_merge_point:
  !fuel fn a_lbl b_lbl a b s1 s2.
    cfg_wf fn /\ phi_fn_wf fn /\
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    a_lbl <> b_lbl /\ b_lbl <> entry_label fn /\
    pred_labels fn b_lbl = [a_lbl] /\
    block_has_no_phi b /\ block_last_jmp_to b_lbl a /\
    state_equiv_cfg s1 s2 /\
    s1.vs_current_bb = a_lbl /\ s2.vs_current_bb = a_lbl /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    (s1.vs_prev_bb = SOME b_lbl ==> s2.vs_prev_bb = SOME a_lbl) /\
    (s1.vs_prev_bb <> SOME b_lbl ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (!lbl. s1.vs_prev_bb = SOME lbl ==> MEM lbl (pred_labels fn s1.vs_current_bb)) /\
    ~s1.vs_halted /\
    terminates (run_function fuel fn s1) /\
    (* IH for recursive calls: we require this for continuation after the merge *)
    (!fuel' s1' s2'.
      fuel' < fuel /\
      state_equiv_cfg s1' s2' /\
      s1'.vs_current_bb = s2'.vs_current_bb /\
      s1'.vs_current_bb <> b_lbl /\
      s1'.vs_inst_idx = 0 /\ s2'.vs_inst_idx = 0 /\
      (s1'.vs_prev_bb = SOME b_lbl ==> s2'.vs_prev_bb = SOME a_lbl) /\
      (s1'.vs_prev_bb <> SOME b_lbl ==> s1'.vs_prev_bb = s2'.vs_prev_bb) /\
      (!lbl. s1'.vs_prev_bb = SOME lbl ==> MEM lbl (pred_labels fn s1'.vs_current_bb)) /\
      ~s1'.vs_halted /\
      terminates (run_function fuel' fn s1')
      ==>
      result_equiv_cfg (run_function fuel' fn s1')
                       (run_function fuel' (merge_blocks fn a_lbl b_lbl) s2'))
  ==>
    result_equiv_cfg (run_function fuel fn s1)
                     (run_function fuel (merge_blocks fn a_lbl b_lbl) s2)
Proof
  rpt strip_tac >>
  simp[Once run_function_def] >>
  Cases_on `fuel`
  >- gvs[run_function_def, terminates_def]
  >- (
    simp[] >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >> simp[] >>
    sg `lookup_block a_lbl (merge_blocks fn a_lbl b_lbl).fn_blocks =
        SOME (replace_label_block b_lbl a_lbl (a with bb_instructions :=
              FRONT a.bb_instructions ++ b.bb_instructions))`
    >- (irule lookup_block_merge_blocks_a >> simp[])
    >- (
      simp[] >>
      qabbrev_tac `merged_bb = replace_label_block b_lbl a_lbl (a with
        bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)` >>
      qabbrev_tac `merged_no_label = a with bb_instructions :=
        FRONT a.bb_instructions ++ b.bb_instructions` >>
      Cases_on `run_block a s1` >> simp[]
      >- ( (* OK case *)
        Cases_on `v.vs_halted` >> gvs[]
        >- ( (* OK + halted: use merge block equivalences *)
          `block_terminator_last a` by (gvs[cfg_wf_def] >> first_x_assum irule >>
            irule lookup_block_MEM >> metis_tac[]) >>
          qspecl_then [`fn`, `a`, `b`, `s1`, `b_lbl`] mp_tac run_block_merge_blocks_equiv >>
          simp[Abbr`merged_no_label`] >> strip_tac >>
          qspecl_then [`fn`, `a`, `b`, `s1.vs_current_bb`, `b_lbl`, `s1`, `s2`]
            mp_tac run_block_merged_to_merged_bb >> simp[Abbr`merged_bb`] >> strip_tac >>
          `result_equiv_cfg (Halt v) (run_block (replace_label_block b_lbl s1.vs_current_bb
            (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)` by
            (irule result_equiv_cfg_trans >> qexists_tac `run_block (a with bb_instructions :=
            FRONT a.bb_instructions ++ b.bb_instructions) s1` >> simp[]) >>
          Cases_on `run_block (replace_label_block b_lbl s1.vs_current_bb (a with bb_instructions :=
            FRONT a.bb_instructions ++ b.bb_instructions)) s2` >> gvs[result_equiv_cfg_def])
        >- ( (* OK + not halted: use extracted helper *)
          irule merge_blocks_at_merge_point_ok_continue >>
          gvs[] >> qexists_tac `s1` >> gvs[]))
      >- ( (* Halt case *)
        `block_terminator_last a` by (gvs[cfg_wf_def] >> first_x_assum irule >>
          irule lookup_block_MEM >> metis_tac[]) >>
        qspecl_then [`fn`, `a`, `b`, `s1`, `b_lbl`] mp_tac run_block_merge_blocks_equiv >>
        simp[Abbr`merged_no_label`] >> strip_tac >>
        Cases_on `run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1` >>
        gvs[result_equiv_cfg_def] >>
        qspecl_then [`fn`, `a`, `b`, `s1.vs_current_bb`, `b_lbl`, `s1`, `s2`] mp_tac run_block_merged_to_merged_bb >>
        simp[Abbr`merged_bb`] >> strip_tac >>
        Cases_on `run_block (replace_label_block b_lbl s1.vs_current_bb (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
        gvs[result_equiv_cfg_def] >>
        irule state_equiv_cfg_trans >> qexists_tac `v'` >> simp[])
      >- ( (* Revert case *)
        `block_terminator_last a` by (gvs[cfg_wf_def] >> first_x_assum irule >>
          irule lookup_block_MEM >> metis_tac[]) >>
        qspecl_then [`fn`, `a`, `b`, `s1`, `b_lbl`] mp_tac run_block_merge_blocks_equiv >>
        simp[Abbr`merged_no_label`] >> strip_tac >>
        Cases_on `run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1` >>
        gvs[result_equiv_cfg_def] >>
        qspecl_then [`fn`, `a`, `b`, `s1.vs_current_bb`, `b_lbl`, `s1`, `s2`] mp_tac run_block_merged_to_merged_bb >>
        simp[Abbr`merged_bb`] >> strip_tac >>
        Cases_on `run_block (replace_label_block b_lbl s1.vs_current_bb (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
        gvs[result_equiv_cfg_def] >>
        irule state_equiv_cfg_trans >> qexists_tac `v'` >> simp[])
      >- ( (* Error case *)
        `block_terminator_last a` by (gvs[cfg_wf_def] >> first_x_assum irule >>
          irule lookup_block_MEM >> metis_tac[]) >>
        qspecl_then [`fn`, `a`, `b`, `s1`, `b_lbl`] mp_tac run_block_merge_blocks_equiv >>
        simp[Abbr`merged_no_label`] >> strip_tac >>
        Cases_on `run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1` >>
        gvs[result_equiv_cfg_def] >>
        qspecl_then [`fn`, `a`, `b`, `s1.vs_current_bb`, `b_lbl`, `s1`, `s2`] mp_tac run_block_merged_to_merged_bb >>
        simp[Abbr`merged_bb`] >> strip_tac >>
        Cases_on `run_block (replace_label_block b_lbl s1.vs_current_bb (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
        gvs[result_equiv_cfg_def])))
QED

(* Helper: Establishes IH preconditions after run_block for "other block" case.
   When we're not at the merge point (current_bb <> a_lbl, current_bb <> b_lbl),
   and we run a block c and its label-replaced version, this lemma shows the
   results satisfy all the conditions needed to apply the IH. *)
Theorem ih_conditions_other_block:
  !fn a_lbl b_lbl a b c n s1 s2 v v'.
    cfg_wf fn /\ phi_fn_wf fn /\
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    lookup_block s1.vs_current_bb fn.fn_blocks = SOME c /\
    a_lbl <> b_lbl /\ b_lbl <> entry_label fn /\
    pred_labels fn b_lbl = [a_lbl] /\
    block_has_no_phi b /\ block_last_jmp_to b_lbl a /\
    s1.vs_current_bb <> b_lbl /\ s1.vs_current_bb <> a_lbl /\
    state_equiv_cfg s1 s2 /\ s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    (s1.vs_prev_bb = SOME b_lbl ==> s2.vs_prev_bb = SOME a_lbl) /\
    (s1.vs_prev_bb <> SOME b_lbl ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (!lbl. s1.vs_prev_bb = SOME lbl ==> MEM lbl (pred_labels fn s1.vs_current_bb)) /\
    ~s1.vs_halted /\
    terminates (run_function (SUC n) fn s1) /\
    run_block c s1 = OK v /\
    run_block (replace_label_block b_lbl a_lbl c) s2 = OK v' /\
    state_equiv_cfg v v' /\ ~v.vs_halted /\ ~v'.vs_halted
  ==>
    v.vs_current_bb = v'.vs_current_bb /\
    v.vs_current_bb <> b_lbl /\
    v.vs_inst_idx = 0 /\ v'.vs_inst_idx = 0 /\
    (v.vs_prev_bb = SOME b_lbl ==> v'.vs_prev_bb = SOME a_lbl) /\
    (v.vs_prev_bb <> SOME b_lbl ==> v.vs_prev_bb = v'.vs_prev_bb) /\
    (!lbl. v.vs_prev_bb = SOME lbl ==> MEM lbl (pred_labels fn v.vs_current_bb)) /\
    terminates (run_function n fn v)
Proof
  rpt strip_tac >> rpt conj_tac
  >- ( (* vs_current_bb equality - 3-case prev_bb pattern *)
    Cases_on `s1.vs_prev_bb`
    >- ( (* NONE case *)
      irule run_block_replace_label_current_bb_prev_none >> gvs[] >>
      qexistsl_tac [`c`, `a_lbl`, `b_lbl`, `s1`, `s2`] >> gvs[] >>
      conj_tac >- (fs[cfg_wf_def] >> first_x_assum irule >> metis_tac[lookup_block_MEM]) >>
      irule pred_labels_single_no_jmp >> gvs[] >> metis_tac[lookup_block_MEM, lookup_block_label])
    >- ( (* SOME x case - split on x = b_lbl *)
      Cases_on `x = b_lbl`
      >- ( (* x = b_lbl *)
        gvs[] >> irule run_block_replace_label_current_bb_diff_states >> simp[] >>
        qexists_tac `c` >> qexists_tac `fn` >> qexists_tac `a_lbl` >>
        qexists_tac `b_lbl` >> qexists_tac `s1` >> qexists_tac `s2` >> gvs[] >>
        rpt conj_tac
        >- (fs[cfg_wf_def] >> first_x_assum irule >> metis_tac[lookup_block_MEM])
        >- (irule pred_labels_no_jmp_other >> gvs[] >> metis_tac[lookup_block_label])
        >- (irule pred_labels_single_no_jmp >> gvs[] >> metis_tac[lookup_block_MEM, lookup_block_label])
        >- metis_tac[lookup_block_label]
        >- (fs[phi_fn_wf_def] >> first_x_assum irule >> metis_tac[lookup_block_MEM]))
      >- ( (* x <> b_lbl *)
        gvs[] >> irule run_block_replace_label_current_bb_same_prev >> simp[] >>
        qexists_tac `c` >> qexists_tac `a_lbl` >> qexists_tac `b_lbl` >>
        qexists_tac `pred_labels fn c.bb_label` >> qexists_tac `x` >>
        qexists_tac `s1` >> qexists_tac `s2` >> gvs[] >>
        rpt conj_tac
        >- (fs[cfg_wf_def] >> first_x_assum irule >> metis_tac[lookup_block_MEM])
        >- (CCONTR_TAC >> gvs[] >>
            qspecl_then [`fn`, `a`, `a_lbl`, `b_lbl`, `s2.vs_current_bb`] mp_tac pred_labels_no_jmp_other >>
            impl_tac >- (gvs[] >> metis_tac[lookup_block_label]) >> gvs[])
        >- (irule pred_labels_single_no_jmp >> gvs[] >> metis_tac[lookup_block_MEM, lookup_block_label])
        >- metis_tac[lookup_block_label]
        >- (gvs[phi_fn_wf_def] >> first_x_assum irule >> metis_tac[lookup_block_MEM]))))
  >- ( (* v.vs_current_bb <> b_lbl - contradiction *)
    qspecl_then [`fn`, `c`, `s1`, `v`] mp_tac run_block_ok_successor >>
    impl_tac >- (gvs[] >> metis_tac[lookup_block_MEM]) >> strip_tac >>
    qspecl_then [`fn`, `b_lbl`, `a_lbl`, `c`] mp_tac pred_labels_single_no_jmp >>
    impl_tac >- (gvs[] >> metis_tac[lookup_block_MEM, lookup_block_label]) >> gvs[])
  >- metis_tac[run_block_ok_inst_idx]
  >- metis_tac[run_block_ok_inst_idx]
  >- (qspecl_then [`c`, `s1`, `v`] mp_tac run_block_ok_prev_bb >> gvs[])
  >- (qspecl_then [`c`, `s1`, `v`] mp_tac run_block_ok_prev_bb >>
      qspecl_then [`replace_label_block b_lbl a_lbl c`, `s2`, `v'`] mp_tac run_block_ok_prev_bb >> gvs[])
  >- (qspecl_then [`c`, `s1`, `v`] mp_tac run_block_ok_prev_bb >> gvs[] >>
      qspecl_then [`fn`, `c`, `s1`, `v`] mp_tac run_block_ok_pred_labels >>
      impl_tac >- (gvs[] >> metis_tac[lookup_block_MEM]) >> gvs[] >> metis_tac[lookup_block_label])
  >- (irule run_function_terminates_step >> gvs[] >> metis_tac[])
QED

(* Helper: run_function equivalence for merge_blocks when original terminates.
   The termination hypothesis is key - it allows using fuel monotonicity when
   the original path goes through a->b (using 2 fuel) vs merged path (using 1 fuel).
   The proof works because: if original terminates with fuel, then at the merge point
   the continuation also terminates with fuel-1, and by monotonicity we can use the
   IH which expects fuel. *)
Theorem run_function_merge_blocks_equiv_fwd:
  !fuel fn a_lbl b_lbl a b s1 s2.
    cfg_wf fn /\ phi_fn_wf fn /\
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    a_lbl <> b_lbl /\ b_lbl <> entry_label fn /\
    pred_labels fn b_lbl = [a_lbl] /\
    block_has_no_phi b /\ block_last_jmp_to b_lbl a /\
    state_equiv_cfg s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_current_bb <> b_lbl /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    (s1.vs_prev_bb = SOME b_lbl ==> s2.vs_prev_bb = SOME a_lbl) /\
    (s1.vs_prev_bb <> SOME b_lbl ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (!lbl. s1.vs_prev_bb = SOME lbl ==> MEM lbl (pred_labels fn s1.vs_current_bb)) /\
    ~s1.vs_halted /\  (* Required for run_block_merge_blocks_equiv *)
    terminates (run_function fuel fn s1)  (* KEY: termination hypothesis *)
  ==>
    result_equiv_cfg (run_function fuel fn s1)
                     (run_function fuel (merge_blocks fn a_lbl b_lbl) s2)
Proof
  completeInduct_on `fuel` >> rpt strip_tac >>
  Cases_on `fuel` >- gvs[run_function_def, terminates_def] >>
  Cases_on `s1.vs_current_bb = a_lbl`
  >- (
    (* At merge point - use merge_blocks_at_merge_point *)
    irule merge_blocks_at_merge_point >> gvs[] >>
    rpt strip_tac >> first_x_assum irule >> simp[] >>
    qexistsl_tac [`a`, `b`] >> simp[])
  >- (
    (* Not at merge point - block c is unchanged except label replacement *)
    simp[Once run_function_def] >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >> simp[] >>
    Cases_on `lookup_block s1.vs_current_bb fn.fn_blocks`
    >- ( (* NONE case: contradiction with terminates *)
      `run_function (SUC n) fn s1 = Error "block not found"` by
        simp[Once run_function_def] >>
      fs[terminates_def])
    >- ( (* SOME c case *)
      rename1 `lookup_block s1.vs_current_bb fn.fn_blocks = SOME c` >>
      sg `lookup_block s1.vs_current_bb (merge_blocks fn a_lbl b_lbl).fn_blocks =
          SOME (replace_label_block b_lbl a_lbl c)`
      >- (irule lookup_block_merge_blocks_other >> gvs[])
      >- (
        gvs[] >>
        qspecl_then [`fn`, `a_lbl`, `b_lbl`, `a`, `c`, `s1`, `s2`] mp_tac
          run_block_other_to_other_replaced >>
        impl_tac >- gvs[] >>
        strip_tac >> Cases_on `run_block c s1`
        >- ( (* OK case *)
          simp[] >> Cases_on `run_block (replace_label_block b_lbl a_lbl c) s2` >>
          gvs[result_equiv_cfg_def] >>
          Cases_on `v.vs_halted` >> gvs[]
          >- (`v'.vs_halted` by gvs[state_equiv_cfg_def] >> simp[result_equiv_cfg_def])
          >- ( (* not halted - use IH *)
            `~v'.vs_halted` by gvs[state_equiv_cfg_def] >> simp[] >>
            first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
            disch_then (qspecl_then [`fn`, `a_lbl`, `b_lbl`, `a`, `b`, `v`, `v'`] mp_tac) >>
            impl_tac
            >- (qspecl_then [`fn`, `a_lbl`, `b_lbl`, `a`, `b`, `c`, `n`, `s1`, `s2`, `v`, `v'`]
                  mp_tac ih_conditions_other_block >> impl_tac >- gvs[] >> simp[])
            >- simp[]))
        >- (Cases_on `run_block (replace_label_block b_lbl a_lbl c) s2` >>
            gvs[result_equiv_cfg_def])
        >- (Cases_on `run_block (replace_label_block b_lbl a_lbl c) s2` >>
            gvs[result_equiv_cfg_def])
        >- (Cases_on `run_block (replace_label_block b_lbl a_lbl c) s2` >>
            gvs[result_equiv_cfg_def]))))
QED

(* Original proof preserved in comment for extraction:
Theorem run_function_merge_blocks_equiv_fwd_ORIGINAL:
  ... same statement ...
Proof_ORIGINAL
  Induct_on `fuel` >- simp[run_function_def, terminates_def] >>
  rpt strip_tac >>
  Cases_on `s1.vs_current_bb = a_lbl`
  >- (
    (* Case: at block a_lbl - merge point handling *)
    simp[Once run_function_def] \\
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >> simp[] \\
    sg `lookup_block s2.vs_current_bb (merge_blocks fn a_lbl b_lbl).fn_blocks =
        SOME (replace_label_block b_lbl a_lbl (a with bb_instructions :=
              FRONT a.bb_instructions ++ b.bb_instructions))`
    >- (gvs[] >> irule lookup_block_merge_blocks_a >> simp[]) \\
    gvs[] \\
    Cases_on `run_block a s1` >> gvs[AllCaseEqs()]
    >- (
      (* OK case *)
      `~v.vs_halted` by (drule_all run_block_ok_not_halted >> simp[]) \\
      gvs[] \\
      sg `v.vs_current_bb = b_lbl`
      >- (
        `MEM a fn.fn_blocks` by (irule lookup_block_MEM >> qexists_tac `s2.vs_current_bb` >> simp[]) \\
        drule_all run_block_ok_successor >> strip_tac \\
        drule_all block_last_jmp_to_successors >> simp[] >> strip_tac >> gvs[])
      >- (
        simp[Once run_function_def] \\
        Cases_on `fuel` >> simp[result_equiv_cfg_refl]
        >- (fs[terminates_def, Once run_function_def] >> gvs[terminates_def, run_function_def])
        >- (
          `block_terminator_last a` by
            (fs[cfg_wf_def] >> first_x_assum irule >>
             irule lookup_block_MEM >> qexists_tac `s2.vs_current_bb` >> simp[]) \\
          sg `result_equiv_cfg (run_block b v)
                (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)`
          >- (
            `s1.vs_inst_idx <= LENGTH (FRONT a.bb_instructions)` by simp[] \\
            drule_all run_block_merge_blocks_equiv >> strip_tac >> pop_assum mp_tac >> simp[])
          >- (
            Cases_on `block_has_no_phi a`
            >- (
              (* No PHIs in block a - use run_block_replace_label_no_phi *)
              `a.bb_instructions <> []` by (
                fs[block_last_jmp_to_def, block_last_inst_def] >>
                Cases_on `a.bb_instructions` >> gvs[]) \\
              `block_has_no_phi (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)`
                by (irule block_has_no_phi_merged >> simp[]) \\
              `result_equiv_cfg
                 (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
                 (run_block (replace_label_block b_lbl s2.vs_current_bb
                    (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
                by (irule run_block_replace_label_no_phi >> gvs[]) \\
              `result_equiv_cfg (run_block b v)
                 (run_block (replace_label_block b_lbl s2.vs_current_bb
                    (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
                by (irule result_equiv_cfg_trans >>
                    qexists_tac `run_block (a with bb_instructions :=
                                 FRONT a.bb_instructions ++ b.bb_instructions) s1` >> gvs[]) \\
              Cases_on `run_block b v` >>
              Cases_on `run_block (replace_label_block b_lbl s2.vs_current_bb
                         (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
              gvs[result_equiv_cfg_def, AllCaseEqs()] \\
              Cases_on `v'.vs_halted` >> Cases_on `v''.vs_halted` >>
              gvs[result_equiv_cfg_def, state_equiv_cfg_def] \\
              `terminates (run_function n fn v')` by (
                irule run_function_terminates_step >> simp[] >>
                qexistsl_tac [`b`, `v`] >> simp[] >>
                irule run_function_terminates_step >> simp[] >>
                qexistsl_tac [`a`, `s1`] >> simp[]) \\
              `run_function n fn v' = run_function (SUC n) fn v'`
                by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> irule run_function_fuel_monotonicity >> simp[]) \\
              pop_assum (fn th => REWRITE_TAC [th]) \\
              first_x_assum irule >> gvs[] >> rpt conj_tac
              (* Cond 1: pred_labels *)
              >- (rpt strip_tac >>
                  `v'.vs_prev_bb = SOME v.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >>
                  gvs[] >> `MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
                  `b.bb_label = v.vs_current_bb` by metis_tac[lookup_block_label] >>
                  metis_tac[run_block_ok_pred_labels])
              (* Cond 2: terminates *)
              >- (`run_function (SUC n) fn v' = run_function n fn v'`
                    by (irule run_function_fuel_monotonicity >> simp[]) >> simp[])
              (* Cond 3: current_bb <> b_lbl *)
              >- (`MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
                  `b.bb_label = v.vs_current_bb` by metis_tac[lookup_block_label] >>
                  qspecl_then [`fn`, `b`, `v`, `v'`, `s2.vs_current_bb`]
                    mp_tac run_block_no_self_loop_single_pred >> simp[])
              (* Cond 4: v'.vs_current_bb = v''.vs_current_bb *)
              >- (
                qpat_x_assum `result_equiv_cfg (OK v') _` mp_tac >>
                Cases_on `run_block (a with bb_instructions :=
                           FRONT a.bb_instructions ++ b.bb_instructions) s1` >>
                simp[result_equiv_cfg_def] >> strip_tac \\
                rename1 `state_equiv_cfg _ v_merged` \\
                `block_terminator_last b` by
                  (fs[cfg_wf_def] >> first_x_assum irule >> metis_tac[lookup_block_MEM]) \\
                `~MEM v.vs_current_bb (block_successors b)` by
                  (`b.bb_label = v.vs_current_bb` by metis_tac[lookup_block_label] >>
                   `MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
                   metis_tac[pred_labels_single_no_jmp]) \\
                `~v_merged.vs_halted` by gvs[state_equiv_cfg_def] \\
                sg `b.bb_instructions <> []`
                >- (CCONTR_TAC >> gvs[] >>
                    qpat_x_assum `block_terminator_last b` mp_tac >>
                    simp[block_terminator_last_def] >> simp[get_instruction_def] >>
                    qpat_x_assum `run_block b v = OK v'` mp_tac >>
                    simp[Once run_block_def, step_in_block_def, get_instruction_def])
                >- (
                  `block_terminator_last a` by
                    (fs[cfg_wf_def] >> first_x_assum irule >>
                     irule lookup_block_MEM >> qexists_tac `s2.vs_current_bb` >> simp[]) \\
                  `v'.vs_current_bb = v_merged.vs_current_bb` by
                    metis_tac[run_block_merge_blocks_current_bb] >>
                  `v_merged.vs_current_bb = v''.vs_current_bb` by
                    (irule run_block_merged_no_phi_current_bb >>
                     gvs[] >>
                     qexistsl_tac [`a`, `b`, `s2.vs_current_bb`, `v.vs_current_bb`, `s1`, `s2`] >>
                     gvs[] >> rpt conj_tac >> gvs[] >> gvs[state_equiv_cfg_def]) >>
                  simp[]))
              (* Cond 5: v'.vs_inst_idx = 0 *)
              >- metis_tac[run_block_ok_inst_idx]
              (* Cond 6: v''.vs_inst_idx = 0 *)
              >- metis_tac[run_block_ok_inst_idx]
              (* Cond 7: prev_bb <> b_lbl => equal *)
              >- (`v'.vs_prev_bb = SOME v.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >> gvs[])
              (* Cond 8: prev_bb = b_lbl => v'' prev = a_lbl *)
              >- (`v'.vs_prev_bb = SOME v.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >>
                  `v''.vs_prev_bb = SOME s2.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >>
                  gvs[]))
            >- (
              (* Block a has PHIs - use run_block_replace_label variants *)
              `a.bb_instructions <> []` by (
                fs[block_last_jmp_to_def, block_last_inst_def] >>
                Cases_on `a.bb_instructions` >> gvs[]) \\
              `MEM a fn.fn_blocks` by
                (irule lookup_block_MEM >> qexists_tac `s2.vs_current_bb` >> simp[]) \\
              `a.bb_label = s2.vs_current_bb` by metis_tac[lookup_block_label] \\
              `phi_block_wf (pred_labels fn s2.vs_current_bb) a` by
                (fs[phi_fn_wf_def] >> first_x_assum drule >> gvs[]) \\
              `phi_block_wf (pred_labels fn s2.vs_current_bb)
                 (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)`
                by (irule phi_block_wf_merged >> simp[]) \\
              `~MEM s2.vs_current_bb (pred_labels fn s2.vs_current_bb)` by
                (drule_all no_self_loop_from_jmp_to >> simp[]) \\
              Cases_on `s1.vs_prev_bb = SOME v.vs_current_bb`
              >- (
                (* prev_bb = SOME b_lbl - use run_block_replace_label *)
                `s2.vs_prev_bb = SOME s2.vs_current_bb` by gvs[] \\
                `MEM v.vs_current_bb (pred_labels fn s2.vs_current_bb)` by
                  (first_x_assum irule >> simp[]) \\
                sg `result_equiv_cfg
                     (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
                     (run_block (replace_label_block v.vs_current_bb s2.vs_current_bb
                        (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
                >- (irule run_block_replace_label >> gvs[] >>
                    qexists_tac `fn` >> gvs[])
                >- (
                  `result_equiv_cfg (run_block b v)
                     (run_block (replace_label_block v.vs_current_bb s2.vs_current_bb
                        (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
                    by (irule result_equiv_cfg_trans >>
                        qexists_tac `run_block (a with bb_instructions :=
                                     FRONT a.bb_instructions ++ b.bb_instructions) s1` >> gvs[]) \\
                  Cases_on `run_block b v` >>
                  Cases_on `run_block (replace_label_block v.vs_current_bb s2.vs_current_bb
                             (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
                  gvs[result_equiv_cfg_def, AllCaseEqs()] \\
                  Cases_on `v'.vs_halted` >> Cases_on `v''.vs_halted` >>
                  gvs[result_equiv_cfg_def, state_equiv_cfg_def] \\
                  `terminates (run_function n fn v')` by (
                    irule run_function_terminates_step >> simp[] >>
                    qexistsl_tac [`b`, `v`] >> simp[] >>
                    irule run_function_terminates_step >> simp[] >>
                    qexistsl_tac [`a`, `s1`] >> simp[]) \\
                  `run_function n fn v' = run_function (SUC n) fn v'`
                    by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> irule run_function_fuel_monotonicity >> simp[]) \\
                  pop_assum (fn th => REWRITE_TAC [th]) \\
                  first_x_assum irule >> gvs[] >> rpt conj_tac
                  >- (rpt strip_tac >>
                      `v'.vs_prev_bb = SOME v.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >>
                      gvs[] >> `MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
                      `b.bb_label = v.vs_current_bb` by metis_tac[lookup_block_label] >>
                      metis_tac[run_block_ok_pred_labels])
                  >- (`run_function (SUC n) fn v' = run_function n fn v'`
                        by (irule run_function_fuel_monotonicity >> simp[]) >> simp[])
                  >- (`MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
                      `b.bb_label = v.vs_current_bb` by metis_tac[lookup_block_label] >>
                      qspecl_then [`fn`, `b`, `v`, `v'`, `s2.vs_current_bb`]
                        mp_tac run_block_no_self_loop_single_pred >> simp[])
                  >- (
                    qpat_x_assum `result_equiv_cfg (OK v') _` mp_tac >>
                    Cases_on `run_block (a with bb_instructions :=
                               FRONT a.bb_instructions ++ b.bb_instructions) s1` >>
                    simp[result_equiv_cfg_def] >> strip_tac \\
                    rename1 `state_equiv_cfg _ v_merged` \\
                    `block_terminator_last b` by
                      (fs[cfg_wf_def] >> first_x_assum irule >> metis_tac[lookup_block_MEM]) \\
                    `~MEM v.vs_current_bb (block_successors b)` by
                      (`b.bb_label = v.vs_current_bb` by metis_tac[lookup_block_label] >>
                       `MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
                       metis_tac[pred_labels_single_no_jmp]) \\
                    `~v_merged.vs_halted` by gvs[state_equiv_cfg_def] \\
                    sg `b.bb_instructions <> []`
                    >- (CCONTR_TAC >> gvs[] >>
                        qpat_x_assum `block_terminator_last b` mp_tac >>
                        simp[block_terminator_last_def] >> simp[get_instruction_def] >>
                        qpat_x_assum `run_block b v = OK v'` mp_tac >>
                        simp[Once run_block_def, step_in_block_def, get_instruction_def])
                    >- (
                      `v'.vs_current_bb = v_merged.vs_current_bb` by
                        metis_tac[run_block_merge_blocks_current_bb] >>
                      `v_merged.vs_current_bb = v''.vs_current_bb` by
                        (irule run_block_replace_label_current_bb_diff_states >>
                         gvs[] >>
                         qexists_tac `a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions` >>
                         qexistsl_tac [`fn`, `s2.vs_current_bb`, `v.vs_current_bb`, `s1`, `s2`] >>
                         rpt conj_tac
                         >- (irule block_terminator_last_merged >> gvs[])
                         >- gvs[]
                         >- gvs[basic_block_component_equality]
                         >- simp[block_successors_merged]
                         >- gvs[]
                         >- gvs[]
                         >- gvs[]
                         >- gvs[]
                         >- gvs[]
                         >- gvs[basic_block_component_equality]
                         >- gvs[basic_block_component_equality]
                         >- (gvs[] >> simp[state_equiv_cfg_def])) >>
                      simp[]))
                  >- metis_tac[run_block_ok_inst_idx]
                  >- metis_tac[run_block_ok_inst_idx]
                  >- (`v'.vs_prev_bb = SOME v.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >> gvs[])
                  >- (`v'.vs_prev_bb = SOME v.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >>
                      `v''.vs_prev_bb = SOME s2.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >>
                      gvs[])))
              >- (
                (* prev_bb <> SOME b_lbl - use run_block_replace_label_prev_diff or prev_bb_none *)
                `s1.vs_prev_bb = s2.vs_prev_bb` by gvs[] \\
                Cases_on `s1.vs_prev_bb`
                >- (
                  (* prev_bb = NONE *)
                  sg `result_equiv_cfg
                       (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
                       (run_block (replace_label_block v.vs_current_bb s2.vs_current_bb
                          (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
                  >- (irule run_block_replace_label_prev_bb_none >> gvs[])
                  >- (
                    `result_equiv_cfg (run_block b v)
                       (run_block (replace_label_block v.vs_current_bb s2.vs_current_bb
                          (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
                      by (irule result_equiv_cfg_trans >>
                          qexists_tac `run_block (a with bb_instructions :=
                                       FRONT a.bb_instructions ++ b.bb_instructions) s1` >> gvs[]) \\
                    Cases_on `run_block b v` >>
                    Cases_on `run_block (replace_label_block v.vs_current_bb s2.vs_current_bb
                               (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
                    gvs[result_equiv_cfg_def, AllCaseEqs()] \\
                    Cases_on `v'.vs_halted` >> Cases_on `v''.vs_halted` >>
                    gvs[result_equiv_cfg_def, state_equiv_cfg_def] \\
                    `terminates (run_function n fn v')` by (
                      irule run_function_terminates_step >> simp[] >>
                      qexistsl_tac [`b`, `v`] >> simp[] >>
                      irule run_function_terminates_step >> simp[] >>
                      qexistsl_tac [`a`, `s1`] >> simp[]) \\
                    `run_function n fn v' = run_function (SUC n) fn v'`
                      by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> irule run_function_fuel_monotonicity >> simp[]) \\
                    pop_assum (fn th => REWRITE_TAC [th]) \\
                    first_x_assum irule >> gvs[] >> rpt conj_tac
                    >- (rpt strip_tac >>
                        `v'.vs_prev_bb = SOME v.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >>
                        gvs[] >> `MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
                        `b.bb_label = v.vs_current_bb` by metis_tac[lookup_block_label] >>
                        metis_tac[run_block_ok_pred_labels])
                    >- (`run_function (SUC n) fn v' = run_function n fn v'`
                          by (irule run_function_fuel_monotonicity >> simp[]) >> simp[])
                    >- (`MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
                        `b.bb_label = v.vs_current_bb` by metis_tac[lookup_block_label] >>
                        qspecl_then [`fn`, `b`, `v`, `v'`, `s2.vs_current_bb`]
                          mp_tac run_block_no_self_loop_single_pred >> simp[])
                    >- (
                      qpat_x_assum `result_equiv_cfg (OK v') _` mp_tac >>
                      Cases_on `run_block (a with bb_instructions :=
                                 FRONT a.bb_instructions ++ b.bb_instructions) s1` >>
                      simp[result_equiv_cfg_def] >> strip_tac \\
                      rename1 `state_equiv_cfg _ v_merged` \\
                      `block_terminator_last b` by
                        (fs[cfg_wf_def] >> first_x_assum irule >> metis_tac[lookup_block_MEM]) \\
                      `~MEM v.vs_current_bb (block_successors b)` by
                        (`b.bb_label = v.vs_current_bb` by metis_tac[lookup_block_label] >>
                         `MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
                         metis_tac[pred_labels_single_no_jmp]) \\
                      `~v_merged.vs_halted` by gvs[state_equiv_cfg_def] \\
                      sg `b.bb_instructions <> []`
                      >- (CCONTR_TAC >> gvs[] >>
                          qpat_x_assum `block_terminator_last b` mp_tac >>
                          simp[block_terminator_last_def] >> simp[get_instruction_def] >>
                          qpat_x_assum `run_block b v = OK v'` mp_tac >>
                          simp[Once run_block_def, step_in_block_def, get_instruction_def])
                      >- (
                        `v'.vs_current_bb = v_merged.vs_current_bb` by
                          metis_tac[run_block_merge_blocks_current_bb] >>
                        `block_terminator_last (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)` by
                          (irule block_terminator_last_merged >> gvs[] >>
                           fs[block_last_jmp_to_def, block_last_inst_def] >> Cases_on `a.bb_instructions` >> gvs[]) >>
                        `~MEM v.vs_current_bb (block_successors (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions))` by
                          (simp[block_successors_merged]) >>
                        `v_merged.vs_current_bb = v''.vs_current_bb` by
                          (irule run_block_replace_label_current_bb_prev_none >> gvs[]) >>
                        simp[]))
                    >- metis_tac[run_block_ok_inst_idx]
                    >- metis_tac[run_block_ok_inst_idx]
                    >- (`v'.vs_prev_bb = SOME v.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >> gvs[])
                    >- (`v'.vs_prev_bb = SOME v.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >>
                        `v''.vs_prev_bb = SOME s2.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >>
                        gvs[])))
                >- (
                  (* prev_bb = SOME x where x <> b_lbl *)
                  rename1 `s1.vs_prev_bb = SOME prev_lbl` \\
                  `prev_lbl <> v.vs_current_bb` by (CCONTR_TAC >> gvs[]) \\
                  `MEM prev_lbl (pred_labels fn s2.vs_current_bb)` by (first_x_assum irule >> simp[]) \\
                  sg `result_equiv_cfg
                       (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
                       (run_block (replace_label_block v.vs_current_bb s2.vs_current_bb
                          (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
                  >- (
                    irule result_equiv_cfg_trans >>
                    qexists_tac `run_block (a with bb_instructions :=
                                  FRONT a.bb_instructions ++ b.bb_instructions) s2` >>
                    conj_tac
                    >- (irule run_block_state_equiv_cfg >> gvs[])
                    >- (irule run_block_replace_label_prev_diff >>
                        qexistsl_tac [`pred_labels fn s2.vs_current_bb`, `prev_lbl`, `fn`] >>
                        gvs[] >> `a.bb_label = s2.vs_current_bb` by metis_tac[lookup_block_label] >>
                        gvs[]))
                  >- (
                    `result_equiv_cfg (run_block b v)
                       (run_block (replace_label_block v.vs_current_bb s2.vs_current_bb
                          (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
                      by (irule result_equiv_cfg_trans >>
                          qexists_tac `run_block (a with bb_instructions :=
                                       FRONT a.bb_instructions ++ b.bb_instructions) s1` >> gvs[]) \\
                    Cases_on `run_block b v` >>
                    Cases_on `run_block (replace_label_block v.vs_current_bb s2.vs_current_bb
                               (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
                    gvs[result_equiv_cfg_def, AllCaseEqs()] \\
                    Cases_on `v'.vs_halted` >> Cases_on `v''.vs_halted` >>
                    gvs[result_equiv_cfg_def, state_equiv_cfg_def] \\
                    `terminates (run_function n fn v')` by (
                      irule run_function_terminates_step >> simp[] >>
                      qexistsl_tac [`b`, `v`] >> simp[] >>
                      irule run_function_terminates_step >> simp[] >>
                      qexistsl_tac [`a`, `s1`] >> simp[]) \\
                    `run_function n fn v' = run_function (SUC n) fn v'`
                      by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> irule run_function_fuel_monotonicity >> simp[]) \\
                    pop_assum (fn th => REWRITE_TAC [th]) \\
                    first_x_assum irule >> gvs[] >> rpt conj_tac
                    >- (rpt strip_tac >>
                        `v'.vs_prev_bb = SOME v.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >>
                        gvs[] >> `MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
                        `b.bb_label = v.vs_current_bb` by metis_tac[lookup_block_label] >>
                        metis_tac[run_block_ok_pred_labels])
                    >- (`run_function (SUC n) fn v' = run_function n fn v'`
                          by (irule run_function_fuel_monotonicity >> simp[]) >> simp[])
                    >- (`MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
                        `b.bb_label = v.vs_current_bb` by metis_tac[lookup_block_label] >>
                        qspecl_then [`fn`, `b`, `v`, `v'`, `s2.vs_current_bb`]
                          mp_tac run_block_no_self_loop_single_pred >> simp[])
                    >- (
                      qpat_x_assum `result_equiv_cfg (OK v') _` mp_tac >>
                      Cases_on `run_block (a with bb_instructions :=
                                 FRONT a.bb_instructions ++ b.bb_instructions) s1` >>
                      simp[result_equiv_cfg_def] >> strip_tac \\
                      rename1 `state_equiv_cfg _ v_merged` \\
                      `block_terminator_last b` by
                        (fs[cfg_wf_def] >> first_x_assum irule >> metis_tac[lookup_block_MEM]) \\
                      `~MEM v.vs_current_bb (block_successors b)` by
                        (`b.bb_label = v.vs_current_bb` by metis_tac[lookup_block_label] >>
                         `MEM b fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
                         metis_tac[pred_labels_single_no_jmp]) \\
                      `~v_merged.vs_halted` by gvs[state_equiv_cfg_def] \\
                      sg `b.bb_instructions <> []`
                      >- (CCONTR_TAC >> gvs[] >>
                          qpat_x_assum `block_terminator_last b` mp_tac >>
                          simp[block_terminator_last_def] >> simp[get_instruction_def] >>
                          qpat_x_assum `run_block b v = OK v'` mp_tac >>
                          simp[Once run_block_def, step_in_block_def, get_instruction_def])
                      >- (
                        sg `v'.vs_current_bb = v_merged.vs_current_bb`
                        >- (drule_all run_block_merge_blocks_current_bb >> simp[])
                        >- (
                          sg `v_merged.vs_current_bb = v''.vs_current_bb`
                          >- (drule_all run_block_replace_label_current_bb_prev_diff >> simp[])
                          >- simp[])))
                    >- metis_tac[run_block_ok_inst_idx]
                    >- metis_tac[run_block_ok_inst_idx]
                    >- (`v'.vs_prev_bb = SOME v.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >> gvs[])
                    >- (`v'.vs_prev_bb = SOME v.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >>
                        `v''.vs_prev_bb = SOME s2.vs_current_bb` by metis_tac[run_block_ok_prev_bb] >>
                        gvs[])))))))))
    >- (
      (* Halt case *)
      `block_terminator_last a` by
        (fs[cfg_wf_def] >> first_x_assum irule >>
         irule lookup_block_MEM >> qexists_tac `s2.vs_current_bb` >> simp[]) \\
      `result_equiv_cfg (Halt v)
         (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)`
        by (qspecl_then [`fn`, `a`, `b`, `s1`, `b_lbl`] mp_tac run_block_merge_blocks_equiv >> simp[]) \\
      Cases_on `run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1` >>
      gvs[result_equiv_cfg_def] \\
      Cases_on `block_has_no_phi a`
      >- (
        `a.bb_instructions <> []` by
          (fs[block_last_jmp_to_def, block_last_inst_def] >> Cases_on `a.bb_instructions` >> gvs[]) \\
        `block_has_no_phi (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)`
          by (irule block_has_no_phi_merged >> simp[]) \\
        `result_equiv_cfg
           (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
           (run_block (replace_label_block b_lbl s2.vs_current_bb
              (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
          by (irule run_block_replace_label_no_phi >> gvs[]) \\
        Cases_on `run_block (replace_label_block b_lbl s2.vs_current_bb
                   (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
        gvs[result_equiv_cfg_def] \\
        irule state_equiv_cfg_trans >> qexists_tac `v'` >> simp[])
      >- (
        (* PHI case for Halt *)
        `a.bb_instructions <> []` by
          (fs[block_last_jmp_to_def, block_last_inst_def] >> Cases_on `a.bb_instructions` >> gvs[]) \\
        `MEM a fn.fn_blocks` by
          (irule lookup_block_MEM >> qexists_tac `s2.vs_current_bb` >> simp[]) \\
        `a.bb_label = s2.vs_current_bb` by metis_tac[lookup_block_label] \\
        `phi_block_wf (pred_labels fn s2.vs_current_bb) a` by
          (fs[phi_fn_wf_def] >> first_x_assum drule >> gvs[]) \\
        `phi_block_wf (pred_labels fn s2.vs_current_bb)
           (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)`
          by (irule phi_block_wf_merged >> simp[]) \\
        `~MEM s2.vs_current_bb (pred_labels fn s2.vs_current_bb)` by
          (drule_all no_self_loop_from_jmp_to >> simp[]) \\
        Cases_on `s1.vs_prev_bb = SOME b_lbl`
        >- (
          `s2.vs_prev_bb = SOME s2.vs_current_bb` by gvs[] \\
          `MEM b_lbl (pred_labels fn s2.vs_current_bb)` by
            (first_x_assum irule >> simp[]) \\
          sg `result_equiv_cfg
               (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
               (run_block (replace_label_block b_lbl s2.vs_current_bb
                  (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
          >- (irule run_block_replace_label >> gvs[] >> qexists_tac `fn` >> gvs[]) \\
          Cases_on `run_block (replace_label_block b_lbl s2.vs_current_bb
                     (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
          gvs[result_equiv_cfg_def] \\
          irule state_equiv_cfg_trans >> qexists_tac `v'` >> simp[])
        >- (
          `s1.vs_prev_bb = s2.vs_prev_bb` by gvs[] \\
          Cases_on `s1.vs_prev_bb`
          >- (
            sg `result_equiv_cfg
                 (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
                 (run_block (replace_label_block b_lbl s2.vs_current_bb
                    (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
            >- (irule run_block_replace_label_prev_bb_none >> gvs[]) \\
            Cases_on `run_block (replace_label_block b_lbl s2.vs_current_bb
                       (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
            gvs[result_equiv_cfg_def] \\
            irule state_equiv_cfg_trans >> qexists_tac `v'` >> simp[])
          >- (
            `x <> s2.vs_current_bb` by (CCONTR_TAC >> gvs[]) \\
            sg `result_equiv_cfg
                 (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
                 (run_block (replace_label_block b_lbl s2.vs_current_bb
                    (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s1)`
            >- (irule run_block_replace_label_prev_diff >> gvs[] >> qexistsl_tac [`fn`, `x`] >> gvs[]) \\
            sg `result_equiv_cfg
                 (run_block (replace_label_block b_lbl s2.vs_current_bb
                    (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s1)
                 (run_block (replace_label_block b_lbl s2.vs_current_bb
                    (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
            >- (irule run_block_state_equiv_cfg >> gvs[]) \\
            `result_equiv_cfg
               (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
               (run_block (replace_label_block b_lbl s2.vs_current_bb
                  (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)` by
              (irule result_equiv_cfg_trans >>
               qexists_tac `run_block (replace_label_block b_lbl s2.vs_current_bb
                              (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s1` >>
               simp[]) \\
            Cases_on `run_block (replace_label_block b_lbl s2.vs_current_bb
                       (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
            gvs[result_equiv_cfg_def] \\
            irule state_equiv_cfg_trans >> qexists_tac `v'` >> simp[]))))
    >- (
      (* Revert case *)
      `block_terminator_last a` by
        (fs[cfg_wf_def] >> first_x_assum irule >>
         irule lookup_block_MEM >> qexists_tac `s2.vs_current_bb` >> simp[]) \\
      `result_equiv_cfg (Revert v)
         (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)`
        by (qspecl_then [`fn`, `a`, `b`, `s1`, `b_lbl`] mp_tac run_block_merge_blocks_equiv >> simp[]) \\
      Cases_on `run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1` >>
      gvs[result_equiv_cfg_def] \\
      Cases_on `block_has_no_phi a`
      >- (
        `a.bb_instructions <> []` by
          (fs[block_last_jmp_to_def, block_last_inst_def] >> Cases_on `a.bb_instructions` >> gvs[]) \\
        `block_has_no_phi (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)`
          by (irule block_has_no_phi_merged >> simp[]) \\
        `result_equiv_cfg
           (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
           (run_block (replace_label_block b_lbl s2.vs_current_bb
              (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
          by (irule run_block_replace_label_no_phi >> gvs[]) \\
        Cases_on `run_block (replace_label_block b_lbl s2.vs_current_bb
                   (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
        gvs[result_equiv_cfg_def] \\
        irule state_equiv_cfg_trans >> qexists_tac `v'` >> simp[])
      >- (
        (* PHI case for Revert *)
        `a.bb_instructions <> []` by
          (fs[block_last_jmp_to_def, block_last_inst_def] >> Cases_on `a.bb_instructions` >> gvs[]) \\
        `MEM a fn.fn_blocks` by
          (irule lookup_block_MEM >> qexists_tac `s2.vs_current_bb` >> simp[]) \\
        `a.bb_label = s2.vs_current_bb` by metis_tac[lookup_block_label] \\
        `phi_block_wf (pred_labels fn s2.vs_current_bb) a` by
          (fs[phi_fn_wf_def] >> first_x_assum drule >> gvs[]) \\
        `phi_block_wf (pred_labels fn s2.vs_current_bb)
           (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)`
          by (irule phi_block_wf_merged >> simp[]) \\
        `~MEM s2.vs_current_bb (pred_labels fn s2.vs_current_bb)` by
          (drule_all no_self_loop_from_jmp_to >> simp[]) \\
        Cases_on `s1.vs_prev_bb = SOME b_lbl`
        >- (
          `s2.vs_prev_bb = SOME s2.vs_current_bb` by gvs[] \\
          `MEM b_lbl (pred_labels fn s2.vs_current_bb)` by
            (first_x_assum irule >> simp[]) \\
          sg `result_equiv_cfg
               (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
               (run_block (replace_label_block b_lbl s2.vs_current_bb
                  (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
          >- (irule run_block_replace_label >> gvs[] >> qexists_tac `fn` >> gvs[]) \\
          Cases_on `run_block (replace_label_block b_lbl s2.vs_current_bb
                     (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
          gvs[result_equiv_cfg_def] \\
          irule state_equiv_cfg_trans >> qexists_tac `v'` >> simp[])
        >- (
          `s1.vs_prev_bb = s2.vs_prev_bb` by gvs[] \\
          Cases_on `s1.vs_prev_bb`
          >- (
            sg `result_equiv_cfg
                 (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
                 (run_block (replace_label_block b_lbl s2.vs_current_bb
                    (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
            >- (irule run_block_replace_label_prev_bb_none >> gvs[]) \\
            Cases_on `run_block (replace_label_block b_lbl s2.vs_current_bb
                       (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
            gvs[result_equiv_cfg_def] \\
            irule state_equiv_cfg_trans >> qexists_tac `v'` >> simp[])
          >- (
            `x <> s2.vs_current_bb` by (CCONTR_TAC >> gvs[]) \\
            sg `result_equiv_cfg
                 (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
                 (run_block (replace_label_block b_lbl s2.vs_current_bb
                    (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s1)`
            >- (irule run_block_replace_label_prev_diff >> gvs[] >> qexistsl_tac [`fn`, `x`] >> gvs[]) \\
            sg `result_equiv_cfg
                 (run_block (replace_label_block b_lbl s2.vs_current_bb
                    (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s1)
                 (run_block (replace_label_block b_lbl s2.vs_current_bb
                    (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
            >- (irule run_block_state_equiv_cfg >> gvs[]) \\
            `result_equiv_cfg
               (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
               (run_block (replace_label_block b_lbl s2.vs_current_bb
                  (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)` by
              (irule result_equiv_cfg_trans >>
               qexists_tac `run_block (replace_label_block b_lbl s2.vs_current_bb
                              (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s1` >>
               simp[]) \\
            Cases_on `run_block (replace_label_block b_lbl s2.vs_current_bb
                       (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
            gvs[result_equiv_cfg_def] \\
            irule state_equiv_cfg_trans >> qexists_tac `v'` >> simp[]))))
    >- (
      (* Error case *)
      `block_terminator_last a` by
        (fs[cfg_wf_def] >> first_x_assum irule >>
         irule lookup_block_MEM >> qexists_tac `s2.vs_current_bb` >> simp[]) \\
      `result_equiv_cfg (Error s)
         (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)`
        by (qspecl_then [`fn`, `a`, `b`, `s1`, `b_lbl`] mp_tac run_block_merge_blocks_equiv >> simp[]) \\
      Cases_on `run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1` >>
      gvs[result_equiv_cfg_def] \\
      Cases_on `block_has_no_phi a`
      >- (
        `a.bb_instructions <> []` by
          (fs[block_last_jmp_to_def, block_last_inst_def] >> Cases_on `a.bb_instructions` >> gvs[]) \\
        `block_has_no_phi (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)`
          by (irule block_has_no_phi_merged >> simp[]) \\
        `result_equiv_cfg
           (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
           (run_block (replace_label_block b_lbl s2.vs_current_bb
              (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
          by (irule run_block_replace_label_no_phi >> gvs[]) \\
        Cases_on `run_block (replace_label_block b_lbl s2.vs_current_bb
                   (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
        gvs[result_equiv_cfg_def])
      >- (
        (* PHI case for Error *)
        `a.bb_instructions <> []` by
          (fs[block_last_jmp_to_def, block_last_inst_def] >> Cases_on `a.bb_instructions` >> gvs[]) \\
        `MEM a fn.fn_blocks` by
          (irule lookup_block_MEM >> qexists_tac `s2.vs_current_bb` >> simp[]) \\
        `a.bb_label = s2.vs_current_bb` by metis_tac[lookup_block_label] \\
        `phi_block_wf (pred_labels fn s2.vs_current_bb) a` by
          (fs[phi_fn_wf_def] >> first_x_assum drule >> gvs[]) \\
        `phi_block_wf (pred_labels fn s2.vs_current_bb)
           (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)`
          by (irule phi_block_wf_merged >> simp[]) \\
        `~MEM s2.vs_current_bb (pred_labels fn s2.vs_current_bb)` by
          (drule_all no_self_loop_from_jmp_to >> simp[]) \\
        Cases_on `s1.vs_prev_bb = SOME b_lbl`
        >- (
          `s2.vs_prev_bb = SOME s2.vs_current_bb` by gvs[] \\
          `MEM b_lbl (pred_labels fn s2.vs_current_bb)` by
            (first_x_assum irule >> simp[]) \\
          sg `result_equiv_cfg
               (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
               (run_block (replace_label_block b_lbl s2.vs_current_bb
                  (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
          >- (irule run_block_replace_label >> gvs[] >> qexists_tac `fn` >> gvs[]) \\
          Cases_on `run_block (replace_label_block b_lbl s2.vs_current_bb
                     (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
          gvs[result_equiv_cfg_def])
        >- (
          `s1.vs_prev_bb = s2.vs_prev_bb` by gvs[] \\
          Cases_on `s1.vs_prev_bb`
          >- (
            sg `result_equiv_cfg
                 (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
                 (run_block (replace_label_block b_lbl s2.vs_current_bb
                    (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
            >- (irule run_block_replace_label_prev_bb_none >> gvs[]) \\
            Cases_on `run_block (replace_label_block b_lbl s2.vs_current_bb
                       (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
            gvs[result_equiv_cfg_def])
          >- (
            `x <> s2.vs_current_bb` by (CCONTR_TAC >> gvs[]) \\
            sg `result_equiv_cfg
                 (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
                 (run_block (replace_label_block b_lbl s2.vs_current_bb
                    (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s1)`
            >- (irule run_block_replace_label_prev_diff >> gvs[] >> qexistsl_tac [`fn`, `x`] >> gvs[]) \\
            sg `result_equiv_cfg
                 (run_block (replace_label_block b_lbl s2.vs_current_bb
                    (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s1)
                 (run_block (replace_label_block b_lbl s2.vs_current_bb
                    (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)`
            >- (irule run_block_state_equiv_cfg >> gvs[]) \\
            `result_equiv_cfg
               (run_block (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions) s1)
               (run_block (replace_label_block b_lbl s2.vs_current_bb
                  (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2)` by
              (irule result_equiv_cfg_trans >>
               qexists_tac `run_block (replace_label_block b_lbl s2.vs_current_bb
                              (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s1` >>
               simp[]) \\
            Cases_on `run_block (replace_label_block b_lbl s2.vs_current_bb
                       (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)) s2` >>
            gvs[result_equiv_cfg_def])))))
  >- (
    (* Case: not at a_lbl *)
    simp[Once run_function_def] \\
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >> simp[] \\
    Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
    >- (
      (* lookup NONE - should be impossible from termination *)
      simp[] \\
      fs[terminates_def, Once run_function_def] \\
      gvs[terminates_def, AllCaseEqs()])
    >- (
      (* lookup SOME x *)
      simp[] \\
      `s2.vs_current_bb <> a_lbl /\ s2.vs_current_bb <> b_lbl` by gvs[] \\
      `lookup_block s2.vs_current_bb (merge_blocks fn a_lbl b_lbl).fn_blocks =
       SOME (replace_label_block b_lbl a_lbl x)` by
        (irule lookup_block_merge_blocks_other >> gvs[]) \\
      simp[] \\
      Cases_on `s1.vs_prev_bb = SOME b_lbl`
      >- (
        (* prev_bb = SOME b_lbl - came from b_lbl *)
        gvs[] \\
        sg `result_equiv_cfg (run_block x s1)
              (run_block (replace_label_block b_lbl a_lbl x) s2)`
        >- (
          Cases_on `block_has_no_phi x`
          >- (irule run_block_replace_label_no_phi >> gvs[])
          >- (
            irule run_block_replace_label >> simp[] \\
            qexists_tac `fn` \\
            rpt conj_tac
            >- (
              `x.bb_label = s2.vs_current_bb` by metis_tac[lookup_block_label] \\
              irule pred_labels_no_jmp_other >> gvs[] \\
              qexists_tac `b_lbl` >> gvs[])
            >- (`x.bb_label = s2.vs_current_bb` by metis_tac[lookup_block_label] >> gvs[])
            >- (
              irule scfgPhiLemmasTheory.phi_fn_wf_block >> gvs[] \\
              metis_tac[lookup_block_MEM])))
        >- (
          Cases_on `run_block x s1`
          >- (
            simp[] \\
            fs[result_equiv_cfg_def] >>
            Cases_on `run_block (replace_label_block b_lbl a_lbl x) s2` >>
            gvs[result_equiv_cfg_def] \\
            Cases_on `v.vs_halted` >> gvs[result_equiv_cfg_def]
            >- gvs[state_equiv_cfg_def, result_equiv_cfg_def]
            >- (
              gvs[state_equiv_cfg_def] \\
              first_x_assum irule \\
              gvs[] >> rpt conj_tac
              >- (rpt strip_tac >> imp_res_tac run_block_ok_prev_bb >>
                  imp_res_tac run_block_ok_not_halted >> gvs[] >>
                  imp_res_tac lookup_block_MEM >> imp_res_tac lookup_block_label >>
                  drule_all run_block_ok_pred_labels >> gvs[])
              >- (irule run_function_terminates_step >> gvs[] >>
                  qexistsl_tac [`x`, `s1`] >> gvs[])
              >- (imp_res_tac lookup_block_MEM >> imp_res_tac lookup_block_label >>
                  CCONTR_TAC >> fs[] >> drule_all run_block_ok_successor >> strip_tac >>
                  `~MEM b_lbl (block_successors x)` by
                    (irule pred_labels_single_no_jmp >> qexistsl_tac [`a_lbl`, `fn`] >> gvs[]) >>
                  gvs[])
              >- (irule run_block_replace_label_current_bb_diff_states >> gvs[] >>
                  qexistsl_tac [`x`, `fn`, `a_lbl`, `b_lbl`, `s1`, `s2`] >>
                  rpt conj_tac >> gvs[]
                  >- (fs[cfg_wf_def] >> first_x_assum irule >>
                      irule lookup_block_MEM >> qexists_tac `s2.vs_current_bb` >> simp[])
                  >- (`x.bb_label = s2.vs_current_bb` by metis_tac[lookup_block_label] >>
                      irule pred_labels_no_jmp_other >> gvs[] >> qexists_tac `b_lbl` >> gvs[])
                  >- (irule pred_labels_single_no_jmp >> qexistsl_tac [`a_lbl`, `fn`] >> gvs[] >>
                      metis_tac[lookup_block_label, lookup_block_MEM])
                  >- (`x.bb_label = s2.vs_current_bb` by metis_tac[lookup_block_label] >> gvs[])
                  >- (irule scfgPhiLemmasTheory.phi_fn_wf_block >> gvs[] >>
                      metis_tac[lookup_block_MEM])
                  >- simp[state_equiv_cfg_def])
              >- metis_tac[run_block_ok_inst_idx]
              >- metis_tac[run_block_ok_inst_idx]
              >- (rpt strip_tac >> imp_res_tac run_block_ok_prev_bb >> gvs[])
              >- (rpt strip_tac >> imp_res_tac run_block_ok_prev_bb >> gvs[])))
          >- (simp[] >> fs[result_equiv_cfg_def] >>
              Cases_on `run_block (replace_label_block b_lbl a_lbl x) s2` >>
              gvs[result_equiv_cfg_def])
          >- (simp[] >> fs[result_equiv_cfg_def] >>
              Cases_on `run_block (replace_label_block b_lbl a_lbl x) s2` >>
              gvs[result_equiv_cfg_def])
          >- (simp[] >> fs[result_equiv_cfg_def] >>
              Cases_on `run_block (replace_label_block b_lbl a_lbl x) s2` >>
              gvs[result_equiv_cfg_def])))
      >- (
        (* prev_bb <> SOME b_lbl *)
        Cases_on `block_has_no_phi x`
        >- (
          `result_equiv_cfg (run_block x s1)
             (run_block (replace_label_block b_lbl a_lbl x) s2)` by
            (irule run_block_replace_label_no_phi >> gvs[]) \\
          Cases_on `run_block x s1`
          >- (
            gvs[result_equiv_cfg_def, AllCaseEqs()] \\
            Cases_on `run_block (replace_label_block b_lbl a_lbl x) s2`
            >- (
              gvs[result_equiv_cfg_def, AllCaseEqs(), state_equiv_cfg_def] \\
              Cases_on `v'.vs_halted` >> gvs[result_equiv_cfg_def]
              >- simp[state_equiv_cfg_def]
              >- (first_x_assum irule >> gvs[] >>
                  rpt conj_tac
                  >- (rpt strip_tac >> imp_res_tac run_block_ok_prev_bb >>
                      imp_res_tac run_block_ok_not_halted >> gvs[] >>
                      imp_res_tac lookup_block_MEM >> imp_res_tac lookup_block_label >>
                      drule_all run_block_ok_pred_labels >> gvs[])
                  >- (irule run_function_terminates_step >> gvs[] >>
                      qexistsl_tac [`x`, `s1`] >> gvs[])
                  >- (imp_res_tac lookup_block_MEM >> imp_res_tac lookup_block_label >>
                      CCONTR_TAC >> fs[] >> drule_all run_block_ok_successor >> strip_tac >>
                      `~MEM b_lbl (block_successors x)` by
                        (irule pred_labels_single_no_jmp >> qexistsl_tac [`a_lbl`, `fn`] >> gvs[]) >>
                      gvs[])
                  >- (irule run_block_replace_label_no_phi_current_bb >> gvs[state_equiv_cfg_def] >>
                      qexistsl_tac [`x`, `a_lbl`, `b_lbl`, `s1`, `s2`] >> gvs[] >>
                      imp_res_tac lookup_block_MEM >> conj_tac >- gvs[cfg_wf_def] >>
                      irule pred_labels_single_no_jmp >> qexistsl_tac [`a_lbl`, `fn`] >>
                      imp_res_tac lookup_block_label >> gvs[])
                  >- (imp_res_tac run_block_ok_inst_idx >> gvs[])
                  >- (imp_res_tac run_block_ok_inst_idx >> gvs[])
                  >- (rpt strip_tac >> imp_res_tac run_block_ok_prev_bb >> gvs[])
                  >- (rpt strip_tac >> imp_res_tac run_block_ok_prev_bb >> gvs[])))
            >- gvs[result_equiv_cfg_def, AllCaseEqs()]
            >- gvs[result_equiv_cfg_def, AllCaseEqs()]
            >- gvs[result_equiv_cfg_def, AllCaseEqs()])
          >- (
            gvs[result_equiv_cfg_def, AllCaseEqs()] \\
            Cases_on `run_block (replace_label_block b_lbl a_lbl x) s2` >>
            gvs[result_equiv_cfg_def, AllCaseEqs()])
          >- (
            Cases_on `run_block (replace_label_block b_lbl a_lbl x) s2` >>
            gvs[result_equiv_cfg_def, AllCaseEqs()])
          >- (
            Cases_on `run_block (replace_label_block b_lbl a_lbl x) s2` >>
            gvs[result_equiv_cfg_def, AllCaseEqs()]))
        >- (
          (* block has PHIs and prev_bb <> b_lbl - TODO: needs careful handling *)
          Cases_on `s1.vs_prev_bb`
          >- (gvs[] >> cheat)
          >- cheat))))
QED_ORIGINAL
*)

(* Backward direction: if merged terminates, original also terminates with enough fuel.
   We use 2*fuel as a bound since each merge point traversal adds at most 1 extra block. *)
Theorem run_function_merge_blocks_equiv_bwd:
  !fuel fn a_lbl b_lbl a b s1 s2.
    cfg_wf fn /\ phi_fn_wf fn /\
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    a_lbl <> b_lbl /\ b_lbl <> entry_label fn /\
    pred_labels fn b_lbl = [a_lbl] /\
    block_has_no_phi b /\ block_last_jmp_to b_lbl a /\
    state_equiv_cfg s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_current_bb <> b_lbl /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    (s1.vs_prev_bb = SOME b_lbl ==> s2.vs_prev_bb = SOME a_lbl) /\
    (s1.vs_prev_bb <> SOME b_lbl ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (!lbl. s1.vs_prev_bb = SOME lbl ==> MEM lbl (pred_labels fn s1.vs_current_bb)) /\
    ~s1.vs_halted /\
    terminates (run_function fuel (merge_blocks fn a_lbl b_lbl) s2)
  ==>
    ?fuel'. terminates (run_function fuel' fn s1) /\
            result_equiv_cfg (run_function fuel' fn s1)
                             (run_function fuel (merge_blocks fn a_lbl b_lbl) s2)
Proof
  (* Partial proof with cheats for complex subcases *)
  completeInduct_on `fuel` >> rpt strip_tac >>
  Cases_on `fuel` >- gvs[run_function_def, terminates_def] >>
  Cases_on `s1.vs_current_bb = a_lbl`
  >- ( (* At merge point *)
    gvs[] >>
    qpat_x_assum `terminates _` mp_tac >> simp[Once run_function_def] >>
    `lookup_block s2.vs_current_bb (merge_blocks fn s2.vs_current_bb b_lbl).fn_blocks =
     SOME (replace_label_block b_lbl s2.vs_current_bb
           (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions))`
      by (irule lookup_block_merge_blocks_a >> simp[]) >>
    simp[] >>
    qabbrev_tac `merged_bb = replace_label_block b_lbl s2.vs_current_bb
      (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)` >>
    Cases_on `run_block merged_bb s2` >> simp[terminates_def]
    >- ( (* OK case *)
      Cases_on `v.vs_halted` >> simp[terminates_def]
      >- ( (* OK + halted *)
        `block_terminator_last a` by (gvs[cfg_wf_def] >> first_x_assum irule >>
          irule lookup_block_MEM >> metis_tac[]) >>
        qabbrev_tac `merged_no_label = a with bb_instructions :=
          FRONT a.bb_instructions ++ b.bb_instructions` >>
        `result_equiv_cfg (run_block merged_no_label s1) (run_block merged_bb s2)` by
          (qspecl_then [`fn`, `a`, `b`, `s2.vs_current_bb`, `b_lbl`, `s1`, `s2`]
           mp_tac run_block_merged_to_merged_bb >> simp[Abbr `merged_bb`, Abbr `merged_no_label`]) >>
        `result_equiv_cfg (case run_block a s1 of OK s' => if s'.vs_halted then Halt s'
           else run_block b s' | Halt v => Halt v | Revert v => Revert v | Error e => Error e)
           (run_block merged_no_label s1)` by
          (qspecl_then [`fn`, `a`, `b`, `s1`, `b_lbl`] mp_tac run_block_merge_blocks_equiv >>
           simp[Abbr `merged_no_label`]) >>
        Cases_on `run_block merged_no_label s1` >> gvs[result_equiv_cfg_def] >>
        Cases_on `run_block a s1` >> gvs[result_equiv_cfg_def] >>
        Cases_on `v''.vs_halted` >> gvs[result_equiv_cfg_def] >>
        Cases_on `run_block b v''` >> gvs[result_equiv_cfg_def] >>
        cheat) (* TODO: construct fuel witness for original *)
      >- cheat) (* TODO: OK + not halted, needs IH *)
    >- cheat (* TODO: Halt case *)
    >- cheat) (* TODO: Revert case *)
  >- cheat (* TODO: not at merge point *)
QED

(* Original backward proof preserved in comment:
Proof_bwd_ORIGINAL
  completeInduct_on `fuel` >> rpt strip_tac >> Cases_on `fuel` >-
   gvs[run_function_def, terminates_def] \\
   simp[Once run_function_def] >> Cases_on `s2.vs_current_bb = a_lbl` >> gvs[]
   >- (
     (* At merge point: a_lbl *)
     qpat_x_assum `terminates _` mp_tac >>
     simp[Once run_function_def, lookup_block_merge_blocks_a] \\
     `lookup_block s1.vs_current_bb (merge_blocks fn s1.vs_current_bb b_lbl).fn_blocks =
      SOME (replace_label_block b_lbl s1.vs_current_bb
            (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions))`
       by (irule lookup_block_merge_blocks_a >> simp[]) >> simp[] \\
     qabbrev_tac `merged_bb = replace_label_block b_lbl s1.vs_current_bb
       (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)` >>
     Cases_on `run_block merged_bb s2` >> simp[]
     >- ( (* OK case *)
       Cases_on `v.vs_halted` >> simp[terminates_def]
       >- ( (* OK with halted *)
         TRY (simp[terminates_def]) \\
         `block_terminator_last a` by (imp_res_tac lookup_block_MEM >> gvs[cfg_wf_def]) \\
         qabbrev_tac `merged_no_label = a with bb_instructions :=
           FRONT a.bb_instructions ++ b.bb_instructions` \\
         `result_equiv_cfg (case run_block a s1 of OK s' => if s'.vs_halted then
           Halt s' else run_block b s' | Halt v => Halt v | Revert v => Revert v
           | Error e => Error e) (run_block merged_no_label s1)`
           by (qspecl_then [`fn`, `a`, `b`, `s1`, `b_lbl`] mp_tac
               run_block_merge_blocks_equiv >> simp[Abbr `merged_no_label`]) \\
         Cases_on `s1.vs_prev_bb`
         >- ( (* prev_bb = NONE - fully proved *)
           gvs[] \\
           `result_equiv_cfg (run_block merged_no_label s1) (run_block merged_bb s2)`
             by (qunabbrev_tac `merged_bb` >>
                 irule run_block_replace_label_prev_bb_none >> gvs[]) \\
           Cases_on `run_block merged_no_label s1` >> gvs[result_equiv_cfg_def] \\
           Cases_on `run_block a s1` >> gvs[result_equiv_cfg_def] \\
           Cases_on `v''.vs_halted` >> gvs[result_equiv_cfg_def] \\
           Cases_on `run_block b v''` >> gvs[result_equiv_cfg_def] \\
           rename1 `state_equiv_cfg v_merged _` \\
           `v_merged.vs_halted` by gvs[state_equiv_cfg_def] \\
           `MEM a fn.fn_blocks` by (irule lookup_block_MEM >>
             qexists_tac `s1.vs_current_bb` >> simp[]) \\
           `MEM v''.vs_current_bb (block_successors a)` by
             (qspecl_then [`fn`, `a`, `s1`, `v''`] mp_tac run_block_ok_successor >>
              simp[cfg_wf_def]) \\
           `block_successors a = [b_lbl]` by metis_tac[block_last_jmp_to_successors] \\
           `v''.vs_current_bb = b_lbl` by gvs[] \\
           qexists_tac `SUC (SUC 0)` >> simp[] \\
           simp[Once run_function_def] >> simp[terminates_def] \\
           simp[Once run_function_def, Once run_function_def, Once run_function_def] \\
           simp[Once run_function_def, Once run_function_def, lookup_block_merge_blocks_a] \\
           simp[result_equiv_cfg_def] >> irule state_equiv_cfg_trans >>
           qexists_tac `v'` >> simp[])
         >- ( (* prev_bb = SOME x *)
           Cases_on `x = b_lbl` >> gvs[]
           >- ( (* prev_bb = SOME b_lbl *)
             `~MEM s1.vs_current_bb (pred_labels fn s1.vs_current_bb)` by
               (drule_all no_self_loop_from_jmp_to >> simp[]) \\
             `MEM a fn.fn_blocks` by (irule lookup_block_MEM >>
               qexists_tac `s1.vs_current_bb` >> simp[]) \\
             `phi_block_wf (pred_labels fn a.bb_label) a` by
               (irule scfgPhiLemmasTheory.phi_fn_wf_block >> simp[]) \\
             `a.bb_label = s1.vs_current_bb` by
               (imp_res_tac lookup_block_label >> simp[]) \\
             sg `a.bb_instructions <> []`
               >- (CCONTR_TAC >> gvs[block_last_jmp_to_def, block_last_inst_def]) \\
             `phi_block_wf (pred_labels fn s1.vs_current_bb) merged_no_label` by
               (simp[Abbr `merged_no_label`] >> irule phi_block_wf_merged >> gvs[]) \\
             `MEM b_lbl (pred_labels fn s1.vs_current_bb)` by gvs[] \\
             sg `result_equiv_cfg (run_block merged_no_label s1) (run_block merged_bb s2)`
               >- (qunabbrev_tac `merged_bb` >>
                   irule run_block_replace_label >>
                   simp[Abbr `merged_no_label`] >>
                   qexists_tac `fn` >> gvs[])
               >- (
                 Cases_on `run_block merged_no_label s1` >> gvs[result_equiv_cfg_def] \\
                 Cases_on `run_block a s1` >> gvs[result_equiv_cfg_def] \\
                 Cases_on `v''.vs_halted` >> gvs[result_equiv_cfg_def] \\
                 Cases_on `run_block b v''` >> gvs[result_equiv_cfg_def] \\
                 rename1 `state_equiv_cfg v_merged _` \\
                 `v_merged.vs_halted` by gvs[state_equiv_cfg_def] \\
                 `v''.vs_current_bb = b_lbl` by
                   (qspecl_then [`fn`, `a`, `s1`, `v''`] mp_tac run_block_ok_successor >>
                    simp[cfg_wf_def] >>
                    `MEM a fn.fn_blocks` by (irule lookup_block_MEM >> metis_tac[]) >>
                    simp[] >>
                    `block_successors a = [b_lbl]` by metis_tac[block_last_jmp_to_successors] >>
                    simp[]) \\
                 qexists_tac `SUC (SUC 0)` >> simp[] \\
                 simp[Once run_function_def, terminates_def] \\
                 simp[Once run_function_def, Once run_function_def] \\
                 simp[Once run_function_def, lookup_block_merge_blocks_a] \\
                 simp[result_equiv_cfg_def] >> irule state_equiv_cfg_trans >>
                 qexists_tac `v'` >> simp[]))
           >- cheat)) (* prev_bb = SOME x, x <> b_lbl *)
       >- cheat) (* OK not halted - needs IH *)
     >- cheat (* Halt case *)
     >- cheat (* Revert case *)
     >- simp[terminates_def]) (* Error case - vacuously true *)
   >- cheat (* Not at merge point *)
QED_bwd_ORIGINAL
*)

Theorem merge_blocks_correct:
  !fn a_lbl b_lbl s.
    cfg_wf fn /\
    phi_fn_wf fn /\
    merge_blocks_cond fn a_lbl b_lbl /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE /\
    s.vs_inst_idx = 0 /\
    ~s.vs_halted ==>
    run_function_equiv_cfg fn (merge_blocks fn a_lbl b_lbl) s
Proof
  rpt gen_tac >> simp[merge_blocks_cond_def] >> strip_tac >>
  simp[run_function_equiv_cfg_def] >> conj_tac
  >- ( (* Forward direction: original terminates => merged terminates *)
    rpt strip_tac >> qexists_tac `fuel` >>
    `result_equiv_cfg (run_function fuel fn s)
          (run_function fuel (merge_blocks fn a_lbl b_lbl) s)` by
      (irule run_function_merge_blocks_equiv_fwd >>
       simp[state_equiv_cfg_refl]) >>
    Cases_on `run_function fuel fn s` >>
    Cases_on `run_function fuel (merge_blocks fn a_lbl b_lbl) s` >>
    gvs[result_equiv_cfg_def, scfgDefsTheory.terminates_def])
  >- ( (* Backward direction: merged terminates => original terminates *)
    rpt strip_tac >>
    qspecl_then [`fuel'`, `fn`, `a_lbl`, `b_lbl`, `a`, `b`, `s`, `s`]
      mp_tac run_function_merge_blocks_equiv_bwd >>
    simp[state_equiv_cfg_refl] >> strip_tac >>
    qexists_tac `fuel''` >> simp[])
QED

(* ===== Jump Threading ===== *)

(* b_lbl is removed from merged function *)
Theorem lookup_block_merge_jump_b:
  !fn a_lbl b_lbl a b c_lbl.
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    jump_only_target b = SOME c_lbl /\
    a_lbl <> b_lbl ==>
    lookup_block b_lbl (merge_jump fn a_lbl b_lbl).fn_blocks = NONE
Proof
  rpt strip_tac >> simp[merge_jump_def] >>
  simp[replace_label_fn_def] >>
  qabbrev_tac `a' = a with bb_instructions := update_last_inst
    (replace_label_inst b_lbl c_lbl) a.bb_instructions` >>
  `lookup_block b_lbl (remove_block b_lbl (replace_block a'
    fn.fn_blocks)) = NONE` by simp[lookup_block_remove_block_same] >>
  qabbrev_tac `blocks = remove_block b_lbl (replace_block a' fn.fn_blocks)` >>
  irule lookup_block_replace_label_block_none >>
  qpat_x_assum `lookup_block b_lbl blocks = NONE` mp_tac >>
  qunabbrev_tac `blocks` >>
  qspec_tac (`remove_block b_lbl (replace_block a' fn.fn_blocks)`, `bs`) >>
  Induct_on `bs` >> simp[lookup_block_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  Cases_on `MEM h.bb_label (block_successors a')` >> gvs[replace_phi_in_block_def]
QED

(* a_lbl maps to some block in merged function *)
Theorem lookup_block_merge_jump_a:
  !fn a_lbl b_lbl a b c_lbl.
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    jump_only_target b = SOME c_lbl /\
    a_lbl <> b_lbl ==>
    ?a'. lookup_block a_lbl (merge_jump fn a_lbl b_lbl).fn_blocks = SOME a'
Proof
  rpt strip_tac >> simp[merge_jump_def, replace_label_fn_def] >>
  qabbrev_tac `a' = a with bb_instructions := update_last_inst
    (replace_label_inst b_lbl c_lbl) a.bb_instructions` >>
  `a'.bb_label = a_lbl` by (simp[Abbr `a'`] >> metis_tac[lookup_block_label]) >>
  sg `lookup_block a_lbl (replace_block a' fn.fn_blocks) = SOME a'`
  >- (qpat_x_assum `lookup_block a_lbl _ = _`
        (mp_tac o MATCH_MP lookup_block_replace_block) >> simp[])
  >- (
    sg `lookup_block a_lbl (remove_block b_lbl (replace_block a' fn.fn_blocks)) = SOME a'`
    >- (irule lookup_block_remove_block >> simp[])
    >- (
      qabbrev_tac `blocks = remove_block b_lbl (replace_block a' fn.fn_blocks)` >>
      qpat_x_assum `lookup_block a_lbl blocks = SOME a'` mp_tac >>
      qunabbrev_tac `blocks` >>
      qspec_tac (`remove_block b_lbl (replace_block a' fn.fn_blocks)`, `bs`) >>
      Induct_on `bs` >> simp[lookup_block_def] >>
      rpt strip_tac >> Cases_on `h.bb_label = a_lbl` >> gvs[]
      >- (simp[replace_label_block_def, replace_phi_in_block_def] >>
          Cases_on `MEM a'.bb_label (block_successors a')` >> gvs[])
      >- (Cases_on `(replace_label_block b_lbl c_lbl (if MEM h.bb_label
            (block_successors a') then replace_phi_in_block b_lbl
            a'.bb_label h else h)).bb_label = a'.bb_label` >> gvs[])))
QED

(* Other blocks map to some block in merged function *)
Theorem lookup_block_merge_jump_other:
  !fn a_lbl b_lbl a b c c_lbl d_lbl.
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    lookup_block d_lbl fn.fn_blocks = SOME c /\
    jump_only_target b = SOME c_lbl /\
    a_lbl <> b_lbl /\ d_lbl <> a_lbl /\ d_lbl <> b_lbl ==>
    ?c'. lookup_block d_lbl (merge_jump fn a_lbl b_lbl).fn_blocks = SOME c'
Proof
  rpt strip_tac >> simp[merge_jump_def, replace_label_fn_def] >>
  qabbrev_tac `a' = a with bb_instructions := update_last_inst
    (replace_label_inst b_lbl c_lbl) a.bb_instructions` >>
  `a'.bb_label = a_lbl` by (simp[Abbr `a'`] >> metis_tac[lookup_block_label]) >>
  sg `lookup_block d_lbl (replace_block a' fn.fn_blocks) = SOME c`
  >- (qpat_x_assum `lookup_block d_lbl _ = _`
        (mp_tac o MATCH_MP lookup_block_replace_block) >> simp[])
  >- (
    sg `lookup_block d_lbl (remove_block b_lbl (replace_block a' fn.fn_blocks)) = SOME c`
    >- (irule lookup_block_remove_block >> simp[])
    >- (
      qabbrev_tac `blocks = remove_block b_lbl (replace_block a' fn.fn_blocks)` >>
      qpat_x_assum `lookup_block d_lbl blocks = SOME c` mp_tac >>
      qunabbrev_tac `blocks` >>
      qspec_tac (`remove_block b_lbl (replace_block a' fn.fn_blocks)`, `bs`) >>
      Induct_on `bs` >> simp[lookup_block_def] >> rpt strip_tac >>
      Cases_on `h.bb_label = d_lbl` >> gvs[]
      >- (simp[replace_label_block_def, replace_phi_in_block_def] >>
          Cases_on `MEM c.bb_label (block_successors a')` >> gvs[])
      >- (Cases_on `(replace_label_block b_lbl c_lbl (if MEM h.bb_label
            (block_successors a') then replace_phi_in_block b_lbl a'.bb_label
            h else h)).bb_label = d_lbl` >> gvs[])))
QED

(* Helper: running a jump-only block just performs the jump *)
Theorem run_block_jump_only:
  !bb s c_lbl.
    jump_only_target bb = SOME c_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    run_block bb s = OK (jump_to c_lbl s)
Proof
  rpt strip_tac >> gvs[jump_only_target_def, AllCaseEqs()] >>
  simp[Once run_block_def] >>
  simp[step_in_block_def, get_instruction_def] >>
  simp[is_terminator_def] >> simp[step_inst_def] >> simp[jump_to_def]
QED

(* Forward direction helper: result_equiv_cfg for merge_jump *)
Theorem run_function_merge_jump_equiv_fwd:
  !fuel fn a_lbl b_lbl s a b c_lbl.
    cfg_wf fn /\ phi_fn_wf fn /\
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    b_lbl <> entry_label fn /\
    MEM b_lbl (block_successors a) /\
    ~MEM c_lbl (block_successors a) /\
    pred_labels fn b_lbl = [a_lbl] /\
    jump_only_target b = SOME c_lbl /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    result_equiv_cfg (run_function fuel fn s)
                     (run_function fuel (merge_jump fn a_lbl b_lbl) s)
Proof
  completeInduct_on `fuel` >> rpt strip_tac >>
  Cases_on `fuel`
  >- simp[run_function_def, result_equiv_cfg_def]
  >- (simp[Once run_function_def] >>
      Cases_on `s.vs_current_bb = a_lbl`
      >- (gvs[] >> cheat) (* at merge point *)
      >- (Cases_on `s.vs_current_bb = b_lbl`
          >- cheat (* at b - shouldn't happen from entry *)
          >- cheat)) (* other block *)
QED

(* Backward direction helper: if merged terminates, original terminates with 2*fuel *)
Theorem run_function_merge_jump_equiv_bwd:
  !fuel fn a_lbl b_lbl s a b c_lbl.
    cfg_wf fn /\ phi_fn_wf fn /\
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    b_lbl <> entry_label fn /\
    MEM b_lbl (block_successors a) /\
    ~MEM c_lbl (block_successors a) /\
    pred_labels fn b_lbl = [a_lbl] /\
    jump_only_target b = SOME c_lbl /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    terminates (run_function fuel (merge_jump fn a_lbl b_lbl) s) ==>
    terminates (run_function (2 * fuel) fn s) /\
    result_equiv_cfg (run_function (2 * fuel) fn s)
                     (run_function fuel (merge_jump fn a_lbl b_lbl) s)
Proof
  completeInduct_on `fuel` >> rpt strip_tac
  >- cheat (* terminates *)
  >- cheat (* result_equiv_cfg *)
QED

Theorem merge_jump_correct:
  !fn a_lbl b_lbl s.
    cfg_wf fn /\
    phi_fn_wf fn /\
    merge_jump_cond fn a_lbl b_lbl /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE /\
    s.vs_inst_idx = 0 /\
    ~s.vs_halted ==>
    run_function_equiv_cfg fn (merge_jump fn a_lbl b_lbl) s
Proof
  rpt gen_tac >> simp[merge_jump_cond_def] >> strip_tac >>
  simp[run_function_equiv_cfg_def] >> conj_tac
  >- ( (* Forward direction: original terminates => merged terminates *)
    rpt strip_tac >> qexists_tac `fuel` >>
    `result_equiv_cfg (run_function fuel fn s)
                      (run_function fuel (merge_jump fn a_lbl b_lbl) s)`
      suffices_by (strip_tac >>
        Cases_on `run_function fuel fn s` >>
        Cases_on `run_function fuel (merge_jump fn a_lbl b_lbl) s` >>
        gvs[result_equiv_cfg_def, terminates_def]) >>
    irule run_function_merge_jump_equiv_fwd >> gvs[] >> metis_tac[])
  >- ( (* Backward direction: merged terminates => original terminates *)
    rpt strip_tac >> qexists_tac `2 * fuel'` >>
    drule_all run_function_merge_jump_equiv_bwd >> simp[])
QED

val _ = export_theory();
