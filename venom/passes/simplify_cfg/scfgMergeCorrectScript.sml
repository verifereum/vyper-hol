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

(* ===== Merging Blocks ===== *)

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
              `block_has_no_phi (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions)`
                by cheat (* TODO: helper lemma for block_has_no_phi on merged block *) \\
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
              `terminates (run_function n fn v')` by cheat (* TODO: derive from outer termination *) \\
              `run_function n fn v' = run_function (SUC n) fn v'`
                by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> irule run_function_fuel_monotonicity >> simp[]) \\
              pop_assum (fn th => REWRITE_TAC [th]) \\
              first_x_assum irule >> gvs[] >> cheat (* TODO: IH conditions *))
            >- (
              (* Block a has PHIs - needs different handling *)
              cheat (* TODO: handle PHI case with run_block_replace_label *))))))
    >- cheat (* Halt case - use run_block_merge_blocks_equiv *)
    >- cheat (* Revert case *)
    >- cheat (* Error case *))
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
              gvs[] \\ cheat (* TODO: IH conditions *)))
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
              >- (first_x_assum irule \\ cheat (* TODO: IH conditions *)))
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
          (* block has PHIs and prev_bb <> b_lbl *)
          Cases_on `s1.vs_prev_bb`
          >- (gvs[] \\ cheat (* TODO: NONE with PHIs *))
          >- cheat (* TODO: SOME prev with PHIs *)))))
QED

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
  cheat (* TODO: prove using 2*fuel bound *)
QED

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
  cheat
QED

val _ = export_theory();
