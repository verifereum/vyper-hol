(*
 * Assign Elimination — Convergence Proofs
 *
 * Measure definitions, invariant preservation, and monotonicity
 * for the copy_prop lattice. Proves that copy_prop analysis terminates.
 *
 * TOP-LEVEL: copy_val_measure_def, copy_prop_measure_inv_def,
 *   copy_prop_measure_def, copy_prop_measure_bound_def,
 *   copy_prop_joined_def
 * EXPORTED: cfg_edge_symmetry, copy_prop_join_absorption,
 *   copy_prop_measure_bounded, copy_prop_measure_monotone,
 *   copy_prop_measure_inv_preserved, copy_prop_measure_inv_initial
 *)

Theory assignElimConvergence
Ancestors
  assignElimDefs dfAnalyzeProofs cfgHelpers cfgAnalysisProps

open assignElimDefsTheory venomInstTheory venomExecProofsTheory
     finite_mapTheory listTheory pred_setTheory arithmeticTheory
     dfAnalyzeDefsTheory dfAnalyzeProofsTheory
     cfgHelpersTheory latticeDefsTheory worklistDefsTheory

(* ===== Convergence machinery for copy_prop lattice ===== *)

(* Measure for a single copy_lattice option value.
   NONE = 0 (bottom, no info yet).
   SOME fmap = max_vars + 1 - CARD(FDOM fmap) (under invariant, ≥ 1).
   This INCREASES for both transitions:
   - NONE → SOME fmap: 0 → max+1-CARD ≥ 1
   - SOME big → SOME small: max+1-CARD(big) → max+1-CARD(small), increases
   The second transition corresponds to losing copies (more conservative). *)
Definition copy_val_measure_def:
  copy_val_measure max_vars (NONE : copy_lattice option) = 0 /\
  copy_val_measure max_vars (SOME fmap) = max_vars + 1 - CARD (FDOM fmap)
End
(* Remove from simpset: subtraction causes side conditions that break proofs *)
val _ = delsimps ["copy_val_measure_def"]

(* Invariant: boundary and inst fmap values have FDOM ⊆ fn_all_assignments.
   No FDOM st.ds_inst bound — non-block labels create keys outside
   df_valid_inst_keys, so we can't maintain that invariant (L053). *)
Definition copy_prop_state_inv_def:
  copy_prop_state_inv fn (st : copy_lattice option df_state) <=>
    (!lbl fmap. FLOOKUP st.ds_boundary lbl = SOME (SOME fmap) ==>
       FDOM fmap SUBSET set (fn_all_assignments fn)) /\
    (!k fmap. FLOOKUP st.ds_inst k = SOME (SOME fmap) ==>
       FDOM fmap SUBSET set (fn_all_assignments fn))
End

(* Extended invariant for convergence proof.
   C1+C2: FDOM bounds (from copy_prop_state_inv)
   C3: fold coherence — ds_inst at lbl keys matches fold from stored v0
   C4: key closure — (lbl,j) in ds_inst implies (lbl,0) in ds_inst
   C5: processed implies boundary exists *)
Definition copy_prop_measure_inv_def:
  copy_prop_measure_inv fn (st : copy_lattice option df_state) <=>
    fn_inst_wf fn /\
    copy_prop_state_inv fn st /\
    (let transfer = copy_prop_transfer (phi_used_vars fn) in
     let instrs_of lbl = case lookup_block lbl fn.fn_blocks of
                           NONE => [] | SOME bb => bb.bb_instructions in
     (* C3: fold coherence *)
     (!lbl v0. FLOOKUP st.ds_inst (lbl, 0n) = SOME v0 ==>
        !k v. FLOOKUP (SND (df_fold_block Forward transfer
                 lbl (instrs_of lbl) v0)) k = SOME v ==>
          FLOOKUP st.ds_inst k = SOME v) /\
     (* C4: key closure *)
     (!lbl j. (lbl, j) IN FDOM st.ds_inst ==>
        (lbl, 0n) IN FDOM st.ds_inst) /\
     (* C5: processed implies boundary exists *)
     (!lbl. (lbl, 0n) IN FDOM st.ds_inst ==>
        lbl IN FDOM st.ds_boundary))
End

(* Boundary measure: sum of per-label boundary-value measures over dfs_pre.
   Covers all labels the worklist might process (not just fn_labels).
   Increases as lattice values move up (NONE→SOME or SOME shrinks). *)
Definition copy_boundary_measure_def:
  copy_boundary_measure fn (st : copy_lattice option df_state) =
    let mv = CARD (set (fn_all_assignments fn)) in
    let dfs_pre = (cfg_analyze fn).cfg_dfs_pre in
    SUM (MAP (\lbl. copy_val_measure mv (df_boundary NONE st lbl))
             (fn_labels fn ++ dfs_pre))
End

(* Joined value for copy propagation at a label *)
Definition copy_prop_joined_def:
  copy_prop_joined fn st lbl =
    let cfg = cfg_analyze fn in
    let edge_vals = MAP (\nbr. df_boundary NONE st nbr)
                        (cfg_preds_of cfg lbl) in
    let base = (case edge_vals of
                  [] => NONE
                | _ => FOLDL copy_prop_join NONE edge_vals) in
    case fn_entry_label fn of
      NONE => base
    | SOME ev_lbl =>
        if lbl = ev_lbl then copy_prop_join (SOME FEMPTY) base else base
End

(* Fresh count: number of dfs_pre labels whose stored v0 matches current
   joined value. Covers all worklist-processable labels. *)
Definition copy_prop_fresh_count_def:
  copy_prop_fresh_count fn (st : copy_lattice option df_state) =
    let dfs_pre = (cfg_analyze fn).cfg_dfs_pre in
    CARD {lbl | MEM lbl (fn_labels fn ++ dfs_pre) /\
                (lbl, 0n) IN FDOM st.ds_inst /\
                FLOOKUP st.ds_inst (lbl, 0n) =
                SOME (copy_prop_joined fn st lbl)}
End

(* Full measure:
   W * boundary_sum + CARD(valid inst slots filled) + fresh_count + dfs_visited.
   W = all_count + 1 ensures boundary increases dominate fresh decreases.
   all_count = LENGTH(fn_labels ++ dfs_pre) (may count some labels twice,
   but that's fine for bounding — it's a conservative weight).
   fresh_count uses the same all_count list for consistency. *)
Definition copy_prop_measure_def:
  copy_prop_measure fn (st : copy_lattice option df_state) =
    let dfs_pre = (cfg_analyze fn).cfg_dfs_pre in
    let all_count = LENGTH (fn_labels fn) + LENGTH dfs_pre in
    (all_count + 1) * copy_boundary_measure fn st +
    CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) +
    copy_prop_fresh_count fn st +
    CARD (FDOM st.ds_boundary INTER set dfs_pre)
End

(* Upper bound *)
Definition copy_prop_measure_bound_def:
  copy_prop_measure_bound fn =
    let max_vars = CARD (set (fn_all_assignments fn)) in
    let nlabels = LENGTH (fn_labels fn) in
    let total_slots = df_total_inst_slots fn.fn_blocks in
    let ndfs = LENGTH (cfg_analyze fn).cfg_dfs_pre in
    let all_count = nlabels + ndfs in
    (all_count + 1) * ((max_vars + 1) * (nlabels + ndfs)) +
    total_slots +
    (nlabels + ndfs) +
    ndfs
End

(* Per-value measure is bounded under the invariant *)
Theorem copy_val_measure_bounded[local]:
  !v mv.
    (case v of NONE => T
     | SOME fmap => CARD (FDOM fmap) <= mv) ==>
    copy_val_measure mv v <= mv + 1
Proof
  Cases >> simp[copy_val_measure_def]
QED

(* Initial state satisfies copy_prop_state_inv *)
Theorem copy_prop_init_state_inv[local]:
  !fn.
    case OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) of
      NONE => copy_prop_state_inv fn
        (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks))
    | SOME (lbl,v) => copy_prop_state_inv fn
        (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks) with
         ds_boundary :=
           (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks)).ds_boundary
             |+ (lbl,v))
Proof
  rpt strip_tac >>
  simp[copy_prop_state_inv_def, LET_THM, init_df_state_def] >>
  Cases_on `fn_entry_label fn` >> simp[] >> rpt gen_tac >> strip_tac >> (
    TRY (qpat_x_assum `FLOOKUP (_ |+ _) _ = _`
           (mp_tac o REWRITE_RULE [FLOOKUP_UPDATE]) >>
         IF_CASES_TAC >> simp[] >> strip_tac >> gvs[FDOM_FEMPTY]) >>
    (* FLOOKUP(FOLDL ... FEMPTY labels) _ = SOME v => v = NONE *)
    `SOME fmap = (NONE : copy_lattice option)` by
      metis_tac[dfAnalyzeProofsTheory.foldl_fupdate_flookup,
                FLOOKUP_EMPTY, optionTheory.NOT_SOME_NONE] >>
    fs[])
QED

(* Bound SUM(MAP f l) when each f(x) <= n *)
Triviality sum_map_le_bound[local]:
  !f (n:num) l. EVERY (\x. f x <= n) l ==> SUM (MAP f l) <= n * LENGTH l
Proof
  Induct_on `l` >> rw[] >> res_tac >>
  fs[arithmeticTheory.MULT_SUC]
QED

(* Helper: each boundary value's measure is bounded *)
Triviality copy_val_measure_boundary_le[local]:
  !fn st lbl.
    (!lbl fmap. FLOOKUP st.ds_boundary lbl = SOME (SOME fmap) ==>
       FDOM fmap SUBSET set (fn_all_assignments fn)) ==>
    copy_val_measure (CARD (set (fn_all_assignments fn)))
                     (df_boundary NONE st lbl) <=
    CARD (set (fn_all_assignments fn)) + 1
Proof
  rpt strip_tac >> irule copy_val_measure_bounded >>
  simp[df_boundary_def] >>
  Cases_on `FLOOKUP st.ds_boundary lbl` >> simp[] >>
  Cases_on `x` >> simp[] >>
  res_tac >> irule CARD_SUBSET >> simp[FDOM_FINITE]
QED

(* Measure is bounded under invariant *)
Theorem copy_prop_measure_bounded:
  !fn st.
    copy_prop_state_inv fn st ==>
    copy_prop_measure fn st <= copy_prop_measure_bound fn
Proof
  rpt strip_tac >>
  fs[copy_prop_state_inv_def] >>
  (* Bound 1: boundary measure *)
  `copy_boundary_measure fn st <=
   (CARD (set (fn_all_assignments fn)) + 1) *
   LENGTH (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre)` by (
    simp_tac std_ss [copy_boundary_measure_def, LET_THM] >>
    irule arithmeticTheory.LESS_EQ_TRANS >>
    irule_at Any sum_map_le_bound >>
    qexists_tac `CARD (set (fn_all_assignments fn)) + 1` >>
    simp[EVERY_MEM, MEM_APPEND] >>
    rpt strip_tac >> irule copy_val_measure_boundary_le >> metis_tac[]) >>
  fs[LENGTH_APPEND] >>
  (* Bound 2: inst CARD *)
  `CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) <=
   (df_total_inst_slots fn.fn_blocks : num)` by (
    match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac `CARD (df_valid_inst_keys fn.fn_blocks)` >>
    simp[df_valid_inst_keys_card] >>
    ONCE_REWRITE_TAC[INTER_COMM] >>
    irule CARD_INTER_LESS_EQ >>
    simp[df_valid_inst_keys_finite]) >>
  (* Bound 3: fresh count *)
  `copy_prop_fresh_count fn st <=
   LENGTH (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre)` by (
    simp_tac std_ss [copy_prop_fresh_count_def, LET_THM] >>
    match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac `CARD (set (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre))` >>
    conj_tac >- (
      irule CARD_SUBSET >> simp[FINITE_LIST_TO_SET, SUBSET_DEF]) >>
    simp[CARD_LIST_TO_SET]) >>
  fs[LENGTH_APPEND] >>
  (* Bound 4: dfs_visited *)
  `CARD (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre) <=
   LENGTH (cfg_analyze fn).cfg_dfs_pre` by (
    match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac `CARD (set (cfg_analyze fn).cfg_dfs_pre)` >>
    simp[CARD_LIST_TO_SET] >>
    ONCE_REWRITE_TAC[INTER_COMM] >>
    irule CARD_INTER_LESS_EQ >>
    simp[FINITE_LIST_TO_SET]) >>
  (* Combine: each component bounded, use monotonicity of + and * *)
  simp_tac std_ss [copy_prop_measure_def, copy_prop_measure_bound_def, LET_THM] >>
  irule arithmeticTheory.LESS_EQ_LESS_EQ_MONO >>
  REVERSE conj_tac >- first_assum ACCEPT_TAC >>
  irule arithmeticTheory.LESS_EQ_LESS_EQ_MONO >>
  REVERSE conj_tac >- first_assum ACCEPT_TAC >>
  irule arithmeticTheory.LESS_EQ_LESS_EQ_MONO >>
  REVERSE conj_tac >- first_assum ACCEPT_TAC >>
  irule arithmeticTheory.LESS_MONO_MULT2 >> simp[]
QED
(* ===== End convergence helpers ===== *)

(* copy_prop_join is idempotent: join(x,x) = x *)
Theorem copy_prop_join_raw_idem[local]:
  !m. copy_prop_join_raw m m = m
Proof
  rw[copy_prop_join_raw_def, fmap_EXT, DRESTRICT_DEF,
     copy_agree_def, EXTENSION] >>
  rw[FLOOKUP_DRESTRICT] >>
  Cases_on `FLOOKUP m x` >> fs[FLOOKUP_DEF]
QED

(* Unconditional CFG symmetry: succs and preds are inverses by construction.
   Does NOT require wf_function — follows from mem_build_preds + fdom_build_succs. *)
Theorem cfg_edge_symmetry:
  !fn a b. MEM b (cfg_succs_of (cfg_analyze fn) a) <=>
           MEM a (cfg_preds_of (cfg_analyze fn) b)
Proof
  rpt gen_tac >>
  simp[cfgHelpersTheory.cfg_analyze_succs, cfgHelpersTheory.cfg_analyze_preds,
       cfgHelpersTheory.mem_build_preds] >>
  eq_tac >> rpt strip_tac
  >- (
    `?blk. MEM blk fn.fn_blocks /\ blk.bb_label = a` by (
      spose_not_then strip_assume_tac >>
      `~MEM a (MAP (\bb. bb.bb_label) fn.fn_blocks)` by (
        simp[MEM_MAP] >> metis_tac[]) >>
      `fmap_lookup_list (build_succs fn.fn_blocks) a = []` by
        metis_tac[cfgHelpersTheory.cfg_succs_of_not_in_labels] >>
      fs[]) >>
    qexists_tac `blk` >> fs[])
  >- metis_tac[]
QED

(* copy_prop_join absorption: join(join(a,b), b) = join(a,b) *)
Theorem copy_prop_join_absorption:
  !a b. copy_prop_join (copy_prop_join a b) b = copy_prop_join a b
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[copy_prop_join_def, copy_prop_join_raw_idem] >>
  rw[copy_prop_join_raw_def, fmap_EXT, DRESTRICT_DEF,
     copy_agree_def, EXTENSION] >>
  rw[FLOOKUP_DRESTRICT]
QED

(* Bridge: df_process_block for copy_prop = fold from copy_prop_joined *)
Triviality copy_prop_process_eq[local]:
  !fn lbl st.
    df_process_block Forward NONE copy_prop_join copy_prop_transfer
      copy_prop_edge_transfer (phi_used_vars fn)
      (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks lbl st =
    let instrs = case lookup_block lbl fn.fn_blocks of
                   NONE => [] | SOME bb => bb.bb_instructions in
    let (fv, inst_map) = df_fold_block Forward
                           (copy_prop_transfer (phi_used_vars fn)) lbl
                           instrs (copy_prop_joined fn st lbl) in
      st with <|ds_boundary := st.ds_boundary |+
                  (lbl, copy_prop_join (df_boundary NONE st lbl) fv);
                ds_inst := FUNION inst_map st.ds_inst|>
Proof
  rw[df_process_block_def, df_joined_val_def] >>
  simp_tac std_ss [LET_THM, direction_case_def] >>
  rw[copy_prop_edge_transfer_def] >>
  simp[copy_prop_joined_def, LET_THM] >>
  Cases_on `fn_entry_label fn` >> simp[]
QED

(* copy_prop_join preserves FDOM ⊆ S *)
Triviality copy_prop_join_fdom_subset[local]:
  !c1 c2 bound.
    (case c1 of NONE => T | SOME fmap => FDOM fmap SUBSET bound) /\
    (case c2 of NONE => T | SOME fmap => FDOM fmap SUBSET bound) ==>
    (case copy_prop_join c1 c2 of NONE => T
     | SOME fmap => FDOM fmap SUBSET bound)
Proof
  Cases_on `c1` >> Cases_on `c2` >>
  simp[copy_prop_join_def, copy_prop_join_raw_def, FDOM_DRESTRICT] >>
  metis_tac[SUBSET_INTER_ABSORPTION, INTER_SUBSET, SUBSET_TRANS]
QED

(* copy_prop_transfer preserves FDOM ⊆ S when inst outputs ⊆ S.
   Key facts: transfer always returns SOME, DRESTRICT shrinks FDOM,
   FUPDATE adds at most one output variable. *)
Triviality copy_prop_transfer_fdom_subset[local]:
  !ctx inst v bound.
    (case v of NONE => T | SOME fmap => FDOM fmap SUBSET bound) /\
    set (inst.inst_outputs) SUBSET bound ==>
    (case copy_prop_transfer ctx inst v of NONE => T
     | SOME fmap => FDOM fmap SUBSET bound)
Proof
  rpt strip_tac >>
  simp[copy_prop_transfer_def, LET_THM] >>
  (* Result is always SOME, so case eliminates to FDOM ⊆ bound *)
  Cases_on `v` >> simp[] >>
  (* Both branches: IF + nested case on operands/outputs *)
  IF_CASES_TAC >> simp[FDOM_DRESTRICT, FDOM_FEMPTY] >>
  TRY (fs[SUBSET_DEF] >> NO_TAC) >>
  Cases_on `inst.inst_operands` >>
  simp[FDOM_DRESTRICT, FDOM_FEMPTY] >>
  TRY (fs[SUBSET_DEF] >> NO_TAC) >>
  Cases_on `inst.inst_outputs` >>
  simp[FDOM_DRESTRICT, FDOM_FEMPTY] >>
  TRY (fs[SUBSET_DEF] >> NO_TAC) >>
  Cases_on `t` >> simp[FDOM_DRESTRICT, FDOM_FEMPTY] >>
  TRY (fs[SUBSET_DEF] >> NO_TAC) >>
  TRY (Cases_on `t'` >> simp[FDOM_DRESTRICT, FDOM_FEMPTY] >>
       TRY (fs[SUBSET_DEF] >> NO_TAC))
QED

(* FOLDL copy_prop_join preserves FDOM ⊆ S *)
Triviality foldl_copy_prop_join_fdom_subset[local]:
  !l init bound.
    (case init of NONE => T | SOME fmap => FDOM fmap SUBSET bound) /\
    EVERY (\v. case v of NONE => T | SOME fmap => FDOM fmap SUBSET bound) l ==>
    (case FOLDL copy_prop_join init l of NONE => T
     | SOME fmap => FDOM fmap SUBSET bound)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  metis_tac[copy_prop_join_fdom_subset]
QED

(* df_boundary values satisfy P under invariant *)
Triviality df_boundary_inv[local]:
  !fn st lbl.
    copy_prop_state_inv fn st ==>
    (case df_boundary NONE st lbl of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn))
Proof
  rpt strip_tac >> simp[df_boundary_def] >>
  CASE_TAC >> simp[] >>
  Cases_on `x` >> simp[] >>
  fs[copy_prop_state_inv_def] >> res_tac
QED

(* Helper: every df_boundary value in a MAP satisfies the invariant *)
Triviality df_boundary_map_inv[local]:
  !fn st lbls.
    copy_prop_state_inv fn st ==>
    EVERY (\v. case v of NONE => T
       | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn))
      (MAP (\nbr. df_boundary NONE st nbr) lbls)
Proof
  Induct_on `lbls` >> simp[] >> rpt strip_tac >> metis_tac[df_boundary_inv]
QED

(* copy_prop_joined satisfies the invariant *)
Triviality copy_prop_joined_inv[local]:
  !fn st lbl.
    copy_prop_state_inv fn st ==>
    (case copy_prop_joined fn st lbl of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn))
Proof
  rpt strip_tac >>
  mp_tac (SPECL [``fn : ir_function``, ``st : copy_lattice option df_state``,
                 ``cfg_preds_of (cfg_analyze fn) lbl``]
    df_boundary_map_inv) >>
  simp[] >> strip_tac >>
  simp[copy_prop_joined_def, LET_THM] >>
  (* Prove base has the property, then handle entry wrapping *)
  Cases_on `MAP (\nbr. df_boundary NONE st nbr)
                (cfg_preds_of (cfg_analyze fn) lbl)` >> simp[]
  >- ((* [] case *)
      Cases_on `fn_entry_label fn` >> simp[] >>
      IF_CASES_TAC >> gvs[] >>
      simp[copy_prop_join_def, copy_prop_join_raw_def, FDOM_FEMPTY])
  >- ((* h::t case *)
      Cases_on `fn_entry_label fn` >> simp[]
      >- (match_mp_tac foldl_copy_prop_join_fdom_subset >> fs[] >>
          irule copy_prop_join_fdom_subset >> simp[])
      >- (IF_CASES_TAC >> gvs[]
          >- (irule copy_prop_join_fdom_subset >> simp[FDOM_FEMPTY] >>
              match_mp_tac foldl_copy_prop_join_fdom_subset >> fs[] >>
              irule copy_prop_join_fdom_subset >> simp[])
          >- (match_mp_tac foldl_copy_prop_join_fdom_subset >> fs[] >>
              irule copy_prop_join_fdom_subset >> simp[])))
QED

(* Specialized fold invariant for copy_prop's FDOM property.
   Curried hypotheses for easy use with drule chains. *)
Triviality copy_prop_fold_fdom[local]:
  !transfer lbl instrs init_val fv im bound.
    df_fold_block Forward transfer lbl instrs init_val = (fv, im) ==>
    (case init_val of NONE => T
     | SOME fmap => FDOM fmap SUBSET bound) ==>
    (!inst v. MEM inst instrs /\
      (case v of NONE => T | SOME fmap => FDOM fmap SUBSET bound) ==>
      (case transfer inst v of NONE => T | SOME fmap => FDOM fmap SUBSET bound))
    ==>
    (case fv of NONE => T | SOME fmap => FDOM fmap SUBSET bound) /\
    (!k v. FLOOKUP im k = SOME v ==>
      (case v of NONE => T | SOME fmap => FDOM fmap SUBSET bound))
Proof
  rpt strip_tac >>
  drule (dfAnalyzeProofsTheory.df_fold_block_forward_invariant
         |> REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then (qspec_then
    `\v. case v of NONE => T | SOME fmap => FDOM fmap SUBSET bound`
    (mp_tac o BETA_RULE)) >>
  simp[] >> strip_tac >> res_tac
QED

(* Transfer preserves FDOM ⊆ bound *)
Triviality copy_prop_transfer_preserves_fdom[local]:
  !fn lbl inst v.
    fn_inst_wf fn /\
    MEM inst (case lookup_block lbl fn.fn_blocks of NONE => []
              | SOME bb => bb.bb_instructions) /\
    (case v of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn)) ==>
    (case copy_prop_transfer (phi_used_vars fn) inst v of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn))
Proof
  rpt strip_tac >>
  irule copy_prop_transfer_fdom_subset >> simp[] >>
  Cases_on `lookup_block lbl fn.fn_blocks` >> fs[MEM] >>
  imp_res_tac lookup_block_MEM >>
  simp[SUBSET_DEF] >> rpt strip_tac >>
  simp[fn_all_assignments_def, MEM_nub, MEM_FLAT, MEM_MAP] >>
  simp[PULL_EXISTS] >>
  qexists_tac `x` >> simp[] >>
  simp[inst_defs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

(* P preserved: processing a block preserves the state invariant *)
Triviality copy_prop_inv_preserved[local]:
  !fn lbl st.
    fn_inst_wf fn /\ copy_prop_state_inv fn st ==>
    copy_prop_state_inv fn
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt strip_tac >>
  simp[copy_prop_state_inv_def, copy_prop_process_eq] >>
  simp_tac std_ss [LET_THM] >> pairarg_tac >> simp[] >>
  (* Establish P(joined) *)
  `case copy_prop_joined fn st lbl of NONE => T
   | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn)`
    by metis_tac[copy_prop_joined_inv]
  (* Establish transfer preserves P *)
  >> `!inst v.
       MEM inst (case lookup_block lbl fn.fn_blocks of NONE => []
                 | SOME bb => bb.bb_instructions) /\
       (case v of NONE => T
        | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn)) ==>
       (case copy_prop_transfer (phi_used_vars fn) inst v of NONE => T
        | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn))`
    by metis_tac[copy_prop_transfer_preserves_fdom]
  (* Apply fold invariant *)
  >> drule copy_prop_fold_fdom
  >> disch_then (qspec_then `set (fn_all_assignments fn)` mp_tac)
  >> simp[]
  >> strip_tac >>
  (* Establish df_boundary fact BEFORE expanding invariant *)
  `case df_boundary NONE st lbl of NONE => T
   | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn)`
    by metis_tac[df_boundary_inv] >>
  fs[copy_prop_state_inv_def] >>
  rpt conj_tac
  (* boundary *)
  >- (rpt gen_tac >> simp[FLOOKUP_UPDATE] >>
      rw[] >> res_tac >>
      mp_tac (Q.SPECL [`df_boundary NONE st lbl`, `fv`, `set (fn_all_assignments fn)`]
                       copy_prop_join_fdom_subset) >>
      simp[] >> strip_tac >>
      Cases_on `copy_prop_join (df_boundary NONE st lbl) fv` >> gvs[])
  (* inst *)
  >- (rpt gen_tac >> simp[FLOOKUP_FUNION] >>
      Cases_on `FLOOKUP inst_map k` >> simp[]
      >- (strip_tac >> res_tac)
      >- (strip_tac >> gvs[] >>
          first_x_assum (qspecl_then [`k`, `SOME fmap`] mp_tac) >> simp[]))
QED

(* measure_inv for initial state — C3,C4,C5 vacuously true since ds_inst=FEMPTY *)
Theorem copy_prop_measure_inv_initial:
  !fn.
    fn_inst_wf fn ==>
    case OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) of
      NONE => copy_prop_measure_inv fn
        (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks))
    | SOME (lbl,v) => copy_prop_measure_inv fn
        (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks) with
         ds_boundary :=
           (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks)).ds_boundary
             |+ (lbl,v))
Proof
  rpt strip_tac >>
  simp[copy_prop_measure_inv_def, init_df_state_def, LET_THM] >>
  mp_tac (SPEC_ALL copy_prop_init_state_inv) >>
  Cases_on `fn_entry_label fn` >> simp[init_df_state_def]
QED

(* SUM(MAP f l) ≤ SUM(MAP g l) when f ≤ g pointwise on l *)
Triviality sum_map_le[local]:
  !f g l. EVERY (\x. f x <= g x) l ==> SUM (MAP f l) <= SUM (MAP g l)
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  irule LESS_EQ_LESS_EQ_MONO >> simp[]
QED

(* SUM(MAP f l) < SUM(MAP g l) when f ≤ g pointwise and strictly < at some MEM *)
Triviality sum_map_lt[local]:
  !f g l. EVERY (\x. f x <= g x) l /\
          (?x. MEM x l /\ f x < g x) ==>
          SUM (MAP f l) < SUM (MAP g l)
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  `SUM (MAP f l) <= SUM (MAP g l)` by (irule sum_map_le >> simp[])
  >- (gvs[] >>
      irule LESS_EQ_LESS_TRANS >>
      qexists_tac `g h + SUM (MAP f l)` >> simp[])
  >- (irule LESS_LESS_EQ_TRANS >>
      qexists_tac `f h + SUM (MAP g l)` >>
      reverse conj_tac >- simp[] >>
      simp[LT_ADD_LCANCEL] >>
      first_x_assum irule >> simp[] >> metis_tac[])
QED

(* Monotonicity: processing a dfs_pre label either leaves state unchanged or
   increases measure. *)
(* Helper: FDOM f ⊆ s ⇒ DRESTRICT f s = f *)
Triviality drestrict_subset_id[local]:
  !f (s:'a -> bool). FDOM f SUBSET s ==> DRESTRICT f s = f
Proof
  rpt strip_tac >>
  simp[GSYM fmap_EQ_THM, FDOM_DRESTRICT, INTER_SUBSET_EQN] >>
  rpt strip_tac >> simp[DRESTRICT_DEF]
QED

(* copy_val_measure strict when join differs *)
Triviality copy_val_measure_join_strict[local]:
  !mv a b.
    (case a of NONE => T | SOME fmap => CARD (FDOM fmap) <= mv) /\
    (case b of NONE => T | SOME fmap => CARD (FDOM fmap) <= mv) /\
    copy_prop_join a b <> a ==>
    copy_val_measure mv a < copy_val_measure mv (copy_prop_join a b)
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[copy_prop_join_def, copy_val_measure_def, copy_prop_join_raw_def,
       FDOM_DRESTRICT] >>
  rpt strip_tac >>
  (* DRESTRICT x ag ≠ x ⇒ ¬(FDOM x ⊆ ag) ⇒ FDOM x ∩ ag ⊂ FDOM x *)
  qabbrev_tac `ag = {x'' | copy_agree x x' x''}` >>
  `~(FDOM x SUBSET ag)` by metis_tac[drestrict_subset_id] >>
  `FDOM x INTER ag PSUBSET FDOM x` by (
    fs[PSUBSET_DEF, INTER_SUBSET, SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
  `CARD (FDOM x INTER ag) < CARD (FDOM x)` by
    (irule CARD_PSUBSET >> simp[FDOM_FINITE]) >>
  simp[LE_SUB_LCANCEL]
QED

(* Case A helper: boundary strictly increases at lbl *)
Triviality boundary_measure_strict[local]:
  !fn lbl st.
    copy_prop_measure_inv fn st /\
    MEM lbl (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre) /\
    copy_val_measure (CARD (set (fn_all_assignments fn)))
                     (df_boundary NONE st lbl) <
    copy_val_measure (CARD (set (fn_all_assignments fn))) new_val ==>
    copy_boundary_measure fn st <
    copy_boundary_measure fn (st with ds_boundary := st.ds_boundary |+ (lbl, new_val))
Proof
  rpt strip_tac >>
  simp[copy_boundary_measure_def, LET_THM] >>
  ntac 2 (once_rewrite_tac[GSYM MAP_APPEND]) >>
  irule sum_map_lt >> simp[] >>
  `!x. copy_val_measure (CARD (set (fn_all_assignments fn)))
         (df_boundary NONE
            (st with ds_boundary := st.ds_boundary |+ (lbl, new_val)) x) =
       if x = lbl then
         copy_val_measure (CARD (set (fn_all_assignments fn))) new_val
       else
         copy_val_measure (CARD (set (fn_all_assignments fn)))
           (df_boundary NONE st x)` by
    (rpt strip_tac >> simp[df_boundary_def, FLOOKUP_UPDATE] >>
     IF_CASES_TAC >> simp[]) >>
  rpt conj_tac >>
  TRY (simp[EVERY_MEM] >> rpt strip_tac >>
       IF_CASES_TAC >> simp[] >> NO_TAC) >>
  qexists_tac `lbl` >> fs[MEM_APPEND]
QED

(* joined only depends on ds_boundary, not ds_inst *)
Triviality copy_prop_joined_inst_irrelevant[local]:
  !fn st X lbl.
    copy_prop_joined fn (st with ds_inst := X) lbl =
    copy_prop_joined fn st lbl
Proof
  simp[copy_prop_joined_def, LET_THM, df_boundary_def]
QED

(* Case B helper: fresh_count increases when v0 at lbl changes to joined *)
Triviality fresh_count_increase[local]:
  !fn st inst_map lbl.
    MEM lbl (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre) /\
    FLOOKUP inst_map (lbl, 0n) = SOME (copy_prop_joined fn st lbl) /\
    (!k. k IN FDOM inst_map ==> FST k = lbl) /\
    FLOOKUP (FUNION inst_map st.ds_inst) (lbl, 0n) <>
      FLOOKUP st.ds_inst (lbl, 0n) ==>
    copy_prop_fresh_count fn st <
    copy_prop_fresh_count fn (st with ds_inst := FUNION inst_map st.ds_inst)
Proof
  rpt strip_tac >>
  simp[copy_prop_fresh_count_def, LET_THM,
       copy_prop_joined_inst_irrelevant] >>
  irule CARD_PSUBSET >>
  simp[PSUBSET_MEMBER] >>
  conj_tac >- (
    irule SUBSET_FINITE >>
    qexists_tac `set (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre)` >>
    simp[SUBSET_DEF, MEM_APPEND]) >>
  conj_tac >- (
    simp[SUBSET_DEF, FDOM_FUNION, FLOOKUP_FUNION] >>
    rpt strip_tac >>
    Cases_on `FLOOKUP inst_map (x, 0n)` >> gvs[] >>
    `(x, 0n) IN FDOM inst_map` by fs[FLOOKUP_DEF] >>
    `FST (x, 0n:num) = lbl` by res_tac >> gvs[]) >>
  qexists_tac `lbl` >>
  conj_tac >- (
    gvs[FDOM_FUNION, FLOOKUP_FUNION, FLOOKUP_DEF, MEM_APPEND]) >>
  gvs[FLOOKUP_FUNION, FLOOKUP_DEF]
QED

(* Key properties of inst_map from df_fold_block *)
Triviality df_fold_block_inst_map_props[local]:
  !transfer lbl instrs v0 fv inst_map.
    df_fold_block Forward transfer lbl instrs v0 = (fv, inst_map) ==>
    (!k. k IN FDOM inst_map ==> FST k = lbl) /\
    (lbl, 0n) IN FDOM inst_map /\
    FLOOKUP inst_map (lbl, 0n) = SOME v0
Proof
  rpt strip_tac >> imp_res_tac df_fold_block_fdom
  >- fs[IN_IMAGE, IN_COUNT]
  >- simp[IN_IMAGE, IN_COUNT]
  >- (qpat_x_assum `_ = (fv, inst_map)` mp_tac >>
      simp[dfAnalyzeDefsTheory.df_fold_block_def,
           dfAnalyzeDefsTheory.direction_case_def] >>
      strip_tac >> imp_res_tac df_fold_forward_at >> fs[])
QED

(* C3 coherence: when ds_inst already has the right v0 at (lbl,0),
   the fold output inst_map is absorbed by FUNION. *)
Triviality funion_fold_coherent[local]:
  !fn lbl st joined instrs fv inst_map.
    copy_prop_measure_inv fn st /\
    instrs = (case lookup_block lbl fn.fn_blocks of
                NONE => [] | SOME bb => bb.bb_instructions) /\
    df_fold_block Forward (copy_prop_transfer (phi_used_vars fn)) lbl
      instrs joined = (fv, inst_map) /\
    FLOOKUP st.ds_inst (lbl, 0n) = SOME joined ==>
    FUNION inst_map st.ds_inst = st.ds_inst
Proof
  rpt strip_tac >>
  (* Specialize C3 from measure_inv for our lbl/joined *)
  `!k v. FLOOKUP inst_map k = SOME v ==> FLOOKUP st.ds_inst k = SOME v` by (
    rpt strip_tac >>
    qpat_x_assum `copy_prop_measure_inv _ _` mp_tac >>
    simp_tac std_ss [copy_prop_measure_inv_def, LET_THM] >>
    strip_tac >>
    first_x_assum (qspecl_then [`lbl`, `joined`] mp_tac) >>
    impl_tac >- simp[] >>
    disch_then (qspecl_then [`k`, `v`] mp_tac) >>
    impl_tac >- (
      qpat_x_assum `instrs = _` (SUBST1_TAC o GSYM) >>
      qpat_x_assum `df_fold_block _ _ _ _ _ = _` (fn th => simp[th])) >>
    simp[]) >>
  (* Now show FUNION absorption *)
  simp[fmap_eq_flookup] >> gen_tac >> simp[FLOOKUP_FUNION] >>
  Cases_on `FLOOKUP inst_map x` >> simp[]
QED

Triviality ds_inst_update_literal[local]:
  !(st : 'a df_state) X.
    (st with ds_inst := X) = <|ds_inst := X; ds_boundary := st.ds_boundary|>
Proof
  simp[dfAnalyzeDefsTheory.df_state_component_equality]
QED

Triviality inst_card_mono[local]:
  !inst_map st fn.
    CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) <=
    CARD (FDOM (FUNION inst_map st.ds_inst) INTER
          df_valid_inst_keys fn.fn_blocks)
Proof
  rpt strip_tac >>
  irule CARD_SUBSET >> simp[FINITE_INTER, FDOM_FUNION] >>
  simp[SUBSET_DEF, IN_INTER] >> metis_tac[IN_UNION]
QED

(* copy_prop_joined depends only on ds_boundary, and is preserved
   when df_boundary values are unchanged *)
Triviality copy_prop_joined_boundary_eq[local]:
  !fn st bnd di.
    (!x. df_boundary NONE <|ds_inst := di; ds_boundary := bnd|> x =
         df_boundary NONE st x) ==>
    !x. copy_prop_joined fn <|ds_inst := di; ds_boundary := bnd|> x =
        copy_prop_joined fn st x
Proof
  rpt strip_tac >>
  simp[copy_prop_joined_def, LET_THM]
QED

(* fresh_count monotonicity under FUNION when joined values are preserved *)
Triviality fresh_count_mono[local]:
  !fn st inst_map lbl bnd.
    (!k. k IN FDOM inst_map ==> FST k = lbl) /\
    FLOOKUP inst_map (lbl, 0n) = SOME (copy_prop_joined fn st lbl) /\
    (!x. copy_prop_joined fn <|ds_inst := FUNION inst_map st.ds_inst;
                                ds_boundary := bnd|> x =
         copy_prop_joined fn st x) ==>
    copy_prop_fresh_count fn st <=
    copy_prop_fresh_count fn
      <|ds_inst := FUNION inst_map st.ds_inst; ds_boundary := bnd|>
Proof
  rpt strip_tac >>
  simp[copy_prop_fresh_count_def, LET_THM] >>
  irule CARD_SUBSET >>
  conj_tac >- (
    irule SUBSET_FINITE >>
    qexists_tac `set (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre)` >>
    simp[SUBSET_DEF, MEM_APPEND]) >>
  simp[SUBSET_DEF, FDOM_FUNION, FLOOKUP_FUNION] >>
  rpt strip_tac >>
  TRY (simp[IN_UNION] >> NO_TAC) >>
  Cases_on `FLOOKUP inst_map (x, 0n)` >> simp[] >>
  `(x, 0n) IN FDOM inst_map` by fs[FLOOKUP_DEF] >>
  `FST (x, 0n:num) = lbl` by res_tac >> gvs[]
QED

Triviality fresh_count_bounded[local]:
  !fn st.
    copy_prop_fresh_count fn st <=
    LENGTH (fn_labels fn) + LENGTH (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  simp_tac std_ss [copy_prop_fresh_count_def, LET_THM] >>
  match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `CARD (set (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre))` >>
  conj_tac >- (
    irule CARD_SUBSET >> simp[FINITE_LIST_TO_SET, SUBSET_DEF]) >>
  match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `LENGTH (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre)` >>
  simp[CARD_LIST_TO_SET, LENGTH_APPEND]
QED

Triviality fold_output_card_bound[local]:
  !fn st lbl instrs joined fv inst_map.
    fn_inst_wf fn /\
    copy_prop_state_inv fn st /\
    instrs = (case lookup_block lbl fn.fn_blocks of
                NONE => [] | SOME bb => bb.bb_instructions) /\
    joined = copy_prop_joined fn st lbl /\
    df_fold_block Forward (copy_prop_transfer (phi_used_vars fn))
      lbl instrs joined = (fv, inst_map) ==>
    (case fv of NONE => T
     | SOME fmap => CARD (FDOM fmap) <= CARD (set (fn_all_assignments fn)))
Proof
  rpt strip_tac >>
  Cases_on `fv` >> simp[] >>
  `FDOM x SUBSET set (fn_all_assignments fn)` suffices_by
    metis_tac[CARD_SUBSET, FINITE_LIST_TO_SET] >>
  drule copy_prop_fold_fdom >>
  disch_then (qspec_then `set (fn_all_assignments fn)` mp_tac) >>
  simp[] >>
  impl_tac >- (
    ASM_REWRITE_TAC [] >>
    conj_tac >- metis_tac[copy_prop_joined_inv] >>
    ASM_REWRITE_TAC [] >>
    metis_tac[copy_prop_transfer_preserves_fdom]) >>
  simp[]
QED

Triviality boundary_card_bound[local]:
  !fn st lbl.
    copy_prop_state_inv fn st ==>
    (case df_boundary NONE st lbl of NONE => T
     | SOME fmap => CARD (FDOM fmap) <= CARD (set (fn_all_assignments fn)))
Proof
  rpt strip_tac >>
  Cases_on `FLOOKUP st.ds_boundary lbl` >> simp[df_boundary_def] >>
  Cases_on `x` >> simp[] >>
  fs[copy_prop_state_inv_def] >>
  first_x_assum drule >> strip_tac >>
  metis_tac[CARD_SUBSET, FINITE_LIST_TO_SET]
QED

Triviality weighted_lt_cancel[local]:
  !w (a:num) a' c. a < a' /\ c <= w ==> (w + 1) * a + c < (w + 1) * a'
Proof
  rpt strip_tac >>
  `(w + 1) * a + c <= (w + 1) * a + w` by simp[] >>
  `(w + 1) * a + w < (w + 1) * (a + 1)` by simp[LEFT_ADD_DISTRIB] >>
  `a + 1 <= a'` by simp[] >>
  `(w + 1) * (a + 1) <= (w + 1) * a'` by simp[LE_MULT_LCANCEL] >>
  simp[]
QED

Theorem copy_prop_measure_monotone:
  !fn lbl st.
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    copy_prop_measure_inv fn st /\
    df_process_block Forward NONE copy_prop_join copy_prop_transfer
      copy_prop_edge_transfer (phi_used_vars fn)
      (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks lbl st <> st ==>
    copy_prop_measure fn st <
    copy_prop_measure fn
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt strip_tac >>
  rewrite_tac[copy_prop_process_eq] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  qabbrev_tac `joined = copy_prop_joined fn st lbl` >>
  qabbrev_tac `instrs = case lookup_block lbl fn.fn_blocks of
                           NONE => [] | SOME bb => bb.bb_instructions` >>
  qabbrev_tac `new_bnd = copy_prop_join (df_boundary NONE st lbl) fv` >>
  `(!k. k IN FDOM inst_map ==> FST k = lbl) /\
   (lbl, 0n) IN FDOM inst_map /\
   FLOOKUP inst_map (lbl, 0n) = SOME joined` by (
    qpat_x_assum `df_fold_block _ _ _ _ _ = _` (fn th =>
      strip_assume_tac (MATCH_MP df_fold_block_inst_map_props th)) >>
    fs[Abbr `joined`]) >>
  `df_process_block Forward NONE copy_prop_join copy_prop_transfer
     copy_prop_edge_transfer (phi_used_vars fn)
     (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
     (cfg_analyze fn) fn.fn_blocks lbl st =
   st with <|ds_inst := FUNION inst_map st.ds_inst;
             ds_boundary := st.ds_boundary |+ (lbl, new_bnd)|>` by (
    rewrite_tac[copy_prop_process_eq] >>
    simp_tac std_ss [LET_THM, Abbr `instrs`, Abbr `joined`, Abbr `new_bnd`] >>
    qpat_x_assum `df_fold_block _ _ _ _ _ = _` (fn th =>
      simp[th])) >>
  (* === Case split: did boundary value at lbl change? === *)
  Cases_on `df_boundary NONE st lbl = new_bnd`
  >- ( (* Case B: boundary unchanged *)
    Cases_on `lbl IN FDOM st.ds_boundary`
    >- ( (* B1: lbl IN FDOM, boundary unchanged *)
      `st.ds_boundary ' lbl = new_bnd` by (
        qpat_x_assum `df_boundary NONE st lbl = new_bnd` mp_tac >>
        simp[df_boundary_def, FLOOKUP_DEF]) >>
      `st.ds_boundary |+ (lbl, new_bnd) = st.ds_boundary` by
        (irule FUPDATE_ELIM >> metis_tac[]) >>
      simp_tac std_ss [copy_prop_measure_def, LET_THM] >>
      `copy_boundary_measure fn
         <|ds_inst := FUNION inst_map st.ds_inst;
           ds_boundary := st.ds_boundary |+ (lbl, new_bnd)|> =
       copy_boundary_measure fn st` by
        simp[copy_boundary_measure_def, LET_THM, df_boundary_def,
             FLOOKUP_UPDATE] >>
      `CARD (FDOM (st.ds_boundary |+ (lbl, new_bnd)) INTER
             set (cfg_analyze fn).cfg_dfs_pre) =
       CARD (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre)` by
        asm_rewrite_tac[] >>
      `CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) <=
       CARD (FDOM (FUNION inst_map st.ds_inst) INTER
             df_valid_inst_keys fn.fn_blocks)` by
        metis_tac[inst_card_mono] >>
      simp[] >>
      Cases_on `FLOOKUP st.ds_inst (lbl, 0n) = SOME joined`
      >- ( (* B1-YES: FUNION absorbed -> contradiction *)
        mp_tac (Q.SPECL [`fn`, `lbl`, `st`, `joined`,
          `instrs`, `fv`, `inst_map`] funion_fold_coherent) >>
        impl_tac >- (
          qpat_x_assum `Abbrev (instrs = _)` (mp_tac o
            REWRITE_RULE [markerTheory.Abbrev_def]) >>
          strip_tac >> simp[]) >>
        strip_tac >>
        qpat_x_assum `FUNION inst_map st.ds_inst = st.ds_inst` (fn funion_th =>
          qpat_x_assum `st.ds_boundary |+ _ = st.ds_boundary` (fn fupd_th =>
            qpat_x_assum `df_process_block _ _ _ _ _ _ _ _ _ _ st = _`
              (fn dpb_th => assume_tac
                (REWRITE_RULE [funion_th, fupd_th] dpb_th)))) >>
        gvs[df_state_component_equality]
      )
      >- ( (* B1-NO: fresh_count strictly increases *)
        mp_tac fresh_count_increase >>
        disch_then (qspecl_then [`fn`, `st`, `inst_map`, `lbl`] mp_tac) >>
        impl_tac >- (
          conj_tac >- simp[MEM_APPEND] >>
          conj_tac >- (
            qpat_x_assum `Abbrev (joined = _)` (mp_tac o
              REWRITE_RULE [markerTheory.Abbrev_def]) >>
            strip_tac >> ASM_REWRITE_TAC []) >>
          conj_tac >- first_assum ACCEPT_TAC >>
          simp[FLOOKUP_FUNION]) >>
        disch_then (assume_tac o ONCE_REWRITE_RULE [ds_inst_update_literal]) >>
        gvs[] >> DECIDE_TAC
      ) (* end B1-NO *)
    ) (* end B1 *)
    >- ( (* B2: lbl NOT in boundary, boundary value unchanged *)
      `new_bnd = NONE` by (
        fs[df_boundary_def] >>
        Cases_on `FLOOKUP st.ds_boundary lbl` >> fs[FLOOKUP_DEF]) >>
      simp_tac std_ss [copy_prop_measure_def, LET_THM] >>
      `copy_boundary_measure fn
         <|ds_inst := FUNION inst_map st.ds_inst;
           ds_boundary := st.ds_boundary |+ (lbl, new_bnd)|> =
       copy_boundary_measure fn st` by (
        rw[copy_boundary_measure_def] >>
        AP_TERM_TAC >> ONCE_REWRITE_TAC [GSYM MAP_APPEND] >>
        simp[MAP_EQ_f, df_boundary_def, FLOOKUP_UPDATE] >>
        rw[] >> fs[FLOOKUP_DEF]) >>
      `CARD (FDOM (st.ds_boundary |+ (lbl, new_bnd)) INTER
             set (cfg_analyze fn).cfg_dfs_pre) =
       CARD (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre) + 1` by (
        `FDOM (st.ds_boundary |+ (lbl, new_bnd)) INTER
           set (cfg_analyze fn).cfg_dfs_pre =
         lbl INSERT (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre)` by (
          simp[EXTENSION, FDOM_FUPDATE, IN_INTER] >> metis_tac[]) >>
        simp[] >>
        `lbl NOTIN (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre)` by
          simp[IN_INTER] >>
        simp[CARD_INSERT, FINITE_INTER]) >>
      `CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) <=
       CARD (FDOM (FUNION inst_map st.ds_inst) INTER
             df_valid_inst_keys fn.fn_blocks)` by
        metis_tac[inst_card_mono] >>
      `copy_prop_fresh_count fn st <=
       copy_prop_fresh_count fn
         <|ds_inst := FUNION inst_map st.ds_inst;
           ds_boundary := st.ds_boundary |+ (lbl, new_bnd)|>` by (
        mp_tac fresh_count_mono >>
        disch_then (qspecl_then [`fn`, `st`, `inst_map`, `lbl`,
          `st.ds_boundary |+ (lbl, new_bnd)`] mp_tac) >>
        impl_tac >- (
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- (
            qpat_x_assum `Abbrev (joined = _)` (mp_tac o
              REWRITE_RULE [markerTheory.Abbrev_def]) >>
            strip_tac >> ASM_REWRITE_TAC []) >>
          irule copy_prop_joined_boundary_eq >>
          simp[df_boundary_def, FLOOKUP_UPDATE] >>
          rw[] >> gvs[df_boundary_def, FLOOKUP_DEF]) >>
        simp[]) >>
      gvs[] >> DECIDE_TAC
    ) (* end B2 *)
  ) (* end Case B *)
  >- ( (* Case A: boundary strictly changed *)
    `case fv of NONE => T
     | SOME fmap => CARD (FDOM fmap) <=
                    CARD (set (fn_all_assignments fn))` by (
      mp_tac fold_output_card_bound >>
      disch_then (qspecl_then [`fn`, `st`, `lbl`, `instrs`, `joined`,
        `fv`, `inst_map`] mp_tac) >>
      impl_tac >- (
        qpat_x_assum `copy_prop_measure_inv _ _` mp_tac >>
        simp_tac std_ss [copy_prop_measure_inv_def] >> strip_tac >>
        qpat_x_assum `Abbrev (joined = _)` (mp_tac o
          REWRITE_RULE [markerTheory.Abbrev_def]) >>
        qpat_x_assum `Abbrev (instrs = _)` (mp_tac o
          REWRITE_RULE [markerTheory.Abbrev_def]) >>
        rpt strip_tac >> ASM_REWRITE_TAC []) >>
      simp[]) >>
    `case df_boundary NONE st lbl of NONE => T
     | SOME fmap => CARD (FDOM fmap) <=
                    CARD (set (fn_all_assignments fn))` by (
      irule boundary_card_bound >>
      fs[copy_prop_measure_inv_def]) >>
    simp_tac std_ss [copy_prop_measure_def, LET_THM] >>
    `copy_boundary_measure fn st <
     copy_boundary_measure fn
       (st with ds_boundary := st.ds_boundary |+ (lbl, new_bnd))` by (
      irule boundary_measure_strict >> simp[MEM_APPEND] >>
      qpat_x_assum `Abbrev (new_bnd = _)` (SUBST_ALL_TAC o
        REWRITE_RULE [markerTheory.Abbrev_def]) >>
      irule copy_val_measure_join_strict >> simp[]) >>
    `copy_boundary_measure fn
       <|ds_inst := FUNION inst_map st.ds_inst;
         ds_boundary := st.ds_boundary |+ (lbl, new_bnd)|> =
     copy_boundary_measure fn
       (st with ds_boundary := st.ds_boundary |+ (lbl, new_bnd))` by
      simp[copy_boundary_measure_def, LET_THM, df_boundary_def] >>
    `CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) <=
     CARD (FDOM (FUNION inst_map st.ds_inst) INTER
           df_valid_inst_keys fn.fn_blocks)` by
      metis_tac[inst_card_mono] >>
    `CARD (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre) <=
     CARD (FDOM (st.ds_boundary |+ (lbl, new_bnd)) INTER
           set (cfg_analyze fn).cfg_dfs_pre)` by (
      irule CARD_SUBSET >> simp[FINITE_INTER, FDOM_FUPDATE] >>
      simp[SUBSET_DEF, IN_INTER] >> metis_tac[IN_INSERT]) >>
    assume_tac (Q.SPECL [`fn`, `st`] fresh_count_bounded) >>
    gvs[] >>
    mp_tac (ISPECL [
      ``LENGTH (fn_labels fn) + LENGTH (cfg_analyze fn).cfg_dfs_pre``,
      ``copy_boundary_measure fn st``,
      ``copy_boundary_measure fn
          (st with ds_boundary := st.ds_boundary |+ (lbl, new_bnd))``,
      ``copy_prop_fresh_count fn st``] weighted_lt_cancel) >>
    simp[] >> DECIDE_TAC
  ) (* end Case A *)
QED

(* measure_inv is preserved by processing *)
Theorem copy_prop_measure_inv_preserved:
  !fn lbl st.
    copy_prop_measure_inv fn st ==>
    copy_prop_measure_inv fn
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt strip_tac >>
  simp[copy_prop_measure_inv_def] >>
  conj_tac >- fs[copy_prop_measure_inv_def] >>
  conj_tac >- (
    irule copy_prop_inv_preserved >>
    fs[copy_prop_measure_inv_def]) >>
  simp[copy_prop_process_eq, LET_THM] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  fs[copy_prop_measure_inv_def, LET_THM] >>
  qabbrev_tac `instrs = case lookup_block lbl fn.fn_blocks of
                           NONE => [] | SOME bb => bb.bb_instructions` >>
  qabbrev_tac `joined = copy_prop_joined fn st lbl` >>
  rpt conj_tac
  (* C3: fold coherence — all inst_map keys have FST=lbl *)
  >- (rpt strip_tac >>
      qunabbrev_tac `instrs` >>
      qpat_x_assum `df_fold_block _ _ lbl _ joined = _`
        (fn th => assume_tac th >>
                  strip_assume_tac (MATCH_MP df_fold_block_inst_map_props th)) >>
      Cases_on `lbl' = lbl`
      >- ((* lbl'=lbl: v0=joined, fold=inst_map *)
        `v0 = joined` by
          (fs[FLOOKUP_FUNION]) >>
        fs[] >>
        simp[FLOOKUP_FUNION])
      >- ((* lbl'≠lbl *)
        `(lbl', 0n) NOTIN FDOM inst_map` by
          (strip_tac >> `FST (lbl', 0n) = lbl` by metis_tac[] >> fs[]) >>
        `FLOOKUP st.ds_inst (lbl', 0n) = SOME v0` by
          fs[FLOOKUP_FUNION, FLOOKUP_DEF] >>
        `FLOOKUP st.ds_inst k = SOME v` by metis_tac[] >>
        `k NOTIN FDOM inst_map` suffices_by
          (strip_tac >> simp[FLOOKUP_FUNION, FLOOKUP_DEF]) >>
        strip_tac >>
        `FST k = lbl` by metis_tac[] >>
        Cases_on `df_fold_block Forward (copy_prop_transfer (phi_used_vars fn))
                    lbl' (case lookup_block lbl' fn.fn_blocks of
                            NONE => [] | SOME bb => bb.bb_instructions) v0` >>
        qpat_x_assum `df_fold_block _ _ lbl' _ _ = (q, r)` (fn th =>
          strip_assume_tac (MATCH_MP df_fold_block_inst_map_props th)) >>
        fs[] >>
        `FST k = lbl'` by metis_tac[flookup_thm] >>
        fs[]))
  (* C4: key closure — (lbl',j) ∈ FDOM(inst_map ⊌ ds_inst) ⇒ (lbl',0) ∈ ... *)
  >- (rpt strip_tac >>
      qpat_x_assum `df_fold_block _ _ lbl _ _ = _` (fn th =>
        strip_assume_tac (MATCH_MP df_fold_block_inst_map_props th)) >>
      fs[FDOM_FUNION] >>
      res_tac >> fs[])
  (* C5: processed implies boundary exists *)
  >- (rpt strip_tac >>
      qpat_x_assum `df_fold_block _ _ lbl _ _ = _` (fn th =>
        strip_assume_tac (MATCH_MP df_fold_block_inst_map_props th)) >>
      fs[FDOM_FUNION, FDOM_FUPDATE] >>
      res_tac >> fs[])
QED

