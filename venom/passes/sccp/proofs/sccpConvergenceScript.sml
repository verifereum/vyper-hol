(*
 * SCCP — Convergence Proofs
 *
 * Measure definitions, invariant preservation, and monotonicity
 * for the sccp_lattice. Proves that sccp analysis terminates.
 *
 * EXPORTED: sccp_join_absorption, cfg_edge_symmetry_sccp,
 *   sccp_measure_bounded, sccp_measure_monotone,
 *   sccp_measure_inv_preserved, sccp_measure_inv_initial
 *)

Theory sccpConvergence
Ancestors
  sccpDefs dfAnalyzeProps cfgAnalysisProps
  venomInst venomWf venomState finite_map list pred_set arithmetic
  dfAnalyzeDefs latticeDefs worklistDefs option
Libs
  BasicProvers

(* ===== Per-value measure ===== *)

(* Measure for a single const_val.
   CL_Top = 0 (no information yet).
   CL_Const/CL_Label = 1 (partial information).
   CL_Bottom = 2 (conflicting/unknown).
   This INCREASES monotonically under const_meet. *)
Definition const_val_measure_def:
  const_val_measure CL_Top = (0:num) /\
  const_val_measure (CL_Const _) = 1 /\
  const_val_measure (CL_Label _) = 1 /\
  const_val_measure CL_Bottom = 2
End

(* const_meet absorption — key lattice property *)
Theorem const_meet_absorption[local]:
  !a b. const_meet (const_meet a b) b = const_meet a b
Proof
  Cases >> Cases >> simp[const_meet_def] >> rw[] >> simp[const_meet_def]
QED

(* const_meet is idempotent *)
Theorem const_meet_idem[local]:
  !x. const_meet x x = x
Proof
  Cases >> simp[const_meet_def]
QED

(* const_val_measure is monotone under const_meet *)
Theorem const_val_measure_mono[local]:
  !a b. const_val_measure a <= const_val_measure (const_meet a b)
Proof
  Cases >> Cases >> simp[const_meet_def, const_val_measure_def] >>
  rw[] >> simp[const_val_measure_def]
QED

(* const_val_measure is strictly increasing when const_meet changes *)
Theorem const_val_measure_strict[local]:
  !a b. const_meet a b <> a ==>
        const_val_measure a < const_val_measure (const_meet a b)
Proof
  Cases >> Cases >> simp[const_meet_def, const_val_measure_def] >>
  rw[] >> simp[const_val_measure_def]
QED

(* ===== sccp_join properties ===== *)

(* sccp_join absorption: join(join(a,b), b) = join(a,b) *)
Theorem sccp_join_absorption:
  !a b. sccp_join (sccp_join a b) b = sccp_join a b
Proof
  rpt gen_tac >>
  simp[sccp_join_def, sccp_lattice_component_equality] >>
  `FINITE (FDOM a.sl_vals UNION FDOM b.sl_vals)` by simp[] >>
  conj_tac
  >- (
    (* sl_vals: FUN_FMAP equality via FLOOKUP extensionality *)
    simp[FLOOKUP_EXT, FUN_EQ_THM, FLOOKUP_FUN_FMAP] >>
    rpt strip_tac >>
    rpt IF_CASES_TAC >> gvs[] >>
    simp[const_lookup_def, FLOOKUP_FUN_FMAP, const_meet_absorption]
  ) >>
  (* sl_targets: set union idempotent *)
  simp[EXTENSION] >> metis_tac[]
QED

(* Use cfg_edge_symmetry_uncond from cfgAnalysisPropsTheory *)

(* ===== Invariant ===== *)

(* Invariant: sl_vals domains and sl_targets are bounded *)
Definition sccp_state_inv_def:
  sccp_state_inv fn (st : sccp_lattice df_state) <=>
    (!lbl lat. FLOOKUP st.ds_boundary lbl = SOME lat ==>
       FDOM lat.sl_vals SUBSET set (fn_all_assignments fn) /\
       lat.sl_targets SUBSET set (fn_labels fn)) /\
    (!k lat. FLOOKUP st.ds_inst k = SOME lat ==>
       FDOM lat.sl_vals SUBSET set (fn_all_assignments fn) /\
       lat.sl_targets SUBSET set (fn_labels fn))
End

(* Extended invariant for convergence *)
Definition sccp_measure_inv_def:
  sccp_measure_inv fn (st : sccp_lattice df_state) <=>
    wf_function fn /\
    sccp_state_inv fn st /\
    (let transfer = sccp_transfer_inst fn in
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

(* ===== Measure definitions ===== *)

(* Per-boundary-value measure: sum of const_val_measures over all
   assignment variables + domain size + target count.
   Domain size is needed because FDOM can grow with CL_Top entries
   which don't change const_lookup but do change the fmap.
   Uses const_lookup which returns CL_Top for missing keys. *)
Definition sccp_val_measure_def:
  sccp_val_measure fn (lat : sccp_lattice) =
    SUM (MAP (\v. const_val_measure (const_lookup lat.sl_vals v))
             (fn_all_assignments fn)) +
    CARD (FDOM lat.sl_vals INTER set (fn_all_assignments fn)) +
    CARD (lat.sl_targets INTER set (fn_labels fn))
End

(* Boundary measure: sum over all worklist-processable labels *)
Definition sccp_boundary_measure_def:
  sccp_boundary_measure fn (st : sccp_lattice df_state) =
    SUM (MAP (\lbl. sccp_val_measure fn (df_boundary sccp_bottom st lbl))
             (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre))
End

(* Joined value for SCCP at a label *)
Definition sccp_joined_def:
  sccp_joined fn st lbl =
    let cfg = cfg_analyze fn in
    let edge_vals = MAP (\nbr. sccp_edge_transfer fn nbr lbl
                                 (df_boundary sccp_bottom st nbr))
                        (cfg_preds_of cfg lbl) in
    let base = (case edge_vals of
                  [] => sccp_bottom
                | _ => FOLDL sccp_join sccp_bottom edge_vals) in
    case fn_entry_label fn of
      NONE => base
    | SOME ev_lbl =>
        if lbl = ev_lbl then sccp_join sccp_bottom base else base
End

(* Fresh count: labels whose stored v0 matches current joined value *)
Definition sccp_fresh_count_def:
  sccp_fresh_count fn (st : sccp_lattice df_state) =
    CARD {lbl | MEM lbl (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre) /\
                (lbl, 0n) IN FDOM st.ds_inst /\
                FLOOKUP st.ds_inst (lbl, 0n) =
                SOME (sccp_joined fn st lbl)}
End

(* Full measure:
   W * boundary_sum + inst_slots + fresh_count + dfs_visited *)
Definition sccp_measure_def:
  sccp_measure fn (st : sccp_lattice df_state) =
    let dfs_pre = (cfg_analyze fn).cfg_dfs_pre in
    let all_count = LENGTH (fn_labels fn) + LENGTH dfs_pre in
    (all_count + 1) * sccp_boundary_measure fn st +
    CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) +
    sccp_fresh_count fn st +
    CARD (FDOM st.ds_boundary INTER set dfs_pre)
End

(* Upper bound *)
Definition sccp_measure_bound_def:
  sccp_measure_bound fn =
    let nlabels = LENGTH (fn_labels fn) in
    let total_slots = df_total_inst_slots fn.fn_blocks in
    let ndfs = LENGTH (cfg_analyze fn).cfg_dfs_pre in
    let all_count = nlabels + ndfs in
    let max_vars = LENGTH (fn_all_assignments fn) in
    let max_labels = LENGTH (fn_labels fn) in
    let per_val_bound = 2 * max_vars + max_vars + max_labels in
    (all_count + 1) * (per_val_bound * (nlabels + ndfs)) +
    total_slots +
    (nlabels + ndfs) +
    ndfs
End

(* ===== Arithmetic helpers ===== *)

Triviality sum_map_le[local]:
  !f g l. EVERY (\x. f x <= g x) l ==> SUM (MAP f l) <= SUM (MAP g l)
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  irule LESS_EQ_LESS_EQ_MONO >> simp[]
QED

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

Triviality sum_map_le_bound[local]:
  !f (n:num) l. EVERY (\x. f x <= n) l ==> SUM (MAP f l) <= n * LENGTH l
Proof
  Induct_on `l` >> rw[] >> res_tac >>
  fs[MULT_SUC]
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

(* ===== sccp_val_measure is bounded ===== *)

Theorem sccp_val_measure_bounded[local]:
  !fn lat.
    FDOM lat.sl_vals SUBSET set (fn_all_assignments fn) /\
    lat.sl_targets SUBSET set (fn_labels fn) ==>
    sccp_val_measure fn lat <=
    2 * LENGTH (fn_all_assignments fn) +
    LENGTH (fn_all_assignments fn) + LENGTH (fn_labels fn)
Proof
  rpt strip_tac >>
  simp[sccp_val_measure_def] >>
  `SUM (MAP (\v. const_val_measure (const_lookup lat.sl_vals v))
           (fn_all_assignments fn)) <=
   2 * LENGTH (fn_all_assignments fn)` by (
    irule sum_map_le_bound >>
    simp[EVERY_MEM] >> rpt strip_tac >>
    Cases_on `const_lookup lat.sl_vals x` >>
    simp[const_val_measure_def]) >>
  `CARD (FDOM lat.sl_vals INTER set (fn_all_assignments fn)) <=
   LENGTH (fn_all_assignments fn)` by (
    irule LESS_EQ_TRANS >>
    qexists_tac `CARD (set (fn_all_assignments fn))` >>
    simp[CARD_LIST_TO_SET] >>
    irule CARD_SUBSET >> simp[FINITE_LIST_TO_SET]) >>
  `CARD (lat.sl_targets INTER set (fn_labels fn)) <=
   LENGTH (fn_labels fn)` by (
    irule LESS_EQ_TRANS >>
    qexists_tac `CARD (set (fn_labels fn))` >>
    simp[CARD_LIST_TO_SET] >>
    irule CARD_SUBSET >> simp[FINITE_LIST_TO_SET]) >>
  simp[]
QED

(* Bottom satisfies the invariant *)
Theorem sccp_bottom_inv[local]:
  !fn. FDOM sccp_bottom.sl_vals SUBSET set (fn_all_assignments fn) /\
       sccp_bottom.sl_targets SUBSET set (fn_labels fn)
Proof
  simp[sccp_bottom_def]
QED

(* df_boundary for sccp *)
Triviality sccp_df_boundary_inv[local]:
  !fn st lbl.
    sccp_state_inv fn st ==>
    FDOM (df_boundary sccp_bottom st lbl).sl_vals
      SUBSET set (fn_all_assignments fn) /\
    (df_boundary sccp_bottom st lbl).sl_targets
      SUBSET set (fn_labels fn)
Proof
  rpt strip_tac >> simp[df_boundary_def] >>
  CASE_TAC >> simp[sccp_bottom_def] >>
  fs[sccp_state_inv_def] >> res_tac
QED

(* ===== Initial state ===== *)

Theorem sccp_init_state_inv[local]:
  !fn.
    case OPTION_MAP (\lbl. (lbl, sccp_bottom)) (fn_entry_label fn) of
      NONE => sccp_state_inv fn
        (init_df_state sccp_bottom (MAP (\bb. bb.bb_label) fn.fn_blocks))
    | SOME (lbl,v) => sccp_state_inv fn
        (init_df_state sccp_bottom (MAP (\bb. bb.bb_label) fn.fn_blocks) with
         ds_boundary :=
           (init_df_state sccp_bottom (MAP (\bb. bb.bb_label) fn.fn_blocks)).ds_boundary
             |+ (lbl,v))
Proof
  rpt strip_tac >>
  simp[sccp_state_inv_def, LET_THM, init_df_state_def] >>
  Cases_on `fn_entry_label fn` >> simp[] >>
  rpt gen_tac >> strip_tac >> (
    TRY (qpat_x_assum `FLOOKUP (_ |+ _) _ = _`
           (mp_tac o REWRITE_RULE [FLOOKUP_UPDATE]) >>
         IF_CASES_TAC >> simp[] >> strip_tac >> gvs[sccp_bottom_def]) >>
    (* All values in the FOLDL are sccp_bottom *)
    RULE_ASSUM_TAC (REWRITE_RULE [GSYM sccp_bottom_def]) >>
    imp_res_tac foldl_fempty_val >>
    gvs[sccp_bottom_def])
QED

(* measure_inv for initial state *)
Theorem sccp_measure_inv_initial:
  !fn.
    wf_function fn ==>
    case OPTION_MAP (\lbl. (lbl, sccp_bottom)) (fn_entry_label fn) of
      NONE => sccp_measure_inv fn
        (init_df_state sccp_bottom (MAP (\bb. bb.bb_label) fn.fn_blocks))
    | SOME (lbl,v) => sccp_measure_inv fn
        (init_df_state sccp_bottom (MAP (\bb. bb.bb_label) fn.fn_blocks) with
         ds_boundary :=
           (init_df_state sccp_bottom (MAP (\bb. bb.bb_label) fn.fn_blocks)).ds_boundary
             |+ (lbl,v))
Proof
  rpt strip_tac >>
  simp[sccp_measure_inv_def, init_df_state_def, LET_THM] >>
  mp_tac (SPEC_ALL sccp_init_state_inv) >>
  Cases_on `fn_entry_label fn` >> simp[init_df_state_def]
QED

(* ===== Measure bounded ===== *)

Triviality sccp_val_measure_boundary_le[local]:
  !fn st lbl.
    sccp_state_inv fn st ==>
    sccp_val_measure fn (df_boundary sccp_bottom st lbl) <=
    3 * LENGTH (fn_all_assignments fn) + LENGTH (fn_labels fn)
Proof
  rpt strip_tac >> irule LESS_EQ_TRANS >>
  irule_at Any sccp_val_measure_bounded >>
  simp[] >> metis_tac[sccp_df_boundary_inv]
QED

Theorem sccp_measure_bounded:
  !fn st.
    sccp_state_inv fn st ==>
    sccp_measure fn st <= sccp_measure_bound fn
Proof
  rpt strip_tac >>
  (* Bound 1: boundary measure *)
  `sccp_boundary_measure fn st <=
   (3 * LENGTH (fn_all_assignments fn) + LENGTH (fn_labels fn)) *
   LENGTH (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre)` by (
    simp_tac std_ss [sccp_boundary_measure_def, LET_THM] >>
    irule LESS_EQ_TRANS >>
    irule_at Any sum_map_le_bound >>
    qexists_tac `3 * LENGTH (fn_all_assignments fn) +
                 LENGTH (fn_labels fn)` >>
    simp[EVERY_MEM, MEM_APPEND] >>
    rpt strip_tac >> irule sccp_val_measure_boundary_le >> metis_tac[]) >>
  fs[LENGTH_APPEND] >>
  (* Bound 2: inst CARD *)
  `CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) <=
   (df_total_inst_slots fn.fn_blocks : num)` by (
    match_mp_tac LESS_EQ_TRANS >>
    qexists_tac `CARD (df_valid_inst_keys fn.fn_blocks)` >>
    simp[df_valid_inst_keys_card] >>
    ONCE_REWRITE_TAC[INTER_COMM] >>
    irule CARD_INTER_LESS_EQ >>
    simp[df_valid_inst_keys_finite]) >>
  (* Bound 3: fresh count *)
  `sccp_fresh_count fn st <=
   LENGTH (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre)` by (
    simp_tac std_ss [sccp_fresh_count_def, LET_THM] >>
    match_mp_tac LESS_EQ_TRANS >>
    qexists_tac `CARD (set (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre))` >>
    conj_tac >- (
      irule CARD_SUBSET >> simp[FINITE_LIST_TO_SET, SUBSET_DEF]) >>
    simp[CARD_LIST_TO_SET]) >>
  fs[LENGTH_APPEND] >>
  (* Bound 4: dfs_visited *)
  `CARD (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre) <=
   LENGTH (cfg_analyze fn).cfg_dfs_pre` by (
    match_mp_tac LESS_EQ_TRANS >>
    qexists_tac `CARD (set (cfg_analyze fn).cfg_dfs_pre)` >>
    simp[CARD_LIST_TO_SET] >>
    ONCE_REWRITE_TAC[INTER_COMM] >>
    irule CARD_INTER_LESS_EQ >>
    simp[FINITE_LIST_TO_SET]) >>
  (* Combine *)
  simp_tac std_ss [sccp_measure_def, sccp_measure_bound_def, LET_THM] >>
  irule LESS_EQ_LESS_EQ_MONO >>
  REVERSE conj_tac >- first_assum ACCEPT_TAC >>
  irule LESS_EQ_LESS_EQ_MONO >>
  REVERSE conj_tac >- first_assum ACCEPT_TAC >>
  irule LESS_EQ_LESS_EQ_MONO >>
  REVERSE conj_tac >- first_assum ACCEPT_TAC >>
  irule LESS_MONO_MULT2 >> simp[]
QED

(* ===== sccp_join preserves invariant ===== *)

Triviality sccp_join_fdom_subset[local]:
  !a b bound.
    FDOM a.sl_vals SUBSET bound /\
    FDOM b.sl_vals SUBSET bound ==>
    FDOM (sccp_join a b).sl_vals SUBSET bound
Proof
  rpt strip_tac >>
  simp[sccp_join_def, FUN_FMAP_DEF, FDOM_FINITE] >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Triviality sccp_join_targets_subset[local]:
  !a b bound.
    a.sl_targets SUBSET bound /\
    b.sl_targets SUBSET bound ==>
    (sccp_join a b).sl_targets SUBSET bound
Proof
  simp[sccp_join_def, SUBSET_DEF] >> metis_tac[]
QED

Triviality foldl_sccp_join_inv[local]:
  !l init bound_v bound_t.
    FDOM init.sl_vals SUBSET bound_v /\
    init.sl_targets SUBSET bound_t /\
    EVERY (\v. FDOM v.sl_vals SUBSET bound_v /\ v.sl_targets SUBSET bound_t) l ==>
    FDOM (FOLDL sccp_join init l).sl_vals SUBSET bound_v /\
    (FOLDL sccp_join init l).sl_targets SUBSET bound_t
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[] >>
  metis_tac[sccp_join_fdom_subset, sccp_join_targets_subset]
QED

(* ===== sccp_transfer_inst preserves invariant ===== *)

(* Helper: FOLDL (\l v. l |+ (v, CL_Bottom)) preserves FDOM ⊆ when outputs ⊆ *)
Triviality foldl_fupdate_bottom_fdom[local]:
  !outs (fm : string |-> const_val) bound.
    FDOM fm SUBSET bound /\ set outs SUBSET bound ==>
    FDOM (FOLDL (\l v. l |+ (v, CL_Bottom)) fm outs) SUBSET bound
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[FDOM_FUPDATE] >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

(* Helper: sccp_eval_phi_for_edge output is from inst_outputs *)
Triviality sccp_eval_phi_output_bound[local]:
  !src_lbl src_vals inst out v.
    sccp_eval_phi_for_edge src_lbl src_vals inst = SOME (out, v) ==>
    MEM out inst.inst_outputs
Proof
  rpt strip_tac >>
  fs[sccp_eval_phi_for_edge_def] >>
  every_case_tac >> fs[]
QED

(* Helper: the FOLDL step in sccp_eval_phis_for_edge preserves FDOM/targets *)
Triviality sccp_eval_phis_step_inv[local]:
  !src_lbl src_vals inst lat bound.
    FDOM lat.sl_vals SUBSET bound /\
    set inst.inst_outputs SUBSET bound ==>
    FDOM ((if inst.inst_opcode = PHI then
             case sccp_eval_phi_for_edge src_lbl src_vals inst of
               NONE => lat
             | SOME (out,v) => lat with sl_vals := lat.sl_vals |+ (out,v)
           else lat)).sl_vals SUBSET bound /\
    (if inst.inst_opcode = PHI then
       case sccp_eval_phi_for_edge src_lbl src_vals inst of
         NONE => lat
       | SOME (out,v) => lat with sl_vals := lat.sl_vals |+ (out,v)
     else lat).sl_targets = lat.sl_targets
Proof
  rpt strip_tac >> IF_CASES_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  Cases_on `x` >> simp[FDOM_FUPDATE] >>
  imp_res_tac sccp_eval_phi_output_bound >>
  fs[SUBSET_DEF]
QED

(* Helper: sccp_eval_phis_for_edge preserves FDOM bounds and sl_targets *)
Triviality sccp_eval_phis_inv[local]:
  !instrs src_lbl src_vals lat bound.
    FDOM lat.sl_vals SUBSET bound /\
    EVERY (\inst. set inst.inst_outputs SUBSET bound) instrs ==>
    FDOM (sccp_eval_phis_for_edge src_lbl src_vals instrs lat).sl_vals
      SUBSET bound /\
    (sccp_eval_phis_for_edge src_lbl src_vals instrs lat).sl_targets =
      lat.sl_targets
Proof
  simp[sccp_eval_phis_for_edge_def] >>
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `FDOM ((if h.inst_opcode = PHI then
            case sccp_eval_phi_for_edge src_lbl src_vals h of
              NONE => lat
            | SOME (out,v) => lat with sl_vals := lat.sl_vals |+ (out,v)
          else lat)).sl_vals SUBSET bound /\
   (if h.inst_opcode = PHI then
      case sccp_eval_phi_for_edge src_lbl src_vals h of
        NONE => lat
      | SOME (out,v) => lat with sl_vals := lat.sl_vals |+ (out,v)
    else lat).sl_targets = lat.sl_targets` by
    (irule sccp_eval_phis_step_inv >> simp[]) >>
  first_x_assum (qspecl_then [`src_lbl`, `src_vals`,
    `if h.inst_opcode = PHI then
       case sccp_eval_phi_for_edge src_lbl src_vals h of
         NONE => lat
       | SOME (out,v) => lat with sl_vals := lat.sl_vals |+ (out,v)
     else lat`, `bound`] mp_tac) >>
  simp[]
QED

(* Helper: FIND SOME implies MEM *)
Triviality find_some_mem[local]:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  Induct_on `l` >> simp[FIND_thm] >>
  rpt strip_tac >> every_case_tac >> fs[] >> metis_tac[]
QED

(* Helper: instructions from lookup_block have outputs in fn_all_assignments *)
Triviality lookup_block_outputs_bound[local]:
  !lbl fn bb.
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    EVERY (\inst. set inst.inst_outputs SUBSET set (fn_all_assignments fn))
      bb.bb_instructions
Proof
  rpt strip_tac >>
  `MEM bb fn.fn_blocks` by
    (fs[lookup_block_def] >> imp_res_tac find_some_mem >> simp[]) >>
  simp[EVERY_MEM, SUBSET_DEF] >> rpt strip_tac >>
  simp[fn_all_assignments_def, MEM_nub, MEM_FLAT, MEM_MAP, PULL_EXISTS,
       inst_defs_def] >>
  metis_tac[]
QED

(* sccp_edge_transfer preserves invariant *)
Triviality sccp_edge_transfer_inv[local]:
  !fn src dst lat.
    FDOM lat.sl_vals SUBSET set (fn_all_assignments fn) /\
    lat.sl_targets SUBSET set (fn_labels fn) ==>
    FDOM (sccp_edge_transfer fn src dst lat).sl_vals
      SUBSET set (fn_all_assignments fn) /\
    (sccp_edge_transfer fn src dst lat).sl_targets
      SUBSET set (fn_labels fn)
Proof
  rpt gen_tac >> strip_tac >>
  simp[sccp_edge_transfer_def] >>
  IF_CASES_TAC >> simp[sccp_bottom_def] >>
  simp[LET_THM] >>
  Cases_on `lookup_block dst fn.fn_blocks` >> simp[]
  >- (simp[sccp_eval_phis_for_edge_def])
  >- (imp_res_tac lookup_block_outputs_bound >>
      `FDOM (lat with sl_targets := EMPTY).sl_vals SUBSET
       set (fn_all_assignments fn)` by simp[] >>
      drule_all sccp_eval_phis_inv >> simp[EMPTY_SUBSET])
QED

(* sccp_transfer_inst preserves FDOM ⊆ and targets ⊆ *)
(* Helper: sccp_transfer_inst only adds outputs to sl_vals *)
Triviality sccp_transfer_inst_fdom[local]:
  !fn inst lat.
    set inst.inst_outputs SUBSET set (fn_all_assignments fn) /\
    FDOM lat.sl_vals SUBSET set (fn_all_assignments fn) ==>
    FDOM (sccp_transfer_inst fn inst lat).sl_vals
      SUBSET set (fn_all_assignments fn)
Proof
  rpt gen_tac >> strip_tac >>
  simp[sccp_transfer_inst_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  TRY (irule foldl_fupdate_bottom_fdom >> simp[]) >>
  TRY (fs[FDOM_FUPDATE, SUBSET_DEF] >> metis_tac[])
QED

(* Helper: labels extracted by FOLDR from operands are subset of
   get_successors *)
Triviality foldr_labels_subset_get_successors[local]:
  !ops. FOLDR (\op acc. case op of Label dst => dst INSERT acc | _ => acc)
              EMPTY ops SUBSET
        set (MAP THE (FILTER IS_SOME (MAP get_label ops)))
Proof
  Induct >> simp[SUBSET_DEF] >> Cases >> simp[get_label_def] >>
  rw[] >> fs[SUBSET_DEF]
QED

(* Helper: TL monotonicity for the FOLDR label extractor *)
Triviality foldr_labels_tl_subset[local]:
  !ops. FOLDR (\op acc. case op of Label dst => dst INSERT acc | _ => acc)
              EMPTY (TL ops) SUBSET
        FOLDR (\op acc. case op of Label dst => dst INSERT acc | _ => acc)
              EMPTY ops
Proof
  Cases >> simp[SUBSET_DEF] >> Cases_on `h` >> simp[]
QED

(* Helper: sccp_transfer_inst for non-terminators doesn't change sl_targets *)
Triviality sccp_transfer_inst_non_term_targets[local]:
  !fn inst lat.
    ~is_terminator inst.inst_opcode ==>
    (sccp_transfer_inst fn inst lat).sl_targets = lat.sl_targets
Proof
  rpt strip_tac >>
  simp[sccp_transfer_inst_def] >>
  rpt IF_CASES_TAC >> fs[is_terminator_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[])
QED

(* Helper: sccp_transfer_inst for terminators adds only successors *)
Triviality sccp_transfer_inst_term_targets[local]:
  !fn inst lat.
    is_terminator inst.inst_opcode ==>
    (sccp_transfer_inst fn inst lat).sl_targets SUBSET
    set (get_successors inst) UNION lat.sl_targets
Proof
  rpt strip_tac >>
  simp[sccp_transfer_inst_def, get_successors_def] >>
  rpt IF_CASES_TAC >> fs[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> fs[get_label_def, SUBSET_DEF]) >>
  rpt strip_tac >> fs[] >> rw[] >>
  TRY (imp_res_tac (SIMP_RULE std_ss [SUBSET_DEF]
         foldr_labels_subset_get_successors) >> fs[]) >>
  TRY (irule SUBSET_TRANS >>
       qexists_tac `FOLDR (\op acc. case op of
           Label dst => dst INSERT acc | _ => acc)
         EMPTY inst.inst_operands UNION lat.sl_targets` >>
       conj_tac >- (simp[SUBSET_DEF] >> rpt strip_tac >>
         imp_res_tac (SIMP_RULE std_ss [SUBSET_DEF]
           foldr_labels_tl_subset) >> simp[]) >-
       (simp[SUBSET_DEF] >> rpt strip_tac >>
         imp_res_tac (SIMP_RULE std_ss [SUBSET_DEF]
           foldr_labels_subset_get_successors) >> simp[]))
QED

(* Helper: successors of well-formed block instructions are in fn_labels *)
Triviality inst_successors_in_fn_labels[local]:
  !fn lbl inst bb.
    wf_function fn /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM inst bb.bb_instructions /\
    is_terminator inst.inst_opcode ==>
    set (get_successors inst) SUBSET set (fn_labels fn)
Proof
  rpt strip_tac >>
  `MEM bb fn.fn_blocks` by
    (fs[lookup_block_def] >> imp_res_tac find_some_mem) >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  (* inst is a terminator, so it must be LAST *)
  `inst = LAST bb.bb_instructions` by (
    fs[bb_well_formed_def] >>
    `?i. i < LENGTH bb.bb_instructions /\ EL i bb.bb_instructions = inst` by
      metis_tac[MEM_EL] >>
    `i = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >>
    `bb.bb_instructions <> []` by fs[] >>
    metis_tac[LAST_EL]) >>
  simp[SUBSET_DEF] >> rpt strip_tac >>
  `MEM x (bb_succs bb)` by (
    simp[bb_succs_def] >>
    Cases_on `bb.bb_instructions` >> gvs[MEM_nub, MEM_REVERSE]) >>
  fs[wf_function_def, fn_succs_closed_def] >>
  metis_tac[]
QED

Triviality sccp_transfer_inv[local]:
  !fn lbl inst lat.
    wf_function fn /\
    MEM inst (case lookup_block lbl fn.fn_blocks of NONE => []
              | SOME bb => bb.bb_instructions) /\
    FDOM lat.sl_vals SUBSET set (fn_all_assignments fn) /\
    lat.sl_targets SUBSET set (fn_labels fn) ==>
    FDOM (sccp_transfer_inst fn inst lat).sl_vals
      SUBSET set (fn_all_assignments fn) /\
    (sccp_transfer_inst fn inst lat).sl_targets
      SUBSET set (fn_labels fn)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac
  (* FDOM *)
  >- (irule sccp_transfer_inst_fdom >> simp[] >>
      Cases_on `lookup_block lbl fn.fn_blocks` >> fs[MEM] >>
      imp_res_tac lookup_block_outputs_bound >>
      fs[EVERY_MEM] >> res_tac)
  (* sl_targets *)
  >- (Cases_on `is_terminator inst.inst_opcode`
      >- (imp_res_tac sccp_transfer_inst_term_targets >>
          Cases_on `lookup_block lbl fn.fn_blocks` >> fs[MEM] >>
          drule_all inst_successors_in_fn_labels >>
          fs[SUBSET_DEF] >> metis_tac[])
      >- (imp_res_tac sccp_transfer_inst_non_term_targets >> simp[]))
QED

(* ===== Bridge: df_process_block for SCCP ===== *)

Theorem sccp_process_eq:
  !fn lbl st.
    df_process_block Forward sccp_bottom sccp_join sccp_transfer_inst
      sccp_edge_transfer
      fn (OPTION_MAP (\lbl. (lbl, sccp_bottom)) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks lbl st =
    let instrs = case lookup_block lbl fn.fn_blocks of
                   NONE => [] | SOME bb => bb.bb_instructions in
    let (fv, inst_map) = df_fold_block Forward
                           (sccp_transfer_inst fn) lbl
                           instrs (sccp_joined fn st lbl) in
    let new_bnd = sccp_join (df_boundary sccp_bottom st lbl) fv in
      if new_bnd = df_boundary sccp_bottom st lbl then st
      else st with ds_boundary := st.ds_boundary |+ (lbl, new_bnd)
Proof
  rw[df_process_block_def, df_joined_val_def] >>
  simp_tac std_ss [LET_THM, direction_case_def] >>
  simp[sccp_joined_def, LET_THM] >>
  Cases_on `fn_entry_label fn` >> simp[sccp_edge_transfer_def]
QED

(* ===== inst_map properties (from df_fold_block) ===== *)

Theorem sccp_fold_inst_map_props:
  !lbl instrs v0 fv inst_map.
    df_fold_block Forward (sccp_transfer_inst fn) lbl instrs v0 =
      (fv, inst_map) ==>
    (!k. k IN FDOM inst_map ==> FST k = lbl) /\
    (lbl, 0n) IN FDOM inst_map /\
    FLOOKUP inst_map (lbl, 0n) = SOME v0
Proof
  rpt strip_tac >> imp_res_tac df_fold_block_fdom
  >- fs[IN_IMAGE, IN_COUNT]
  >- simp[IN_IMAGE, IN_COUNT]
  >- (qpat_x_assum `_ = (fv, inst_map)` mp_tac >>
      simp[df_fold_block_def, df_fold_forward_def, direction_case_def] >>
      strip_tac >> imp_res_tac df_fold_forward_at >> fs[])
QED

(* inst_map CARD monotone *)
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

Triviality ds_inst_update_literal[local]:
  !(st : 'a df_state) X.
    (st with ds_inst := X) = <|ds_inst := X; ds_boundary := st.ds_boundary|>
Proof
  simp[df_state_component_equality]
QED

(* ===== sccp_val_measure strict when join differs ===== *)

(* const_lookup on sccp_join *)
Triviality const_lookup_sccp_join[local]:
  !a b v.
    const_lookup (sccp_join a b).sl_vals v =
    const_meet (const_lookup a.sl_vals v) (const_lookup b.sl_vals v)
Proof
  rpt strip_tac >>
  simp[sccp_join_def, const_lookup_def] >>
  `FINITE (FDOM a.sl_vals UNION FDOM b.sl_vals)` by simp[] >>
  simp[FLOOKUP_FUN_FMAP] >>
  IF_CASES_TAC >> simp[] >>
  fs[IN_UNION] >> simp[FLOOKUP_DEF, const_meet_def]
QED

(* Per-variable measure: sccp_join weakly increases each variable *)
Triviality sccp_join_per_var_mono[local]:
  !a b v.
    const_val_measure (const_lookup a.sl_vals v) <=
    const_val_measure (const_lookup (sccp_join a b).sl_vals v)
Proof
  rpt strip_tac >>
  simp[const_lookup_sccp_join, const_val_measure_mono]
QED

(* Per-variable measure: strict if const_meet differs *)
Triviality sccp_join_per_var_strict[local]:
  !a b v.
    const_meet (const_lookup a.sl_vals v) (const_lookup b.sl_vals v) <>
    const_lookup a.sl_vals v ==>
    const_val_measure (const_lookup a.sl_vals v) <
    const_val_measure (const_lookup (sccp_join a b).sl_vals v)
Proof
  rpt strip_tac >>
  simp[const_lookup_sccp_join] >>
  irule const_val_measure_strict >> simp[]
QED

(* sccp_val_measure is weakly monotone under sccp_join *)
Triviality sccp_val_measure_join_mono[local]:
  !fn a b.
    FDOM a.sl_vals SUBSET set (fn_all_assignments fn) /\
    a.sl_targets SUBSET set (fn_labels fn) /\
    FDOM b.sl_vals SUBSET set (fn_all_assignments fn) /\
    b.sl_targets SUBSET set (fn_labels fn) ==>
    sccp_val_measure fn a <= sccp_val_measure fn (sccp_join a b)
Proof
  rpt strip_tac >>
  simp[sccp_val_measure_def] >>
  `SUM (MAP (\v. const_val_measure (const_lookup a.sl_vals v))
            (fn_all_assignments fn)) <=
   SUM (MAP (\v. const_val_measure (const_lookup (sccp_join a b).sl_vals v))
            (fn_all_assignments fn))` by (
    irule sum_map_le >> simp[EVERY_MEM] >> rpt strip_tac >>
    simp[sccp_join_per_var_mono]) >>
  `CARD (FDOM a.sl_vals INTER set (fn_all_assignments fn)) <=
   CARD (FDOM (sccp_join a b).sl_vals INTER set (fn_all_assignments fn))` by (
    irule CARD_SUBSET >> simp[FINITE_INTER, FINITE_LIST_TO_SET] >>
    simp[sccp_join_def, FUN_FMAP_DEF, FDOM_FINITE, SUBSET_DEF, IN_INTER] >>
    metis_tac[]) >>
  `CARD (a.sl_targets INTER set (fn_labels fn)) <=
   CARD ((sccp_join a b).sl_targets INTER set (fn_labels fn))` by (
    irule CARD_SUBSET >> simp[FINITE_INTER, FINITE_LIST_TO_SET] >>
    simp[sccp_join_def, SUBSET_DEF, IN_INTER] >> metis_tac[]) >>
  simp[]
QED

(* Helper: 3-component strict increase when at least one is strict *)
Triviality three_component_strict[local]:
  !(a1:num) a2 a3 b1 b2 b3.
    a1 <= b1 /\ a2 <= b2 /\ a3 <= b3 /\
    (a1 < b1 \/ a2 < b2 \/ a3 < b3) ==>
    a1 + a2 + a3 < b1 + b2 + b3
Proof
  DECIDE_TAC
QED

(* When the weighted component strictly increases, it dominates any decrease
   in the bounded component c (bounded by k). b and d must be monotone. *)
Triviality mult_strict_bound[local]:
  !(k:num) a a'. a < a' ==> (k + 1) * a + k < (k + 1) * a'
Proof
  Induct_on `k` >- simp[] >>
  rpt strip_tac >>
  first_x_assum (drule_then assume_tac) >>
  simp_tac std_ss [MULT_CLAUSES, ADD_CLAUSES] >> DECIDE_TAC
QED

Triviality weighted_four_component_strict[local]:
  !(k:num) a a' b b' c c' d d'.
    a < a' /\ b <= b' /\ c <= k /\ d <= d' ==>
    (k + 1) * a + b + c + d < (k + 1) * a' + b' + c' + d'
Proof
  rpt strip_tac >>
  `(k + 1) * a + k < (k + 1) * a'` by (irule mult_strict_bound >> simp[]) >>
  DECIDE_TAC
QED

Triviality boundary_measure_inst_irrelevant[local]:
  !fn di1 di2 bnd.
    sccp_boundary_measure fn <|ds_inst := di1; ds_boundary := bnd|> =
    sccp_boundary_measure fn <|ds_inst := di2; ds_boundary := bnd|>
Proof
  simp[sccp_boundary_measure_def, df_boundary_def]
QED

Triviality const_lookup_in_dom[local]:
  !fm v. v IN FDOM fm ==> const_lookup fm v = fm ' v
Proof
  rw[const_lookup_def, FLOOKUP_DEF]
QED

(* If sccp_join a b ≠ a, the measure strictly increases *)
Triviality sccp_val_measure_join_strict[local]:
  !fn a b.
    FDOM a.sl_vals SUBSET set (fn_all_assignments fn) /\
    a.sl_targets SUBSET set (fn_labels fn) /\
    FDOM b.sl_vals SUBSET set (fn_all_assignments fn) /\
    b.sl_targets SUBSET set (fn_labels fn) /\
    sccp_join a b <> a ==>
    sccp_val_measure fn a < sccp_val_measure fn (sccp_join a b)
Proof
  rpt strip_tac >>
  simp_tac std_ss [sccp_val_measure_def] >>
  irule three_component_strict >>
  rpt conj_tac
  (* Weak mono: SUM *)
  >- (irule sum_map_le >> simp[EVERY_MEM] >> rpt strip_tac >>
      simp[sccp_join_per_var_mono])
  (* Weak mono: FDOM CARD *)
  >- (irule CARD_SUBSET >> simp[FINITE_INTER, FINITE_LIST_TO_SET] >>
      simp[sccp_join_def, FUN_FMAP_DEF, FDOM_FINITE, SUBSET_DEF, IN_INTER] >>
      metis_tac[])
  (* Weak mono: targets CARD *)
  >- (irule CARD_SUBSET >> simp[FINITE_INTER, FINITE_LIST_TO_SET] >>
      simp[sccp_join_def, SUBSET_DEF, IN_INTER] >> metis_tac[])
  (* Strict: at least one component increases *)
  >> Cases_on `(sccp_join a b).sl_vals = a.sl_vals`
  >- (
    (* sl_vals same → targets differ *)
    DISJ2_TAC >> DISJ2_TAC >>
    `(sccp_join a b).sl_targets <> a.sl_targets` by (
      strip_tac >> qpat_x_assum `sccp_join a b <> a` mp_tac >>
      simp[sccp_lattice_component_equality]) >>
    `a.sl_targets PSUBSET (sccp_join a b).sl_targets` by (
      simp[PSUBSET_DEF, sccp_join_def, EXTENSION, SUBSET_DEF] >>
      metis_tac[]) >>
    `a.sl_targets INTER set (fn_labels fn) PSUBSET
     (sccp_join a b).sl_targets INTER set (fn_labels fn)` by (
      simp[PSUBSET_DEF, SUBSET_DEF, IN_INTER, EXTENSION] >>
      conj_tac >- (fs[sccp_join_def, SUBSET_DEF] >> metis_tac[]) >>
      fs[PSUBSET_DEF, SUBSET_DEF, EXTENSION, sccp_join_def] >>
      metis_tac[]) >>
    irule CARD_PSUBSET >> simp[FINITE_INTER, FINITE_LIST_TO_SET]
  )
  >- (
    (* sl_vals differ → domain grew or value changed *)
    Cases_on `FDOM (sccp_join a b).sl_vals = FDOM a.sl_vals`
    >- (
      (* Same domain → some value changed → SUM increases *)
      DISJ1_TAC >>
      irule sum_map_lt >> simp[EVERY_MEM] >>
      REVERSE conj_tac
      >- (rpt strip_tac >> simp[sccp_join_per_var_mono]) >>
      (* Find variable where value changed *)
      `?v. v IN FDOM a.sl_vals /\
           (sccp_join a b).sl_vals ' v <> a.sl_vals ' v` by (
        spose_not_then strip_assume_tac >>
        qpat_x_assum `_ <> a.sl_vals` mp_tac >>
        simp[fmap_EXT]) >>
      `MEM v (fn_all_assignments fn)` by fs[SUBSET_DEF] >>
      qexists_tac `v` >> simp[] >>
      simp[const_lookup_sccp_join] >>
      irule const_val_measure_strict >>
      (* Bridge FAPPLY to const_lookup *)
      `const_lookup a.sl_vals v = a.sl_vals ' v` by
        (irule const_lookup_in_dom >> fs[]) >>
      `v IN FDOM (sccp_join a b).sl_vals` by fs[] >>
      `const_lookup (sccp_join a b).sl_vals v = (sccp_join a b).sl_vals ' v` by
        (irule const_lookup_in_dom >> fs[]) >>
      metis_tac[const_lookup_sccp_join]
    )
    >- (
      (* Domain grew → FDOM CARD increases *)
      DISJ2_TAC >> DISJ1_TAC >>
      `FDOM a.sl_vals PSUBSET FDOM (sccp_join a b).sl_vals` by (
        simp[PSUBSET_DEF, sccp_join_def, FUN_FMAP_DEF, FDOM_FINITE,
             SUBSET_DEF] >> metis_tac[]) >>
      `FDOM (sccp_join a b).sl_vals SUBSET set (fn_all_assignments fn)` by
        (irule sccp_join_fdom_subset >> simp[]) >>
      `FDOM a.sl_vals INTER set (fn_all_assignments fn) PSUBSET
       FDOM (sccp_join a b).sl_vals INTER set (fn_all_assignments fn)` by (
        fs[PSUBSET_DEF, SUBSET_DEF, IN_INTER, EXTENSION] >> metis_tac[]) >>
      irule CARD_PSUBSET >> simp[FINITE_INTER, FINITE_LIST_TO_SET]
    )
  )
QED

(* ===== Boundary measure strict ===== *)

Triviality boundary_measure_strict[local]:
  !fn lbl st new_val.
    sccp_state_inv fn st /\
    MEM lbl (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre) /\
    sccp_val_measure fn (df_boundary sccp_bottom st lbl) <
    sccp_val_measure fn new_val ==>
    sccp_boundary_measure fn st <
    sccp_boundary_measure fn (st with ds_boundary := st.ds_boundary |+ (lbl, new_val))
Proof
  rpt strip_tac >>
  simp[sccp_boundary_measure_def, LET_THM] >>
  ntac 2 (once_rewrite_tac[GSYM MAP_APPEND]) >>
  irule sum_map_lt >> simp[] >>
  `!x. sccp_val_measure fn
         (df_boundary sccp_bottom
            (st with ds_boundary := st.ds_boundary |+ (lbl, new_val)) x) =
       if x = lbl then sccp_val_measure fn new_val
       else sccp_val_measure fn (df_boundary sccp_bottom st x)` by
    (rpt strip_tac >> simp[df_boundary_def, FLOOKUP_UPDATE] >>
     IF_CASES_TAC >> simp[]) >>
  rpt conj_tac >>
  TRY (simp[EVERY_MEM] >> rpt strip_tac >>
       IF_CASES_TAC >> simp[] >> NO_TAC) >>
  qexists_tac `lbl` >> fs[MEM_APPEND]
QED

(* ===== Fresh count helpers ===== *)

(* joined only depends on ds_boundary *)
Triviality sccp_joined_inst_irrelevant[local]:
  !fn st X lbl.
    sccp_joined fn (st with ds_inst := X) lbl =
    sccp_joined fn st lbl
Proof
  simp[sccp_joined_def, LET_THM, df_boundary_def]
QED

Triviality fresh_count_increase[local]:
  !fn st inst_map lbl.
    MEM lbl (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre) /\
    FLOOKUP inst_map (lbl, 0n) = SOME (sccp_joined fn st lbl) /\
    (!k. k IN FDOM inst_map ==> FST k = lbl) /\
    FLOOKUP (FUNION inst_map st.ds_inst) (lbl, 0n) <>
      FLOOKUP st.ds_inst (lbl, 0n) ==>
    sccp_fresh_count fn st <
    sccp_fresh_count fn (st with ds_inst := FUNION inst_map st.ds_inst)
Proof
  rpt strip_tac >>
  simp[sccp_fresh_count_def, LET_THM,
       sccp_joined_inst_irrelevant] >>
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

(* fresh_count bounded *)
Triviality fresh_count_bounded[local]:
  !fn st.
    sccp_fresh_count fn st <=
    LENGTH (fn_labels fn) + LENGTH (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  simp_tac std_ss [sccp_fresh_count_def, LET_THM] >>
  match_mp_tac LESS_EQ_TRANS >>
  qexists_tac `CARD (set (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre))` >>
  conj_tac >- (
    irule CARD_SUBSET >> simp[FINITE_LIST_TO_SET, SUBSET_DEF]) >>
  match_mp_tac LESS_EQ_TRANS >>
  qexists_tac `LENGTH (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre)` >>
  simp[CARD_LIST_TO_SET, LENGTH_APPEND]
QED

(* C3 fold coherence: when ds_inst already has right v0, FUNION is absorbed *)
Triviality funion_fold_coherent[local]:
  !fn lbl st joined instrs fv inst_map.
    sccp_measure_inv fn st /\
    instrs = (case lookup_block lbl fn.fn_blocks of
                NONE => [] | SOME bb => bb.bb_instructions) /\
    df_fold_block Forward (sccp_transfer_inst fn) lbl
      instrs joined = (fv, inst_map) /\
    FLOOKUP st.ds_inst (lbl, 0n) = SOME joined ==>
    FUNION inst_map st.ds_inst = st.ds_inst
Proof
  rpt strip_tac >>
  `!k v. FLOOKUP inst_map k = SOME v ==> FLOOKUP st.ds_inst k = SOME v` by (
    rpt strip_tac >>
    qpat_x_assum `sccp_measure_inv _ _` mp_tac >>
    simp_tac std_ss [sccp_measure_inv_def, LET_THM] >>
    strip_tac >>
    first_x_assum (qspecl_then [`lbl`, `joined`] mp_tac) >>
    impl_tac >- simp[] >>
    disch_then (qspecl_then [`k`, `v`] mp_tac) >>
    impl_tac >- (
      qpat_x_assum `instrs = _` (SUBST1_TAC o GSYM) >>
      qpat_x_assum `df_fold_block _ _ _ _ _ = _` (fn th => simp[th])) >>
    simp[]) >>
  simp[fmap_eq_flookup] >> gen_tac >> simp[FLOOKUP_FUNION] >>
  Cases_on `FLOOKUP inst_map x` >> simp[]
QED

(* joined boundary eq *)
Triviality sccp_joined_boundary_eq[local]:
  !fn st bnd di.
    (!x. df_boundary sccp_bottom <|ds_inst := di; ds_boundary := bnd|> x =
         df_boundary sccp_bottom st x) ==>
    !x. sccp_joined fn <|ds_inst := di; ds_boundary := bnd|> x =
        sccp_joined fn st x
Proof
  rpt strip_tac >>
  simp[sccp_joined_def, LET_THM]
QED

Triviality fresh_count_mono[local]:
  !fn st inst_map lbl bnd.
    (!k. k IN FDOM inst_map ==> FST k = lbl) /\
    FLOOKUP inst_map (lbl, 0n) = SOME (sccp_joined fn st lbl) /\
    (!x. sccp_joined fn <|ds_inst := FUNION inst_map st.ds_inst;
                            ds_boundary := bnd|> x =
         sccp_joined fn st x) ==>
    sccp_fresh_count fn st <=
    sccp_fresh_count fn
      <|ds_inst := FUNION inst_map st.ds_inst; ds_boundary := bnd|>
Proof
  rpt strip_tac >>
  simp[sccp_fresh_count_def, LET_THM] >>
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

(* ===== Invariant preservation ===== *)

(* Wrapper for df_fold_block_forward_invariant with drule-friendly shape *)
Triviality sccp_fold_inv[local]:
  !transfer lbl instrs init_val fv im bound_v bound_t.
    df_fold_block Forward transfer lbl instrs init_val = (fv, im) ==>
    FDOM init_val.sl_vals SUBSET bound_v /\
    init_val.sl_targets SUBSET bound_t ==>
    (!inst v. MEM inst instrs /\
      FDOM v.sl_vals SUBSET bound_v /\ v.sl_targets SUBSET bound_t ==>
      FDOM (transfer inst v).sl_vals SUBSET bound_v /\
      (transfer inst v).sl_targets SUBSET bound_t) ==>
    FDOM fv.sl_vals SUBSET bound_v /\ fv.sl_targets SUBSET bound_t /\
    (!k v. FLOOKUP im k = SOME v ==>
      FDOM v.sl_vals SUBSET bound_v /\ v.sl_targets SUBSET bound_t)
Proof
  rpt strip_tac >>
  drule (dfAnalyzePropsTheory.df_fold_block_forward_invariant
         |> REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then (qspec_then
    `\v. FDOM v.sl_vals SUBSET bound_v /\ v.sl_targets SUBSET bound_t`
    (mp_tac o BETA_RULE)) >>
  simp[] >> strip_tac >> res_tac
QED

(* sccp_joined satisfies invariant *)
(* Helper: case-split on list and use foldl_sccp_join_inv *)
Triviality case_foldl_inv[local]:
  !l bound_v bound_t.
    FDOM sccp_bottom.sl_vals SUBSET bound_v /\
    sccp_bottom.sl_targets SUBSET bound_t /\
    EVERY (\v. FDOM v.sl_vals SUBSET bound_v /\
               v.sl_targets SUBSET bound_t) l ==>
    FDOM (case l of [] => sccp_bottom
            | v2::v3 => FOLDL sccp_join sccp_bottom l).sl_vals
      SUBSET bound_v /\
    (case l of [] => sccp_bottom
            | v2::v3 => FOLDL sccp_join sccp_bottom l).sl_targets
      SUBSET bound_t
Proof
  Cases >> simp[] >> rpt gen_tac >> disch_tac >>
  irule foldl_sccp_join_inv >> fs[] >>
  metis_tac[sccp_join_fdom_subset, sccp_join_targets_subset]
QED

Triviality sccp_joined_inv[local]:
  !fn st lbl.
    sccp_state_inv fn st ==>
    FDOM (sccp_joined fn st lbl).sl_vals
      SUBSET set (fn_all_assignments fn) /\
    (sccp_joined fn st lbl).sl_targets
      SUBSET set (fn_labels fn)
Proof
  rpt gen_tac >> strip_tac >>
  simp[sccp_joined_def, LET_THM] >>
  Cases_on `fn_entry_label fn` >> gvs[]
  >- ((* NONE case *)
      irule case_foldl_inv >>
      simp[sccp_bottom_inv, EVERY_MAP, EVERY_MEM] >>
      rpt gen_tac >> disch_tac >>
      irule sccp_edge_transfer_inv >> metis_tac[sccp_df_boundary_inv])
  >- ((* SOME x case *)
      IF_CASES_TAC >> gvs[]
      >- ((* lbl = x: gvs substituted x→lbl, so goal uses lbl *)
          `FDOM (case MAP (\nbr. sccp_edge_transfer fn nbr lbl
                      (df_boundary sccp_bottom st nbr))
                    (cfg_preds_of (cfg_analyze fn) lbl)
                 of [] => sccp_bottom
                  | v2::v3 => FOLDL sccp_join sccp_bottom
                      (MAP (\nbr. sccp_edge_transfer fn nbr lbl
                        (df_boundary sccp_bottom st nbr))
                        (cfg_preds_of (cfg_analyze fn) lbl))).sl_vals
            SUBSET set (fn_all_assignments fn) /\
           (case MAP (\nbr. sccp_edge_transfer fn nbr lbl
                      (df_boundary sccp_bottom st nbr))
                    (cfg_preds_of (cfg_analyze fn) lbl)
                 of [] => sccp_bottom
                  | v2::v3 => FOLDL sccp_join sccp_bottom
                      (MAP (\nbr. sccp_edge_transfer fn nbr lbl
                        (df_boundary sccp_bottom st nbr))
                        (cfg_preds_of (cfg_analyze fn) lbl))).sl_targets
            SUBSET set (fn_labels fn)` by (
            irule case_foldl_inv >>
            simp[sccp_bottom_inv, EVERY_MAP, EVERY_MEM] >>
            rpt gen_tac >> disch_tac >>
            irule sccp_edge_transfer_inv >> metis_tac[sccp_df_boundary_inv]) >>
          conj_tac
          >- (irule sccp_join_fdom_subset >> simp[sccp_bottom_inv])
          >- (irule sccp_join_targets_subset >> simp[sccp_bottom_inv]))
      >- ((* lbl ≠ x: same as NONE *)
          irule case_foldl_inv >>
          simp[sccp_bottom_inv, EVERY_MAP, EVERY_MEM] >>
          rpt gen_tac >> disch_tac >>
          irule sccp_edge_transfer_inv >> metis_tac[sccp_df_boundary_inv]))
QED

(* Processing preserves state invariant *)
Triviality sccp_inv_preserved[local]:
  !fn lbl st.
    wf_function fn /\ sccp_state_inv fn st ==>
    sccp_state_inv fn
      (df_process_block Forward sccp_bottom sccp_join sccp_transfer_inst
         sccp_edge_transfer
         fn (OPTION_MAP (\lbl. (lbl, sccp_bottom)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt strip_tac >>
  simp[sccp_process_eq] >>
  simp_tac std_ss [LET_THM] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  (* Boundary-changed case: only ds_boundary updated *)
  imp_res_tac sccp_df_boundary_inv >>
  drule sccp_fold_inv >>
  disch_then (qspecl_then [`set (fn_all_assignments fn)`,
                            `set (fn_labels fn)`] mp_tac) >>
  simp[sccp_joined_inv] >>
  (impl_tac >- metis_tac[sccp_transfer_inv]) >>
  strip_tac >>
  fs[sccp_state_inv_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> simp[FLOOKUP_UPDATE] >> rw[] >> gvs[] >>
      TRY res_tac >>
      TRY (irule sccp_join_fdom_subset) >>
      TRY (irule sccp_join_targets_subset) >>
      simp[])
  >- metis_tac[]
QED

(* measure_inv preservation *)
Theorem sccp_measure_inv_preserved:
  !fn lbl st.
    sccp_measure_inv fn st ==>
    sccp_measure_inv fn
      (df_process_block Forward sccp_bottom sccp_join sccp_transfer_inst
         sccp_edge_transfer
         fn (OPTION_MAP (\lbl. (lbl, sccp_bottom)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt strip_tac >>
  simp[sccp_measure_inv_def] >>
  conj_tac >- fs[sccp_measure_inv_def] >>
  conj_tac >- (
    irule sccp_inv_preserved >>
    fs[sccp_measure_inv_def]) >>
  (* New df_process_block only updates ds_boundary, ds_inst unchanged.
     So C3-C5 (about ds_inst) are trivially preserved. *)
  simp[sccp_process_eq] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  fs[sccp_measure_inv_def] >> metis_tac[]
QED

(* ===== Monotonicity ===== *)

Theorem sccp_measure_monotone:
  !fn lbl st.
    MEM lbl (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre) /\
    sccp_measure_inv fn st /\
    df_process_block Forward sccp_bottom sccp_join sccp_transfer_inst
      sccp_edge_transfer
      fn (OPTION_MAP (\lbl. (lbl, sccp_bottom)) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks lbl st <> st ==>
    sccp_measure fn st <
    sccp_measure fn
      (df_process_block Forward sccp_bottom sccp_join sccp_transfer_inst
         sccp_edge_transfer
         fn (OPTION_MAP (\lbl. (lbl, sccp_bottom)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt strip_tac >>
  rewrite_tac[sccp_process_eq] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  qabbrev_tac `joined = sccp_joined fn st lbl` >>
  qabbrev_tac `instrs = case lookup_block lbl fn.fn_blocks of
                           NONE => [] | SOME bb => bb.bb_instructions` >>
  qabbrev_tac `new_bnd = sccp_join (df_boundary sccp_bottom st lbl) fv` >>
  (* New df_process_block: if boundary unchanged, result = st.
     Since result <> st, boundary must have changed. *)
  `new_bnd <> df_boundary sccp_bottom st lbl` by (
    strip_tac >>
    qpat_x_assum `_ <> st` mp_tac >> simp[] >>
    rewrite_tac[sccp_process_eq] >>
    simp_tac std_ss [LET_THM] >>
    qunabbrev_tac `instrs` >> qunabbrev_tac `joined` >>
    qpat_x_assum `df_fold_block _ _ _ _ _ = _` (fn th => simp[th]) >>
    fs[markerTheory.Abbrev_def]) >>
  (* Result is st with updated boundary only — ds_inst unchanged *)
  (* lbl is now directly in fn_labels ++ dfs_pre from hypothesis *)
  `sccp_state_inv fn st` by fs[sccp_measure_inv_def] >>
  `FDOM (df_boundary sccp_bottom st lbl).sl_vals
     SUBSET set (fn_all_assignments fn) /\
   (df_boundary sccp_bottom st lbl).sl_targets
     SUBSET set (fn_labels fn)` by
    metis_tac[sccp_df_boundary_inv] >>
  qunabbrev_tac `joined` >> qunabbrev_tac `instrs` >> qunabbrev_tac `new_bnd` >>
  drule sccp_fold_inv >>
  disch_then (qspecl_then [`set (fn_all_assignments fn)`,
                            `set (fn_labels fn)`] mp_tac) >>
  simp[sccp_joined_inv] >>
  (impl_tac >- (fs[sccp_measure_inv_def] >> metis_tac[sccp_transfer_inv])) >>
  strip_tac >>
  (* Boundary strictly changed — sccp_val_measure_join_strict *)
  `df_boundary sccp_bottom st lbl <> sccp_join (df_boundary sccp_bottom st lbl) fv`
    by metis_tac[] >>
  drule_all sccp_val_measure_join_strict >> strip_tac >>
  drule_all boundary_measure_strict >> strip_tac >>
  (* Component: fc bounded by all_count *)
  assume_tac (Q.SPECL [`fn`, `st`] fresh_count_bounded) >>
  (* Component: bc monotone *)
  `CARD (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre) <=
   CARD (FDOM (st.ds_boundary |+ (lbl,
     sccp_join (df_boundary sccp_bottom st lbl) fv)) INTER
     set (cfg_analyze fn).cfg_dfs_pre)` by (
    irule CARD_SUBSET >> simp[FINITE_INTER, FDOM_FUPDATE] >>
    simp[SUBSET_DEF, IN_INTER] >> metis_tac[IN_INSERT]) >>
  (* Use weighted_four_component_strict for the final arithmetic.
     ds_inst unchanged so ic_old = ic_new, fc bounded, bm strict, bc mono *)
  simp_tac std_ss [sccp_measure_def, LET_THM] >>
  irule weighted_four_component_strict >>
  gvs[FDOM_FUPDATE]
QED

Triviality foldl_inst_only_boundary[local]:
  !lbls (f : 'a df_state -> string -> 'a df_state) acc.
    (!st lbl. (f st lbl).ds_boundary = st.ds_boundary) ==>
    (FOLDL f acc lbls).ds_boundary = acc.ds_boundary
Proof Induct >> simp[]
QED

Triviality populate_inst_ds_boundary[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st.
    (df_populate_inst dir bottom join transfer edge_transfer ctx
       entry_val cfg bbs lbls st).ds_boundary = st.ds_boundary
Proof
  rpt gen_tac >>
  simp[df_populate_inst_def] >>
  irule foldl_inst_only_boundary >>
  simp[LET_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[]
QED

(* ===== Helpers for df_populate_inst structural properties ===== *)

(* Fold outputs for different labels have disjoint domains *)
Triviality fold_block_keys_disjoint[local]:
  !dir transfer lbl1 lbl2 instrs1 instrs2 init1 init2.
    lbl1 <> lbl2 ==>
    DISJOINT (FDOM (SND (df_fold_block dir transfer lbl1 instrs1 init1)))
             (FDOM (SND (df_fold_block dir transfer lbl2 instrs2 init2)))
Proof
  rpt strip_tac >>
  Cases_on `df_fold_block dir transfer lbl1 instrs1 init1` >>
  Cases_on `df_fold_block dir transfer lbl2 instrs2 init2` >>
  simp[DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] >>
  rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  qpat_assum `df_fold_block _ _ lbl1 _ _ = _`
    (strip_assume_tac o MATCH_MP dfAnalyzeProofsTheory.df_fold_block_keys) >>
  qpat_assum `df_fold_block _ _ lbl2 _ _ = _`
    (strip_assume_tac o MATCH_MP dfAnalyzeProofsTheory.df_fold_block_keys) >>
  metis_tac[FLOOKUP_DEF, NOT_NONE_SOME]
QED

(* Step 1: monotonicity — if m ⊑ acc and disjoint, then m ⊑ FOLDL *)
Triviality foldl_funion_preserves_submap[local]:
  !lbls (f : string -> ('a # num, 'b) fmap) acc m.
    m SUBMAP acc /\
    (!l. MEM l lbls ==> DISJOINT (FDOM (f l)) (FDOM m)) ==>
    m SUBMAP FOLDL (\st' l. FUNION (f l) st') acc lbls
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> rpt conj_tac >>
  metis_tac[SUBMAP_FUNION, DISJOINT_SYM]
QED

(* Step 2: FOLDL of FUNION submap — if MEM and ALL_DISTINCT, component ⊑ result *)
Triviality foldl_funion_submap[local]:
  !lbls (f : string -> ('a # num, 'b) fmap) acc lbl.
    MEM lbl lbls /\ ALL_DISTINCT lbls /\
    (!l1 l2. MEM l1 lbls /\ MEM l2 lbls /\ l1 <> l2 ==>
             DISJOINT (FDOM (f l1)) (FDOM (f l2))) ==>
    f lbl SUBMAP FOLDL (\acc l. FUNION (f l) acc) acc lbls
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (irule foldl_funion_preserves_submap >>
      simp[SUBMAP_FUNION_ID] >> metis_tac[MEM])
QED

(* Populate inst result's ds_inst is a FOLDL of FUNIONs *)
Triviality populate_inst_ds_inst[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st.
    (df_populate_inst dir bottom join transfer edge_transfer
       ctx entry_val cfg bbs lbls st).ds_inst =
    FOLDL (\acc lbl.
      let joined = df_joined_val dir bottom join edge_transfer ctx
                                 entry_val cfg st lbl in
      let instrs = (case lookup_block lbl bbs of
                      NONE => [] | SOME bb => bb.bb_instructions) in
      let (final_val, inst_map) = df_fold_block dir (transfer ctx)
                                    lbl instrs joined in
      FUNION inst_map acc) st.ds_inst lbls
Proof
  Induct_on `lbls`
  \\ simp[df_populate_inst_def, LET_THM]
  \\ rpt gen_tac
  \\ pairarg_tac \\ simp[]
  \\ last_x_assum (qspecl_then [`dir`, `bottom`, `join`, `transfer`,
       `edge_transfer`, `ctx`, `entry_val`, `cfg`, `bbs`,
       `st with ds_inst := FUNION inst_map st.ds_inst`] mp_tac)
  \\ simp_tac std_ss [df_joined_val_def, df_boundary_def, df_state_accfupds,
       df_populate_inst_def, LET_THM]
QED

(* Fold from populate submap: for each label in the list, the fold inst_map
   is a submap of the final populated ds_inst *)
Triviality populate_inst_submap[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st
   lbl bb.
    MEM lbl lbls /\ ALL_DISTINCT lbls /\
    lookup_block lbl bbs = SOME bb ==>
    let joined = df_joined_val dir bottom join edge_transfer ctx
                               entry_val cfg st lbl in
    let (fv, im) = df_fold_block dir (transfer ctx) lbl
                      bb.bb_instructions joined in
    im SUBMAP (df_populate_inst dir bottom join transfer edge_transfer
                 ctx entry_val cfg bbs lbls st).ds_inst
Proof
  rpt gen_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  simp[populate_inst_ds_inst] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  qho_match_abbrev_tac `_ SUBMAP FOLDL (\acc lbl. FUNION (f lbl) acc) _ _` >>
  `im = f lbl` by simp[Abbr `f`] >>
  pop_assum SUBST1_TAC >>
  irule foldl_funion_submap >> rw[Abbr `f`] >>
  irule fold_block_keys_disjoint >> simp[]
QED

(* Helper: FOLDL FUNION membership — if k in FDOM (FOLDL FUNION),
   then k came from some f(l) with MEM l lbls *)
Triviality foldl_funion_mem[local]:
  !lbls (f : string -> ('a # num, 'b) fmap) acc k.
    k IN FDOM (FOLDL (\acc l. FUNION (f l) acc) acc lbls) /\
    k NOTIN FDOM acc ==>
    ?l. MEM l lbls /\ k IN FDOM (f l)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  gvs[FUNION_DEF] >> metis_tac[MEM]
QED

(* FLOOKUP from FOLDL of disjoint FUNIONs: value came from exactly one f(l) *)
(* df_fold_block Forward stores init_val at (lbl, 0) *)
Triviality df_fold_block_at_zero[local]:
  !transfer lbl instrs init_val fv im.
    df_fold_block Forward transfer lbl instrs init_val = (fv, im) ==>
    FLOOKUP im (lbl, 0n) = SOME init_val
Proof
  rw[dfAnalyzeDefsTheory.df_fold_block_def] >>
  drule dfAnalyzeProofsTheory.df_fold_forward_at >> simp[]
QED

Triviality foldl_funion_flookup[local]:
  !lbls (f : string -> ('a # num, 'b) fmap) k v.
    FLOOKUP (FOLDL (\acc l. FUNION (f l) acc) FEMPTY lbls) k = SOME v /\
    ALL_DISTINCT lbls /\
    (!l1 l2. MEM l1 lbls /\ MEM l2 lbls /\ l1 <> l2 ==>
       DISJOINT (FDOM (f l1)) (FDOM (f l2))) ==>
    ?l. MEM l lbls /\ FLOOKUP (f l) k = SOME v
Proof
  rpt strip_tac >>
  `k IN FDOM (FOLDL (\acc l. FUNION (f l) acc) FEMPTY lbls)` by
    fs[FLOOKUP_DEF] >>
  drule foldl_funion_mem >> simp[] >> strip_tac >>
  qexists `l` >> simp[] >>
  `f l SUBMAP FOLDL (\acc l. FUNION (f l) acc) FEMPTY lbls` by (
    irule foldl_funion_submap >> metis_tac[]) >>
  fs[SUBMAP_FLOOKUP_EQN, FLOOKUP_DEF]
QED

(* All inst keys in populated result have (lbl,0) present (key closure) *)
(* Helper: in a FOLDL of disjoint FUNIONs, if (lbl,j) is a key then
   (lbl,0) is also a key, provided each f(l) has that closure property
   and keys from f(l) have FST = l. *)
Triviality foldl_funion_key_closure[local]:
  !lbls (f : string -> (string # num, 'b) fmap) lbl j.
    (lbl, j) IN FDOM (FOLDL (\acc l. FUNION (f l) acc) FEMPTY lbls) /\
    ALL_DISTINCT lbls /\
    (!l. (lbl,j) IN FDOM (f l) ==> lbl = l) /\
    (!l. (lbl,0n) IN FDOM (f l) ==> lbl = l) /\
    (lbl, 0n) IN FDOM (f lbl) /\
    (!l1 l2. l1 <> l2 ==> DISJOINT (FDOM (f l1)) (FDOM (f l2))) ==>
    (lbl, 0n) IN FDOM (FOLDL (\acc l. FUNION (f l) acc) FEMPTY lbls)
Proof
  rpt strip_tac >>
  drule foldl_funion_mem >> (impl_tac >- simp[]) >> strip_tac >>
  `lbl = l` by metis_tac[] >> gvs[] >>
  `f l SUBMAP FOLDL (\acc l. FUNION (f l) acc) FEMPTY lbls` by (
    irule foldl_funion_submap >> metis_tac[]) >>
  fs[SUBMAP_DEF, FLOOKUP_DEF]
QED

Triviality populate_inst_key_closure[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st lbl j.
    (lbl, j) IN FDOM (df_populate_inst dir bottom join transfer edge_transfer
                        ctx entry_val cfg bbs lbls st).ds_inst /\
    ALL_DISTINCT lbls /\
    st.ds_inst = FEMPTY ==>
    (lbl, 0n) IN FDOM (df_populate_inst dir bottom join transfer edge_transfer
                         ctx entry_val cfg bbs lbls st).ds_inst
Proof
  rpt strip_tac >>
  (* Abbreviate the ds_inst result to avoid alpha-variant FOLDL issues *)
  qabbrev_tac `R = (df_populate_inst dir bottom join transfer edge_transfer
    ctx entry_val cfg bbs lbls st).ds_inst` >>
  gvs[populate_inst_ds_inst] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  qpat_x_assum `Abbrev (R = _)` mp_tac >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  strip_tac >>
  (* Now goal is (lbl,0) IN FDOM R, with R abbreviated.
     Hypothesis: (lbl,j) IN FDOM R and R = FOLDL ... FEMPTY ... *)
  qpat_x_assum `Abbrev (R = _)` (strip_assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qabbrev_tac `f = \l. SND (df_fold_block dir (transfer ctx) l
    (case lookup_block l bbs of NONE => [] | SOME bb => bb.bb_instructions)
    (df_joined_val dir bottom join edge_transfer ctx entry_val cfg st l))` >>
  `R = FOLDL (\acc l. FUNION (f l) acc) FEMPTY lbls` by
    (simp[Abbr `f`]) >>
  (* Step 1: find which f(l) contains (lbl,j) *)
  `?l. MEM l lbls /\ (lbl,j) IN FDOM (f l)` by (
    `(lbl,j) IN FDOM (FOLDL (\acc l. FUNION (f l) acc) FEMPTY lbls)` by
      fs[] >>
    drule foldl_funion_mem >> simp[]) >>
  suspend "main"
QED

Resume populate_inst_key_closure[main]:
  (* Case-split df_fold_block for l *)
  Cases_on `df_fold_block dir (transfer ctx) l
    (case lookup_block l bbs of NONE => [] | SOME bb => bb.bb_instructions)
    (df_joined_val dir bottom join edge_transfer ctx entry_val cfg st l)` >>
  rename1 `df_fold_block _ _ l _ _ = (fv_l, im_l)` >>
  `f l = im_l` by simp[Abbr `f`] >>
  (* Step 1: lbl = l *)
  `lbl = l` by (
    drule dfAnalyzeProofsTheory.df_fold_block_keys >>
    disch_then (qspec_then `(lbl,j)` mp_tac) >>
    simp[] >> impl_tac >- fs[FLOOKUP_DEF] >> simp[]) >>
  fs[] >> (* substitute lbl=l but keep im_l *)
  (* Step 2: (l,0) in im_l *)
  `(l, 0n) IN FDOM im_l` by (
    Cases_on `dir` >> fs[]
    >- (drule dfAnalyzeProofsTheory.df_fold_block_fdom >>
        simp[IN_IMAGE, IN_COUNT])
    >- (drule dfAnalyzeProofsTheory.df_fold_block_fdom_backward >>
        simp[IN_IMAGE, IN_COUNT])) >>
  (* Step 3: im_l = f l SUBMAP R, so (l,0) IN FDOM R *)
  `f l SUBMAP R` by (
    qpat_x_assum `R = FOLDL _ _ _` (fn th => REWRITE_TAC [th]) >>
    irule foldl_funion_submap >> simp[] >> rw[Abbr `f`] >>
    irule fold_block_keys_disjoint >> simp[]) >>
  `(l, 0n) IN FDOM (f l)` by fs[] >>
  metis_tac[SUBMAP_DEF, FLOOKUP_DEF]
QED

Finalise populate_inst_key_closure

(* df_process_block never modifies ds_inst *)
Triviality df_process_block_inst_unchanged[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st.
    (df_process_block dir bottom join transfer edge_transfer
       ctx entry_val cfg bbs lbl st).ds_inst = st.ds_inst
Proof
  rpt gen_tac >> simp[df_process_block_def] >>
  pairarg_tac >> simp[] >> rpt IF_CASES_TAC >> simp[]
QED

(* Helper: FOLDL |+ accumulates FDOM *)
Triviality foldl_fupdate_fdom[local]:
  !lbls (bottom : 'a) acc.
    FDOM (FOLDL (\m lbl. m |+ (lbl, bottom)) acc lbls) =
    FDOM acc UNION set lbls
Proof
  Induct >> simp[FDOM_FUPDATE] >>
  simp[EXTENSION] >> metis_tac[]
QED

(* init_df_state boundary contains all labels *)
Triviality init_df_state_boundary_fdom[local]:
  !bottom lbls.
    FDOM (init_df_state bottom lbls).ds_boundary = set lbls
Proof
  simp[init_df_state_def, foldl_fupdate_fdom]
QED

(* populate_inst_mem: key in populated ds_inst implies MEM label *)
Triviality populate_inst_mem[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st lbl j.
    (lbl, j) IN FDOM (df_populate_inst dir bottom join transfer edge_transfer
                        ctx entry_val cfg bbs lbls st).ds_inst /\
    (lbl, j) NOTIN FDOM st.ds_inst ==>
    MEM lbl lbls
Proof
  rpt strip_tac >>
  qpat_x_assum `_ IN FDOM _` mp_tac >>
  simp[populate_inst_ds_inst] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  qho_match_abbrev_tac `(lbl,j) IN FDOM (FOLDL (\acc l. FUNION (f l) acc)
    st.ds_inst lbls) ==> _` >>
  strip_tac >>
  drule foldl_funion_mem >> (impl_tac >- fs[]) >> strip_tac >>
  (* f(l) = SND(df_fold_block ...), and (lbl,j) IN FDOM (f l) *)
  Cases_on `df_fold_block dir (transfer ctx) l
    (case lookup_block l bbs of NONE => [] | SOME bb => bb.bb_instructions)
    (df_joined_val dir bottom join edge_transfer ctx entry_val cfg st l)` >>
  `f l = r` by simp[Abbr `f`] >>
  `lbl = l` by (
    drule dfAnalyzeProofsTheory.df_fold_block_keys >>
    disch_then (qspec_then `(lbl,j)` mp_tac) >>
    simp[] >> impl_tac >- fs[FLOOKUP_DEF] >> simp[]) >>
  gvs[]
QED

(* df_analyze_invariant_forward with Q = combined sccp invariant.
   Proves sccp_measure_inv, ds_inst = FEMPTY, and boundary FDOM in one shot. *)
local
  val base = INST_TYPE [alpha |-> ``:sccp_lattice``, beta |-> ``:ir_function``]
    (SIMP_RULE std_ss [LET_THM]
      dfAnalyzeProofsTheory.df_analyze_invariant_forward);
  val Q_var = mk_var("Q", ``:sccp_lattice df_state -> bool``);
  val fn_var = mk_var("fn", ``:ir_function``);
in
  val df_inv_fwd_combined = SPEC_ALL base
    |> INST [Q_var |-> ``\st:sccp_lattice df_state.
         sccp_measure_inv (^fn_var) st /\ st.ds_inst = FEMPTY /\
         set (MAP (\bb:basic_block. bb.bb_label) (^fn_var).fn_blocks) SUBSET
         FDOM st.ds_boundary``]
    |> SIMP_RULE bool_ss [] |> GEN_ALL;
end;

(* The measure invariant holds at the fixpoint. *)
Theorem sccp_measure_inv_at_fixpoint:
  !fn. wf_function fn ==>
    sccp_measure_inv fn (sccp_df_analyze fn)
Proof
  gen_tac >> strip_tac >>
  simp[sccp_df_analyze_def, df_analyze_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV)) >> simp[] >>
  qmatch_goalsub_abbrev_tac `df_populate_inst _ _ _ _ _ _ _ _ _ _ wl_result` >>
  (* Step 1: prove measure_inv, ds_inst = FEMPTY, and boundary FDOM for
     wl_result in one df_analyze_invariant_forward call *)
  (* Step 1: prove measure_inv, ds_inst = FEMPTY, and boundary FDOM
     for wl_result in one combined df_analyze_invariant_forward call *)
  `sccp_measure_inv fn wl_result /\ wl_result.ds_inst = FEMPTY /\
   set (MAP (\bb. bb.bb_label) fn.fn_blocks) SUBSET
   FDOM wl_result.ds_boundary` by (
    qunabbrev_tac `wl_result` >>
    irule df_inv_fwd_combined >>
    simp[df_process_block_inst_unchanged] >>
    rpt conj_tac
    (* bounded measure: sccp_measure_inv gives the bound *)
    >- (qexistsl_tac [`sccp_measure_bound fn`, `sccp_measure fn`] >>
        rpt conj_tac
        >- (rpt strip_tac >> irule sccp_measure_bounded >>
            fs[sccp_measure_inv_def])
        >> rpt gen_tac >> strip_tac >>
        irule sccp_measure_monotone >> fs[MEM_APPEND])
    (* preservation: measure_inv, boundary grows *)
    >- (rpt gen_tac >> strip_tac >> rpt conj_tac
        >- (irule sccp_measure_inv_preserved >> simp[])
        >> simp[df_process_block_def, LET_THM] >>
        pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[] >>
        fs[SUBSET_DEF, FDOM_FUPDATE])
    (* initial state: ds_inst = FEMPTY *)
    >- (Cases_on `fn_entry_label fn` >> simp[init_df_state_def])
    (* initial state: boundary FDOM *)
    >- (Cases_on `fn_entry_label fn` >>
        simp[init_df_state_boundary_fdom, FDOM_FUPDATE, SUBSET_DEF])
    (* initial state: sccp_measure_inv *)
    >> mp_tac (SPEC_ALL sccp_measure_inv_initial) >>
    Cases_on `fn_entry_label fn` >> simp[]) >>
  (* Step 2: populate preserves measure_inv *)
  qabbrev_tac `result = df_populate_inst Forward sccp_bottom sccp_join
    sccp_transfer_inst sccp_edge_transfer fn
    (OPTION_MAP (\lbl. (lbl,sccp_bottom)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks (MAP (\bb. bb.bb_label) fn.fn_blocks)
    wl_result` >>
  simp[sccp_measure_inv_def] >>
  conj_tac
  >- suspend "state_inv"
  >> simp[LET_THM] >>
  rpt conj_tac
  >- suspend "C3"
  >- suspend "C4"
  >> suspend "C5"
QED

Resume sccp_measure_inv_at_fixpoint[state_inv]:
  simp[sccp_state_inv_def] >> conj_tac
  (* boundary part: result.ds_boundary = wl_result.ds_boundary *)
  >- (qunabbrev_tac `result` >> simp[populate_inst_ds_boundary] >>
      fs[sccp_measure_inv_def, sccp_state_inv_def])
  (* inst part: each value in result.ds_inst satisfies FDOM bounds.
     result.ds_inst = FOLDL of fold results over FEMPTY.
     Each fold result satisfies bounds by sccp_fold_inv + sccp_joined_inv. *)
  >> rpt gen_tac >> disch_tac >>
  (* Unfold result abbreviation *)
  qpat_x_assum `Abbrev (result = _)` (mp_tac o
    REWRITE_RULE [markerTheory.Abbrev_def]) >>
  strip_tac >>
  qpat_x_assum `FLOOKUP result.ds_inst k = SOME lat` mp_tac >>
  qpat_x_assum `result = _` (fn th => REWRITE_TAC [th]) >>
  (* Derive MEM lbl *)
  strip_tac >>
  `MEM (FST k) (MAP (\bb. bb.bb_label) fn.fn_blocks)` by (
    Cases_on `k` >> gvs[] >>
    `(q,r) IN FDOM (df_populate_inst Forward sccp_bottom sccp_join
        sccp_transfer_inst sccp_edge_transfer fn
        (OPTION_MAP (\lbl. (lbl,sccp_bottom)) (fn_entry_label fn))
        (cfg_analyze fn) fn.fn_blocks
        (MAP (\bb. bb.bb_label) fn.fn_blocks) wl_result).ds_inst` by
      fs[FLOOKUP_DEF] >>
    drule populate_inst_mem >> simp[]) >>
  (* unfold to FOLDL *)
  qpat_x_assum `FLOOKUP (df_populate_inst _ _ _ _ _ _ _ _ _ _ _).ds_inst
                  k = SOME lat` mp_tac >>
  simp[populate_inst_ds_inst] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  qho_match_abbrev_tac `FLOOKUP (FOLDL (\acc l. FUNION (f l) acc) FEMPTY _)
                          k = SOME lat ==> _` >>
  strip_tac >>
  (* lat came from some f(l) for MEM l *)
  (* Use foldl_funion_flookup to find which f(l) contains k *)
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `!l1 l2. MEM l1 (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
            MEM l2 (MAP (\bb. bb.bb_label) fn.fn_blocks) /\ l1 <> l2 ==>
            DISJOINT (FDOM (f l1)) (FDOM (f l2))` by (
    rw[Abbr `f`] >> irule fold_block_keys_disjoint >> simp[]) >>
  drule_all foldl_funion_flookup >> strip_tac >>
  (* f(l) = SND(df_fold_block ...) and lat ∈ f(l), so lat satisfies P *)
  (* Decompose f(l) via Cases_on *)
  Cases_on `df_fold_block Forward (sccp_transfer_inst fn) l
    (case lookup_block l fn.fn_blocks of NONE => []
     | SOME bb => bb.bb_instructions)
    (df_joined_val Forward sccp_bottom sccp_join sccp_edge_transfer fn
       (OPTION_MAP (\lbl. (lbl,sccp_bottom)) (fn_entry_label fn))
       (cfg_analyze fn) wl_result l)` >>
  rename1 `df_fold_block _ _ l _ _ = (fv_l, im_l)` >>
  `f l = im_l` by simp[Abbr `f`] >>
  `FLOOKUP im_l k = SOME lat` by fs[] >>
  (* Convert df_joined_val to sccp_joined for sccp_fold_inv *)
  `df_joined_val Forward sccp_bottom sccp_join sccp_edge_transfer fn
     (OPTION_MAP (\lbl. (lbl,sccp_bottom)) (fn_entry_label fn))
     (cfg_analyze fn) wl_result l = sccp_joined fn wl_result l` by (
    simp[dfAnalyzeDefsTheory.df_joined_val_def, sccp_joined_def, LET_THM,
         dfAnalyzeDefsTheory.direction_case_def] >>
    Cases_on `fn_entry_label fn` >> simp[sccp_edge_transfer_def]) >>
  fs[] >>
  drule sccp_fold_inv >>
  disch_then (qspecl_then [`set (fn_all_assignments fn)`,
                            `set (fn_labels fn)`] mp_tac) >>
  `sccp_state_inv fn wl_result` by fs[sccp_measure_inv_def] >>
  simp[sccp_joined_inv] >>
  (impl_tac >- metis_tac[sccp_transfer_inv]) >>
  strip_tac >> res_tac >> simp[]
QED

Resume sccp_measure_inv_at_fixpoint[C3]:
  (* Goal: ∀lbl v0. FLOOKUP result.ds_inst (lbl,0) = SOME v0 ⇒
       ∀k v. FLOOKUP (SND(df_fold_block ...)) k = SOME v ⇒
             FLOOKUP result.ds_inst k = SOME v
     Why true: result.ds_inst = FOLDL of fold results. The fold for lbl
     with input joined_val is a SUBMAP of result. v0 = joined_val because
     df_fold_forward_at stores it at (lbl,0). So the fold with v0 is the
     same fold, and its result is a submap. *)
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  (* Derive MEM lbl from FLOOKUP result.ds_inst *)
  `MEM lbl (MAP (\bb. bb.bb_label) fn.fn_blocks)` by (
    `(lbl, 0n) IN FDOM result.ds_inst` by fs[flookup_thm] >>
    qpat_assum `Abbrev (result = _)` (strip_assume_tac o
      REWRITE_RULE [markerTheory.Abbrev_def]) >> fs[] >>
    drule populate_inst_mem >> simp[]) >>
  `?bb. lookup_block lbl fn.fn_blocks = SOME bb` by
    metis_tac[dfAnalyzeProofsTheory.lookup_block_exists] >>
  (* Unfold result to FOLDL form *)
  qpat_x_assum `Abbrev (result = _)` (mp_tac o
    REWRITE_RULE [markerTheory.Abbrev_def]) >> strip_tac >>
  qpat_x_assum `FLOOKUP result.ds_inst _ = SOME v0` mp_tac >>
  qpat_x_assum `result = _` (fn th => REWRITE_TAC [th]) >>
  simp[populate_inst_ds_inst] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  qho_match_abbrev_tac `FLOOKUP (FOLDL (\acc l. FUNION (f l) acc)
    FEMPTY _) _ = SOME _ ==> _` >>
  strip_tac >>
  (* f lbl is the fold result for lbl; it's a submap of the FOLDL *)
  `f lbl SUBMAP FOLDL (\acc l. FUNION (f l) acc) FEMPTY
     (MAP (\bb. bb.bb_label) fn.fn_blocks)` by (
    irule foldl_funion_submap >> simp[] >>
    rw[Abbr `f`] >> irule fold_block_keys_disjoint >> simp[]) >>
  (* Cases_on the fold for lbl *)
  Cases_on `df_fold_block Forward (sccp_transfer_inst fn) lbl
    bb.bb_instructions
    (df_joined_val Forward sccp_bottom sccp_join sccp_edge_transfer fn
       (OPTION_MAP (\lbl. (lbl,sccp_bottom)) (fn_entry_label fn))
       (cfg_analyze fn) wl_result lbl)` >>
  rename1 `df_fold_block _ _ lbl _ _ = (fv_pop, im_pop)` >>
  `f lbl = im_pop` by simp[Abbr `f`] >>
  (* df_fold_forward_at: FLOOKUP im_pop (lbl,0) = SOME joined_val *)
  `FLOOKUP im_pop (lbl, 0n) = SOME
    (df_joined_val Forward sccp_bottom sccp_join sccp_edge_transfer fn
       (OPTION_MAP (\lbl. (lbl,sccp_bottom)) (fn_entry_label fn))
       (cfg_analyze fn) wl_result lbl)` by (
    drule df_fold_block_at_zero >> simp[]) >>
  (* From submap: same FLOOKUP in the FOLDL *)
  `FLOOKUP (FOLDL (\acc l. FUNION (f l) acc) FEMPTY
     (MAP (\bb. bb.bb_label) fn.fn_blocks)) (lbl, 0n) = SOME
    (df_joined_val Forward sccp_bottom sccp_join sccp_edge_transfer fn
       (OPTION_MAP (\lbl. (lbl,sccp_bottom)) (fn_entry_label fn))
       (cfg_analyze fn) wl_result lbl)` by
    metis_tac[SUBMAP_FLOOKUP_EQN] >>
  (* v0 = joined_val *)
  `v0 = df_joined_val Forward sccp_bottom sccp_join sccp_edge_transfer fn
     (OPTION_MAP (\lbl. (lbl,sccp_bottom)) (fn_entry_label fn))
     (cfg_analyze fn) wl_result lbl` by fs[] >>
  fs[] >>
  (* v0 = joined_val, so the outer fold with v0 IS f(lbl) = im_pop.
     im_pop SUBMAP FOLDL, so FLOOKUP in FOLDL follows from FLOOKUP in im_pop *)
  metis_tac[SUBMAP_FLOOKUP_EQN]
QED

Resume sccp_measure_inv_at_fixpoint[C4]:
  (* Goal: (lbl,j) ∈ FDOM result.ds_inst ⇒ (lbl,0) ∈ FDOM result.ds_inst *)
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `Abbrev (result = _)` (strip_assume_tac o
    REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `result = _` (fn th =>
    fs[th] >> assume_tac (SYM th)) >>
  irule populate_inst_key_closure >>
  gvs[wf_function_def, fn_labels_def] >>
  metis_tac[]
QED

Resume sccp_measure_inv_at_fixpoint[C5]:
  (* Goal: (lbl,0) ∈ FDOM result.ds_inst ⇒ lbl ∈ FDOM result.ds_boundary *)
  rpt gen_tac >> strip_tac >>
  (* result.ds_boundary = wl_result.ds_boundary *)
  `result.ds_boundary = wl_result.ds_boundary` by
    (qunabbrev_tac `result` >> simp[populate_inst_ds_boundary]) >>
  simp[] >>
  (* (lbl,0) ∈ FDOM result.ds_inst implies MEM lbl (MAP ...) *)
  `MEM lbl (MAP (\bb. bb.bb_label) fn.fn_blocks)` by (
    qpat_assum `Abbrev (result = _)` (strip_assume_tac o
      REWRITE_RULE [markerTheory.Abbrev_def]) >> fs[] >>
    drule populate_inst_mem >> simp[]) >>
  (* boundary FDOM already proved in Step 1 *)
  fs[SUBSET_DEF]
QED

Finalise sccp_measure_inv_at_fixpoint

(* Corollary: domain of analysis is bounded by fn_all_assignments. *)
Theorem sccp_state_inv_at_fixpoint:
  !fn. wf_function fn ==>
    sccp_state_inv fn (sccp_df_analyze fn)
Proof
  rpt strip_tac >>
  imp_res_tac sccp_measure_inv_at_fixpoint >>
  fs[sccp_measure_inv_def]
QED

