(*
 * Variable Definition Analysis — Internal Proofs
 *
 * Consumers import it through varDefAnalysisScript.sml.
 *)

Theory varDefProofs
Ancestors
  dfAnalyzeProofs varDefDefs cfgAnalysisProps dfAnalyzeProps venomWf cfgCorrectnessProof dfHelperProofs dfHelperDefs

(* ===== Convergence infrastructure ===== *)

(* Total instruction slots: each block with n instructions has n+1 slots
   (one per instruction boundary, including the post-block value) *)
Definition vardef_total_inst_slots_def:
  vardef_total_inst_slots fn =
    SUM (MAP (\bb. LENGTH bb.bb_instructions + 1) fn.fn_blocks)
End

(* Valid instruction keys: all (label, index) pairs for a function.
   Uses IMAGE + count to avoid set comprehension representation issues. *)
Definition vardef_valid_inst_keys_def:
  vardef_valid_inst_keys fn =
    BIGUNION (set (MAP (\bb.
       IMAGE (\i. (bb.bb_label, i)) (count (LENGTH bb.bb_instructions + 1)))
                      fn.fn_blocks))
End

(* Compute the joined value for a label from current state *)
Definition vardef_joined_def:
  vardef_joined fn st lbl =
    let all_vars = fn_all_assignments fn in
    let cfg = cfg_analyze fn in
    let edge_vals = MAP (\nbr. df_boundary all_vars st nbr)
                        (cfg_preds_of cfg lbl) in
    let base = (case edge_vals of
                  [] => all_vars
                | _ => FOLDL list_intersect all_vars edge_vals) in
    case fn_entry_label fn of
      NONE => base
    | SOME ev_lbl =>
        if lbl = ev_lbl then list_intersect [] base else base
End

(* State invariant for convergence:
   - Boundary values are ALL_DISTINCT subsets of all_vars
   - FDOM ds_inst ⊆ valid keys (ensures CARD bounded by total_slots)
   - Inst values are subsets of all_vars (enables set-cardinality complement)
   - For each processed label, current joined ⊆ stored v0
     (enables inst_complement non-decrease in measure_increases)
   - ds_inst values at lbl keys match a fold from ds_inst(lbl, 0)
     (enables fold comparison for inst_complement monotonicity) *)
Definition vardef_state_inv_def:
  vardef_state_inv fn (st : string list df_state) <=>
    let all_vars = fn_all_assignments fn in
    (!lbl v. FLOOKUP st.ds_boundary lbl = SOME v ==>
       ALL_DISTINCT v /\ set v SUBSET set all_vars) /\
    FDOM st.ds_inst SUBSET vardef_valid_inst_keys fn /\
    (!k v. FLOOKUP st.ds_inst k = SOME v ==>
       set v SUBSET set all_vars) /\
    (!lbl v0. FLOOKUP st.ds_inst (lbl, 0n) = SOME v0 ==>
       set (vardef_joined fn st lbl) SUBSET set v0) /\
    (!lbl v0. FLOOKUP st.ds_inst (lbl, 0n) = SOME v0 ==>
       !k v. FLOOKUP (SND (df_fold_block Forward (vardef_transfer ())
                lbl (case lookup_block lbl fn.fn_blocks of
                       NONE => [] | SOME bb => bb.bb_instructions) v0))
              k = SOME v ==>
         FLOOKUP st.ds_inst k = SOME v) /\
    (!lbl v0. FLOOKUP st.ds_inst (lbl, 0n) = SOME v0 ==>
       ?P. v0 = FILTER P all_vars) /\
    (!lbl j. (lbl, j) IN FDOM st.ds_inst ==>
       (lbl, 0n) IN FDOM st.ds_inst) /\
    (!lbl. (lbl, 0n) IN FDOM st.ds_inst ==>
       lbl IN FDOM st.ds_boundary)
End

(* Inst complement: sum over all FDOM keys of
   (CARD(set all_vars) - CARD(set value)). Captures how much room
   remains for values to shrink in the set ordering. *)
Definition vardef_inst_complement_def:
  vardef_inst_complement fn (st : string list df_state) =
    let all_vars = fn_all_assignments fn in
    SIGMA (\k. CARD (set all_vars) -
               CARD (set (THE (FLOOKUP st.ds_inst k)))) (FDOM st.ds_inst)
End

(* Measure: boundary complement sum + inst complement + FDOM size.
   Three components handle all ways the state can change:
   1. Boundary shrinks at some label → boundary complement increases
   2. Inst values shrink (set-wise) → inst complement increases
   3. First-time processing adds new inst keys → CARD increases
   Case "boundary unchanged, FDOM unchanged, values unchanged" is
   impossible — proved via FILTER characterization (filter_set_eq_filter_eq)
   and invariant C6 (v0 is a FILTER of all_vars). *)
Definition vardef_measure_def:
  vardef_measure fn (st : string list df_state) =
    let all_vars = fn_all_assignments fn in
    let labels = fn_labels fn in
    SUM (MAP (\lbl. LENGTH all_vars -
                    LENGTH (df_boundary all_vars st lbl)) labels) +
    vardef_inst_complement fn st +
    CARD (FDOM st.ds_inst)
End

(* Measure upper bound *)
Definition vardef_measure_bound_def:
  vardef_measure_bound fn =
    let all_vars = fn_all_assignments fn in
    let labels = fn_labels fn in
    let total_slots = vardef_total_inst_slots fn in
    LENGTH all_vars * LENGTH labels +
    CARD (set all_vars) * total_slots +
    total_slots
End

(* ===== Valid inst keys infrastructure ===== *)

(* Valid inst keys is finite *)
Theorem valid_inst_keys_finite[local]:
  !fn. FINITE (vardef_valid_inst_keys fn)
Proof
  rw[vardef_valid_inst_keys_def, listTheory.MEM_MAP] >>
  rw[pred_setTheory.IMAGE_FINITE]
QED

(* Valid inst keys CARD ≤ total_slots *)
Theorem valid_inst_keys_card[local]:
  !fn. CARD (vardef_valid_inst_keys fn) <= vardef_total_inst_slots fn
Proof
  rw[vardef_valid_inst_keys_def, vardef_total_inst_slots_def,
     dfAnalyzeProofsTheory.bigunion_image_card_le_sum]
QED

(* FDOM of fold result ⊆ valid_inst_keys when label is in fn_blocks *)
Theorem df_fold_block_fdom_subset[local]:
  !fn lbl bb init_val fv im.
    MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\
    df_fold_block Forward (vardef_transfer ()) lbl
      bb.bb_instructions init_val = (fv, im) ==>
    FDOM im SUBSET vardef_valid_inst_keys fn
Proof
  rw[] >> drule dfAnalyzeProofsTheory.df_fold_block_fdom >> rw[] >>
  rw[vardef_valid_inst_keys_def, pred_setTheory.SUBSET_DEF,
     pred_setTheory.IN_BIGUNION, listTheory.MEM_MAP,
     pred_setTheory.IN_IMAGE, pred_setTheory.IN_COUNT] >>
  qexists_tac `IMAGE (\i. (bb.bb_label, i))
    (count (LENGTH bb.bb_instructions + 1))` >>
  rw[pred_setTheory.IN_IMAGE, pred_setTheory.IN_COUNT] >>
  qexists_tac `bb` >> rw[]
QED

(* ===== Convergence helper lemmas ===== *)

(* df_boundary length ≤ LENGTH all_vars (from ALL_DISTINCT + subset) *)
Theorem df_boundary_length_le[local]:
  !fn st lbl.
    vardef_state_inv fn st ==>
    LENGTH (df_boundary (fn_all_assignments fn) st lbl) <=
    LENGTH (fn_all_assignments fn)
Proof
  rw[dfAnalyzeDefsTheory.df_boundary_def, vardef_state_inv_def, LET_THM] >>
  Cases_on `FLOOKUP st.ds_boundary lbl` >> simp[] >>
  res_tac >>
  `FINITE (set (fn_all_assignments fn))` by
    rw[listTheory.FINITE_LIST_TO_SET] >>
  `CARD (set x) <= CARD (set (fn_all_assignments fn))` by
    metis_tac[pred_setTheory.CARD_SUBSET] >>
  `CARD (set x) = LENGTH x` by
    metis_tac[listTheory.ALL_DISTINCT_CARD_LIST_TO_SET] >>
  `CARD (set (fn_all_assignments fn)) <= LENGTH (fn_all_assignments fn)` by
    rw[listTheory.CARD_LIST_TO_SET] >>
  DECIDE_TAC
QED

(* CARD(FDOM ds_inst) ≤ total_slots under invariant *)
Triviality fdom_card_le_slots:
  !fn st. vardef_state_inv fn st ==>
    CARD (FDOM st.ds_inst) <= vardef_total_inst_slots fn
Proof
  rw[vardef_state_inv_def, LET_THM] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `CARD (vardef_valid_inst_keys fn)` >>
  rw[valid_inst_keys_card] >>
  irule pred_setTheory.CARD_SUBSET >>
  rw[valid_inst_keys_finite]
QED

(* inst_complement ≤ C * total_slots under invariant *)
Triviality inst_complement_bounded:
  !fn st. vardef_state_inv fn st ==>
    vardef_inst_complement fn st <=
    CARD (set (fn_all_assignments fn)) * vardef_total_inst_slots fn
Proof
  rw[vardef_inst_complement_def, LET_THM] >>
  `!k. k IN FDOM st.ds_inst ==>
     CARD (set (fn_all_assignments fn)) -
     CARD (set (THE (FLOOKUP st.ds_inst k))) <=
     CARD (set (fn_all_assignments fn))` by rw[] >>
  `SIGMA (\k. CARD (set (fn_all_assignments fn)) -
              CARD (set (THE (FLOOKUP st.ds_inst k)))) (FDOM st.ds_inst) <=
   SIGMA (\k. CARD (set (fn_all_assignments fn))) (FDOM st.ds_inst)` by
    (irule pred_setTheory.SUM_IMAGE_MONO_LESS_EQ >> rw[]) >>
  `CARD (FDOM st.ds_inst) <= vardef_total_inst_slots fn` by
    metis_tac[fdom_card_le_slots] >>
  `(\k:string#num. CARD (set (fn_all_assignments fn))) =
   K (CARD (set (fn_all_assignments fn)))` by
    rw[FUN_EQ_THM, combinTheory.K_DEF] >>
  fs[pred_setTheory.SUM_IMAGE_CONSTANT] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `CARD (set (fn_all_assignments fn)) *
               CARD (FDOM st.ds_inst)` >>
  simp[]
QED

(* Measure bounded: m st ≤ bound *)
Theorem vardef_measure_bounded[local]:
  !fn st. vardef_state_inv fn st ==>
    vardef_measure fn st <= vardef_measure_bound fn
Proof
  rw[vardef_measure_def, vardef_measure_bound_def, LET_THM] >>
  `SUM (MAP (\lbl. LENGTH (fn_all_assignments fn) -
       LENGTH (df_boundary (fn_all_assignments fn) st lbl))
       (fn_labels fn)) <=
   LENGTH (fn_all_assignments fn) * LENGTH (fn_labels fn)` by
    (irule dfAnalyzeProofsTheory.sum_map_le_bound >> rw[listTheory.EVERY_MEM] >>
     metis_tac[df_boundary_length_le]) >>
  `vardef_inst_complement fn st <=
   CARD (set (fn_all_assignments fn)) * vardef_total_inst_slots fn` by
    metis_tac[inst_complement_bounded] >>
  `CARD (FDOM st.ds_inst) <= vardef_total_inst_slots fn` by
    metis_tac[fdom_card_le_slots] >>
  DECIDE_TAC
QED

(* df_boundary ALL_DISTINCT under invariant *)
Theorem df_boundary_all_distinct[local]:
  !fn st lbl.
    vardef_state_inv fn st ==>
    ALL_DISTINCT (df_boundary (fn_all_assignments fn) st lbl)
Proof
  rw[dfAnalyzeDefsTheory.df_boundary_def, vardef_state_inv_def, LET_THM] >>
  Cases_on `FLOOKUP st.ds_boundary lbl` >> simp[] >>
  res_tac >>
  rw[listTheory.all_distinct_nub, venomInstTheory.fn_all_assignments_def]
QED

(* df_boundary set ⊆ all_vars under invariant *)
Theorem df_boundary_subset[local]:
  !fn st lbl.
    vardef_state_inv fn st ==>
    set (df_boundary (fn_all_assignments fn) st lbl) SUBSET
    set (fn_all_assignments fn)
Proof
  rw[dfAnalyzeDefsTheory.df_boundary_def, vardef_state_inv_def, LET_THM] >>
  Cases_on `FLOOKUP st.ds_boundary lbl` >> simp[] >>
  res_tac
QED

(* lookup_block lbl bbs = SOME bb ==> MEM bb bbs /\ bb.bb_label = lbl *)
Triviality lookup_block_mem:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  rw[venomInstTheory.lookup_block_def] >> drule venomInstTheory.FIND_MEM >> simp[]
QED

Triviality lookup_block_label:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  rw[venomInstTheory.lookup_block_def] >> drule venomInstTheory.FIND_P >> simp[]
QED

(* vardef_joined monotonicity: shrinking a boundary preserves joined ⊆. *)
Triviality vardef_joined_boundary_mono:
  !fn st lbl new_bv lbl'.
    set new_bv SUBSET set (df_boundary (fn_all_assignments fn) st lbl) ==>
    set (vardef_joined fn
       (st with ds_boundary := st.ds_boundary |+ (lbl, new_bv)) lbl')
    SUBSET set (vardef_joined fn st lbl')
Proof
  rw[vardef_joined_def, LET_THM] >>
  (* Establish pointwise boundary subset *)
  `!nbr. set (df_boundary (fn_all_assignments fn)
     (st with ds_boundary := st.ds_boundary |+ (lbl, new_bv)) nbr)
   SUBSET set (df_boundary (fn_all_assignments fn) st nbr)` by
    (gen_tac >> simp[dfAnalyzeDefsTheory.df_boundary_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
     rw[] >> fs[dfAnalyzeDefsTheory.df_boundary_def]) >>
  Cases_on `fn_entry_label fn` >> simp[]
  >- ((* NONE: same as old proof *)
      Cases_on `cfg_preds_of (cfg_analyze fn) lbl'` >> simp[] >>
      irule pred_setTheory.SUBSET_TRANS >>
      qexists_tac `set (FOLDL list_intersect
        (list_intersect (fn_all_assignments fn)
           (df_boundary (fn_all_assignments fn) st h))
        (MAP (\nbr. df_boundary (fn_all_assignments fn)
           (st with ds_boundary := st.ds_boundary |+ (lbl,new_bv)) nbr) t))` >>
      conj_tac
      >- (irule foldl_list_intersect_acc_mono >>
          rw[list_intersect_set, pred_setTheory.SUBSET_DEF,
             pred_setTheory.IN_INTER] >>
          metis_tac[pred_setTheory.SUBSET_DEF])
      >- (irule foldl_list_intersect_mono >>
          rw[listTheory.EL_MAP] >> metis_tac[]))
  >> (* SOME ev_lbl *)
  IF_CASES_TAC >> simp[]
  >- ((* lbl' = ev_lbl: list_intersect [] _ = [] ⊆ anything *)
      simp[dfHelperDefsTheory.list_intersect_def])
  >> (* lbl' ≠ ev_lbl: same as NONE *)
  Cases_on `cfg_preds_of (cfg_analyze fn) lbl'` >> simp[] >>
  irule pred_setTheory.SUBSET_TRANS >>
  qexists_tac `set (FOLDL list_intersect
    (list_intersect (fn_all_assignments fn)
       (df_boundary (fn_all_assignments fn) st h))
    (MAP (\nbr. df_boundary (fn_all_assignments fn)
       (st with ds_boundary := st.ds_boundary |+ (lbl,new_bv)) nbr) t))` >>
  conj_tac
  >- (irule foldl_list_intersect_acc_mono >>
      rw[list_intersect_set, pred_setTheory.SUBSET_DEF,
         pred_setTheory.IN_INTER] >>
      metis_tac[pred_setTheory.SUBSET_DEF])
  >- (irule foldl_list_intersect_mono >>
      rw[listTheory.EL_MAP] >> metis_tac[])
QED

(* Bridge: df_process_block for vardef = fold from vardef_joined *)
Triviality vardef_process_eq:
  !fn lbl st.
    df_process_block Forward (fn_all_assignments fn) list_intersect
      vardef_transfer vardef_edge_transfer ()
      (OPTION_MAP (\lbl. (lbl, [] : string list)) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks lbl st =
    let instrs = case lookup_block lbl fn.fn_blocks of
                   NONE => [] | SOME bb => bb.bb_instructions in
    let (fv, inst_map) = df_fold_block Forward (vardef_transfer ()) lbl
                           instrs (vardef_joined fn st lbl) in
    let new_bnd = list_intersect
                    (df_boundary (fn_all_assignments fn) st lbl) fv in
      if new_bnd = df_boundary (fn_all_assignments fn) st lbl then st
      else st with ds_boundary := st.ds_boundary |+ (lbl, new_bnd)
Proof
  rw[dfAnalyzeDefsTheory.df_process_block_def,
     dfAnalyzeDefsTheory.df_joined_val_def] >>
  simp_tac std_ss [LET_THM, dfAnalyzeDefsTheory.direction_case_def] >>
  rw[varDefDefsTheory.vardef_edge_transfer_def] >>
  simp[vardef_joined_def, LET_THM] >>
  Cases_on `fn_entry_label fn` >> simp[]
QED

(* MEM lbl labels ==> lookup_block finds a block *)
Triviality lookup_block_exists:
  !lbl bbs. MEM lbl (MAP (\bb. bb.bb_label) bbs) ==>
    ?bb. lookup_block lbl bbs = SOME bb
Proof
  Induct_on `bbs` >>
  rw[venomInstTheory.lookup_block_def, listTheory.FIND_thm] >>
  `?bb. lookup_block lbl bbs = SOME bb` by metis_tac[] >>
  fs[venomInstTheory.lookup_block_def]
QED

(* vardef_state_inv is preserved by df_process_block *)
Theorem vardef_inv_preserved[local]:
  !fn lbl st.
    wf_function fn /\ MEM lbl (fn_labels fn) /\ vardef_state_inv fn st ==>
    vardef_state_inv fn
      (df_process_block Forward (fn_all_assignments fn) list_intersect
         vardef_transfer vardef_edge_transfer ()
         (OPTION_MAP (\lbl. (lbl, [] : string list)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt strip_tac >>
  rewrite_tac[vardef_process_eq] >> simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >- simp[] >>
  simp_tac (srw_ss()) [vardef_state_inv_def, LET_THM,
    finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FDOM_FUPDATE] >>
  qpat_assum `vardef_state_inv fn st`
    (strip_assume_tac o SIMP_RULE std_ss [vardef_state_inv_def, LET_THM]) >>
  rpt conj_tac
  >- suspend "C1"
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- suspend "C4"
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >> suspend "C8"
QED

Resume vardef_inv_preserved[C1]:
  rpt gen_tac >> IF_CASES_TAC >> simp[] >> strip_tac
  (* lbl = lbl': v = list_intersect (df_boundary ...) fv *)
  >- (gvs[] >> conj_tac
      >- (irule list_intersect_all_distinct >>
          irule df_boundary_all_distinct >> first_assum ACCEPT_TAC)
      >> simp[list_intersect_set] >>
      irule pred_setTheory.SUBSET_TRANS >>
      qexists `set (df_boundary (fn_all_assignments fn) st lbl)` >>
      simp[pred_setTheory.INTER_SUBSET] >>
      irule df_boundary_subset >> first_assum ACCEPT_TAC)
  (* lbl ≠ lbl': exact match with C1 assumption *)
  >> qpat_x_assum `!l v. FLOOKUP st.ds_boundary l = SOME v ==> _`
       (drule_then strip_assume_tac) >> simp[]
QED

Resume vardef_inv_preserved[C4]:
  rpt gen_tac >> strip_tac >>
  irule pred_setTheory.SUBSET_TRANS >>
  qexists `set (vardef_joined fn st lbl')` >> conj_tac
  >- (irule vardef_joined_boundary_mono >>
      simp[list_intersect_set, pred_setTheory.INTER_SUBSET])
  >> res_tac
QED

Resume vardef_inv_preserved[C8]:
  rpt strip_tac >>
  qpat_x_assum `!lbl. _ ==> lbl IN FDOM _` (drule_then assume_tac) >>
  simp[]
QED

Finalise vardef_inv_preserved

(* ===== Measure increases helpers ===== *)

(* ===== Measure increases ===== *)

(* Boundary length at any label: boundary-only update ≤ old state *)
Triviality df_boundary_len_mono:
  !fn st lbl new_bv fv x.
    Abbrev (new_bv = list_intersect
              (df_boundary (fn_all_assignments fn) st lbl) fv) ==>
    LENGTH (df_boundary (fn_all_assignments fn)
              (st with ds_boundary := st.ds_boundary |+ (lbl, new_bv)) x) <=
    LENGTH (df_boundary (fn_all_assignments fn) st x)
Proof
  rpt strip_tac >>
  simp[dfAnalyzeDefsTheory.df_boundary_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `x = lbl` >> simp[] >>
  fs[markerTheory.Abbrev_def, dfAnalyzeDefsTheory.df_boundary_def] >>
  metis_tac[list_intersect_length_le]
QED

(* SML-level instantiations of sum_complement_mono/strict for the
   measure proof. Boundary-only update (no ds_inst change). *)
val new_st_tm_ = ``(st : string list df_state) with
                     ds_boundary := st.ds_boundary |+ (lbl,new_bv)``;
val bdy_f_ = ``\(x:string). LENGTH
                (df_boundary (fn_all_assignments fn)
                             (st : string list df_state) x) : num``;
val bdy_g_ = ``\(x:string). LENGTH
                (df_boundary (fn_all_assignments fn) ^new_st_tm_ x) : num``;
val bdy_n_ = ``LENGTH (fn_all_assignments fn) : num``;
val bdy_ls_ = ``fn_labels fn : string list``;

val sum_complement_mono_inst = sum_complement_mono
  |> INST_TYPE [alpha |-> ``:string``]
  |> SPECL [bdy_f_, bdy_g_, bdy_n_, bdy_ls_]
  |> SIMP_RULE std_ss [];

val sum_complement_strict_inst = sum_complement_strict
  |> INST_TYPE [alpha |-> ``:string``]
  |> SPECL [bdy_f_, bdy_g_, bdy_n_, bdy_ls_, ``lbl : string``]
  |> SIMP_RULE std_ss [];

(* When processing a label changes the state, the measure strictly increases.
   Since ds_inst is never modified by df_process_block, only the boundary
   SUM component changes. inst_complement and CARD(FDOM ds_inst) cancel. *)
Theorem vardef_measure_increases[local]:
  !fn lbl st.
    let process = df_process_block Forward (fn_all_assignments fn)
                    list_intersect vardef_transfer vardef_edge_transfer ()
                    (OPTION_MAP (\lbl. (lbl, [] : string list))
                       (fn_entry_label fn))
                    (cfg_analyze fn) fn.fn_blocks in
    wf_function fn /\ MEM lbl (fn_labels fn) /\
    vardef_state_inv fn st /\ process lbl st <> st ==>
    vardef_measure fn st < vardef_measure fn (process lbl st)
Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  rewrite_tac[vardef_process_eq] >> simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  qabbrev_tac `old_bv = df_boundary (fn_all_assignments fn) st lbl` >>
  qabbrev_tac `new_bv = list_intersect old_bv fv` >>
  (* IF-true: process = st, contradicts assumption *)
  IF_CASES_TAC
  >- (qpat_x_assum `_ <> st` mp_tac >> simp[] >>
      rewrite_tac[vardef_process_eq] >> simp_tac std_ss [LET_THM] >>
      qpat_x_assum `df_fold_block _ _ _ _ _ = _`
        (fn th => simp[th]) >>
      fs[markerTheory.Abbrev_def])
  >>
  (* IF-false: only ds_boundary updated. ds_inst unchanged so
     inst_complement and CARD cancel. Only boundary SUM is strict. *)
  simp_tac std_ss [vardef_measure_def, LET_THM] >>
  simp[] >>
  (* inst_complement and CARD(FDOM) are equal on both sides *)
  `vardef_inst_complement fn
     (st with ds_boundary := st.ds_boundary |+ (lbl, new_bv)) =
   vardef_inst_complement fn st` by
    simp[vardef_inst_complement_def, LET_THM] >>
  simp[] >>
  (* Reduce to: boundary SUM strictly increases *)
  match_mp_tac sum_complement_strict_inst >> rpt conj_tac
  >- simp[]  (* MEM lbl *)
  >- ((* strict: boundary at lbl is strictly shorter *)
      `ALL_DISTINCT old_bv` by
        (fs[markerTheory.Abbrev_def] >>
         metis_tac[df_boundary_all_distinct]) >>
      `new_bv <> old_bv` by fs[markerTheory.Abbrev_def] >>
      `LENGTH new_bv < LENGTH old_bv` by
        (fs[markerTheory.Abbrev_def] >>
         metis_tac[dfHelperProofsTheory.list_intersect_strict_length]) >>
      simp[dfAnalyzeDefsTheory.df_boundary_def,
           finite_mapTheory.FLOOKUP_UPDATE] >>
      fs[markerTheory.Abbrev_def, dfAnalyzeDefsTheory.df_boundary_def] >>
      qpat_x_assum `old_bv = _` (fn th => REWRITE_TAC [GSYM th]) >>
      simp[])
  >- metis_tac[df_boundary_length_le]
  >> rpt gen_tac >> strip_tac >> conj_tac
  >- (irule df_boundary_len_mono >>
      qexists `fv` >> fs[markerTheory.Abbrev_def])
  >> metis_tac[df_boundary_length_le]
QED

(* ===== Shared convergence helpers ===== *)

(* dfs_pre labels are in fn_labels *)
Triviality dfs_pre_in_fn_labels[local]:
  !fn. wf_function fn ==>
    EVERY (\lbl. MEM lbl (fn_labels fn)) (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  `!lbl. MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
         MEM lbl (fn_labels fn)` suffices_by
    simp[listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  `set (cfg_analyze fn).cfg_dfs_post = set (cfg_analyze fn).cfg_dfs_pre /\
   set (cfg_analyze fn).cfg_dfs_post =
   {lbl | cfg_reachable_of (cfg_analyze fn) lbl}` by
    metis_tac[cfgAnalysisPropsTheory.cfg_analyze_reachable_sets] >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by
    (fs[pred_setTheory.EXTENSION, pred_setTheory.GSPECIFICATION] >>
     metis_tac[listTheory.MEM]) >>
  metis_tac[cfgCorrectnessProofTheory.cfg_analyze_reachable_in_labels]
QED

(* Initial state satisfies vardef_state_inv *)
Triviality vardef_init_state_inv[local]:
  !fn.
    wf_function fn ==>
    case OPTION_MAP (\lbl. (lbl, [] : string list)) (fn_entry_label fn) of
      NONE => vardef_state_inv fn
        (init_df_state (fn_all_assignments fn)
           (MAP (\bb. bb.bb_label) fn.fn_blocks))
    | SOME (lbl,v) => vardef_state_inv fn
        (init_df_state (fn_all_assignments fn)
           (MAP (\bb. bb.bb_label) fn.fn_blocks) with
         ds_boundary :=
           (init_df_state (fn_all_assignments fn)
              (MAP (\bb. bb.bb_label) fn.fn_blocks)).ds_boundary |+ (lbl,v))
Proof
  rpt strip_tac >>
  simp[vardef_state_inv_def, LET_THM,
       dfAnalyzeDefsTheory.init_df_state_def,
       venomInstTheory.fn_entry_label_def] >>
  Cases_on `entry_block fn` >> simp[] >> rpt gen_tac >> strip_tac >> (
    (* Both cases: decompose FLOOKUP |+ for SOME, then resolve v *)
    TRY (qpat_x_assum `FLOOKUP (_ |+ _) _ = _`
           (mp_tac o REWRITE_RULE [finite_mapTheory.FLOOKUP_UPDATE]) >>
         IF_CASES_TAC >> simp[] >> strip_tac) >>
    (* FLOOKUP(FOLDL ... FEMPTY labels) _ = SOME v => v = fn_all_assignments *)
    imp_res_tac dfAnalyzeProofsTheory.foldl_fempty_val >>
    simp[listTheory.all_distinct_nub,
         venomInstTheory.fn_all_assignments_def])
QED

(* ===== Fixpoint ===== *)

val fixpoint_restricted_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_analyze_fixpoint_process_restricted));

Theorem vardef_fixpoint:
  !fn.
    wf_function fn ==>
    let cfg = cfg_analyze fn in
    let all_vars = fn_all_assignments fn in
    let entry_val =
      OPTION_MAP (λlbl. (lbl, [] : string list)) (fn_entry_label fn) in
    let process = df_process_block Forward all_vars list_intersect
                    vardef_transfer vardef_edge_transfer ()
                    entry_val cfg fn.fn_blocks in
    is_fixpoint process cfg.cfg_dfs_pre (vardef_analyze fn)
Proof
  rpt strip_tac >>
  simp_tac std_ss [LET_THM, varDefDefsTheory.vardef_analyze_def] >>
  irule fixpoint_restricted_fwd >>
  conj_tac
  >- ((* Existential witnesses *)
      qexistsl_tac [`vardef_state_inv fn`,
                     `vardef_measure_bound fn`,
                     `vardef_measure fn`,
                     `\lbl. MEM lbl (fn_labels fn)`] >>
      rpt conj_tac
      >- rw[vardef_measure_bounded]
      >- (rpt strip_tac >> fs[] >>
          metis_tac[vardef_inv_preserved])
      >- (rpt strip_tac >> fs[] >>
          metis_tac[vardef_measure_increases])
      >- (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
          metis_tac[cfgCorrectnessProofTheory.cfg_analyze_succ_labels])
      >- metis_tac[dfs_pre_in_fn_labels]
      >- metis_tac[vardef_init_state_inv])
  >>
  (* wl_deps_complete *)
  match_mp_tac (SIMP_RULE std_ss [LET_THM]
    dfAnalyzeProofsTheory.df_process_deps_complete_proof |>
    SPEC ``Forward : direction`` |>
    SIMP_RULE std_ss [dfAnalyzeDefsTheory.direction_case_def]) >>
  rw[list_intersect_absorption] >>
  metis_tac[cfg_edge_symmetry_uncond]
QED

(* ===== Boundedness ===== *)

Theorem vardef_out_bounded:
  !fn lbl v.
    wf_function fn /\
    MEM v (vardef_out_of fn lbl) ==>
    MEM v (fn_all_assignments fn)
Proof
  rpt strip_tac >>
  fs[varDefDefsTheory.vardef_out_of_def] >>
  `EVERY (\v. MEM v (fn_all_assignments fn))
     (df_boundary (fn_all_assignments fn) (vardef_analyze fn) lbl)`
    suffices_by (rw[listTheory.EVERY_MEM]) >>
  simp_tac std_ss [varDefDefsTheory.vardef_analyze_def, LET_THM] >>
  irule (SIMP_RULE std_ss [LET_THM]
    dfAnalyzeProofsTheory.df_analyze_boundary_invariant_restricted) >>
  rpt conj_tac
  >- simp[listTheory.EVERY_MEM]
  >- (rpt strip_tac >>
      fs[dfHelperDefsTheory.list_intersect_def, listTheory.EVERY_MEM,
         listTheory.MEM_FILTER])
  >- (Cases_on `fn_entry_label fn` >> simp[])
  >> qexistsl_tac [`vardef_state_inv fn`, `vardef_measure_bound fn`,
                    `vardef_measure fn`,
                    `\lbl. MEM lbl (fn_labels fn)`] >>
  rpt conj_tac
  >- simp[vardef_measure_bounded]
  >- metis_tac[vardef_inv_preserved]
  >- metis_tac[vardef_measure_increases]
  >- (simp[dfAnalyzeDefsTheory.direction_case_def] >>
      rw[listTheory.EVERY_MEM] >>
      metis_tac[cfgCorrectnessProofTheory.cfg_analyze_succ_labels])
  >- (simp[dfAnalyzeDefsTheory.direction_case_def] >>
      metis_tac[dfs_pre_in_fn_labels])
  >- metis_tac[vardef_init_state_inv]
QED

(* ===== Soundness helpers ===== *)

(* FOLDL list_intersect membership: result is subset of every element *)
Triviality foldl_intersect_mem_each[local]:
  !xs (a : 'a list) v.
    MEM v (FOLDL list_intersect a xs) ==>
    !x. MEM x xs ==> MEM v x
Proof
  Induct >> rw[]
  >- (`set (FOLDL list_intersect (list_intersect a h) xs) SUBSET
       set (list_intersect a h)` by
        metis_tac[dfHelperProofsTheory.foldl_list_intersect_subset] >>
      fs[dfHelperDefsTheory.list_intersect_def, listTheory.MEM_FILTER,
         pred_setTheory.SUBSET_DEF])
  >- metis_tac[]
QED

(* Reusable: vardef_analyze = df_analyze with specific params (LET-free) *)
val vardef_analyze_unfold =
  GSYM (SIMP_RULE std_ss [LET_THM] varDefDefsTheory.vardef_analyze_def);

(* Reusable: establish fixpoint in unfolded form *)
val vardef_fixpoint_unfolded =
  SIMP_RULE std_ss [LET_THM] vardef_fixpoint;

(* Vardef-specialized intra-transfer: df_at at SUC idx = transfer applied *)
Triviality vardef_at_intra[local]:
  !fn lbl bb idx.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    SUC idx <= LENGTH bb.bb_instructions ==>
    df_at (fn_all_assignments fn) (vardef_analyze fn) lbl (SUC idx) =
    vardef_transfer () (EL idx bb.bb_instructions)
      (df_at (fn_all_assignments fn) (vardef_analyze fn) lbl idx)
Proof
  rpt strip_tac >>
  `is_fixpoint
     (df_process_block Forward (fn_all_assignments fn) list_intersect
        vardef_transfer vardef_edge_transfer ()
        (OPTION_MAP (\lbl. (lbl, [] : string list)) (fn_entry_label fn))
        (cfg_analyze fn) fn.fn_blocks)
     (cfg_analyze fn).cfg_dfs_pre (vardef_analyze fn)` by
    (mp_tac vardef_fixpoint_unfolded >> simp[]) >>
  qspecl_then [`Forward`, `fn_all_assignments fn`, `list_intersect`,
    `vardef_transfer`, `vardef_edge_transfer`, `()`,
    `OPTION_MAP (\lbl. (lbl, [] : string list)) (fn_entry_label fn)`,
    `fn`, `lbl`, `bb`, `idx`]
    mp_tac (SIMP_RULE std_ss [LET_THM] dfAnalyzePropsTheory.df_at_intra_transfer) >>
  simp[dfAnalyzeDefsTheory.direction_case_def, vardef_analyze_unfold]
QED

(* Vardef-specialized inter-transfer: df_at at 0 = joined *)
Triviality vardef_at_inter[local]:
  !fn lbl bb.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    df_at (fn_all_assignments fn) (vardef_analyze fn) lbl 0 =
    vardef_joined fn (vardef_analyze fn) lbl
Proof
  rpt strip_tac >>
  `is_fixpoint
     (df_process_block Forward (fn_all_assignments fn) list_intersect
        vardef_transfer vardef_edge_transfer ()
        (OPTION_MAP (\lbl. (lbl, [] : string list)) (fn_entry_label fn))
        (cfg_analyze fn) fn.fn_blocks)
     (cfg_analyze fn).cfg_dfs_pre (vardef_analyze fn)` by
    (mp_tac vardef_fixpoint_unfolded >> simp[]) >>
  qspecl_then [`Forward`, `fn_all_assignments fn`, `list_intersect`,
    `vardef_transfer`, `vardef_edge_transfer`, `()`,
    `OPTION_MAP (\lbl. (lbl, [] : string list)) (fn_entry_label fn)`,
    `fn`, `lbl`, `bb`]
    mp_tac (SIMP_RULE std_ss [LET_THM] dfAnalyzePropsTheory.df_at_inter_transfer) >>
  simp[dfAnalyzeDefsTheory.direction_case_def,
       dfAnalyzeDefsTheory.df_joined_val_def,
       varDefDefsTheory.vardef_edge_transfer_def,
       vardef_joined_def, vardef_analyze_unfold, LET_THM] >>
  Cases_on `fn_entry_label fn` >> simp[]
QED

(* Transfer decomposition: v in transfer output => v in input or in inst_defs *)
Triviality vardef_transfer_mem[local]:
  !inst input v.
    MEM v (vardef_transfer () inst input) ==>
    MEM v input \/ MEM v (inst_defs inst)
Proof
  rw[varDefDefsTheory.vardef_transfer_def] >>
  fs[dfHelperProofsTheory.list_union_mem]
QED

(* df_at unwinding: v at index n => v at index 0 or assigned in block *)
Triviality vardef_df_at_unwind[local]:
  !n fn lbl bb v.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    n <= LENGTH bb.bb_instructions /\
    MEM v (df_at (fn_all_assignments fn) (vardef_analyze fn) lbl n) ==>
    MEM v (df_at (fn_all_assignments fn) (vardef_analyze fn) lbl 0) \/
    var_assigned_in_block fn lbl v
Proof
  Induct >> rw[] >>
  `df_at (fn_all_assignments fn) (vardef_analyze fn) lbl (SUC n) =
   vardef_transfer () (EL n bb.bb_instructions)
     (df_at (fn_all_assignments fn) (vardef_analyze fn) lbl n)` by
    (irule vardef_at_intra >> simp[]) >>
  fs[] >>
  `MEM v (df_at (fn_all_assignments fn) (vardef_analyze fn) lbl n) \/
   MEM v (inst_defs (EL n bb.bb_instructions))` by
    metis_tac[vardef_transfer_mem]
  >- (first_x_assum (qspecl_then [`fn`, `lbl`, `bb`, `v`] mp_tac) >> simp[])
  >> disj2_tac >> simp[varDefDefsTheory.var_assigned_in_block_def] >>
  simp[listTheory.EXISTS_MEM] >>
  qexists_tac `EL n bb.bb_instructions` >> simp[] >>
  `n < LENGTH bb.bb_instructions` by simp[] >>
  metis_tac[listTheory.MEM_EL]
QED

(* Boundary membership => output membership (from fixpoint + list_intersect) *)
Triviality vardef_boundary_in_output[local]:
  !fn lbl bb v.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM v (df_boundary (fn_all_assignments fn) (vardef_analyze fn) lbl) ==>
    MEM v (df_at (fn_all_assignments fn) (vardef_analyze fn) lbl
             (LENGTH bb.bb_instructions))
Proof
  rpt strip_tac >>
  (* Step 1: establish fixpoint *)
  `is_fixpoint
     (df_process_block Forward (fn_all_assignments fn) list_intersect
        vardef_transfer vardef_edge_transfer ()
        (OPTION_MAP (\lbl. (lbl, [] : string list)) (fn_entry_label fn))
        (cfg_analyze fn) fn.fn_blocks)
     (cfg_analyze fn).cfg_dfs_pre (vardef_analyze fn)` by
    (mp_tac vardef_fixpoint_unfolded >> simp[]) >>
  (* Step 2: apply df_boundary_fixpoint (Forward case) *)
  qspecl_then [`Forward`, `fn_all_assignments fn`, `list_intersect`,
    `vardef_transfer`, `vardef_edge_transfer`, `()`,
    `OPTION_MAP (\lbl. (lbl, [] : string list)) (fn_entry_label fn)`,
    `fn`, `lbl`, `bb`]
    mp_tac (SIMP_RULE std_ss [LET_THM] dfAnalyzePropsTheory.df_boundary_fixpoint) >>
  simp[dfAnalyzeDefsTheory.direction_case_def, vardef_analyze_unfold] >>
  strip_tac >>
  (* Step 3: from list_intersect(boundary, df_at) = boundary, get MEM *)
  metis_tac[dfHelperProofsTheory.list_intersect_mem]
QED

(* Joined value membership => every predecessor boundary has v *)
Triviality vardef_joined_in_pred_boundary[local]:
  !fn lbl pred v.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks <> NONE /\
    MEM pred (cfg_preds_of (cfg_analyze fn) lbl) /\
    MEM v (df_at (fn_all_assignments fn) (vardef_analyze fn) lbl 0) ==>
    MEM v (df_boundary (fn_all_assignments fn) (vardef_analyze fn) pred)
Proof
  rpt strip_tac >>
  `?bb. lookup_block lbl fn.fn_blocks = SOME bb` by
    (Cases_on `lookup_block lbl fn.fn_blocks` >> fs[]) >>
  qspecl_then [`fn`, `lbl`, `bb`] mp_tac vardef_at_inter >>
  simp[LET_THM] >> strip_tac >>
  (* MEM v (df_at lbl 0) → MEM v (vardef_joined ...) *)
  `MEM v (vardef_joined fn (vardef_analyze fn) lbl)` by fs[] >>
  (* Move MEM v joined to goal as implication, expand, handle entry_label *)
  pop_assum mp_tac >>
  simp_tac std_ss [vardef_joined_def, LET_THM] >>
  Cases_on `fn_entry_label fn` >> simp[]
  >- ((* NONE: MEM v (case MAP of [] => all | _::_ => FOLDL) ==> goal *)
      Cases_on `MAP (\nbr. df_boundary (fn_all_assignments fn)
                    (vardef_analyze fn) nbr)
                   (cfg_preds_of (cfg_analyze fn) lbl)` >> simp[]
      >- (Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> fs[]) >>
      strip_tac >>
      `!x. MEM x (h::t) ==> MEM v x` by
        metis_tac[foldl_intersect_mem_each, listTheory.FOLDL] >>
      `MEM (df_boundary (fn_all_assignments fn)
              (vardef_analyze fn) pred) (h::t)` by
        (qpat_x_assum `MAP _ _ = h::t` (SUBST1_TAC o SYM) >>
         simp[listTheory.MEM_MAP] >> qexists_tac `pred` >> simp[]) >>
      metis_tac[])
  >> (* SOME ev_lbl *)
  IF_CASES_TAC >> simp[dfHelperDefsTheory.list_intersect_def] >>
  (* lbl ≠ ev_lbl: same as NONE *)
  Cases_on `MAP (\nbr. df_boundary (fn_all_assignments fn)
                    (vardef_analyze fn) nbr)
                   (cfg_preds_of (cfg_analyze fn) lbl)` >> simp[]
  >- (Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> fs[]) >>
  strip_tac >>
  `!x. MEM x (h::t) ==> MEM v x` by
    metis_tac[foldl_intersect_mem_each, listTheory.FOLDL] >>
  `MEM (df_boundary (fn_all_assignments fn)
          (vardef_analyze fn) pred) (h::t)` by
    (qpat_x_assum `MAP _ _ = h::t` (SUBST1_TAC o SYM) >>
     simp[listTheory.MEM_MAP] >> qexists_tac `pred` >> simp[]) >>
  metis_tac[]
QED

(* ===== Path helpers ===== *)

(* FRONT of a valid cfg path of length >= 2 is itself a valid cfg path *)
Triviality is_cfg_path_front[local]:
  !cfg l1 l2 rest.
    is_cfg_path cfg (l1::l2::rest) ==>
    is_cfg_path cfg (FRONT (l1::l2::rest))
Proof
  Induct_on `rest` >>
  simp[cfgDefsTheory.is_cfg_path_def, listTheory.FRONT_CONS] >>
  rpt strip_tac >>
  Cases_on `rest` >>
  fs[cfgDefsTheory.is_cfg_path_def, listTheory.FRONT_CONS] >>
  Cases_on `t` >>
  fs[cfgDefsTheory.is_cfg_path_def, listTheory.FRONT_CONS] >>
  metis_tac[]
QED

(* The last element of FRONT is a successor-predecessor of the last element *)
Triviality is_cfg_path_last_succ[local]:
  !cfg l1 l2 rest.
    is_cfg_path cfg (l1::l2::rest) ==>
    MEM (LAST (l1::l2::rest))
        (cfg_succs_of cfg (LAST (FRONT (l1::l2::rest))))
Proof
  Induct_on `rest` >>
  simp[cfgDefsTheory.is_cfg_path_def, listTheory.FRONT_CONS,
       listTheory.LAST_CONS] >>
  rpt strip_tac >>
  Cases_on `rest` >>
  fs[cfgDefsTheory.is_cfg_path_def, listTheory.FRONT_CONS,
     listTheory.LAST_CONS] >>
  metis_tac[]
QED

(* All labels on a cfg path from a reachable entry are reachable *)
Triviality is_cfg_path_all_reachable[local]:
  !cfg fn path.
    wf_function fn /\
    cfg = cfg_analyze fn /\
    is_cfg_path cfg path /\
    path <> [] /\
    cfg_reachable_of cfg (HD path) ==>
    EVERY (\lbl. cfg_reachable_of cfg lbl) path
Proof
  Induct_on `path` >> simp[] >>
  rpt strip_tac >>
  Cases_on `path`
  >- simp[listTheory.EVERY_DEF] >>
  fs[cfgDefsTheory.is_cfg_path_def] >>
  `fn.fn_blocks <> []` by
    fs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def] >>
  `entry_block fn = SOME (HD fn.fn_blocks)` by
    simp[venomInstTheory.entry_block_def, listTheory.NULL_EQ] >>
  `cfg_path (cfg_analyze fn) (HD fn.fn_blocks).bb_label h` by
    metis_tac[cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability] >>
  `cfg_path (cfg_analyze fn) h h'` by
    (simp[cfgDefsTheory.cfg_path_def] >>
     irule (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) >>
     qexists_tac `h'` >> simp[]) >>
  `cfg_path (cfg_analyze fn) (HD fn.fn_blocks).bb_label h'` by
    metis_tac[relationTheory.RTC_RTC, cfgDefsTheory.cfg_path_def] >>
  `cfg_reachable_of (cfg_analyze fn) h'` by
    metis_tac[cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability] >>
  simp[] >> first_x_assum irule >> simp[]
QED

(* Entry label is reachable *)
Triviality entry_reachable[local]:
  !fn.
    wf_function fn /\
    fn.fn_blocks <> [] ==>
    cfg_reachable_of (cfg_analyze fn) (HD fn.fn_blocks).bb_label
Proof
  rpt strip_tac >>
  `entry_block fn = SOME (HD fn.fn_blocks)` by
    simp[venomInstTheory.entry_block_def, listTheory.NULL_EQ] >>
  `cfg_path (cfg_analyze fn) (HD fn.fn_blocks).bb_label
     (HD fn.fn_blocks).bb_label` by
    simp[cfgDefsTheory.cfg_path_def] >>
  metis_tac[cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability]
QED

(* Entry boundary is always []: follows from boundary_fixpoint + entry at
   position 0 being [] when no predecessors, or FOLDL of pred boundaries
   (which all contain boundary(entry) = [] by induction on iterations).
   Simplest proof: at fixpoint, boundary(entry) = list_intersect(boundary(entry),
   df_at(entry, LENGTH instrs)). And entry_val gives boundary(entry) starts as [].
   Since list_intersect([], x) = [], boundary stays [].
   
   Proof via wl_iterate_invariant with P = vardef_state_inv ∧ entry_boundary = []. *)

Triviality vardef_entry_boundary_empty[local]:
  !fn.
    wf_function fn /\
    fn.fn_blocks <> [] ==>
    df_boundary (fn_all_assignments fn) (vardef_analyze fn)
      (HD fn.fn_blocks).bb_label = []
Proof
  rpt strip_tac
  >> `FLOOKUP (vardef_analyze fn).ds_boundary (HD fn.fn_blocks).bb_label = SOME []`
       suffices_by simp[dfAnalyzeDefsTheory.df_boundary_def]
  >> simp[varDefDefsTheory.vardef_analyze_def, dfAnalyzeDefsTheory.df_analyze_def, LET_THM]
  >> qmatch_goalsub_abbrev_tac `wl_iterate changed process deps wl0 st0'`
  >> `FLOOKUP (SND (wl_iterate changed process deps wl0 st0')).ds_boundary
        (HD fn.fn_blocks).bb_label = SOME ([] : string list)`
       suffices_by simp[df_populate_inst_boundary]
  >> `(\st. vardef_state_inv fn st /\
       FLOOKUP st.ds_boundary (HD fn.fn_blocks).bb_label = SOME ([] : string list))
      (SND (wl_iterate changed process deps wl0 st0'))` suffices_by simp[]
  >> unabbrev_all_tac
  >> irule (SIMP_RULE std_ss [LET_THM]
       dfAnalyzeProofsTheory.df_analyze_invariant_forward)
  >> simp[] >> rpt conj_tac
  >- ((* vardef_state_inv fn st0' *)
      mp_tac (Q.SPEC `fn` vardef_init_state_inv) >>
      Cases_on `fn_entry_label fn` >> simp[])
  >- ((* FLOOKUP st0'.ds_boundary entry = SOME [] *)
      `fn_entry_label fn = SOME (HD fn.fn_blocks).bb_label`
        by simp[venomInstTheory.fn_entry_label_def,
                venomInstTheory.entry_block_def, listTheory.NULL_EQ]
      >> simp[dfAnalyzeDefsTheory.init_df_state_def,
              finite_mapTheory.FLOOKUP_UPDATE])
  >- ((* Q preserved *)
      rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[vardef_inv_preserved]
      >> rewrite_tac[vardef_process_eq] >> simp_tac std_ss [LET_THM]
      >> pairarg_tac >> simp[]
      >> IF_CASES_TAC >> simp[finite_mapTheory.FLOOKUP_UPDATE]
      >> rw[dfAnalyzeDefsTheory.df_boundary_def,
            dfHelperDefsTheory.list_intersect_def])
  >- ((* measure *)
      qexistsl_tac [`vardef_measure_bound fn`, `vardef_measure fn`]
      >> simp[vardef_measure_bounded]
      >> metis_tac[vardef_measure_increases])
QED

(* ===== Soundness ===== *)

Theorem vardef_sound:
  !fn lbl v path.
    wf_function fn /\
    fn.fn_blocks <> [] /\
    MEM v (vardef_out_of fn lbl) /\
    is_cfg_path (cfg_analyze fn) path /\
    path <> [] /\
    HD path = (HD fn.fn_blocks).bb_label /\
    LAST path = lbl ==>
    ?lbl'. MEM lbl' path /\ var_assigned_in_block fn lbl' v
Proof
  gen_tac
  >> measureInduct_on `LENGTH path`
  >> rpt strip_tac
  >> Cases_on `path` >> fs[]
  >> Cases_on `t` >> fs[]
  (* Base case: path = [entry] *)
  >- (
    `vardef_out_of fn (HD fn.fn_blocks).bb_label = []` by
      (simp[varDefDefsTheory.vardef_out_of_def]
       >> metis_tac[vardef_entry_boundary_empty])
    >> fs[]
  )
  (* Step case: path = entry :: h' :: t' *)
  >> `MEM lbl (h'::t')` by
       (qpat_x_assum `LAST _ = lbl` (SUBST1_TAC o SYM)
        >> simp[rich_listTheory.MEM_LAST])
  >> `cfg_reachable_of (cfg_analyze fn) (HD fn.fn_blocks).bb_label` by
       (irule entry_reachable >> simp[])
  >> `EVERY (\l. cfg_reachable_of (cfg_analyze fn) l)
        ((HD fn.fn_blocks).bb_label::h'::t')` by
       (mp_tac (Q.SPECL [`cfg_analyze fn`, `fn`,
                          `(HD fn.fn_blocks).bb_label::h'::t'`]
                  is_cfg_path_all_reachable)
        >> simp[])
  >> `cfg_reachable_of (cfg_analyze fn) lbl` by
       fs[listTheory.EVERY_MEM]
  >> `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
       (irule reachable_in_dfs_pre >> simp[])
  >> `?bb. lookup_block lbl fn.fn_blocks = SOME bb` by
       (irule lookup_block_exists >> simp[]
        >> mp_tac dfs_pre_in_fn_labels >> simp[listTheory.EVERY_MEM]
        >> strip_tac >> `MEM lbl (fn_labels fn)` by metis_tac[]
        >> fs[venomInstTheory.fn_labels_def])
  >> `MEM v (df_at (fn_all_assignments fn) (vardef_analyze fn) lbl
               (LENGTH bb.bb_instructions))` by
       (irule vardef_boundary_in_output >> simp[]
        >> fs[varDefDefsTheory.vardef_out_of_def])
  >> `MEM v (df_at (fn_all_assignments fn) (vardef_analyze fn) lbl 0) \/
      var_assigned_in_block fn lbl v` by
       (irule vardef_df_at_unwind >> simp[]
        >> metis_tac[arithmeticTheory.LESS_EQ_REFL])
  (* Assigned case: witness lbl *)
  >| [ALL_TAC, qexists_tac `lbl` >> fs[]]
  (* IH case: v comes from predecessor *)
  >> qabbrev_tac `entry_lbl = (HD fn.fn_blocks).bb_label`
  >> `MEM (LAST (entry_lbl::h'::t'))
         (cfg_succs_of (cfg_analyze fn) (LAST (FRONT (entry_lbl::h'::t'))))` by
       metis_tac[is_cfg_path_last_succ]
  >> `LAST (entry_lbl::h'::t') = lbl` by
       simp[Abbr `entry_lbl`]
  >> `MEM (LAST (FRONT (entry_lbl::h'::t')))
          (cfg_preds_of (cfg_analyze fn) lbl)` by
       metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond]
  >> sg `MEM v (df_boundary (fn_all_assignments fn) (vardef_analyze fn)
               (LAST (FRONT (entry_lbl::h'::t'))))`
  >- (match_mp_tac vardef_joined_in_pred_boundary
      >> qexists_tac `lbl` >> simp[]
      >> metis_tac[optionTheory.NOT_NONE_SOME])
  >> `is_cfg_path (cfg_analyze fn) (FRONT (entry_lbl::h'::t'))` by
       metis_tac[is_cfg_path_front]
  >> sg `MEM v (vardef_out_of fn (LAST (FRONT (entry_lbl::h'::t'))))`
  >- (simp[varDefDefsTheory.vardef_out_of_def]
      >> fs[listTheory.FRONT_CONS])
  (* Apply IH to shorter path FRONT(entry::h'::t') *)
  >> first_x_assum (qspecl_then [`FRONT (entry_lbl::h'::t')`] mp_tac)
  >> impl_tac >- simp[listTheory.LENGTH_FRONT_CONS]
  >> disch_then (qspecl_then [`v`] mp_tac)
  >> impl_tac >- simp[listTheory.FRONT_CONS]
  >> strip_tac >> qexists_tac `lbl'`
  >> fs[listTheory.FRONT_CONS]
  >> metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL, listTheory.MEM]
QED
