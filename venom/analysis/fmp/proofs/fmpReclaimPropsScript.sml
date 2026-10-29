(* Static certificates for the indexed reclaim analysis.  No theorem in this
 * file identifies checked plans with operational allocation safety. *)
Theory fmpReclaimProps
Ancestors
  fmpReclaimDefs fmpAnalysisProps fmpAliasProps rich_list list finite_map pair arithmetic

Theorem fmp_pop_prefix_decomposition:
  !xs dead. FST (fmp_pop_prefix dead xs) ++ SND (fmp_pop_prefix dead xs) = xs
Proof
  Induct >> simp[fmp_pop_prefix_def] >> rpt gen_tac >>
  first_x_assum (qspec_then `dead` mp_tac) >>
  Cases_on `dead h` >> simp[] >>
  Cases_on `fmp_pop_prefix dead xs` >> gvs[]
QED

Theorem fmp_pop_prefix_dead:
  !xs dead. EVERY dead (FST (fmp_pop_prefix dead xs))
Proof
  Induct >> simp[fmp_pop_prefix_def] >> rpt gen_tac >>
  first_x_assum (qspec_then `dead` mp_tac) >>
  Cases_on `dead h` >> simp[] >>
  Cases_on `fmp_pop_prefix dead xs` >> gvs[]
QED

Theorem fmp_pop_prefix_maximal:
  !xs dead. SND (fmp_pop_prefix dead xs) <> [] ==>
    ~dead (HD (SND (fmp_pop_prefix dead xs)))
Proof
  Induct >> simp[fmp_pop_prefix_def] >> rpt gen_tac >>
  first_x_assum (qspec_then `dead` mp_tac) >>
  Cases_on `dead h` >> simp[] >>
  Cases_on `fmp_pop_prefix dead xs` >> gvs[]
QED

Theorem fmp_pop_target_lowest:
  fmp_pop_target popped = SOME mark ==>
    ?newer. popped = newer ++ [mark]
Proof
  Cases_on `popped` >> simp[fmp_pop_target_def] >> strip_tac >>
  qexists `FRONT (h::t)` >> gvs[APPEND_FRONT_LAST]
QED

Theorem fmp_pop_target_mem:
  fmp_pop_target popped = SOME mark ==> MEM mark popped
Proof
  strip_tac >> drule fmp_pop_target_lowest >> strip_tac >> simp[]
QED

Theorem fmp_pop_at_certificate:
  fmp_pop_at infos fn live env p inst st = (popped,kept) /\ popped <> [] ==>
    st.frs_stack = popped ++ kept /\
    EVERY (fmp_mark_dead (fn_insts fn) env
      (live_vars_at live (FST p) (SND p))) popped /\
    (kept <> [] ==> ~fmp_mark_dead (fn_insts fn) env
      (live_vars_at live (FST p) (SND p)) (HD kept))
Proof
  simp[fmp_pop_at_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[fmp_pop_prefix_decomposition, fmp_pop_prefix_dead,
            fmp_pop_prefix_maximal, FST, SND]
QED

Theorem fmp_step_pop_effect:
  fmp_pop_at infos fn live env p inst st = (popped,kept) ==>
    fmp_reclaim_step infos fn live env p inst (SOME st) =
      (fmp_pop_target popped,
       SOME (fmp_apply_effect infos inst (st with frs_stack := kept)))
Proof
  simp[fmp_reclaim_step_def]
QED

Theorem fmp_transfer_step:
  fmp_reclaim_step infos fn live env p inst st = (target,next) ==>
    fmp_transfer infos fn live env p inst st = next
Proof simp[fmp_transfer_def]
QED

Theorem fmp_step_unreachable:
  fmp_reclaim_step infos fn live env p inst NONE = (NONE,NONE)
Proof simp[fmp_reclaim_step_def]
QED

Theorem fmp_step_target_checked:
  FST (fmp_reclaim_step infos fn live env p inst (SOME st)) = SOME mark ==>
    st.frs_can_reclaim /\ fmp_is_reclaim_point infos inst /\
    ~EXISTS (fmp_capture_veto fn live p) st.frs_captures /\
    fmp_mark_dead (fn_insts fn) env
      (live_vars_at live (FST p) (SND p)) mark
Proof
  simp[fmp_reclaim_step_def] >>
  Cases_on `fmp_pop_at infos fn live env p inst st` >> simp[] >>
  strip_tac >> drule fmp_pop_target_mem >>
  gvs[fmp_pop_at_def, AllCaseEqs()] >>
  `EVERY (fmp_mark_dead (fn_insts fn) env
      (live_vars_at live (FST p) (SND p))) q` by
    metis_tac[fmp_pop_prefix_dead, FST] >>
  gvs[EVERY_MEM]
QED

(* The pre-state at offset k is the fold of exactly TAKE k instructions.
 * This formulation does not confuse instruction ids with original indices. *)
Definition fmp_run_prefix_def:
  fmp_run_prefix transfer lbl [] (idx:num) acc = acc /\
  fmp_run_prefix transfer lbl (inst::rest) idx acc =
    fmp_run_prefix transfer lbl rest (idx+1) (transfer (lbl,idx) inst acc)
End

Theorem fmp_fold_before_start:
  !insts idx acc m transfer lbl j.
    j < idx ==>
    FLOOKUP (SND (fmp_fold_forward transfer lbl insts idx acc m)) (lbl,j) =
      FLOOKUP m (lbl,j)
Proof
  Induct >> simp[fmp_fold_forward_def, FLOOKUP_UPDATE] >> rpt strip_tac
QED

Theorem fmp_fold_prestate_lookup:
  !insts k idx acc m transfer lbl.
    k <= LENGTH insts ==>
    FLOOKUP (SND (fmp_fold_forward transfer lbl insts idx acc m)) (lbl,idx+k) =
      SOME (fmp_run_prefix transfer lbl (TAKE k insts) idx acc)
Proof
  Induct >- simp[fmp_fold_forward_def, fmp_run_prefix_def, FLOOKUP_UPDATE] >>
  rpt gen_tac >> Cases_on `k`
  >- (simp[fmp_fold_forward_def, fmp_run_prefix_def] >>
      simp[fmp_fold_before_start, FLOOKUP_UPDATE]) >>
  simp[fmp_fold_forward_def, fmp_run_prefix_def, ADD_CLAUSES] >>
  strip_tac >>
  `SUC (idx+n) = (idx+1)+n` by simp[] >>
  asm_rewrite_tac[] >> first_x_assum irule >> simp[]
QED

Theorem fmp_scan_candidate_lookup:
  !insts idx states infos fn live env lbl.
    MEM (p,mark) (fmp_scan_candidates infos fn live env states lbl insts idx) <=>
    ?k. k < LENGTH insts /\ p = (lbl,idx+k) /\
      FST (fmp_reclaim_step infos fn live env p (EL k insts)
        (df_at NONE states lbl (idx+k))) = SOME mark
Proof
  Induct >- simp[fmp_scan_candidates_def] >> rpt gen_tac >>
  simp[Once EXISTS_NUM, fmp_scan_candidates_def, ADD_CLAUSES] >>
  Cases_on `FST (fmp_reclaim_step infos fn live env (lbl,idx) h
    (df_at NONE states lbl idx))` >>
  Cases_on `p = (lbl,idx)` >> gvs[ADD_CLAUSES, GSYM ADD1] >> metis_tac[]
QED

Theorem fmp_scan_no_end_candidate:
  ~MEM ((lbl,idx+LENGTH insts),mark)
    (fmp_scan_candidates infos fn live env states lbl insts idx)
Proof simp[fmp_scan_candidate_lookup]
QED

Theorem analyze_fmp_reclaims_ready:
  fmp_info_valid ctx infos /\ MEM fn ctx.ctx_functions /\
  wf_function fn /\ fn_inst_wf fn /\ fn.fn_fmp_signature = NONE /\
  fmp_reclaim_states infos fn = SOME states /\
  fmp_candidate_plan infos ctx fn states = plan /\
  fmp_reclaim_plan_ok infos ctx fn plan ==>
  analyze_fmp_reclaims infos ctx fn = SOME plan
Proof simp[analyze_fmp_reclaims_def] >> metis_tac[]
QED

Theorem analyze_fmp_reclaims_checked:
  analyze_fmp_reclaims infos ctx fn = SOME plan ==>
  fmp_info_valid ctx infos /\ MEM fn ctx.ctx_functions /\
  fmp_reclaim_plan_ok infos ctx fn plan
Proof simp[analyze_fmp_reclaims_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_reclaim_plan_ok_lookup:
  fmp_reclaim_plan_ok infos ctx fn plan /\ FLOOKUP plan point = SOME target ==>
  fmp_reclaim_entry_ok infos ctx fn point target
Proof simp[fmp_reclaim_plan_ok_def] >> metis_tac[]
QED

Theorem analyze_fmp_reclaims_target_checked:
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  FLOOKUP plan point = SOME target ==>
  ?bb states env st.
    lookup_block (FST point) fn.fn_blocks = SOME bb /\
    SND point < LENGTH bb.bb_instructions /\
    fmp_base_analyze (fn_insts fn) = SOME env /\
    fmp_reclaim_states infos fn = SOME states /\
    df_at NONE states (FST point) (SND point) = SOME st /\
    fmp_restore_target_ok infos ctx fn (liveness_analyze fn)
      st.frs_captures point target /\
    FST (fmp_reclaim_step infos fn (liveness_analyze fn) env point
      (EL (SND point) bb.bb_instructions) (SOME st)) = SOME target
Proof
  rpt strip_tac >> drule analyze_fmp_reclaims_checked >> strip_tac >>
  drule fmp_reclaim_plan_ok_lookup >> disch_then drule >>
  simp[fmp_reclaim_entry_ok_def] >> strip_tac >>
  Cases_on `fmp_base_analyze (fn_insts fn)` >> gvs[] >>
  Cases_on `fmp_reclaim_states infos fn` >> gvs[] >>
  rename1 `fmp_reclaim_states infos fn = SOME states` >>
  Cases_on `lookup_block (FST point) fn.fn_blocks` >> gvs[] >>
  Cases_on `df_at NONE states (FST point) (SND point)` >> gvs[] >>
  metis_tac[]
QED

Theorem analyze_fmp_reclaims_deterministic:
  analyze_fmp_reclaims infos ctx fn = SOME p1 /\
  analyze_fmp_reclaims infos ctx fn = SOME p2 ==> p1 = p2
Proof rpt strip_tac >> gvs[]
QED

Theorem fmp_reclaim_states_has_bases:
  fmp_reclaim_states infos fn = SOME states ==>
    ?env. fmp_base_analyze (fn_insts fn) = SOME env
Proof
  simp[fmp_reclaim_states_def] >>
  Cases_on `fmp_base_analyze (fn_insts fn)` >> simp[]
QED

Theorem fmp_scan_unreachable:
  (!k. k < LENGTH insts ==> df_at NONE states lbl (idx+k) = NONE) ==>
    fmp_scan_candidates infos fn live env states lbl insts idx = []
Proof
  strip_tac >> Cases_on `fmp_scan_candidates infos fn live env states lbl insts idx` >>
  simp[] >> rename1 `_ = entry::rest` >>
  Cases_on `entry` >> rename1 `_ = (point,mark)::rest` >>
  `MEM (point,mark)
    (fmp_scan_candidates infos fn live env states lbl insts idx)` by simp[] >>
  gvs[fmp_scan_candidate_lookup] >>
  metis_tac[fmp_step_unreachable, FST, optionTheory.NOT_SOME_NONE]
QED

val _ = List.app (fn thy => List.app (fn (name,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle dependency in " ^ thy ^ "." ^ name))
  (DB.thms thy))
  ["fmpAnalysisDefs", "fmpAnalysisProps", "fmpAliasDefs", "fmpAliasProps",
   "fmpReclaimDefs", "fmpReclaimProps"];
