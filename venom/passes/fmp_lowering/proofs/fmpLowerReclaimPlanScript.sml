(* Analysis side of the reclaim ledger.  The populated reclaim states are the
 * per-block fold of the transfer from the joined block entry, the candidate
 * plan selects exactly the analysis step's target at each original point, and
 * a block-stable predecessor's exit stack extends its successor's entry
 * stack.  The ledger invariant relates an analysis stack to concrete regions
 * at or above a relocation floor fmp0. *)
Theory fmpLowerReclaimPlan
Ancestors
  fmpLowerProps fmpLowerIndexedProps fmpLedgerProps fmpReclaimProps
  fmpReclaimDefs dfAnalyzeDefs venomExecProps venomInst alist rich_list list finite_map
  pair arithmetic

(* ===== Ledger invariant with a floor ===== *)

Definition fmp_ledger_inv_def:
  fmp_ledger_inv insts env fmp0 s lo stack <=>
    ?regions. fmp_ledger_ok insts env s lo regions /\
      MAP (\r. r.fr_mark) regions = stack /\
      EVERY (\r. fmp0 <= r.fr_lo) regions
End

Theorem fmp_ledger_prefix:
  !ps top ks. fmp_ledger_ok insts env s top (ps ++ ks) ==>
    fmp_ledger_ok insts env s top ps
Proof
  Induct >> rw[fmp_ledger_ok_def] >> metis_tac[]
QED

Theorem fmp_ledger_inv_nil[simp]:
  fmp_ledger_inv insts env fmp0 s lo []
Proof
  simp[fmp_ledger_inv_def]
QED

Theorem fmp_ledger_inv_prefix:
  fmp_ledger_inv insts env fmp0 s lo (ps ++ ks) ==>
  fmp_ledger_inv insts env fmp0 s lo ps
Proof
  rw[fmp_ledger_inv_def] >> gvs[MAP_EQ_APPEND] >>
  drule fmp_ledger_prefix >> strip_tac >>
  qexists `l10` >> gvs[EVERY_APPEND]
QED

Theorem fmp_ledger_inv_frame:
  fmp_ledger_inv insts env fmp0 s lo stack /\
  (!v. MEM v stack ==> lookup_var v s' = lookup_var v s) ==>
  fmp_ledger_inv insts env fmp0 s' lo stack
Proof
  rw[fmp_ledger_inv_def] >> qexists `regions` >> simp[] >>
  irule fmp_ledger_frame >> qexists `s` >> simp[] >>
  fs[MEM_MAP, PULL_EXISTS]
QED

Theorem fmp_ledger_inv_push:
  fmp_ledger_inv insts env fmp0 s lo stack /\ fmp0 <= lo /\ lo <= hi /\
  hi < dimword (:256) /\
  fmp_dalloca_query insts env mark = SOME site /\ ~MEM mark stack /\
  (!v. MEM v stack ==> lookup_var v s' = lookup_var v s) /\
  lookup_var mark s' = SOME (n2w lo) ==>
  fmp_ledger_inv insts env fmp0 s' hi (mark::stack)
Proof
  rw[fmp_ledger_inv_def] >>
  qexists `<| fr_mark := mark; fr_site := site; fr_lo := lo; fr_hi := hi |>
           :: regions` >>
  simp[fmp_ledger_ok_def] >>
  irule fmp_ledger_frame >> qexists `s` >> simp[] >>
  fs[MEM_MAP, PULL_EXISTS]
QED

(* ===== Pops ===== *)

Theorem fmp_pop_at_none:
  fmp_pop_at infos fn live env p inst st = (popped,kept) /\
  fmp_pop_target popped = NONE ==>
  popped = [] /\ kept = st.frs_stack
Proof
  strip_tac >>
  `popped = []` by (Cases_on `popped` >> fs[fmp_pop_target_def]) >>
  gvs[] >> qpat_x_assum `fmp_pop_at _ _ _ _ _ _ _ = _` mp_tac >>
  rw[fmp_pop_at_def] >>
  qmatch_asmsub_abbrev_tac `fmp_pop_prefix dead xs = _` >>
  qspecl_then [`xs`, `dead`] mp_tac fmp_pop_prefix_decomposition >>
  simp[]
QED

Theorem fmp_pop_at_kept:
  fmp_pop_at infos fn live env p inst st = (popped,kept) ==>
  ?ps. st.frs_stack = ps ++ kept
Proof
  Cases_on `fmp_pop_target popped`
  >- (rpt strip_tac >> drule_all fmp_pop_at_none >> simp[]) >>
  strip_tac >>
  `popped <> []` by (strip_tac >> gvs[fmp_pop_target_def]) >>
  drule_all fmp_pop_at_certificate >> metis_tac[]
QED

(* A restore to the lowest popped mark reads that mark's region base, and the
 * kept stack's ledger then tops out at it. *)
Theorem fmp_pop_restore_ledger:
  fmp_ledger_inv insts env fmp0 s lo st.frs_stack /\
  fmp_pop_at infos fn live aenv p inst st = (popped,kept) /\
  fmp_pop_target popped = SOME target ==>
  ?newtop. lookup_var target s = SOME (n2w newtop) /\
    fmp0 <= newtop /\ newtop <= lo /\ MEM target st.frs_stack /\
    fmp_ledger_inv insts env fmp0 s newtop kept
Proof
  rw[fmp_ledger_inv_def] >>
  `popped <> []` by (strip_tac >> gvs[fmp_pop_target_def]) >>
  drule_all fmp_pop_at_certificate >> strip_tac >>
  `MAP (\r. r.fr_mark) regions = popped ++ kept` by metis_tac[] >>
  gvs[MAP_EQ_APPEND] >>
  `l10 <> []` by (strip_tac >> gvs[]) >>
  drule_all fmp_ledger_split >> strip_tac >>
  drule fmp_pop_target_lowest >> strip_tac >>
  `(LAST l10).fr_mark = target` by
    (`LAST (MAP (\r. r.fr_mark) l10) = target` by
       (qpat_x_assum `MAP _ l10 = _` SUBST1_TAC >>
        simp[LAST_APPEND_CONS]) >>
     gvs[LAST_MAP]) >>
  `MEM (LAST l10) (l10 ++ l20)` by simp[MEM_LAST_NOT_NIL] >>
  drule_all fmp_ledger_mark >> strip_tac >>
  qexists `(LAST l10).fr_lo` >> gvs[EVERY_APPEND, EVERY_MEM] >>
  rpt conj_tac >>
  TRY (qexists `l20` >> simp[] >> NO_TAC) >>
  metis_tac[MEM_LAST_NOT_NIL, MEM_APPEND, MEM]
QED

(* ===== Effects on the stack ===== *)

Theorem fmp_apply_effect_clear_stack:
  fmp_clears_marks infos inst ==>
  (fmp_apply_effect infos inst st).frs_stack = []
Proof
  simp[fmp_apply_effect_def, fmp_empty_reclaim_state_def]
QED

Theorem fmp_apply_effect_dalloca_stack:
  ~fmp_clears_marks infos inst /\ inst.inst_opcode = DALLOCA /\
  inst.inst_outputs = [out] ==>
  (fmp_apply_effect infos inst st).frs_stack = out::st.frs_stack
Proof
  simp[fmp_apply_effect_def, fmpAliasDefsTheory.fmp_single_output_def]
QED

Theorem fmp_apply_effect_other_stack:
  ~fmp_clears_marks infos inst /\ inst.inst_opcode <> DALLOCA ==>
  (fmp_apply_effect infos inst st).frs_stack = st.frs_stack
Proof
  simp[fmp_apply_effect_def]
QED

(* ===== Populated states along a block ===== *)

Theorem fmp_fold_forward_other_label:
  !insts idx acc m. l <> lbl ==>
    FLOOKUP (SND (fmp_fold_forward transfer lbl insts idx acc m)) (l,k) =
      FLOOKUP m (l,k)
Proof
  Induct >> simp[fmp_fold_forward_def, FLOOKUP_UPDATE]
QED

Theorem fmp_fold_forward_final:
  !insts idx acc m.
    FST (fmp_fold_forward transfer lbl insts idx acc m) =
      fmp_run_prefix transfer lbl insts idx acc
Proof
  Induct >> simp[fmp_fold_forward_def, fmp_run_prefix_def]
QED

Theorem fmp_run_prefix_snoc:
  !xs idx acc.
    fmp_run_prefix transfer lbl (xs ++ [x]) idx acc =
      transfer (lbl,idx + LENGTH xs) x (fmp_run_prefix transfer lbl xs idx acc)
Proof
  Induct >> simp[fmp_run_prefix_def, ADD1]
QED

Theorem fmp_populate_foldl_lookup:
  !lbls st0 F' key v.
    (!lbl. MEM lbl lbls ==> FLOOKUP (F' lbl) key = NONE \/
                            FLOOKUP (F' lbl) key = SOME v) /\
    (FLOOKUP st0.ds_inst key = SOME v \/
     ?lbl. MEM lbl lbls /\ FLOOKUP (F' lbl) key = SOME v) ==>
    FLOOKUP (FOLDL (\st lbl. st with ds_inst := FUNION (F' lbl) st.ds_inst)
      st0 lbls).ds_inst key = SOME v
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> first_x_assum irule >>
  simp[FLOOKUP_FUNION] >>
  Cases_on `FLOOKUP (F' h) key` >> simp[] >>
  metis_tac[optionTheory.SOME_11, optionTheory.NOT_SOME_NONE]
QED

Theorem fmp_populate_boundary:
  (fmp_populate transfer entry cfg bbs states).ds_boundary =
    states.ds_boundary
Proof
  simp[fmp_populate_def] >>
  `!lbls st0. (FOLDL (\st lbl. st with ds_inst := FUNION
      (SND (fmp_fold_at transfer entry cfg bbs states lbl)) st.ds_inst)
      st0 lbls).ds_boundary = st0.ds_boundary` suffices_by simp[] >>
  Induct >> simp[]
QED

Theorem fmp_populate_joined:
  fmp_joined entry cfg (fmp_populate transfer entry cfg bbs states) lbl =
    fmp_joined entry cfg states lbl
Proof
  simp[fmp_joined_def, df_joined_val_def, df_boundary_def,
       fmp_populate_boundary]
QED

Theorem fmp_populate_df_at:
  ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\ MEM bb bbs /\
  k <= LENGTH bb.bb_instructions ==>
  df_at NONE (fmp_populate transfer entry cfg bbs states) bb.bb_label k =
    fmp_run_prefix transfer bb.bb_label (TAKE k bb.bb_instructions) 0
      (fmp_joined entry cfg states bb.bb_label)
Proof
  strip_tac >>
  `lookup_block bb.bb_label bbs = SOME bb` by
    metis_tac[venomExecPropsTheory.MEM_lookup_block] >>
  qmatch_goalsub_abbrev_tac `_ = v` >>
  `FLOOKUP (fmp_populate transfer entry cfg bbs states).ds_inst
     (bb.bb_label,k) = SOME v` suffices_by simp[df_at_def] >>
  simp[fmp_populate_def] >>
  qspecl_then [`MAP (\bb. bb.bb_label) bbs`, `states`,
    `\lbl. SND (fmp_fold_at transfer entry cfg bbs states lbl)`,
    `(bb.bb_label,k)`, `v`] mp_tac fmp_populate_foldl_lookup >>
  simp[] >> disch_then irule >>
  `FLOOKUP (SND (fmp_fold_at transfer entry cfg bbs states bb.bb_label))
     (bb.bb_label,k) = SOME v` by
    (simp[fmp_fold_at_def, Abbr `v`] >>
     qspecl_then [`bb.bb_instructions`, `k`, `0`,
       `fmp_joined entry cfg states bb.bb_label`, `FEMPTY`, `transfer`,
       `bb.bb_label`] mp_tac fmp_fold_prestate_lookup >>
     simp[]) >>
  rpt conj_tac
  >- (rpt strip_tac >> Cases_on `lbl = bb.bb_label` >> simp[] >>
      simp[fmp_fold_at_def, fmp_fold_forward_other_label])
  >> disj2_tac >> qexists `bb.bb_label` >> simp[MEM_MAP] >> metis_tac[]
QED

Theorem fmp_reclaim_states_populate:
  fmp_reclaim_states infos fn = SOME states ==>
  ?env ebb result.
    fmp_base_analyze (fn_insts fn) = SOME env /\
    entry_block fn = SOME ebb /\
    states = fmp_populate (fmp_transfer infos fn (liveness_analyze fn) env)
      (SOME (ebb.bb_label,SOME fmp_empty_reclaim_state)) (cfg_analyze fn)
      fn.fn_blocks result
Proof
  rw[fmp_reclaim_states_def] >> gvs[AllCaseEqs()] >>
  gvs[fmp_reclaim_analyze_fuel_def, AllCaseEqs()] >> metis_tac[]
QED

(* An accepted analysis passed the PHI-readiness guard on every block. *)
Theorem fmp_reclaim_states_phi_ready:
  fmp_reclaim_states infos fn = SOME states ==>
  EVERY (fmp_phi_ready_block (liveness_analyze fn)) fn.fn_blocks
Proof
  rw[fmp_reclaim_states_def] >> gvs[AllCaseEqs()]
QED

(* Every block of an accepted analysis is stable: processing it again
   leaves the states as they are. *)
Theorem fmp_reclaim_states_stable:
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  entry_block fn = SOME ebb /\ MEM bb fn.fn_blocks ==>
  fmp_process_block (fmp_transfer infos fn (liveness_analyze fn) env)
    (SOME (ebb.bb_label,SOME fmp_empty_reclaim_state)) (cfg_analyze fn)
    fn.fn_blocks bb.bb_label states = states
Proof
  rw[fmp_reclaim_states_def] >> gvs[AllCaseEqs(), EVERY_MEM]
QED

Theorem fmp_reclaim_states_df_at_suc:
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\ MEM bb fn.fn_blocks /\
  k < LENGTH bb.bb_instructions ==>
  df_at NONE states bb.bb_label (SUC k) =
    fmp_transfer infos fn (liveness_analyze fn) env (bb.bb_label,k)
      (EL k bb.bb_instructions) (df_at NONE states bb.bb_label k)
Proof
  strip_tac >> drule fmp_reclaim_states_populate >> strip_tac >> gvs[] >>
  simp[fmp_populate_df_at] >>
  `TAKE (SUC k) bb.bb_instructions =
     TAKE k bb.bb_instructions ++ [EL k bb.bb_instructions]` by
    simp[ADD1, TAKE_EL_SNOC, SNOC_APPEND] >>
  simp[fmp_run_prefix_snoc, LENGTH_TAKE]
QED

Theorem fmp_reclaim_states_df_at_entry:
  fmp_reclaim_states infos fn = SOME states /\
  entry_block fn = SOME ebb /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\ MEM bb fn.fn_blocks ==>
  df_at NONE states bb.bb_label 0 =
    fmp_joined (SOME (ebb.bb_label,SOME fmp_empty_reclaim_state))
      (cfg_analyze fn) states bb.bb_label
Proof
  strip_tac >> drule fmp_reclaim_states_populate >> strip_tac >> gvs[] >>
  simp[fmp_populate_df_at, fmp_populate_joined, fmp_run_prefix_def]
QED

Theorem fmp_reclaim_states_df_at_exit:
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  entry_block fn = SOME ebb /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\ MEM bb fn.fn_blocks ==>
  df_at NONE states bb.bb_label (LENGTH bb.bb_instructions) =
    FST (fmp_fold_at (fmp_transfer infos fn (liveness_analyze fn) env)
      (SOME (ebb.bb_label,SOME fmp_empty_reclaim_state)) (cfg_analyze fn)
      fn.fn_blocks states bb.bb_label)
Proof
  strip_tac >> drule fmp_reclaim_states_populate >> strip_tac >> gvs[] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    metis_tac[venomExecPropsTheory.MEM_lookup_block] >>
  simp[fmp_populate_df_at, fmp_fold_at_def, fmp_fold_forward_final,
       fmp_populate_joined]
QED

(* A reachable point stays reachable along its block. *)
Theorem fmp_transfer_some:
  ?st'. fmp_transfer infos fn live env p inst (SOME st) = SOME st'
Proof
  simp[fmp_transfer_def, fmp_reclaim_step_def] >>
  Cases_on `fmp_pop_at infos fn live env p inst st` >> simp[]
QED

(* ===== Candidate plan selection ===== *)

Theorem fmp_plan_of_list_lookup:
  !l. FLOOKUP (fmp_plan_of_list l) p = ALOOKUP l p
Proof
  Induct >> simp[fmp_plan_of_list_def] >> Cases >>
  simp[fmp_plan_of_list_def, FLOOKUP_UPDATE] >> rw[]
QED

Theorem fmp_candidate_plan_lookup:
  fmp_base_analyze (fn_insts fn) = SOME env /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\ MEM bb fn.fn_blocks /\
  k < LENGTH bb.bb_instructions ==>
  FLOOKUP (fmp_candidate_plan infos (ctx:venom_context) fn states)
    (bb.bb_label,k) =
    FST (fmp_reclaim_step infos fn (liveness_analyze fn) env (bb.bb_label,k)
      (EL k bb.bb_instructions) (df_at NONE states bb.bb_label k))
Proof
  strip_tac >>
  simp[fmp_candidate_plan_def, fmp_plan_of_list_lookup] >>
  qmatch_goalsub_abbrev_tac `ALOOKUP cands pt` >>
  `!t. MEM (pt,t) cands <=>
     FST (fmp_reclaim_step infos fn (liveness_analyze fn) env (bb.bb_label,k)
       (EL k bb.bb_instructions) (df_at NONE states bb.bb_label k)) = SOME t`
    by (simp[Abbr `cands`, Abbr `pt`, fmp_collect_candidates_def, MEM_FLAT,
             MEM_MAP, PULL_EXISTS, fmp_scan_candidate_lookup] >>
        rw[EQ_IMP_THM]
        >- (`lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
             lookup_block bb'.bb_label fn.fn_blocks = SOME bb'` by
              metis_tac[venomExecPropsTheory.MEM_lookup_block] >>
            `bb' = bb` by gvs[] >> gvs[])
        >> qexists `bb` >> simp[]) >>
  Cases_on `ALOOKUP cands pt`
  >- (gvs[ALOOKUP_NONE, MEM_MAP] >>
      Cases_on `FST (fmp_reclaim_step infos fn (liveness_analyze fn) env
        (bb.bb_label,k) (EL k bb.bb_instructions)
        (df_at NONE states bb.bb_label k))` >> simp[] >>
      metis_tac[FST])
  >> drule ALOOKUP_MEM >> metis_tac[]
QED

Theorem analyze_fmp_reclaims_candidate:
  analyze_fmp_reclaims infos ctx fn = SOME plan ==>
  ?states. fmp_reclaim_states infos fn = SOME states /\
    plan = fmp_candidate_plan infos ctx fn states
Proof
  simp[analyze_fmp_reclaims_def, AllCaseEqs()] >> metis_tac[]
QED

(* The restores the walker selects at a point all name the plan's target. *)
Theorem fmp_select_point_plan:
  fmp_select_point_restores p rest = (bases,later) /\
  (!b. MEM (p,b) rest <=> FLOOKUP plan p = SOME b) ==>
  (FLOOKUP plan p = NONE ==> bases = []) /\
  (!t. FLOOKUP plan p = SOME t ==> bases <> [] /\ EVERY (\b. b = t) bases)
Proof
  strip_tac >> drule fmp_select_point_restores_once >> strip_tac >>
  rpt conj_tac >> rpt strip_tac
  >- (Cases_on `bases` >> gvs[] >> metis_tac[MEM, optionTheory.NOT_NONE_SOME])
  >- (Cases_on `bases` >> gvs[] >> metis_tac[MEM])
  >> gvs[EVERY_MEM] >> rpt strip_tac >> gvs[]
QED

(* ===== Inter-block join under block stability ===== *)

Theorem fmp_common_top_prefix:
  !xs ys. (?a. xs = fmp_common_top xs ys ++ a) /\
          (?b. ys = fmp_common_top xs ys ++ b)
Proof
  ho_match_mp_tac fmp_common_top_ind >> rw[fmp_common_top_def] >> gvs[]
QED

Theorem fmp_option_join_prefix:
  fmp_reclaim_option_join x y = SOME z ==>
  (!a. x = SOME a ==> ?k. a.frs_stack = z.frs_stack ++ k) /\
  (!b. y = SOME b ==> ?k. b.frs_stack = z.frs_stack ++ k)
Proof
  Cases_on `x` >> Cases_on `y` >>
  rw[fmp_reclaim_option_join_def, fmp_reclaim_join_def] >>
  simp[fmp_reclaim_state_accessors] >>
  metis_tac[fmp_common_top_prefix, APPEND_NIL]
QED

Theorem fmp_join_fold_prefix:
  !vals acc z. FOLDL fmp_reclaim_option_join acc vals = SOME z ==>
    (!a. acc = SOME a ==> ?k. a.frs_stack = z.frs_stack ++ k) /\
    (!b. MEM (SOME b) vals ==> ?k. b.frs_stack = z.frs_stack ++ k)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `fmp_reclaim_option_join acc h`
  >- (Cases_on `acc` >> Cases_on `h` >>
      gvs[fmp_reclaim_option_join_def]) >>
  drule fmp_option_join_prefix >> strip_tac >> gvs[] >>
  rpt strip_tac >> gvs[] >> metis_tac[APPEND_ASSOC]
QED

Theorem df_state_boundary_update_id:
  st with ds_boundary := st.ds_boundary |+ (l,v) = st ==>
  df_boundary NONE st l = v
Proof
  strip_tac >>
  `(st with ds_boundary := st.ds_boundary |+ (l,v)).ds_boundary =
     st.ds_boundary` by (first_assum SUBST1_TAC >> REFL_TAC) >>
  fs[] >> simp[df_boundary_def] >>
  pop_assum (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem fmp_process_block_stable:
  fmp_process_block transfer entry cfg bbs lbl states = states /\
  FST (fmp_fold_at transfer entry cfg bbs states lbl) = SOME exit_st ==>
  ?b. df_boundary NONE states lbl = SOME b /\
    ?k. exit_st.frs_stack = b.frs_stack ++ k
Proof
  strip_tac >>
  `fmp_reclaim_option_join (df_boundary NONE states lbl) (SOME exit_st) =
     df_boundary NONE states lbl` by
    (CCONTR_TAC >>
     qpat_x_assum `fmp_process_block _ _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac std_ss [fmp_process_block_def, LET_THM] >>
     strip_tac >> drule df_state_boundary_update_id >> strip_tac >>
     metis_tac[]) >>
  Cases_on `df_boundary NONE states lbl`
  >- fs[fmp_reclaim_option_join_def] >>
  drule fmp_option_join_prefix >> simp[] >> metis_tac[]
QED

Theorem fmp_joined_pred_prefix:
  fmp_process_block transfer entry cfg bbs pred states = states /\
  MEM pred (cfg_preds_of cfg succ) /\
  FST (fmp_fold_at transfer entry cfg bbs states pred) = SOME exit_st /\
  fmp_joined entry cfg states succ = SOME entry_st ==>
  ?ks. exit_st.frs_stack = entry_st.frs_stack ++ ks
Proof
  strip_tac >> drule_all fmp_process_block_stable >> strip_tac >>
  qabbrev_tac `vals = MAP (\nbr. df_boundary NONE states nbr)
    (cfg_preds_of cfg succ)` >>
  `MEM (SOME b) vals` by (simp[Abbr `vals`, MEM_MAP] >> metis_tac[]) >>
  `vals <> []` by (strip_tac >> gvs[]) >>
  `?z. FOLDL fmp_reclaim_option_join NONE vals = SOME z /\
       ?k. entry_st.frs_stack ++ k = z.frs_stack` suffices_by
    (strip_tac >> drule fmp_join_fold_prefix >> strip_tac >>
     first_x_assum drule >> strip_tac >> metis_tac[APPEND_ASSOC]) >>
  `?z. FOLDL fmp_reclaim_option_join NONE vals = SOME z` by
    (Cases_on `FOLDL fmp_reclaim_option_join NONE vals` >> simp[] >>
     `!vs acc. FOLDL fmp_reclaim_option_join acc vs = NONE ==>
        acc = NONE /\ EVERY IS_NONE vs` by
       (Induct >> simp[] >> rpt gen_tac >> strip_tac >>
        first_x_assum drule >> Cases_on `acc` >> Cases_on `h` >>
        simp[fmp_reclaim_option_join_def]) >>
     first_x_assum drule >> simp[EXISTS_MEM] >> qexists `SOME b` >> simp[]) >>
  qexists `z` >> simp[] >>
  qpat_x_assum `fmp_joined _ _ _ _ = _` mp_tac >>
  Cases_on `vals` >> gvs[] >>
  simp[fmp_joined_def, df_joined_val_def] >>
  qpat_x_assum `_ = h::t` (SUBST1_TAC o SYM) >> simp[] >>
  Cases_on `entry` >> simp[] >>
  TRY (strip_tac >> qexists `[]` >> simp[] >> NO_TAC) >>
  PairCases_on `x` >> simp[] >> IF_CASES_TAC >> simp[] >>
  TRY (strip_tac >> qexists `[]` >> simp[] >> NO_TAC) >>
  strip_tac >> drule fmp_option_join_prefix >> simp[] >> metis_tac[]
QED

Theorem fmp_option_join_empty:
  fmp_reclaim_option_join (SOME fmp_empty_reclaim_state) y = SOME st ==>
  st.frs_stack = []
Proof
  Cases_on `y` >>
  simp[fmp_reclaim_option_join_def, fmp_reclaim_join_def,
       fmp_empty_reclaim_state_def, fmp_common_top_def] >>
  rw[] >> simp[fmp_common_top_def]
QED

Theorem fmp_joined_entry_empty:
  fmp_joined (SOME (lbl,SOME fmp_empty_reclaim_state)) cfg states lbl =
    SOME st ==>
  st.frs_stack = []
Proof
  simp[fmp_joined_def, df_joined_val_def] >>
  metis_tac[fmp_option_join_empty]
QED

(* The parameter prefix of an entry block neither pops nor changes a
 * reachable analysis state. *)
Theorem fmp_transfer_parameter:
  MEM inst.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM] ==>
  fmp_transfer infos fn live env p inst (SOME st) = SOME st
Proof
  strip_tac >>
  `~fmp_is_reclaim_point infos inst /\ ~fmp_clears_marks infos inst` by
    (gvs[fmp_is_reclaim_point_def, fmp_clears_marks_def, fmp_callee_info_def,
         fmpAnalysisDefsTheory.fmp_invoke_target_def]) >>
  simp[fmp_transfer_def, fmp_reclaim_step_def, fmp_pop_at_def] >>
  `inst.inst_opcode <> DALLOCA` by (strip_tac >> gvs[]) >>
  `fmp_getfmp_outputs inst = []` by gvs[fmp_getfmp_outputs_def] >>
  simp[fmp_apply_effect_def, dfHelperDefsTheory.list_union_def,
       fmp_reclaim_state_component_equality]
QED

(* ===== Joined entry states ===== *)

Theorem fmp_join_fold_none:
  !vs acc. FOLDL fmp_reclaim_option_join acc vs = NONE ==>
    acc = NONE /\ EVERY IS_NONE vs
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> Cases_on `acc` >> Cases_on `h` >>
  simp[fmp_reclaim_option_join_def]
QED


Theorem fmp_option_join_some:
  y <> NONE ==> ?st. fmp_reclaim_option_join x y = SOME st
Proof
  Cases_on `x` >> Cases_on `y` >> simp[fmp_reclaim_option_join_def]
QED


Theorem fmp_case_foldl:
  (case xs of [] => NONE | v2::v3 => FOLDL fmp_reclaim_option_join NONE xs) =
  FOLDL fmp_reclaim_option_join NONE xs
Proof
  Cases_on `xs` >> simp[]
QED


Theorem fmp_joined_some:
  FOLDL fmp_reclaim_option_join NONE
    (MAP (\nbr. df_boundary NONE states nbr) (cfg_preds_of cfg lbl)) <> NONE ==>
  ?st. fmp_joined entry cfg states lbl = SOME st
Proof
  strip_tac >> Cases_on `entry` >>
  simp[fmp_joined_def, df_joined_val_def, fmp_case_foldl]
  >- metis_tac[optionTheory.option_CASES] >>
  PairCases_on `x` >> rw[] >>
  metis_tac[fmp_option_join_some, optionTheory.option_CASES]
QED


(* The entry block always has a joined state. *)
Theorem fmp_joined_entry_some:
  ?st. fmp_joined (SOME (lbl,SOME fmp_empty_reclaim_state)) cfg states lbl =
       SOME st
Proof
  simp[fmp_joined_def, df_joined_val_def, fmp_case_foldl] >>
  qmatch_goalsub_abbrev_tac `fmp_reclaim_option_join _ b` >>
  Cases_on `b` >> simp[fmp_reclaim_option_join_def]
QED


(* A block-stable predecessor with an exit state gives its successor a
   joined state. *)
Theorem fmp_joined_pred_some:
  fmp_process_block transfer entry cfg bbs pred states = states /\
  MEM pred (cfg_preds_of cfg succ) /\
  FST (fmp_fold_at transfer entry cfg bbs states pred) = SOME exit_st ==>
  ?entry_st. fmp_joined entry cfg states succ = SOME entry_st
Proof
  strip_tac >> drule_all fmp_process_block_stable >> strip_tac >>
  irule fmp_joined_some >> strip_tac >>
  drule fmp_join_fold_none >>
  simp[EXISTS_MEM, MEM_MAP, PULL_EXISTS] >>
  qexists `pred` >> simp[]
QED
