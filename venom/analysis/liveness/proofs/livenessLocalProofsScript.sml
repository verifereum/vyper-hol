Theory livenessLocalProofs
Ancestors
  livenessConvergenceProofs
Libs
  listTheory pred_setTheory pairTheory finite_mapTheory indexedListsTheory
  livenessDefsTheory livenessBlockProofsTheory livenessTransferProofsTheory
  livenessInvariantProofsTheory livenessTerminationProofsTheory
  worklistDefsTheory dfAnalyzeDefsTheory cfgAnalysisPropsTheory

Theorem liveness_recompute_coherent:
  lv_coherent fn.fn_blocks (liveness_recompute fn)
Proof
  mp_tac liveness_recompute_invariant >>
  simp[lv_inv_def]
QED

(* A seed cannot disappear from the queue without having been processed. *)
Theorem liveness_recompute_processed:
  MEM l (cfg_analyze fn).cfg_dfs_post ==>
  lv_processed (liveness_recompute fn) l
Proof
  strip_tac >>
  `lv_processed (liveness_recompute fn) l \/
   MEM l (FST (wl_iterate (liveness_changed fn.fn_blocks)
     (liveness_block fn.fn_blocks (cfg_analyze fn))
     (cfg_preds_of (cfg_analyze fn)) (cfg_analyze fn).cfg_dfs_post
     (init_df_state [] (MAP (\bb. bb.bb_label) fn.fn_blocks))))` suffices_by
    simp[liveness_recompute_queue_empty] >>
  simp[liveness_recompute_def] >>
  irule (liveness_recompute_lift |> Q.INST
    [`Q` |-> `\p. lv_processed (SND p) l \/ MEM l (FST p)`]
    |> BETA_RULE) >> simp[] >>
  rpt strip_tac >> Cases_on `p` >> Cases_on `q` >> gvs[] >>
  Cases_on `liveness_changed fn.fn_blocks h r
    (liveness_block fn.fn_blocks (cfg_analyze fn) h r)` >>
  gvs[wl_step_def, lv_processed_block, MEM_APPEND] >> metis_tac[]
QED

Theorem liveness_recompute_boundary_entry:
  df_boundary [] (liveness_recompute fn) lbl =
  live_vars_at (liveness_recompute fn) lbl 0
Proof
  simp[live_vars_at_def] >>
  metis_tac[liveness_recompute_coherent, lv_coherent_boundary]
QED

Theorem liveness_recompute_transfer:
  !fn lbl bb idx.
    wf_function fn ==>
    let lr = liveness_recompute fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    SUC idx <= LENGTH bb.bb_instructions ==>
    live_vars_at lr lbl idx =
      liveness_transfer fn.fn_blocks (EL idx bb.bb_instructions)
        (live_vars_at lr lbl (SUC idx))
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_post` by
    (drule cfg_analyze_reachable_sets >> simp[EXTENSION] >> metis_tac[]) >>
  drule liveness_recompute_processed >> strip_tac >>
  `liveness_instrs fn.fn_blocks lbl = bb.bb_instructions` by
    simp[liveness_instrs_def] >>
  `lv_coherent fn.fn_blocks (liveness_recompute fn)` by
    simp[liveness_recompute_coherent] >>
  `idx < LENGTH (liveness_instrs fn.fn_blocks lbl)` by simp[] >>
  drule_all lv_coherent_transfer >> simp[live_vars_at_def]
QED

Theorem liveness_recompute_uses:
  !fn lbl bb idx v.
    wf_function fn ==>
    let lr = liveness_recompute fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    idx < LENGTH bb.bb_instructions /\
    MEM v (inst_uses (EL idx bb.bb_instructions)) ==>
    MEM v (live_vars_at lr lbl idx)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >> strip_tac >>
  drule_then assume_tac liveness_recompute_transfer >>
  pop_assum (qspecl_then [`lbl`, `bb`, `idx`] mp_tac) >>
  fs[] >> simp[liveness_transfer_def, live_update_mem]
QED

Theorem liveness_recompute_propagate:
  !fn lbl bb idx v.
    wf_function fn ==>
    let lr = liveness_recompute fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    idx < LENGTH bb.bb_instructions /\
    MEM v (live_vars_at lr lbl (SUC idx)) /\
    ~MEM v (inst_defs (EL idx bb.bb_instructions)) ==>
    MEM v (live_vars_at lr lbl idx)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >> strip_tac >>
  drule_then assume_tac liveness_recompute_transfer >>
  pop_assum (qspecl_then [`lbl`, `bb`, `idx`] mp_tac) >>
  fs[] >> simp[liveness_transfer_def, live_update_mem]
QED

Theorem liveness_recompute_propagate_range:
  !fn lbl bb i j v.
    wf_function fn ==>
    let lr = liveness_recompute fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    i <= j /\ j <= LENGTH bb.bb_instructions /\
    MEM v (live_vars_at lr lbl j) /\
    (!k. i <= k /\ k < j ==> ~MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    MEM v (live_vars_at lr lbl i)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  Induct_on `j - i`
  >- (rpt strip_tac >> `i = j` by decide_tac >> gvs[]) >>
  rpt strip_tac >> `i < j` by decide_tac >>
  `MEM v (live_vars_at (liveness_recompute fn) lbl (SUC i))` by
    (first_x_assum (qspecl_then [`j`, `SUC i`] mp_tac) >>
     (impl_tac >- decide_tac) >>
     disch_then irule >> simp[] >> rpt conj_tac >> TRY decide_tac >>
     rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  drule_all liveness_recompute_propagate >>
  simp_tac std_ss [LET_THM] >>
  disch_then (qspecl_then [`lbl`, `bb`, `i`, `v`] mp_tac) >> simp[]
QED

Theorem liveness_recompute_not_live_forward:
  !fn lbl bb i j v.
    wf_function fn ==>
    let lr = liveness_recompute fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    i <= j /\ j <= LENGTH bb.bb_instructions /\
    ~MEM v (live_vars_at lr lbl i) /\
    (!k. i <= k /\ k < j ==> ~MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    ~MEM v (live_vars_at lr lbl j)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >> strip_tac >>
  CCONTR_TAC >> gvs[] >>
  drule_then assume_tac liveness_recompute_propagate_range >>
  pop_assum (qspecl_then [`lbl`, `bb`, `i`, `j`, `v`] mp_tac) >>
  simp_tac std_ss [LET_THM] >> simp[]
QED

Theorem liveness_recompute_forward_or_used:
  !fn lbl bb i j v.
    wf_function fn ==>
    let lr = liveness_recompute fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    i <= j /\ j <= LENGTH bb.bb_instructions /\
    MEM v (live_vars_at lr lbl i) /\
    (!k. i <= k /\ k < j ==> ~MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    MEM v (live_vars_at lr lbl j) \/
    (?k. i <= k /\ k < j /\ MEM v (inst_uses (EL k bb.bb_instructions)))
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  Induct_on `j - i` >> rpt strip_tac
  >- (`i = j` by decide_tac >> gvs[]) >>
  `i < j` by decide_tac >>
  drule_then assume_tac liveness_recompute_transfer >>
  pop_assum (qspecl_then [`lbl`, `bb`, `i`] mp_tac) >>
  simp_tac std_ss [LET_THM] >>
  (impl_tac >- simp[]) >> strip_tac >>
  `MEM v (liveness_transfer fn.fn_blocks (EL i bb.bb_instructions)
            (live_vars_at (liveness_recompute fn) lbl (SUC i)))` by
    metis_tac[] >>
  pop_assum mp_tac >> simp[liveness_transfer_def, live_update_mem] >> strip_tac
  >- (qpat_x_assum `!j i. _ = j - i ==> _`
        (qspecl_then [`j`, `SUC i`] mp_tac) >>
      simp[] >> metis_tac[DECIDE ``SUC i <= k ==> i <= k``])
  >- (disj2_tac >> qexists_tac `i` >> simp[])
QED

(* PHI map inversion: absence from all incoming operands implies passthrough. *)
Theorem lv_pair_update_flookup[local]:
  !pairs (m:string |-> num) n v i.
    FLOOKUP (FOLDL (\m (l,w). m |+ (w,n)) m pairs) v = SOME i ==>
    FLOOKUP m v = SOME i \/ MEM v (MAP SND pairs)
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[FLOOKUP_UPDATE] >> Cases_on `h1 = v` >> gvs[]
QED

Theorem lv_phi_op_map_mem[local]:
  !phis n acc_op acc_m src v i.
    FLOOKUP (FST (FOLDL
      (\(op_map,matching) (j,phi).
        (FOLDL (\m (l,w). m |+ (w,j)) op_map
           (phi_pairs phi.inst_operands),
         case FIND (\(l,w). l = src) (phi_pairs phi.inst_operands) of
           NONE => matching
         | SOME (_,w) => matching |+ (j,w)))
      (acc_op,acc_m) (MAPi (\k phi. (n+k,phi)) phis))) v = SOME i ==>
    FLOOKUP acc_op v = SOME i \/
    ?phi. MEM phi phis /\ MEM v (MAP SND (phi_pairs phi.inst_operands))
Proof
  Induct >> simp[MAPi_def] >> rpt gen_tac >> simp[combinTheory.o_DEF] >>
  `MAPi (\k phi'. (n + SUC k, phi')) phis =
   MAPi (\k phi'. (SUC n + k, phi')) phis` by
    (irule MAPi_CONG >> simp[]) >>
  pop_assum SUBST1_TAC >> strip_tac >>
  first_x_assum (qspecl_then [
    `SUC n`,
    `FOLDL (\m (l,w). m |+ (w,n)) acc_op (phi_pairs h.inst_operands)`,
    `case FIND (\(l,w). l = src) (phi_pairs h.inst_operands) of
       NONE => acc_m | SOME (_,w) => acc_m |+ (n,w)`,
    `src`, `v`, `i`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[]
  >- (drule lv_pair_update_flookup >> strip_tac >> gvs[] >>
      disj2_tac >> qexists_tac `h` >> simp[])
  >- (disj2_tac >> metis_tac[])
QED

Theorem lv_phi_op_map_char[local]:
  !src phis v i.
    FLOOKUP (FST (build_phi_maps src phis)) v = SOME i ==>
    ?phi. MEM phi phis /\ MEM v (MAP SND (phi_pairs phi.inst_operands))
Proof
  rw[build_phi_maps_def, LET_THM] >>
  qspecl_then [`phis`, `0`, `FEMPTY`, `FEMPTY`, `src`, `v`, `i`]
    mp_tac lv_phi_op_map_mem >> simp[]
QED

Theorem recompute_input_vars_from_non_phi:
  !src_lbl instrs base v.
    MEM v base /\
    (!inst. MEM inst (collect_phis instrs) ==>
            ~MEM v (MAP SND (phi_pairs inst.inst_operands))) ==>
    MEM v (input_vars_from src_lbl instrs base)
Proof
  rpt strip_tac >> simp[input_vars_from_def, LET_THM] >>
  Cases_on `NULL (collect_phis instrs)` >- simp[] >>
  Cases_on `build_phi_maps src_lbl (collect_phis instrs)` >>
  rename1 `_ = (op_map, matching)` >> simp[] >> simp[Once UNCURRY] >>
  `FLOOKUP op_map v = NONE` by
    (Cases_on `FLOOKUP op_map v` >> simp[] >>
     `FLOOKUP (FST (build_phi_maps src_lbl (collect_phis instrs))) v = SOME x` by
       gvs[] >>
     drule lv_phi_op_map_char >> strip_tac >> metis_tac[]) >>
  irule foldl_passthrough >> simp[]
QED

Theorem liveness_recompute_cross_block:
  !fn pred_lbl pred_bb succ_lbl succ_bb v.
    wf_function fn ==>
    let lr = liveness_recompute fn in
    let cfg = cfg_analyze fn in
    MEM pred_lbl cfg.cfg_dfs_pre /\
    MEM succ_lbl cfg.cfg_dfs_pre /\
    MEM succ_lbl (cfg_succs_of cfg pred_lbl) /\
    lookup_block pred_lbl fn.fn_blocks = SOME pred_bb /\
    lookup_block succ_lbl fn.fn_blocks = SOME succ_bb /\
    MEM v (live_vars_at lr succ_lbl 0) /\
    (!inst. MEM inst (collect_phis succ_bb.bb_instructions) ==>
            ~MEM v (MAP SND (phi_pairs inst.inst_operands))) ==>
    MEM v (live_vars_at lr pred_lbl (LENGTH pred_bb.bb_instructions))
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) pred_lbl` by
    (drule cfg_analyze_reachable_sets >> simp[EXTENSION] >> metis_tac[]) >>
  drule_all liveness_recompute_edge_subset >>
  simp[liveness_instrs_def, liveness_edge_transfer_def, SUBSET_DEF] >>
  strip_tac >> simp[live_vars_at_def] >> first_x_assum irule >>
  irule recompute_input_vars_from_non_phi >> gvs[live_vars_at_def]
QED

Theorem liveness_recompute_not_live_cross_block:
  !fn pred_lbl pred_bb succ_lbl succ_bb v.
    wf_function fn ==>
    let lr = liveness_recompute fn in
    let cfg = cfg_analyze fn in
    MEM pred_lbl cfg.cfg_dfs_pre /\
    MEM succ_lbl cfg.cfg_dfs_pre /\
    MEM succ_lbl (cfg_succs_of cfg pred_lbl) /\
    lookup_block pred_lbl fn.fn_blocks = SOME pred_bb /\
    lookup_block succ_lbl fn.fn_blocks = SOME succ_bb /\
    ~MEM v (live_vars_at lr pred_lbl (LENGTH pred_bb.bb_instructions)) /\
    (!inst. MEM inst (collect_phis succ_bb.bb_instructions) ==>
            ~MEM v (MAP SND (phi_pairs inst.inst_operands))) ==>
    ~MEM v (live_vars_at lr succ_lbl 0)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >> strip_tac >>
  CCONTR_TAC >> gvs[] >>
  drule_then assume_tac liveness_recompute_cross_block >>
  pop_assum (qspecl_then [`pred_lbl`, `pred_bb`, `succ_lbl`, `succ_bb`, `v`] mp_tac) >>
  simp_tac std_ss [LET_THM] >> simp[]
QED

val _ = List.app (fn (_,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail "oracle in liveness local API")
  (DB.thms "livenessLocalProofs");
