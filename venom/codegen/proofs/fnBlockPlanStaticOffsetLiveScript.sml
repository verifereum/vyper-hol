(* Definition locations and paths for OFFSET liveness. *)
Theory fnBlockPlanStaticOffsetLive
Ancestors
  fnFrameStepsRevertForward venomExecProofs rich_list list stackPlanGen venomWf pair
  livenessConvergenceProofs livenessDefs livenessBlockProofs
  codegenReadyCompute pred_set livenessProofs venomInst basePtrProofs finite_map
  fnFrameStepsPhi
  removeUnusedSsaProofs

Theorem ready_output_location_unique:
  !fn db k ub j v.
    codegen_ready_fn fn /\
    MEM db fn.fn_blocks /\ k < LENGTH db.bb_instructions /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    MEM ub fn.fn_blocks /\ j < LENGTH ub.bb_instructions /\
    MEM v (EL j ub.bb_instructions).inst_outputs ==>
    db = ub /\ k = j
Proof
  rpt strip_tac >>
  `ssa_form fn /\ fn_inst_ids_distinct fn` by
    gvs[codegen_ready_fn_def, wf_function_def] >>
  drule_all ssa_output_location >> strip_tac >>
  metis_tac[PAIR_EQ]
QED

Theorem ready_output_available:
  !fn db k ub uopt v.
    codegen_ready_fn fn /\
    MEM db fn.fn_blocks /\ k < LENGTH db.bb_instructions /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    def_available_at fn ub uopt v ==>
    fn_dominates fn db.bb_label ub.bb_label /\
    (ub = db ==> !use. uopt = SOME use ==>
      ?j. k < j /\ j < LENGTH db.bb_instructions /\
          EL j db.bb_instructions = use)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  `?p. p < LENGTH def_bb.bb_instructions /\
       EL p def_bb.bb_instructions = def_inst` by metis_tac[MEM_EL] >>
  `db = def_bb /\ k = p` by
    (irule ready_output_location_unique >> metis_tac[]) >>
  gvs[] >> rpt strip_tac >> gvs[] >>
  `i < LENGTH db.bb_instructions` by decide_tac >>
  `k = i` by (irule (cj 2 ready_output_location_unique) >> metis_tac[]) >>
  metis_tac[]
QED

Theorem fn_path_last_visit:
  !path fn d. is_fn_path fn path /\ MEM d path ==>
    ?tail. is_fn_path fn (d :: tail) /\
           LAST (d :: tail) = LAST path /\ ~MEM d tail
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `is_fn_path fn (a :: rest)` >> strip_tac >>
  Cases_on `MEM d rest`
  >- (`is_fn_path fn rest` by
        (Cases_on `rest` >> gvs[is_fn_path_def]) >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac `tail` >> Cases_on `rest` >> gvs[]) >>
  `d = a` by gvs[] >> qexists_tac `rest` >> simp[]
QED

Theorem fn_dominates_last_visit:
  !fn d n. fn_dominates fn d n ==>
    ?tail. is_fn_path fn (d :: tail) /\ LAST (d :: tail) = n /\
           ~MEM d tail /\ EVERY (fn_reachable fn) (d :: tail)
Proof
  rpt strip_tac >>
  `fn_reachable fn n` by gvs[fn_dominates_def] >>
  `?entry. fn_entry_label fn = SOME entry /\
     RTC (fn_cfg_edge fn) entry n` by gvs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >>
  `MEM d path` by (gvs[fn_dominates_def] >> metis_tac[]) >>
  drule_all fn_path_last_visit >> strip_tac >>
  qexists_tac `tail` >> simp[EVERY_MEM] >> rpt strip_tac >>
  irule is_fn_path_all_reachable >>
  qexists_tac `d :: tail` >> simp[] >>
  metis_tac[fn_dominates_dom_reachable]
QED

Theorem ready_output_other_location:
  !fn db k v ub j.
    codegen_ready_fn fn /\
    MEM db fn.fn_blocks /\ k < LENGTH db.bb_instructions /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    MEM ub fn.fn_blocks /\ j < LENGTH ub.bb_instructions /\
    (db <> ub \/ k <> j) ==>
    ~MEM v (EL j ub.bb_instructions).inst_outputs
Proof
  metis_tac[ready_output_location_unique]
QED

Theorem input_vars_from_predecessor_exit:
  !fn pred succ pb sb v.
    wf_function fn /\ fn_reachable fn pred /\ fn_cfg_edge fn pred succ /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    lookup_block succ fn.fn_blocks = SOME sb /\
    MEM v (input_vars_from pred sb.bb_instructions
      (live_vars_at (liveness_analyze fn) succ 0)) ==>
    MEM v (live_vars_at (liveness_analyze fn) pred
      (LENGTH pb.bb_instructions))
Proof
  rpt strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) pred` by
    metis_tac[fn_reachable_cfg_analyze] >>
  `MEM succ (cfg_succs_of (cfg_analyze fn) pred)` by
    metis_tac[fn_cfg_edge_cfg_analyze] >>
  drule_all liveness_recompute_edge_subset >>
  simp[liveness_edge_transfer_def, liveness_instrs_def,
       SUBSET_DEF, GSYM live_vars_at_def, GSYM liveness_analyze_def]
QED

(* Copy of makeSsaCurrentDemandDominance$current_collect_phis_length, kept until it moves below make_ssa. *)
Theorem collect_phis_length_bound:
  !instrs. LENGTH (collect_phis instrs) <= LENGTH instrs
Proof
  Induct >> simp[collect_phis_def] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[]
QED

Theorem phi_ready_postprefix_edge:
  !fn lbl bb pred v.
    wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\ bb.bb_label = lbl /\
    phi_block_ready (liveness_analyze fn) bb /\
    MEM v (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (collect_phis bb.bb_instructions))) /\
    (!k. k < LENGTH (collect_phis bb.bb_instructions) ==>
      ~MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0))
Proof
  rpt strip_tac >> irule input_vars_from_non_phi >> reverse conj_tac
  >- (drule live_vars_at_propagate_range >> simp[] >> disch_then irule >> simp[] >>
      qexists_tac `LENGTH (collect_phis bb.bb_instructions)` >>
      simp[collect_phis_length_bound]) >>
  gvs[phi_block_ready_def, EVERY_MEM, inst_uses_def] >>
  metis_tac[phi_pairs_mem_operand_vars]
QED

Theorem ready_phi_block:
  !fn bb. codegen_ready_fn fn /\ MEM bb fn.fn_blocks ==>
    phi_block_ready (liveness_analyze fn) bb
Proof
  rpt strip_tac >>
  `phi_operands_ready fn` by gvs[codegen_ready_fn_def] >>
  qpat_x_assum `phi_operands_ready fn` mp_tac >>
  rewrite_tac[phi_operands_ready_def] >>
  Cases_on `EVERY (\bb. NULL (collect_phis bb.bb_instructions)) fn.fn_blocks`
  >- (strip_tac >>
      `collect_phis bb.bb_instructions = []` by
        (qpat_x_assum `EVERY _ fn.fn_blocks` mp_tac >>
         simp[EVERY_MEM, NULL_EQ] >> disch_then drule >> simp[]) >>
      simp[phi_block_ready_def, phi_uses_disjoint_def]) >>
  simp[EVERY_MEM]
QED

Theorem ready_postprefix_edge:
  !fn lbl bb pred v.
    codegen_ready_fn fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\ bb.bb_label = lbl /\
    MEM v (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (collect_phis bb.bb_instructions))) /\
    (!k. k < LENGTH (collect_phis bb.bb_instructions) ==>
      ~MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0))
Proof
  rpt strip_tac >> irule phi_ready_postprefix_edge >> simp[] >>
  conj_tac >- gvs[codegen_ready_fn_def] >>
  irule ready_phi_block >> metis_tac[lookup_block_MEM]
QED

Theorem phi_input_fold_trigger[local]:
  !op_map matching v idx src.
    FLOOKUP op_map v = SOME idx /\ FLOOKUP matching idx = SOME src ==>
    !live acc placed.
    (MEM idx placed ==> MEM src acc) /\ (MEM v live \/ MEM src acc) ==>
    MEM src (FST (FOLDL (\(acc, placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME i => if MEM i placed then (acc, placed)
                  else case FLOOKUP matching i of
                         NONE => (acc, placed)
                       | SOME picked => (acc ++ [picked], i :: placed))
      (acc, placed) live))
Proof
  rpt gen_tac >> strip_tac >> Induct >- simp[] >>
  rpt gen_tac >> rename1 `FOLDL _ _ (head :: live)` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `FLOOKUP op_map head` >> simp[]
  >- (first_x_assum irule >> gvs[] >> metis_tac[]) >>
  rename1 `FLOOKUP op_map head = SOME i` >>
  Cases_on `MEM i placed` >> simp[]
  >- (first_x_assum irule >> gvs[] >> metis_tac[]) >>
  Cases_on `FLOOKUP matching i` >> simp[]
  >- (first_x_assum irule >> gvs[] >> metis_tac[]) >>
  first_x_assum irule >> Cases_on `idx = i` >> gvs[] >> metis_tac[]
QED

Theorem phi_input_fold_selected:
  !live acc placed op_map matching v idx.
    FLOOKUP op_map v = SOME idx /\ FLOOKUP matching idx = SOME v /\
    (MEM idx placed ==> MEM v acc) /\ (MEM v live \/ MEM v acc) ==>
    MEM v (FST (FOLDL (\(acc, placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME i => if MEM i placed then (acc, placed)
                  else case FLOOKUP matching i of
                         NONE => (acc, placed)
                       | SOME src => (acc ++ [src], i :: placed))
      (acc, placed) live))
Proof
  metis_tac[phi_input_fold_trigger]
QED

Theorem input_vars_from_trigger_maps:
  !pred instrs live op_map matching w idx src.
    build_phi_maps pred (collect_phis instrs) = (op_map, matching) /\
    FLOOKUP op_map w = SOME idx /\ FLOOKUP matching idx = SOME src /\
    MEM w live ==>
    MEM src (input_vars_from pred instrs live)
Proof
  rpt strip_tac >> simp[input_vars_from_def] >>
  Cases_on `NULL (collect_phis instrs)`
  >- gvs[NULL_EQ, build_phi_maps_def] >> simp[] >>
  qpat_x_assum `build_phi_maps _ _ = _` (fn th => rewrite_tac[th]) >>
  simp[Once UNCURRY] >>
  irule phi_input_fold_trigger >> simp[] >> metis_tac[]
QED

Theorem input_vars_from_selected_maps:
  !pred instrs live op_map matching v idx.
    build_phi_maps pred (collect_phis instrs) = (op_map, matching) /\
    FLOOKUP op_map v = SOME idx /\ FLOOKUP matching idx = SOME v /\
    MEM v live ==>
    MEM v (input_vars_from pred instrs live)
Proof
  metis_tac[input_vars_from_trigger_maps]
QED

Theorem phi_pair_updates_lookup[local]:
  !pairs (m:string |-> num) v i.
    FLOOKUP (FOLDL (\m (l,w). m |+ (w,i)) m pairs) v =
      if MEM v (MAP SND pairs) then SOME i else FLOOKUP m v
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `h` >>
  rename1 `(lbl,w)` >>
  simp[FLOOKUP_UPDATE] >> Cases_on `MEM v (MAP SND pairs)` >> simp[] >>
  Cases_on `w = v` >> simp[]
QED

Theorem phi_maps_fold_selected[local]:
  !items (om:string |-> num) (mm:num |-> string) pred v idx src.
    EVERY (\(i,phi).
      (MEM v (MAP SND (phi_pairs phi.inst_operands)) ==> i = idx) /\
      (i = idx ==> MEM v (MAP SND (phi_pairs phi.inst_operands)) /\
        FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) =
                    SOME (pred,src))) items /\
    (MEM idx (MAP FST items) \/
     (FLOOKUP om v = SOME idx /\ FLOOKUP mm idx = SOME src)) ==>
    FLOOKUP (FST (FOLDL (\(op_map,matching) (i,phi).
      (FOLDL (\m (l,w). m |+ (w,i)) op_map (phi_pairs phi.inst_operands),
       case FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) of
         NONE => matching | SOME (_,w) => matching |+ (i,w)))
      (om,mm) items)) v = SOME idx /\
    FLOOKUP (SND (FOLDL (\(op_map,matching) (i,phi).
      (FOLDL (\m (l,w). m |+ (w,i)) op_map (phi_pairs phi.inst_operands),
       case FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) of
         NONE => matching | SOME (_,w) => matching |+ (i,w)))
      (om,mm) items)) idx = SOME src
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `h` >>
  rename1 `(i,phi) :: items` >> simp[NoAsms] >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac assume_tac) >>
  first_x_assum irule >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `EVERY _ items` kall_tac >>
  Cases_on `i = idx`
  >- (qpat_x_assum `i = idx ==> _` drule >> strip_tac >>
      qpat_x_assum `MEM _ _ ==> _` kall_tac >>
      gvs[phi_pair_updates_lookup, FLOOKUP_UPDATE]) >>
  `~MEM v (MAP SND (phi_pairs phi.inst_operands))` by metis_tac[] >>
  qpat_x_assum `MEM _ _ ==> _` kall_tac >>
  qpat_x_assum `i = idx ==> _` kall_tac >>
  Cases_on `FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands)` >>
  gvs[phi_pair_updates_lookup, FLOOKUP_UPDATE, AllCaseEqs()] >>
  rename1 `FIND _ _ = SOME found` >> Cases_on `found` >>
  simp[FLOOKUP_UPDATE]
QED

Theorem phi_disjoint_source_index[local]:
  !phis i j v.
    phi_uses_disjoint phis /\ EVERY (\phi. phi.inst_opcode = PHI) phis /\
    i < LENGTH phis /\ j < LENGTH phis /\
    MEM v (MAP SND (phi_pairs (EL i phis).inst_operands)) /\
    MEM v (MAP SND (phi_pairs (EL j phis).inst_operands)) ==> i = j
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `i` >> Cases_on `j` >>
  gvs[phi_uses_disjoint_def, EVERY_MEM, inst_uses_def] >>
  metis_tac[phi_pairs_mem_operand_vars, EL_MEM]
QED

Theorem build_phi_maps_trigger:
  !phis pred w j src.
    phi_uses_disjoint phis /\ EVERY (\phi. phi.inst_opcode = PHI) phis /\
    j < LENGTH phis /\
    ALL_DISTINCT (MAP FST (phi_pairs (EL j phis).inst_operands)) /\
    MEM (pred,src) (phi_pairs (EL j phis).inst_operands) /\
    MEM w (MAP SND (phi_pairs (EL j phis).inst_operands)) ==>
    FLOOKUP (FST (build_phi_maps pred phis)) w = SOME j /\
    FLOOKUP (SND (build_phi_maps pred phis)) j = SOME src
Proof
  rpt gen_tac >> strip_tac >>
  `FIND (\(l,w). l = pred) (phi_pairs (EL j phis).inst_operands) =
     SOME (pred,src)` by (irule phi_pair_find_selected >> simp[]) >>
  simp[NoAsms, build_phi_maps_def, LET_THM] >>
  irule phi_maps_fold_selected >> conj_tac
  >- (simp[EVERY_EL, indexedListsTheory.EL_MAPi,
           indexedListsTheory.LENGTH_MAPi] >> rpt strip_tac >> gvs[] >>
      metis_tac[phi_disjoint_source_index]) >>
  disj1_tac >> simp[MEM_MAP, indexedListsTheory.MEM_MAPi] >>
  qexists_tac `(j, EL j phis)` >> simp[] >> metis_tac[]
QED

Theorem build_phi_maps_selected:
  !phis pred v j.
    phi_uses_disjoint phis /\ EVERY (\phi. phi.inst_opcode = PHI) phis /\
    j < LENGTH phis /\
    ALL_DISTINCT (MAP FST (phi_pairs (EL j phis).inst_operands)) /\
    MEM (pred,v) (phi_pairs (EL j phis).inst_operands) ==>
    FLOOKUP (FST (build_phi_maps pred phis)) v = SOME j /\
    FLOOKUP (SND (build_phi_maps pred phis)) j = SOME v
Proof
  rpt gen_tac >> strip_tac >> irule build_phi_maps_trigger >> simp[] >>
  simp[MEM_MAP] >> metis_tac[SND]
QED

Theorem input_vars_from_trigger_phi:
  !instrs phi pred src w live.
    phi_uses_disjoint (collect_phis instrs) /\
    MEM phi (collect_phis instrs) /\
    ALL_DISTINCT (MAP FST (phi_pairs phi.inst_operands)) /\
    MEM (pred,src) (phi_pairs phi.inst_operands) /\
    MEM w (MAP SND (phi_pairs phi.inst_operands)) /\ MEM w live ==>
    MEM src (input_vars_from pred instrs live)
Proof
  rpt strip_tac >>
  `?j. j < LENGTH (collect_phis instrs) /\
       EL j (collect_phis instrs) = phi` by metis_tac[MEM_EL] >>
  `EVERY (\phi. phi.inst_opcode = PHI) (collect_phis instrs)` by
    (simp[EVERY_MEM] >> metis_tac[collect_phis_mem]) >>
  `FLOOKUP (FST (build_phi_maps pred (collect_phis instrs))) w = SOME j /\
   FLOOKUP (SND (build_phi_maps pred (collect_phis instrs))) j = SOME src` by
    (irule build_phi_maps_trigger >> simp[]) >>
  irule input_vars_from_trigger_maps >> simp[] >>
  qexistsl_tac [`j`, `SND (build_phi_maps pred (collect_phis instrs))`,
    `FST (build_phi_maps pred (collect_phis instrs))`, `w`] >> simp[]
QED

Theorem input_vars_from_selected_phi:
  !instrs phi pred v live.
    phi_uses_disjoint (collect_phis instrs) /\
    MEM phi (collect_phis instrs) /\
    ALL_DISTINCT (MAP FST (phi_pairs phi.inst_operands)) /\
    MEM (pred,v) (phi_pairs phi.inst_operands) /\ MEM v live ==>
    MEM v (input_vars_from pred instrs live)
Proof
  rpt strip_tac >> irule input_vars_from_trigger_phi >> simp[] >>
  qexistsl_tac [`phi`, `v`] >> simp[MEM_MAP] >> metis_tac[SND]
QED

Theorem ready_live_range[local]:
  !fn lbl bb i j v.
    codegen_ready_fn fn /\ fn_reachable fn lbl /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    i <= j /\ j <= LENGTH bb.bb_instructions /\
    MEM v (live_vars_at (liveness_analyze fn) lbl j) /\
    (!p. i <= p /\ p < j ==>
      ~MEM v (inst_defs (EL p bb.bb_instructions))) ==>
    MEM v (live_vars_at (liveness_analyze fn) lbl i)
Proof
  rpt strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[fn_reachable_in_cfg_dfs_pre] >>
  drule live_vars_at_propagate_range >> simp[] >> disch_then irule >> simp[] >>
  metis_tac[]
QED

Theorem ready_postprefix_predecessor[local]:
  !fn pred lbl pb bb v.
    codegen_ready_fn fn /\ fn_reachable fn pred /\ fn_reachable fn lbl /\
    fn_cfg_edge fn pred lbl /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM v (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (collect_phis bb.bb_instructions))) /\
    (!p. p < LENGTH (collect_phis bb.bb_instructions) ==>
      ~MEM v (inst_defs (EL p bb.bb_instructions))) ==>
    MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))
Proof
  rpt strip_tac >> irule input_vars_from_predecessor_exit >> simp[] >>
  (conj_tac >- gvs[codegen_ready_fn_def]) >>
  qexistsl_tac [`bb`, `lbl`] >> simp[] >>
  irule ready_postprefix_edge >> simp[] >>
  conj_tac >- metis_tac[lookup_block_label] >>
  irule fn_reachable_in_cfg_dfs_pre >> gvs[codegen_ready_fn_def]
QED

Theorem ready_reachable_lookup[local]:
  !fn lbl. codegen_ready_fn fn /\ fn_reachable fn lbl ==>
    ?bb. lookup_block lbl fn.fn_blocks = SOME bb
Proof
  rpt strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by
    metis_tac[fn_reachable_cfg_analyze] >>
  drule cfgAnalysisPropsTheory.cfg_analyze_reachable_in_labels >>
  simp[fn_labels_def, MEM_MAP] >> strip_tac >>
  irule_at Any MEM_lookup_block >> simp[] >> gvs[wf_function_def, fn_labels_def] >>
  metis_tac[]
QED

Theorem ready_live_path:
  !path fn ub j v.
    codegen_ready_fn fn /\ path <> [] /\ is_fn_path fn path /\
    EVERY (fn_reachable fn) path /\
    lookup_block (LAST path) fn.fn_blocks = SOME ub /\
    LENGTH (collect_phis ub.bb_instructions) <= j /\
    j <= LENGTH ub.bb_instructions /\
    MEM v (live_vars_at (liveness_analyze fn) (LAST path) j) /\
    (!lbl bb p. MEM lbl path /\ lookup_block lbl fn.fn_blocks = SOME bb /\
       p < LENGTH bb.bb_instructions ==> ~MEM v (inst_defs (EL p bb.bb_instructions))) ==>
    !bb. lookup_block (HD path) fn.fn_blocks = SOME bb ==>
      MEM v (live_vars_at (liveness_analyze fn) (HD path)
        (LENGTH (collect_phis bb.bb_instructions)))
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `is_fn_path fn (lbl :: rest)` >> strip_tac >>
  Cases_on `rest`
  >- (gvs[] >> irule ready_live_range >> simp[] >>
      qexists_tac `j` >> simp[] >> rpt strip_tac >>
      first_x_assum irule >> decide_tac) >>
  rename1 `is_fn_path fn (lbl :: succ :: tail)` >>
  gvs[Once is_fn_path_def] >> rpt strip_tac >>
  `?sb. lookup_block succ fn.fn_blocks = SOME sb` by
    metis_tac[ready_reachable_lookup] >>
  `MEM v (live_vars_at (liveness_analyze fn) succ
      (LENGTH (collect_phis sb.bb_instructions)))` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl
      (LENGTH bb.bb_instructions))` by
    (irule ready_postprefix_predecessor >> simp[] >>
     qexistsl_tac [`sb`, `succ`] >> simp[] >>
     qx_gen_tac `p` >> disch_tac >>
     qpat_x_assum `!lbl' bb p. _` irule >> simp[] >>
     `LENGTH (collect_phis sb.bb_instructions) <= LENGTH sb.bb_instructions` by
       simp[collect_phis_length_bound] >>
     conj_tac >- decide_tac >> qexists_tac `succ` >> simp[]) >>
  irule ready_live_range >> simp[] >>
  qexists_tac `LENGTH bb.bb_instructions` >>
  simp[collect_phis_length_bound] >> metis_tac[]
QED

Theorem ready_output_suffix_live:
  !fn db k v j.
    codegen_ready_fn fn /\ MEM db fn.fn_blocks /\
    k < LENGTH db.bb_instructions /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    fn_reachable fn db.bb_label /\
    k < j /\ j <= LENGTH db.bb_instructions /\
    MEM v (live_vars_at (liveness_analyze fn) db.bb_label j) ==>
    MEM v (live_vars_at (liveness_analyze fn) db.bb_label (k+1))
Proof
  rpt strip_tac >>
  `lookup_block db.bb_label fn.fn_blocks = SOME db` by
    (irule MEM_lookup_block >> simp[] >> gvs[codegen_ready_fn_def, wf_function_def, fn_labels_def]) >>
  irule ready_live_range >> simp[] >>
  qexists_tac `j` >> simp[] >>
  qx_gen_tac `p` >> strip_tac >> simp[inst_defs_def] >>
  irule ready_output_other_location >> simp[] >>
  qexistsl_tac [`db`, `fn`, `k`] >> simp[] >> decide_tac
QED

Theorem ready_output_other_block_no_defs[local]:
  !fn db k v lbl bb p.
    codegen_ready_fn fn /\ MEM db fn.fn_blocks /\
    k < LENGTH db.bb_instructions /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    lbl <> db.bb_label /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    p < LENGTH bb.bb_instructions ==> ~MEM v (inst_defs (EL p bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >> simp[inst_defs_def] >>
  irule ready_output_other_location >> simp[] >>
  qexistsl_tac [`db`, `fn`, `k`] >> simp[] >>
  metis_tac[lookup_block_MEM, lookup_block_label]
QED

Theorem ready_output_dominated_live:
  !fn db k v ub j.
    codegen_ready_fn fn /\ MEM db fn.fn_blocks /\
    k < LENGTH db.bb_instructions /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    MEM ub fn.fn_blocks /\ fn_dominates fn db.bb_label ub.bb_label /\
    LENGTH (collect_phis ub.bb_instructions) <= j /\
    j <= LENGTH ub.bb_instructions /\
    MEM v (live_vars_at (liveness_analyze fn) ub.bb_label j) /\
    (ub = db ==> k < j) ==>
    MEM v (live_vars_at (liveness_analyze fn) db.bb_label (k+1))
Proof
  rpt gen_tac >> strip_tac >>
  `fn_reachable fn db.bb_label` by metis_tac[fn_dominates_dom_reachable] >>
  Cases_on `ub = db`
  >- (gvs[] >> irule ready_output_suffix_live >> simp[] >> metis_tac[]) >>
  `lookup_block db.bb_label fn.fn_blocks = SOME db /\
   lookup_block ub.bb_label fn.fn_blocks = SOME ub` by
    (conj_tac >> irule MEM_lookup_block >> simp[] >>
     gvs[codegen_ready_fn_def, wf_function_def, fn_labels_def]) >>
  drule fn_dominates_last_visit >> strip_tac >>
  Cases_on `tail`
  >- (gvs[] >> metis_tac[]) >>
  rename1 `is_fn_path fn (db.bb_label :: first :: rest)` >>
  `?fb. lookup_block first fn.fn_blocks = SOME fb` by
    (irule ready_reachable_lookup >> gvs[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) first
      (LENGTH (collect_phis fb.bb_instructions)))` by
    (irule (SRULE [] (Q.SPEC `first :: rest` ready_live_path)) >> simp[] >>
     (conj_tac >- gvs[]) >>
     qexistsl_tac [`j`, `rest`, `ub`] >>
     gvs[Once is_fn_path_def] >> rpt gen_tac >> strip_tac >>
     irule ready_output_other_block_no_defs >> simp[] >>
     qexistsl_tac [`db`, `fn`, `k`, `lbl`] >> simp[] >> metis_tac[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) db.bb_label
      (LENGTH db.bb_instructions))` by
    (irule ready_postprefix_predecessor >> simp[] >>
     qexistsl_tac [`fb`, `first`] >>
     gvs[Once is_fn_path_def] >> qx_gen_tac `p` >> disch_tac >>
     irule ready_output_other_block_no_defs >> simp[] >>
     (conj_tac >- (mp_tac (Q.SPEC `fb.bb_instructions` collect_phis_length_bound) >> decide_tac)) >>
     qexistsl_tac [`db`, `fn`, `k`, `first`] >> simp[]) >>
  irule ready_output_suffix_live >> simp[] >>
  qexists_tac `LENGTH db.bb_instructions` >> simp[]
QED

(* Copy of makeSsaCurrentWfSsa$current_wf_nonphi_after_collect, kept until it moves below make_ssa. *)
Theorem non_phi_after_collect_phis[local]:
  !instrs j. j < LENGTH instrs /\ (EL j instrs).inst_opcode <> PHI ==>
    LENGTH (collect_phis instrs) <= j
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `j` >>
  simp[collect_phis_def] >> Cases_on `h.inst_opcode = PHI` >> simp[]
QED

Theorem ready_ordinary_use_available[local]:
  !fn ub use v.
    codegen_ready_fn fn /\ MEM ub fn.fn_blocks /\
    MEM use ub.bb_instructions /\ use.inst_opcode <> PHI /\
    MEM (Var v) use.inst_operands ==>
    def_available_at fn ub (SOME use) v
Proof
  rpt strip_tac >>
  `def_dominates_uses fn` by
    gvs[codegen_ready_fn_def, wf_function_def, wf_ssa_def] >>
  gvs[def_dominates_uses_def] >> metis_tac[]
QED

Theorem ready_output_ordinary_use_live:
  !fn db k v ub use.
    codegen_ready_fn fn /\ MEM db fn.fn_blocks /\
    k < LENGTH db.bb_instructions /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    MEM ub fn.fn_blocks /\ MEM use ub.bb_instructions /\
    use.inst_opcode <> PHI /\ MEM (Var v) use.inst_operands ==>
    MEM v (live_vars_at (liveness_analyze fn) db.bb_label (k+1))
Proof
  rpt gen_tac >> strip_tac >>
  `def_available_at fn ub (SOME use) v` by
    metis_tac[ready_ordinary_use_available] >>
  drule_all ready_output_available >> strip_tac >>
  `?j. j < LENGTH ub.bb_instructions /\ EL j ub.bb_instructions = use /\
       (ub = db ==> k < j)` by
    (Cases_on `ub = db` >> gvs[] >> metis_tac[MEM_EL]) >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `fn_reachable fn ub.bb_label` by metis_tac[fn_dominates_def] >>
  `lookup_block ub.bb_label fn.fn_blocks = SOME ub` by
    (irule MEM_lookup_block >> simp[] >> gvs[wf_function_def, fn_labels_def]) >>
  `MEM v (live_vars_at (liveness_analyze fn) ub.bb_label j)` by
    (drule live_vars_at_uses >> simp[] >> disch_then irule >> simp[] >>
     simp[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
     irule fn_reachable_in_cfg_dfs_pre >> simp[]) >>
  irule ready_output_dominated_live >> simp[] >>
  qexistsl_tac [`j`, `ub`] >> simp[] >>
  irule non_phi_after_collect_phis >> simp[]
QED

Theorem collect_phis_index:
  !instrs j. j < LENGTH (collect_phis instrs) ==>
    EL j (collect_phis instrs) = EL j instrs /\
    (EL j instrs).inst_opcode = PHI
Proof
  Induct >- simp[collect_phis_def] >> rpt gen_tac >> simp[collect_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `j` >> simp[]
QED

Theorem phi_index_in_prefix:
  !instrs j. j < LENGTH instrs /\ (EL j instrs).inst_opcode = PHI /\
    (!i. i < j ==> (EL i instrs).inst_opcode = PHI) ==>
    j < LENGTH (collect_phis instrs)
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `j`
  >- simp[collect_phis_def] >>
  rename1 `SUC n < LENGTH (h::t)` >> strip_tac >>
  `h.inst_opcode = PHI` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[collect_phis_def] >> first_x_assum irule >> gvs[] >>
  qx_gen_tac `i` >> strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem ready_phi_use_location:
  !fn ub use. codegen_ready_fn fn /\ MEM ub fn.fn_blocks /\
    MEM use ub.bb_instructions /\ use.inst_opcode = PHI ==>
    ?j. j < LENGTH (collect_phis ub.bb_instructions) /\
        EL j ub.bb_instructions = use /\
        EL j (collect_phis ub.bb_instructions) = use
Proof
  rpt strip_tac >>
  `?j. j < LENGTH ub.bb_instructions /\ EL j ub.bb_instructions = use` by
    metis_tac[MEM_EL] >>
  `bb_well_formed ub` by gvs[codegen_ready_fn_def, wf_function_def] >>
  `j < LENGTH (collect_phis ub.bb_instructions)` by
    (irule phi_index_in_prefix >> simp[] >>
     gvs[bb_well_formed_def] >> metis_tac[]) >>
  qexists_tac `j` >> simp[collect_phis_index]
QED

Theorem ready_output_not_phi_def[local]:
  !fn db k v ub p.
    codegen_ready_fn fn /\ MEM db fn.fn_blocks /\
    k < LENGTH db.bb_instructions /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    (EL k db.bb_instructions).inst_opcode <> PHI /\
    MEM ub fn.fn_blocks /\ p < LENGTH (collect_phis ub.bb_instructions) ==>
    ~MEM v (inst_defs (EL p ub.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >> simp[inst_defs_def] >> disch_tac >>
  `p < LENGTH ub.bb_instructions` by
    (mp_tac (Q.SPEC `ub.bb_instructions` collect_phis_length_bound) >> decide_tac) >>
  `db = ub /\ k = p` by
    (irule ready_output_location_unique >> metis_tac[]) >>
  gvs[] >> metis_tac[collect_phis_index]
QED

Theorem ready_output_phi_entry_live[local]:
  !fn db k v ub use.
    codegen_ready_fn fn /\ MEM db fn.fn_blocks /\
    k < LENGTH db.bb_instructions /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    (EL k db.bb_instructions).inst_opcode <> PHI /\
    MEM ub fn.fn_blocks /\ MEM use ub.bb_instructions /\
    use.inst_opcode = PHI /\ MEM (Var v) use.inst_operands /\
    fn_reachable fn ub.bb_label ==>
    MEM v (live_vars_at (liveness_analyze fn) ub.bb_label 0)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ready_phi_use_location >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM ub.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[fn_reachable_in_cfg_dfs_pre] >>
  `lookup_block ub.bb_label fn.fn_blocks = SOME ub` by
    (irule MEM_lookup_block >> simp[] >> gvs[wf_function_def, fn_labels_def]) >>
  `j < LENGTH ub.bb_instructions` by
    (mp_tac (Q.SPEC `ub.bb_instructions` collect_phis_length_bound) >> decide_tac) >>
  `MEM v (live_vars_at (liveness_analyze fn) ub.bb_label j)` by
    (drule live_vars_at_uses >> simp[] >> disch_then irule >>
     simp[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  irule ready_live_range >> simp[] >> qexists_tac `j` >> simp[] >>
  qx_gen_tac `p` >> strip_tac >>
  irule ready_output_not_phi_def >> simp[] >>
  qexistsl_tac [`db`, `fn`, `k`] >> simp[] >> decide_tac
QED

Theorem ready_phi_edge_available[local]:
  !fn ub use v.
    codegen_ready_fn fn /\ MEM ub fn.fn_blocks /\
    MEM use ub.bb_instructions /\ use.inst_opcode = PHI /\
    MEM (Var v) use.inst_operands ==>
    ?pred pb. phi_edge_uses_wf fn ub use /\
      MEM (pred,v) (phi_pairs use.inst_operands) /\
      MEM pb fn.fn_blocks /\ pb.bb_label = pred /\
      fn_cfg_edge fn pred ub.bb_label /\ def_available_at fn pb NONE v
Proof
  rpt strip_tac >>
  `def_dominates_uses fn` by gvs[codegen_ready_fn_def] >>
  `phi_edge_uses_wf fn ub use` by
    (gvs[def_dominates_uses_def] >> metis_tac[]) >>
  `?pred. MEM (pred,v) (phi_pairs use.inst_operands)` by
    (irule phi_well_formed_var_pair >> gvs[phi_edge_uses_wf_def]) >>
  metis_tac[phi_edge_uses_wf_def]
QED

Theorem ready_output_phi_use_live:
  !fn db k v ub use.
    codegen_ready_fn fn /\ MEM db fn.fn_blocks /\
    k < LENGTH db.bb_instructions /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    (EL k db.bb_instructions).inst_opcode <> PHI /\
    MEM ub fn.fn_blocks /\ MEM use ub.bb_instructions /\
    use.inst_opcode = PHI /\ MEM (Var v) use.inst_operands ==>
    MEM v (live_vars_at (liveness_analyze fn) db.bb_label (k+1))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ready_phi_edge_available >> strip_tac >>
  drule_all ready_output_available >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `fn_reachable fn pred` by metis_tac[fn_dominates_def] >>
  `fn_reachable fn ub.bb_label` by metis_tac[fn_reachable_step] >>
  `lookup_block pred fn.fn_blocks = SOME pb /\
   lookup_block ub.bb_label fn.fn_blocks = SOME ub` by
    (conj_tac >> irule MEM_lookup_block >> simp[] >>
     gvs[wf_function_def, fn_labels_def]) >>
  `MEM v (live_vars_at (liveness_analyze fn) ub.bb_label 0)` by
    (irule ready_output_phi_entry_live >> simp[] >>
     conj_tac >- (qexistsl_tac [`db`, `k`] >> simp[]) >>
     qexists_tac `use` >> simp[]) >>
  `MEM v (input_vars_from pred ub.bb_instructions
      (live_vars_at (liveness_analyze fn) ub.bb_label 0))` by
    (`phi_block_ready (liveness_analyze fn) ub` by metis_tac[ready_phi_block] >>
     irule input_vars_from_selected_phi >> simp[] >>
     (conj_tac >- gvs[phi_block_ready_def]) >>
     qexists_tac `use` >>
     `?j. j < LENGTH (collect_phis ub.bb_instructions) /\
       EL j (collect_phis ub.bb_instructions) = use` by
       metis_tac[ready_phi_use_location] >>
     gvs[phi_block_ready_def, phi_edge_uses_wf_def] >> metis_tac[MEM_EL]) >>
  `MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))` by
    (irule input_vars_from_predecessor_exit >> simp[] >> metis_tac[]) >>
  irule ready_output_dominated_live >> simp[] >>
  qexistsl_tac [`LENGTH pb.bb_instructions`, `pb`] >>
  simp[collect_phis_length_bound] >> metis_tac[]
QED

Theorem ready_offset_output_live:
  !fn bb k v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    k < LENGTH bb.bb_instructions /\
    (EL k bb.bb_instructions).inst_opcode = OFFSET /\
    MEM v (EL k bb.bb_instructions).inst_outputs ==>
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (k+1))
Proof
  rpt gen_tac >> strip_tac >>
  `offset_outputs_used fn` by gvs[codegen_ready_fn_def] >>
  `MEM (EL k bb.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[MEM_EL]) >>
  `?ub use. MEM ub fn.fn_blocks /\ MEM use ub.bb_instructions /\
      MEM (Var v) use.inst_operands` by
    (gvs[offset_outputs_used_def, EVERY_MEM, EXISTS_MEM,
         fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  Cases_on `use.inst_opcode = PHI`
  >- (irule ready_output_phi_use_live >> simp[] >>
      qexistsl_tac [`ub`, `use`] >> simp[]) >>
  irule ready_output_ordinary_use_live >> simp[] >>
  qexistsl_tac [`ub`, `use`] >> simp[]
QED
