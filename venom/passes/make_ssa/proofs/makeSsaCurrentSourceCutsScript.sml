Theory makeSsaCurrentSourceCuts
Ancestors
  list rich_list makeSsaCurrentTreeTrace makeSsaCurrentRenameTrace
  makeSsaCurrentFinalBlock makeSsaCurrentCleanupShape makeSsaDefs
  makeSsaCurrentAnalysis makeSsaCurrentTokens cfgHelpers venomWf venomInst
  makeSsaCurrentTreePaths makeSsaCurrentInduct cfgTransformProps
  makeSsaCurrentPlacementCut
  venomExecProofs

Theorem current_local_trace_lengths:
  !aa xs s rs H E ys s' rs' H' E'.
  current_local_trace aa xs s rs H E ys s' rs' H' E' ==>
  LENGTH aa = LENGTH xs /\ LENGTH ys = LENGTH xs
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem current_local_trace_append:
  !ap xp yp s rs H E aq xq yq s' rs' H' E'.
  LENGTH ap = LENGTH xp /\ LENGTH ap = LENGTH yp ==>
  (current_local_trace (ap ++ aq) (xp ++ xq) s rs H E
     (yp ++ yq) s' rs' H' E' <=>
   ?sm rm Hm Em.
     current_local_trace ap xp s rs H E yp sm rm Hm Em /\
     current_local_trace aq xq sm rm Hm Em yq s' rs' H' E')
Proof
  Induct >> Cases_on `xp` >> Cases_on `yp` >>
  simp[current_local_trace_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`t`, `t'`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem current_local_trace_split_at:
  !n aa xs ys s rs H E s' rs' H' E'.
  n <= LENGTH aa /\ n <= LENGTH xs /\ n <= LENGTH ys ==>
  (current_local_trace aa xs s rs H E ys s' rs' H' E' <=>
   ?sm rm Hm Em.
     current_local_trace (TAKE n aa) (TAKE n xs) s rs H E
       (TAKE n ys) sm rm Hm Em /\
     current_local_trace (DROP n aa) (DROP n xs) sm rm Hm Em
       (DROP n ys) s' rs' H' E')
Proof
  Induct >- simp[current_local_trace_def] >>
  Cases_on `aa` >> Cases_on `xs` >> Cases_on `ys` >>
  simp[NoAsms, current_local_trace_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`t`, `t'`, `t''`] mp_tac) >>
  simp[NoAsms] >> metis_tac[]
QED

Definition current_source_cut_def:
  current_source_cut A
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,
     (bbs1 : basic_block list),(bbs2 : basic_block list)) n rs E <=>
  ?ap aq xp xq yp yq sm Hm.
    A l = ap ++ aq /\ bb.bb_instructions = xp ++ xq /\ ren = yp ++ yq /\
    LENGTH ap = n /\ LENGTH xp = n /\ LENGTH yp = n /\
    current_local_trace ap xp s0 rs0 H0 E0 yp sm rs Hm E /\
    current_local_trace aq xq sm rs Hm E yq s1 rs1 H1 E1
End

Theorem current_source_cut_exists:
  current_event_trace A finalH
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  n <= LENGTH bb.bb_instructions ==>
  ?rs E. current_source_cut A
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) n rs E
Proof
  simp[current_event_trace_def] >> rpt strip_tac >>
  drule current_local_trace_lengths >> strip_tac >>
  `?sm rm Hm Em.
     current_local_trace (TAKE n (A l)) (TAKE n bb.bb_instructions)
       s0 rs0 H0 E0 (TAKE n ren) sm rm Hm Em /\
     current_local_trace (DROP n (A l)) (DROP n bb.bb_instructions)
       sm rm Hm Em (DROP n ren) s1 rs1 H1 E1` by
    metis_tac[current_local_trace_split_at] >>
  qexistsl_tac [`rm`, `Em`] >> simp[current_source_cut_def] >>
  qexistsl_tac [`TAKE n (A l)`, `DROP n (A l)`,
    `TAKE n bb.bb_instructions`, `DROP n bb.bb_instructions`,
    `TAKE n ren`, `DROP n ren`, `sm`, `Hm`] >>
  simp[TAKE_DROP, LENGTH_TAKE]
QED

Theorem current_source_cut_start:
  current_source_cut A
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) 0 rs E <=>
  rs = rs0 /\ E = E0 /\
  current_local_trace (A l) bb.bb_instructions s0 rs0 H0 E0
    ren s1 rs1 H1 E1
Proof
  simp[current_source_cut_def, current_local_trace_def] >> metis_tac[]
QED

Theorem current_source_cut_end:
  current_source_cut A
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)
    (LENGTH bb.bb_instructions) rs E <=>
  rs = rs1 /\ E = E1 /\
  current_local_trace (A l) bb.bb_instructions s0 rs0 H0 E0
    ren s1 rs1 H1 E1
Proof
  eq_tac
  >- (simp[current_source_cut_def] >> rpt strip_tac >>
      `xq = []` by
        (qpat_x_assum `LENGTH xp = _` mp_tac >>
         qpat_assum `bb.bb_instructions = _` (fn th => rewrite_tac[th]) >>
         simp[]) >>
      qpat_x_assum `xq = []` SUBST_ALL_TAC >>
      drule current_local_trace_lengths >> strip_tac >>
      qpat_x_assum `LENGTH xp = _` kall_tac >>
      qpat_x_assum `LENGTH ap = _` kall_tac >>
      qpat_x_assum `LENGTH yp = _` kall_tac >>
      gvs[current_local_trace_def]) >>
  rpt strip_tac >> gvs[current_source_cut_def] >>
  drule current_local_trace_lengths >> strip_tac >>
  qexistsl_tac [`A l`, `[]`, `bb.bb_instructions`, `[]`, `ren`, `[]`, `s1`, `H1`] >>
  simp[current_local_trace_def]
QED

Theorem current_source_cut_step:
  current_source_cut A
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) n rs E /\
  n < LENGTH bb.bb_instructions ==>
  ?sm Hm sn rn Hn En.
    current_local_trace (TAKE n (A l)) (TAKE n bb.bb_instructions)
      s0 rs0 H0 E0 (TAKE n ren) sm rs Hm E /\
    current_inst_trace (EL n (A l)) (EL n bb.bb_instructions)
      sm rs Hm E (EL n ren) sn rn Hn En /\
    current_source_cut A
      (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) (SUC n) rn En
Proof
  simp[current_source_cut_def] >> rpt strip_tac >>
  `xq <> []` by
    (strip_tac >> gvs[] >> fs[]) >>
  Cases_on `aq` >> Cases_on `xq` >> Cases_on `yq` >>
  fs[current_local_trace_def] >>
  rename1 `current_inst_trace h h' sm rs Hm E h'' sn rn Hn En` >>
  qexistsl_tac [`sm`, `Hm`, `sn`, `rn`, `Hn`, `En`] >>
  conj_tac
  >- metis_tac[TAKE_LENGTH_APPEND, APPEND_ASSOC] >>
  conj_tac
  >- simp[EL_APPEND_EQN] >>
  qexistsl_tac [`ap ++ [h]`, `t`, `xp ++ [h']`, `t'`,
    `yp ++ [h'']`, `t''`, `sn`, `Hn`] >>
  simp[APPEND_ASSOC, current_local_trace_append, current_local_trace_def] >>
  metis_tac[]
QED

(* Only pass-stage equations and provenance: no runtime simulation fields. *)
Definition current_structural_certificate_def:
  current_structural_certificate s fn fn' s' A H events <=>
  ?defs ins si annsss renamed ctrs visited.
    defs = compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))) /\
    add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
      (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
        (liveness_analyze fn) fn) fn.fn_blocks defs = (ins,si) /\
    LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
      (ZIP (fn.fn_blocks,ins)) annsss /\
    A = current_annotation_map ins annsss /\
    current_tree_trace A (current_succ_map fn) (current_dom_tree fn)
      si (init_current_rename_state defs) ins [] CurrentDefault []
      ctrs s' renamed H visited events /\
    fn' = fn with fn_blocks :=
      simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed
End

Theorem current_make_ssa_stages:
  entry_block fn = SOME eb /\ make_ssa_current_fn s fn = (fn',s') ==>
  ?defs ins si ctrs renamed.
    defs = compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))) /\
    add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
      (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
        (liveness_analyze fn) fn) fn.fn_blocks defs = (ins,si) /\
    rename_current_blocks si (init_current_rename_state defs) ins
      (current_succ_map fn) (current_dom_tree fn) = (ctrs,s',renamed) /\
    fn' = fn with fn_blocks :=
      simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed
Proof
  strip_tac >>
  `fn_entry_label fn = SOME eb.bb_label` by
    fs[entry_block_def, fn_entry_label_def, AllCaseEqs()] >>
  gvs[make_ssa_current_fn_def, current_frontier_map_def, current_pred_map_def,
    current_succ_map_def, current_dom_postorder_def, current_dom_tree_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  metis_tac[]
QED

Theorem current_structural_certificate_exists:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  make_ssa_current_fn s fn = (fn',s') ==>
  ?A H events. current_structural_certificate s fn fn' s' A H events
Proof
  strip_tac >> drule_all current_make_ssa_stages >> strip_tac >>
  qpat_x_assum `defs = _` SUBST_ALL_TAC >>
  drule_all current_actual_tree_trace >>
  disch_then (qspecl_then [`[]`, `CurrentDefault`] strip_assume_tac) >>
  qexistsl_tac [`current_annotation_map ins annsss`, `H'`, `events`] >>
  simp[current_structural_certificate_def] >> metis_tac[]
QED

Theorem current_structural_certificate_final_event:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  events = before ++ ev::after ==>
  lookup_block (current_event_label ev) fn'.fn_blocks =
    SOME (if blocks_have_leading_phi fn.fn_blocks then
      simplify_current_phi_block
        (current_replay_edges (current_succ_map fn) (ev::after)
          (current_event_renamed_block ev))
      else current_replay_edges (current_succ_map fn) (ev::after)
          (current_event_renamed_block ev))
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  qpat_x_assum `events = _`
    (mp_tac o PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >> strip_tac >>
  drule_all current_trace_final_event >> strip_tac >>
  gvs[current_cleanup_if_lookup]
QED

Definition current_event_input_block_def:
  current_event_input_block
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,
     (bbs1 : basic_block list),(bbs2 : basic_block list)) = bb
End

Theorem current_trace_event_input_shape:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    ALL_DISTINCT (MAP current_event_label events) ==>
    !ev old. MEM ev events /\ lookup_block (current_event_label ev) bbs = SOME old ==>
      current_edge_shape old (current_event_input_block ev)) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    ALL_DISTINCT (MAP current_event_label events) ==>
    !ev old. MEM ev events /\ lookup_block (current_event_label ev) bbs = SOME old ==>
      current_edge_shape old (current_event_input_block ev))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      simp[current_event_label_def] >> rpt strip_tac
      >- (gvs[current_event_label_def, current_event_input_block_def] >>
          simp[current_edge_shape_refl]) >>
      `current_event_label ev <> lbl` by metis_tac[MEM_MAP] >>
      `x.bb_label = lbl` by metis_tac[lookup_block_label] >>
      `lookup_block (current_event_label ev)
         (replace_block lbl (x with bb_instructions := insts1) bbs) = SOME old` by
        simp[lookup_block_replace_neq] >>
      drule current_succ_phis_fold_lookup >> strip_tac >>
      first_x_assum drule >> disch_then drule >> strip_tac >>
      metis_tac[current_edge_shape_trans, current_block_edge_fold_shape])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  simp[ALL_DISTINCT_APPEND, MEM_MAP] >> rpt strip_tac
  >- (first_x_assum drule >> disch_then drule >> metis_tac[]) >>
  `~MEM (current_event_label ev) (MAP current_event_label events1)` by
    metis_tac[MEM_MAP] >>
  `lookup_block (current_event_label ev) bbs1 =
     SOME (current_replay_edges sm events1 old)` by
    metis_tac[cj 1 current_trace_unvisited_lookup] >>
  `current_edge_shape (current_replay_edges sm events1 old)
     (current_event_input_block ev)` by metis_tac[] >>
  metis_tac[current_edge_shape_trans, current_replay_edges_shape]
QED

Theorem current_inst_trace_opcode:
  current_inst_trace aa inst s rs H E inst' s' rs' H' E' ==>
  inst'.inst_opcode = inst.inst_opcode
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[]
QED

Theorem current_local_trace_opcodes:
  !aa xs s rs H E ys s' rs' H' E'.
  current_local_trace aa xs s rs H E ys s' rs' H' E' ==>
  MAP instruction_inst_opcode ys = MAP instruction_inst_opcode xs
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >> gvs[] >>
  drule current_inst_trace_opcode >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem current_edge_shape_opcodes:
  current_edge_shape old new ==>
  MAP instruction_inst_opcode new.bb_instructions =
    MAP instruction_inst_opcode old.bb_instructions
Proof
  simp[current_edge_shape_def, LIST_REL_EL_EQN] >> strip_tac >>
  irule LIST_EQ >> simp[EL_MAP]
QED

(* Any later edge rewrites and cleanup preserve the ordinary suffix's
   positions. This boundary deliberately says nothing about execution. *)
Theorem current_event_ordinary_index:
  current_event_trace A H
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  bb.bb_instructions = pre ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH tail /\
  (EL i tail).inst_opcode <> PHI ==>
  current_inst_no_id
    (EL (LENGTH pre + i)
      (if enabled then simplify_current_phi_block
         (current_replay_edges sm later (bb with bb_instructions := ren))
       else current_replay_edges sm later (bb with bb_instructions := ren)).bb_instructions) =
  current_inst_no_id (EL (LENGTH pre + i) ren)
Proof
  simp[current_event_trace_def] >> rpt strip_tac >>
  drule current_local_trace_opcodes >> strip_tac >>
  qspecl_then [`later`, `bb with bb_instructions := ren`] assume_tac
    current_replay_edges_shape >>
  drule current_edge_shape_opcodes >> simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `simplify_current_phi_block rb` >>
  `MAP instruction_inst_opcode rb.bb_instructions =
    MAP instruction_inst_opcode pre ++ MAP instruction_inst_opcode tail` by
    metis_tac[MAP_APPEND] >>
  `?rp rt. rb.bb_instructions = rp ++ rt /\
    MAP instruction_inst_opcode rp = MAP instruction_inst_opcode pre /\
    MAP instruction_inst_opcode rt = MAP instruction_inst_opcode tail` by
    metis_tac[MAP_EQ_APPEND] >>
  fs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  `EVERY (\inst. inst.inst_opcode = PHI) rp` by
    (fs[EVERY_EL] >> metis_tac[]) >>
  `(HD rt).inst_opcode <> PHI /\ i < LENGTH rt` by
    (Cases_on `rt` >> Cases_on `tail` >> gvs[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `i + LENGTH pre < LENGTH ren` by fs[] >>
  `(EL (i + LENGTH pre) ren).inst_opcode <> PHI` by
    (qpat_x_assum `!n. _ ==> (EL n ren).inst_opcode = _`
      (qspec_then `i + LENGTH pre` mp_tac) >> simp[EL_APPEND_EQN]) >>
  `EL (i + LENGTH pre) rb.bb_instructions = EL (i + LENGTH pre) ren` by
    (fs[current_edge_shape_def, LIST_REL_EL_EQN]) >>
  `current_inst_no_id (EL (LENGTH rp + i)
      (simplify_current_phi_block rb).bb_instructions) =
    current_inst_no_id (EL i rt)` by
    (irule current_cleanup_block_ordinary_index >> simp[] >> metis_tac[]) >>
  `EL i rt = EL (i + LENGTH pre) ren` by
    (qpat_x_assum `EL _ rb.bb_instructions = _` mp_tac >>
     simp[EL_APPEND_EQN]) >>
  Cases_on `enabled` >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem current_prefix_lookup:
  !olds news l old.
  LIST_REL (\old new. ?pre.
    new = old with bb_instructions := pre ++ old.bb_instructions /\
    EVERY (\inst. inst.inst_opcode = PHI) pre) olds news /\
  lookup_block l olds = SOME old ==>
  ?pre. lookup_block l news =
    SOME (old with bb_instructions := pre ++ old.bb_instructions) /\
    EVERY (\inst. inst.inst_opcode = PHI) pre
Proof
  Induct >> Cases_on `news` >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >> gvs[] >> IF_CASES_TAC >>
  gvs[lookup_block_def, FIND_thm] >> metis_tac[]
QED

Theorem current_certificate_source_shape:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM ev events /\ lookup_block (current_event_label ev) fn.fn_blocks = SOME old ==>
  ?pre. EVERY (\inst. inst.inst_opcode = PHI) pre /\
    current_edge_shape
      (old with bb_instructions := pre ++ old.bb_instructions)
      (current_event_input_block ev) /\ current_event_trace A H ev
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >>
  drule current_actual_insertion_prefix >> strip_tac >>
  `LIST_REL (\old new. ?pre.
     new = old with bb_instructions := pre ++ old.bb_instructions /\
     EVERY (\inst. inst.inst_opcode = PHI) pre) fn.fn_blocks ins` by
    (irule LIST_REL_mono >> goal_assum $ drule_at Any >>
     simp[] >> rpt strip_tac >> qexists_tac `pre` >> simp[] >>
     gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
     simp[build_phi_inst_supply_def] >> strip_tac >> gvs[]) >>
  drule_all current_prefix_lookup >> strip_tac >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  `ALL_DISTINCT (MAP current_event_label events)` by
    metis_tac[cj 1 current_trace_event_labels_distinct] >>
  qexists_tac `pre` >> simp[] >> conj_tac
  >- metis_tac[cj 1 current_trace_event_input_shape] >>
  metis_tac[cj 1 current_tree_trace_events, EVERY_MEM]
QED

Theorem current_edge_shape_ordinary_partition:
  current_edge_shape old bb /\ old.bb_instructions = pre ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH tail /\
  (EL i tail).inst_opcode <> PHI ==>
  ?bp bt. bb.bb_instructions = bp ++ bt /\ LENGTH bp = LENGTH pre /\
    LENGTH bt = LENGTH tail /\ EVERY (\inst. inst.inst_opcode = PHI) bp /\
    (bt = [] \/ (HD bt).inst_opcode <> PHI) /\
    EL i bt = EL i tail
Proof
  strip_tac >> gvs[] >> drule current_edge_shape_opcodes >> strip_tac >>
  `?bp bt. bb.bb_instructions = bp ++ bt /\
    MAP instruction_inst_opcode bp = MAP instruction_inst_opcode pre /\
    MAP instruction_inst_opcode bt = MAP instruction_inst_opcode tail` by
    metis_tac[MAP_APPEND, MAP_EQ_APPEND] >>
  qexistsl_tac [`bp`, `bt`] >> simp[] >>
  fs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  conj_tac
  >- (fs[EVERY_EL] >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `bt` >> Cases_on `tail` >> gvs[] >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt (qpat_x_assum `LENGTH pre + LENGTH tail = LENGTH old.bb_instructions` kall_tac) >>
  qpat_x_assum `current_edge_shape _ _`
    (mp_tac o REWRITE_RULE [current_edge_shape_def, LIST_REL_EL_EQN]) >>
  disch_then (qspec_then `LENGTH pre + i` mp_tac o CONJUNCT2 o CONJUNCT2) >>
  simp[EL_APPEND_EQN]
QED

(* The source index i includes the original leading PHIs, but not the
   inserted prefix. Cuts and the final position share exactly p+i. *)
Theorem current_certificate_ordinary_position:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  events = before ++ (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after /\
  lookup_block l fn.fn_blocks = SOME old /\
  old.bb_instructions = phis ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  j < LENGTH tail /\ (EL j tail).inst_opcode <> PHI /\ i = LENGTH phis + j ==>
  ?ip out rs E sm Hm sn rn Hn En.
    EVERY (\inst. inst.inst_opcode = PHI) ip /\
    current_edge_shape
      (old with bb_instructions := ip ++ old.bb_instructions) bb /\
    lookup_block l fn'.fn_blocks = SOME out /\
    current_source_cut A
      (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) (LENGTH ip + i) rs E /\
    current_inst_trace (EL (LENGTH ip + i) (A l)) (EL i old.bb_instructions)
      sm rs Hm E (EL (LENGTH ip + i) ren) sn rn Hn En /\
    current_source_cut A
      (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)
      (SUC (LENGTH ip + i)) rn En /\
    current_inst_no_id (EL (LENGTH ip + i) out.bb_instructions) =
      current_inst_no_id (EL (LENGTH ip + i) ren)
Proof
  strip_tac >> gvs[] >>
  drule current_certificate_source_shape >>
  disch_then (qspecl_then [`old`,
    `(l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)`, `eb`] mp_tac) >>
  simp[current_event_label_def, current_event_input_block_def] >>
  strip_tac >>
  `?bp bt. bb.bb_instructions = bp ++ bt /\
     LENGTH bp = LENGTH pre + LENGTH phis /\ LENGTH bt = LENGTH tail /\
     EVERY (\inst. inst.inst_opcode = PHI) bp /\
     (bt = [] \/ (HD bt).inst_opcode <> PHI) /\ EL j bt = EL j tail` by
    (drule current_edge_shape_ordinary_partition >>
     disch_then (qspecl_then [`tail`, `pre ++ phis`, `j`] mp_tac) >>
     simp[EVERY_APPEND, APPEND_ASSOC]) >>
  gvs[] >>
  `LENGTH bp + j < LENGTH bb.bb_instructions` by simp[] >>
  `EL (LENGTH bp + j) bb.bb_instructions = EL j tail` by
    simp[EL_APPEND_EQN] >>
  `?rs E. current_source_cut A
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) (LENGTH bp + j) rs E` by
    metis_tac[current_source_cut_exists, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  drule_all current_source_cut_step >> strip_tac >>
  `current_inst_no_id (EL (LENGTH bp + j)
     (if blocks_have_leading_phi fn.fn_blocks then
       simplify_current_phi_block
         (current_replay_edges (current_succ_map fn)
           ((l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after)
           (bb with bb_instructions := ren))
      else current_replay_edges (current_succ_map fn)
           ((l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after)
           (bb with bb_instructions := ren)).bb_instructions) =
    current_inst_no_id (EL (LENGTH bp + j) ren)` by
    (irule current_event_ordinary_index >> simp[] >> metis_tac[]) >>
  drule current_structural_certificate_final_event >>
  disch_then (qspecl_then
    [`(l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)`, `eb`, `before`, `after`] mp_tac) >>
  simp[current_event_label_def, current_event_renamed_block_def] >> strip_tac >>
  qexists_tac `pre` >> goal_assum $ drule_at Any >>
  fs[EL_APPEND_EQN, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  metis_tac[]
QED
