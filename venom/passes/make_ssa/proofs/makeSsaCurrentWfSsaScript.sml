(*
 * MakeSSA (make_ssa_current_fn, the supply variant the O1 dispatcher runs)
 * produces SSA: every variable is written once, and every use is reached
 * only through its definition.  The premises are those of the run's
 * simulation lemmas (o1ContractMakeSsa); the same statement covers the
 * first run (no PHIs in the input) and the second (the first run's PHIs).
 * One more premise: each input PHI names every label once, and only
 * predecessors.  The pass never drops a pair, so an extra or repeated label
 * would survive into the output and break phi_edge_uses_wf; on the second
 * run the first run's wf_ssa output gives it.
 *)
Theory makeSsaCurrentWfSsa
Ancestors
  livenessTransferProofs
  makeSsaDefs makeSsaCurrentProps venomWf cfgWf venomInst irSupply
  unitShapeDefs o1PassContract makeSsaCurrentRenameTrace list
  makeSsaCurrentSourceCuts makeSsaCurrentAllocation makeSsaCurrentTreeTrace
  makeSsaCurrentFinalBlock makeSsaCurrentTreePaths makeSsaCurrentTraceCertificate
  makeSsaCurrentAvailability venomExecProofs allocaRemapSSA
  makeSsaCurrentCleanupShape sorting venomFnScheduleRunner
  makeSsaCurrentCleanupBoundary makeSsaCurrentEdgeTrace makeSsaCurrentFinalSlots
  makeSsaCurrentSimDefs
  makeSsaCurrentAnalysis dominatorProofs dominatorDefs
  makeSsaCurrentPathBridge makeSsaCurrentGraphCut makeSsaCurrentCertificate
  makeSsaCurrentTokens makeSsaCurrentLiveTransport livenessAnalysisProps
  makeSsaCurrentDemand makeSsaCurrentDemandDominance makeSsaCurrentDominanceBridge
  makeSsaCurrentDemandedCut makeSsaCurrentTokenGraph makeSsaCurrentLastSite
  makeSsaCurrentPlacementCut makeSsaCurrentOccurrence makeSsaCurrentCutTokens
  makeSsaCurrentDefSupport makeSsaCurrentPlacement makeSsaCurrentFrontier
  makeSsaCurrentInduct makeSsaCurrentSelectedLive cfgDefs cfgHelpers finite_map
  codegenReadyCompute makeSsaCurrentCfg
  venomWfProps
Libs
  rich_listTheory

(* PHI-prefix extension of a block list, and that it keeps every block's
   successors. *)
Definition phi_extends_def:
  phi_extends bbs bbs' <=>
    LENGTH bbs' = LENGTH bbs /\
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs /\
    !j. j < LENGTH bbs ==>
      ?phis.
        (EL j bbs').bb_instructions =
          phis ++ (EL j bbs).bb_instructions /\
        EVERY (\i. i.inst_opcode = PHI) phis
End

Definition succs_preserved_def:
  succs_preserved bbs bbs' <=>
    !lbl bb. lookup_block lbl bbs' = SOME bb ==>
      ?bb0. lookup_block lbl bbs = SOME bb0 /\
            bb_succs bb = bb_succs bb0
End

Triviality phi_prefix_preserves_succs:
  !bb1 bb2 phis.
    bb1.bb_instructions = phis ++ bb2.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI) phis ==>
    bb_succs bb1 = bb_succs bb2
Proof
  rpt strip_tac >> Cases_on `bb2.bb_instructions`
  >- (Cases_on `phis` >> gvs[bb_succs_def] >>
      sg `MEM (LAST (h::t)) (h::t)` >- metis_tac[LAST_MEM, MEM] >>
      gvs[EVERY_MEM] >> gvs[get_successors_def, is_terminator_def])
  >> Cases_on `phis` >- gvs[bb_succs_def]
  >> sg `bb_succs bb1 =
         nub (REVERSE (get_successors (LAST (h'::(t' ++ h::t)))))` >-
       (simp[bb_succs_def] >> gvs[]) >>
  sg `bb_succs bb2 =
      nub (REVERSE (get_successors (LAST (h::t))))` >- simp[bb_succs_def] >>
  ASM_REWRITE_TAC[] >>
  AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [CONS_APPEND] THENC
                        ONCE_REWRITE_CONV [APPEND_ASSOC])) >>
  REWRITE_TAC[LAST_APPEND_CONS]
QED

Theorem phi_extends_succs_preserved:
  !bbs bbs'. phi_extends bbs bbs' /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    succs_preserved bbs bbs'
Proof
  rw[phi_extends_def, succs_preserved_def] >>
  imp_res_tac lookup_block_MEM >> gvs[MEM_EL] >>
  first_x_assum (qspec_then `n` mp_tac) >> gvs[] >> strip_tac >>
  qexists_tac `EL n bbs` >>
  imp_res_tac lookup_block_label >>
  sg `(EL n bbs).bb_label = lbl` >-
    (qpat_x_assum `MAP _ bbs' = MAP _ bbs` (mp_tac o
       Q.AP_TERM `\ls. EL n ls`) >>
     simp[EL_MAP]) >>
  conj_tac
  >- (irule MEM_lookup_block >> gvs[MEM_EL] >> metis_tac[])
  >> metis_tac[phi_prefix_preserves_succs]
QED

(* Ownership refers to the immutable original output occurrence, never to
   the supply-generated spelling of a renamed variable. *)
Definition current_wf_token_owner_def:
  (current_wf_token_owner fn (CurrentDefault w) v <=> v = w) /\
  (current_wf_token_owner fn (CurrentInserted w l) v <=> v = w) /\
  (current_wf_token_owner fn (CurrentOriginal l i j) v <=>
    ?bb. lookup_block l fn.fn_blocks = SOME bb /\
      i < LENGTH bb.bb_instructions /\
      j < LENGTH (EL i bb.bb_instructions).inst_outputs /\
      EL j (EL i bb.bb_instructions).inst_outputs = v)
End

Theorem current_wf_token_owner_functional:
  current_wf_token_owner fn t v /\ current_wf_token_owner fn t w ==> v = w
Proof
  Cases_on `t` >> simp[current_wf_token_owner_def] >> rpt strip_tac >> gvs[]
QED

Theorem current_wf_output_token_owners:
  !xs j t. current_wf_token_owner fn t v /\
    (!k. k < LENGTH xs /\ EL k xs = v ==>
      current_wf_token_owner fn (CurrentOriginal l i (j + k)) v) ==>
    current_wf_token_owner fn (current_output_token v l i j xs t) v
Proof
  Induct >> simp[current_output_token_def] >> rpt strip_tac >>
  qpat_x_assum `!j t. _` irule >> reverse conj_tac
  >- (Cases_on `h = v` >> simp[] >>
      qpat_x_assum `!k. _` (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!k. _` (qspec_then `SUC k` mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem current_wf_original_scan_owners:
  !insts i t. current_wf_token_owner fn t v /\
    (!k j. k < LENGTH insts /\ j < LENGTH (EL k insts).inst_outputs ==>
      current_wf_token_owner fn (CurrentOriginal l (i + k) j)
        (EL j (EL k insts).inst_outputs)) ==>
    current_wf_token_owner fn (current_original_scan v l i insts t) v
Proof
  Induct >> simp[current_original_scan_def] >> rpt strip_tac >>
  qpat_x_assum `!i t. _` irule >> reverse conj_tac
  >- (irule current_wf_output_token_owners >> simp[] >>
      rpt strip_tac >>
      qpat_x_assum `!k j. _` (qspecl_then [`0`, `k`] mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!k j. _` (qspecl_then [`SUC k`, `j`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem current_wf_original_scan_owner:
  lookup_block l fn.fn_blocks = SOME bb /\
  n <= LENGTH bb.bb_instructions /\ current_wf_token_owner fn t v ==>
  current_wf_token_owner fn
    (current_original_scan v l 0 (TAKE n bb.bb_instructions) t) v
Proof
  strip_tac >> irule current_wf_original_scan_owners >> simp[] >>
  rpt strip_tac >> simp[current_wf_token_owner_def] >> gvs[EL_TAKE]
QED

Theorem current_wf_block_token_owner:
  current_wf_token_owner fn t v ==>
  current_wf_token_owner fn (current_block_token fn inserted v l t) v
Proof
  strip_tac >> simp[current_block_token_def] >>
  Cases_on `lookup_block l fn.fn_blocks` >> simp[] >>
  irule current_wf_original_scan_owners >> reverse conj_tac
  >- (Cases_on `inserted v l` >> simp[current_wf_token_owner_def]) >>
  rpt strip_tac >> simp[current_wf_token_owner_def]
QED

Theorem current_wf_chain_token_owner:
  !path t. current_wf_token_owner fn t v ==>
    current_wf_token_owner fn (current_chain_token fn inserted v path t) v
Proof
  Induct >> simp[current_chain_token_def] >> rpt strip_tac >>
  first_x_assum irule >> irule current_wf_block_token_owner >> simp[]
QED

Theorem current_wf_inherited_token_owner:
  current_wf_token_owner fn (current_inherited_token fn inserted v path) v
Proof
  simp[current_inherited_token_def] >>
  irule current_wf_chain_token_owner >> simp[current_wf_token_owner_def]
QED

Theorem current_wf_owned_names_distinct:
  current_history_valid V H /\
  current_wf_token_owner fn t v /\ current_wf_token_owner fn u w /\ v <> w /\
  (!x. t <> CurrentDefault x) /\ (!x. u <> CurrentDefault x) /\
  current_token_name H t = SOME n /\ current_token_name H u = SOME m ==>
  n <> m
Proof
  strip_tac >> strip_tac >> gvs[] >>
  `t = u` by metis_tac[current_allocated_name_injective] >>
  metis_tac[current_wf_token_owner_functional]
QED

Theorem current_wf_source_cut_env:
  current_source_cut A ev n rs E ==>
  E = FOLDL (\env (t,v). (v =+ t) env) (current_event_entry_env ev)
    (FLAT (TAKE n (A (current_event_label ev))))
Proof
  PairCases_on `ev` >>
  simp[current_source_cut_def, current_event_entry_env_def,
       current_event_label_def] >> rpt strip_tac >>
  qpat_x_assum `current_local_trace aq _ _ _ _ _ _ _ _ _ _` kall_tac >>
  drule current_local_trace_exit_env >> gvs[TAKE_APPEND]
QED

Theorem current_wf_source_cut_env_unique:
  current_source_cut A ev n rs E /\ current_source_cut A ev n rs' E' ==>
  E = E'
Proof
  metis_tac[current_wf_source_cut_env]
QED

Theorem current_wf_original_annotations_take[local]:
  !insts n i. TAKE i (current_original_annotations l n insts) =
    current_original_annotations l n (TAKE i insts)
Proof
  Induct >> simp[current_original_annotations_def] >>
  gen_tac >> Cases_on `i` >> simp[current_original_annotations_def]
QED

Theorem current_wf_block_annotation_prefix_scan:
  i <= LENGTH old.bb_instructions ==>
  FOLDL (\env (t,w). (w =+ t) env) E
    (FLAT (TAKE (LENGTH pre + i) (current_block_annotations old pre))) v =
  current_original_scan v old.bb_label 0 (TAKE i old.bb_instructions)
    (if (?inst. MEM inst pre /\ MEM v inst.inst_outputs)
     then CurrentInserted v old.bb_label else E v)
Proof
  strip_tac >>
  `LENGTH (current_inserted_annotations old.bb_label pre) = LENGTH pre` by
    simp[current_inserted_annotations_def] >>
  simp[current_block_annotations_def, TAKE_APPEND,
       current_wf_original_annotations_take, TAKE_LENGTH_TOO_LONG,
       FLAT_APPEND, FOLDL_APPEND,
       current_original_annotations_scan, current_inserted_annotations_scan]
QED

Theorem current_wf_source_cut_original_scan:
  i <= LENGTH old.bb_instructions /\
  current_source_cut A ev (LENGTH pre + i) rs E /\
  current_event_label ev = old.bb_label /\
  A old.bb_label = current_block_annotations old pre ==>
  current_original_scan v old.bb_label 0 (TAKE i old.bb_instructions)
    (if (?inst. MEM inst pre /\ MEM v inst.inst_outputs)
     then CurrentInserted v old.bb_label else current_event_entry_env ev v) = E v
Proof
  strip_tac >> drule current_wf_source_cut_env >>
  disch_then SUBST1_TAC >> asm_rewrite_tac[] >>
  sym_tac >> irule current_wf_block_annotation_prefix_scan >> simp[]
QED

Theorem current_wf_source_cut_owner:
  lookup_block (current_event_label ev) fn.fn_blocks = SOME old /\
  A (current_event_label ev) = current_block_annotations old pre /\
  i <= LENGTH old.bb_instructions /\
  current_source_cut A ev (LENGTH pre + i) rs E /\
  current_wf_token_owner fn (current_event_entry_env ev v) v ==>
  current_wf_token_owner fn (E v) v
Proof
  strip_tac >>
  `current_event_label ev = old.bb_label` by metis_tac[lookup_block_label] >>
  `A old.bb_label = current_block_annotations old pre` by metis_tac[] >>
  drule_all current_wf_source_cut_original_scan >>
  disch_then (qspec_then `v` (SUBST1_TAC o SYM)) >>
  irule current_wf_original_scan_owner >>
  Cases_on `?inst. MEM inst pre /\ MEM v inst.inst_outputs` >>
  simp[current_wf_token_owner_def] >> metis_tac[]
QED

Theorem current_wf_output_token_default[local]:
  !xs j t. current_output_token v l i j xs t = CurrentDefault v <=>
    t = CurrentDefault v /\ ~MEM v xs
Proof
  Induct >> simp[current_output_token_def] >> rpt gen_tac >>
  Cases_on `h = v` >> simp[] >> metis_tac[]
QED

Theorem current_wf_original_scan_default:
  !insts i t. current_original_scan v l i insts t = CurrentDefault v <=>
    t = CurrentDefault v /\ EVERY (\inst. ~MEM v inst.inst_outputs) insts
Proof
  Induct >> simp[current_original_scan_def, current_wf_output_token_default] >>
  metis_tac[]
QED

Theorem current_wf_block_token_default:
  current_block_token fn ins v l t = CurrentDefault v <=>
  t = CurrentDefault v /\
  (!bb. lookup_block l fn.fn_blocks = SOME bb ==>
    ~ins v l /\ EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions)
Proof
  Cases_on `lookup_block l fn.fn_blocks` >>
  simp[current_block_token_def, current_wf_original_scan_default] >>
  Cases_on `ins v l` >> simp[]
QED

Theorem current_wf_chain_token_default:
  !ls t. current_chain_token fn ins v ls t = CurrentDefault v <=>
    t = CurrentDefault v /\
    EVERY (\l. current_block_token fn ins v l (CurrentDefault v) = CurrentDefault v) ls
Proof
  Induct >> simp[current_chain_token_def, current_wf_block_token_default] >>
  metis_tac[]
QED

Theorem current_wf_demand_live:
  !fn v l i. current_demand fn v l i ==>
  wf_function fn /\ all_reachable fn /\
  (!pb phi. MEM pb fn.fn_blocks /\
    MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) ==>
  MEM v (live_vars_at (liveness_analyze fn) l i)
Proof
  ntac 2 gen_tac >> ho_match_mp_tac current_demand_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  `MEM l (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `MEM l (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[current_all_labels_dfs_pre]
  >- (drule live_vars_at_uses >> simp[] >> metis_tac[])
  >- (fs[MEM_MAP] >> metis_tac[lookup_block_MEM, pairTheory.SND])
  >- (drule live_vars_at_propagate >> simp[] >> metis_tac[]) >>
  `MEM l' (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `MEM l' (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[current_all_labels_dfs_pre] >>
  `fn_cfg_edge fn l l'` by
    (simp[fn_cfg_edge_def] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  drule live_vars_at_cross_block >> simp[] >> disch_then irule >>
  simp[GSYM current_cfg_edge_succs] >>
  qexistsl [`sb`, `l'`] >> simp[] >> metis_tac[lookup_block_MEM]
QED

Theorem current_wf_single_available_nondefault:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME bb /\
  current_tree_ancestor_path (current_dom_tree fn) l path /\
  i <= LENGTH bb.bb_instructions /\ current_available fn v l i /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 ==>
  current_original_scan v l 0 (TAKE i bb.bb_instructions)
    (if current_actual_inserted fn v l then CurrentInserted v l
     else current_inherited_token fn (current_actual_inserted fn) v path)
    <> CurrentDefault v
Proof
  strip_tac >>
  `MEM l (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `fn_reachable fn l` by
    (gvs[all_reachable_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  drule_all current_available_definition >> strip_tac >>
  spose_not_then assume_tac >>
  gvs[current_wf_original_scan_default] >>
  Cases_on `current_actual_inserted fn v l` >> gvs[] >>
  Cases_on `db = bb`
  >- (gvs[] >> drule_all current_available_local_index >> strip_tac >>
      `MEM (EL j bb.bb_instructions) (TAKE i bb.bb_instructions)` by
        (simp[MEM_EL] >> qexists `j` >> simp[EL_TAKE]) >>
      fs[EVERY_MEM] >> metis_tac[]) >>
  `fn_dominates fn db.bb_label l` by
    metis_tac[current_available_unique_dominates] >>
  `MEM db.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `db.bb_label <> l` by
    (strip_tac >>
     `lookup_block l fn.fn_blocks = SOME db` by
       (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >> gvs[]) >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) db.bb_label l` by
    (simp[strict_dominates_def] >> metis_tac[current_semantic_dominates]) >>
  drule_all current_actual_path_chain >> strip_tac >>
  `MEM db.bb_label path` by
    (drule_all current_actual_chain_membership >> simp[]) >>
  gvs[current_inherited_token_def, current_wf_chain_token_default, EVERY_MEM] >>
  `lookup_block db.bb_label fn.fn_blocks = SOME db` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  qpat_x_assum `!l. MEM l path ==> _` (qspec_then `db.bb_label` mp_tac) >>
  simp[current_wf_block_token_default, EVERY_MEM] >> metis_tac[]
QED

Theorem current_wf_live_default_edge[local]:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn a b /\
  (!pb phi. MEM pb fn.fn_blocks /\ MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) /\
  ~current_actual_inserted fn v b /\ current_phi_cut_clear fn v b /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
  current_inherited_token fn (current_actual_inserted fn) v (REVERSE qs) =
    CurrentDefault v ==>
  ~current_actual_inserted fn v a /\ current_phi_cut_clear fn v a /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) a = SOME vs /\ MEM v vs) /\
  ?ps. current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps) =
      CurrentDefault v
Proof
  strip_tac >>
  `?ab bb. lookup_block a fn.fn_blocks = SOME ab /\
           lookup_block b fn.fn_blocks = SOME bb` by
    (gvs[fn_cfg_edge_def, wf_function_def, fn_succs_closed_def,
         fn_labels_def, MEM_MAP] >> metis_tac[MEM_lookup_block]) >>
  `MEM a (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  drule_all current_actual_token_chain >> strip_tac >>
  `current_block_token fn (current_actual_inserted fn) v a
     (current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps)) =
     CurrentDefault v` by
    (irule EQ_TRANS >> qexists `current_inherited_token fn
       (current_actual_inserted fn) v (REVERSE qs)` >> conj_tac
     >- (irule current_actual_demanded_cut_tokens >> simp[] >> metis_tac[]) >>
     simp[]) >>
  `~current_actual_inserted fn v a /\
   EVERY (\inst. ~MEM v inst.inst_outputs) ab.bb_instructions /\
   current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps) =
      CurrentDefault v` by
    (gvs[current_wf_block_token_default] >> metis_tac[]) >>
  `!k. k < LENGTH ab.bb_instructions ==>
    ~MEM v (inst_defs (EL k ab.bb_instructions))` by
    (fs[EVERY_MEM, inst_defs_def] >> metis_tac[EL_MEM]) >>
  `current_phi_cut_clear fn v a` by
    (simp[current_phi_cut_clear_def] >> rpt strip_tac >> gvs[] >>
     metis_tac[current_collect_phis_length, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) a = SOME vs /\ MEM v vs` by
    (irule current_selected_live_edge >> simp[] >>
     qexistsl [`b`, `bb`] >> simp[] >>
     metis_tac[current_phi_cut_clear_def, lookup_block_MEM]) >>
  simp[] >> metis_tac[]
QED

Theorem current_wf_live_default_route[local]:
  !ls a b. wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ LRC (fn_cfg_edge fn) ls a b /\
  (!pb phi. MEM pb fn.fn_blocks /\ MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) /\
  ~current_actual_inserted fn v b /\ current_phi_cut_clear fn v b /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs) /\
  (?qs. current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE qs) =
      CurrentDefault v) ==>
  ~current_actual_inserted fn v a /\ current_phi_cut_clear fn v a /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) a = SOME vs /\ MEM v vs) /\
  ?ps. current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps) =
      CurrentDefault v
Proof
  Induct
  >- (pure_rewrite_tac[LRC_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  pure_rewrite_tac[LRC_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`z`, `b`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  irule current_wf_live_default_edge >> simp[] >> metis_tac[]
QED

Theorem current_wf_path_lrc[local]:
  !fn path. path <> [] /\ is_fn_path fn path ==>
    LRC (fn_cfg_edge fn) (FRONT path) (HD path) (LAST path)
Proof
  gen_tac >> Induct_on `path` >> simp[] >>
  Cases_on `path` >>
  simp[is_fn_path_def, LRC_def, FRONT_CONS] >>
  rpt strip_tac >> qexists_tac `h` >> simp[] >>
  qpat_x_assum `_ ==> LRC _ _ _ _` mp_tac >> simp[]
QED

Theorem current_wf_analysis_dominates:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM l (fn_labels fn) /\
  dominates (dom_analyze (cfg_analyze fn) fn) d l ==>
  fn_dominates fn d l
Proof
  strip_tac >> rewrite_tac[fn_dominates_def] >> conj_tac
  >- metis_tac[current_all_labels_reachable, current_cfg_reachable] >>
  gen_tac >> strip_tac >>
  `LRC (fn_cfg_edge fn) (FRONT path) (HD path) (LAST path)` by
    metis_tac[current_wf_path_lrc] >>
  ` (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a)) = fn_cfg_edge fn` by
    simp[FUN_EQ_THM, current_cfg_edge_succs] >>
  `HD path = eb.bb_label` by gvs[fn_entry_label_def] >>
  `d = l \/ MEM d (FRONT path)` by
    (irule dom_on_every_path >>
     qexistsl [`eb`, `fn`] >> gvs[dominates_def]) >>
  metis_tac[MEM_FRONT_NOT_NIL, MEM_LAST_NOT_NIL]
QED

Theorem current_wf_tree_ancestor_dominates:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM l (fn_labels fn) /\
  current_tree_ancestor_path (current_dom_tree fn) l path /\ MEM d path ==>
  fn_dominates fn d l
Proof
  strip_tac >> irule current_wf_analysis_dominates >>
  drule_all current_actual_path_chain >> strip_tac >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) d l` by
    metis_tac[current_actual_chain_membership, MEM_REVERSE] >>
  gvs[strict_dominates_def] >> metis_tac[]
QED

(* Consumer probe: the annotation at an output position names exactly the
   concrete output at that position.  Defaults cannot be substituted here. *)
Theorem current_wf_inst_output_name[local]:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' /\
  current_annotations_ok V H anns /\ j < LENGTH anns ==>
  j < LENGTH inst'.inst_outputs /\
  current_token_name H' (FST (EL j anns)) = SOME (EL j inst'.inst_outputs)
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >>
  drule_all current_outputs_trace_names >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  first_x_assum (qspec_then `j` mp_tac) >>
  Cases_on `EL j anns` >> simp[]
QED

(* Updates cannot invent a token: its owner was assigned in the prefix,
   or the token was inherited at entry. *)
Theorem current_wf_fold_origin[local]:
  !anns E v.
  FOLDL (\env (t,w). (w =+ t) env) E anns v = E v \/
  MEM (FOLDL (\env (t,w). (w =+ t) env) E anns v,v) anns
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> simp[] >>
  first_x_assum (qspecl_then [`(h1 =+ h0) E`, `v`] mp_tac) >>
  Cases_on `h1 = v` >> simp[combinTheory.APPLY_UPDATE_THM] >>
  metis_tac[]
QED

Theorem current_wf_local_origin[local]:
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  E' v = E v \/ ?k. k < LENGTH annss /\ MEM (E' v,v) (EL k annss)
Proof
  strip_tac >> drule current_local_trace_exit_env >> strip_tac >>
  qspec_then `FLAT annss` (qspecl_then [`E`, `v`] mp_tac)
    current_wf_fold_origin >>
  simp[MEM_FLAT, MEM_EL] >> metis_tac[]
QED

Theorem current_wf_source_cut_origin[local]:
  current_source_cut A ev n rs E ==>
  E v = current_event_entry_env ev v \/
  ?k. k < n /\ k < LENGTH (A (current_event_label ev)) /\
    MEM (E v,v) (EL k (A (current_event_label ev)))
Proof
  PairCases_on `ev` >>
  simp[current_event_entry_env_def, current_event_label_def, current_source_cut_def] >> rpt strip_tac >>
  qpat_x_assum `current_local_trace aq xq _ _ _ _ _ _ _ _ _` kall_tac >>
  drule current_wf_local_origin >>
  disch_then (qspec_then `v` strip_assume_tac)
  >- simp[] >>
  disj2_tac >> qexists_tac `k` >> simp[EL_APPEND_EQN]
QED

Theorem current_wf_local_output_name[local]:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  current_annotations_ok V H (FLAT annss) ==>
  !k j. k < LENGTH annss /\ j < LENGTH (EL k annss) ==>
    k < LENGTH insts' /\ j < LENGTH (EL k insts').inst_outputs /\
    current_token_name H' (FST (EL j (EL k annss))) =
      SOME (EL j (EL k insts').inst_outputs)
Proof
  Induct >> simp[current_local_trace_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  `current_annotations_ok V H h` by
    metis_tac[current_annotations_split, FLAT] >>
  rpt gen_tac >> strip_tac >> Cases_on `k`
  >- (gvs[] >> drule_all current_wf_inst_output_name >>
      strip_tac >>
      drule current_local_trace_history >> strip_tac >> gvs[] >>
      metis_tac[current_token_name_append_stable]) >>
  `current_annotations_ok V H1 (FLAT annss)` by
    (gvs[current_inst_trace_def] >>
     irule current_outputs_trace_remaining >> metis_tac[FLAT]) >>
  first_x_assum drule >> simp[] >>
  disch_then (qspecl_then [`n`, `j`] mp_tac) >> gvs[]
QED

Theorem current_wf_outputs_trace_length[local]:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' ==>
  LENGTH names = LENGTH anns
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

(* Full output alignment, including repeated outputs within an instruction. *)
Theorem current_wf_local_output_alignment:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  MAP LENGTH annss = MAP (\inst. LENGTH inst.inst_outputs) insts'
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >> gvs[] >>
  conj_tac
  >- (gvs[current_inst_trace_def] >>
      drule current_wf_outputs_trace_length >> strip_tac >>
      Cases_on `inst.inst_opcode = PHI` >> gvs[]) >>
  first_x_assum drule >> simp[]
QED

Theorem current_wf_local_output_relation:
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  current_annotations_ok V H (FLAT annss) ==>
  LIST_REL (LIST_REL (\(t,v) n. current_token_name H' t = SOME n))
    annss (MAP (\inst. inst.inst_outputs) insts')
Proof
  strip_tac >> drule current_wf_local_output_alignment >> strip_tac >>
  drule current_wf_local_output_name >> simp[] >> strip_tac >>
  `LENGTH annss = LENGTH insts'` by metis_tac[LENGTH_MAP] >>
  simp[LIST_REL_EL_EQN, EL_MAP] >>
  qx_gen_tac `k` >> strip_tac >> conj_tac
  >- (qpat_x_assum `MAP LENGTH _ = _`
        (mp_tac o Q.AP_TERM `EL k`) >> simp[EL_MAP]) >>
  qx_gen_tac `j` >> strip_tac >>
  first_x_assum (qspecl_then [`V`, `k`, `j`] mp_tac) >>
  Cases_on `EL j (EL k annss)` >> gvs[]
QED

Theorem current_wf_named_outputs_distinct:
  !anns names.
  LIST_REL (\(t,v) n. current_token_name H t = SOME n) anns names /\
  ALL_DISTINCT (MAP FST anns) /\
  EVERY (\(t,v). !w. t <> CurrentDefault w) anns /\
  current_history_valid V H ==>
  ALL_DISTINCT names
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  Cases_on `names` >> simp[] >> rpt strip_tac >>
  gvs[MEM_EL, LIST_REL_EL_EQN] >>
      `n < LENGTH anns` by metis_tac[] >>
      qpat_x_assum `!i. i < LENGTH t ==> _` (qspec_then `n` mp_tac) >>
      Cases_on `EL n anns` >> simp[] >> strip_tac >>
      `!w. q <> CurrentDefault w` by
        (qpat_x_assum `EVERY _ anns` mp_tac >>
         simp[EVERY_EL] >> disch_then (qspec_then `n` mp_tac) >> simp[]) >>
      `h0 = q` by metis_tac[current_allocated_name_injective] >>
      qpat_x_assum `!i. h0 = _ ==> _` (qspec_then `n` mp_tac) >>
      simp[EL_MAP]
QED

Theorem current_wf_event_output_relation:
  current_event_trace A H ev /\ current_event_valid A V ev ==>
  LIST_REL (LIST_REL (\(t,v) n. current_token_name H t = SOME n))
    (A (current_event_label ev))
    (MAP (\inst. inst.inst_outputs)
      (current_event_renamed_block ev).bb_instructions)
Proof
  PairCases_on `ev` >>
  simp[current_event_trace_def, current_event_valid_def,
    current_event_label_def, current_event_renamed_block_def] >> strip_tac >>
  drule_all current_wf_local_output_relation >> strip_tac >>
  irule LIST_REL_mono >> goal_assum $ drule_at Any >>
  rpt strip_tac >> irule LIST_REL_mono >> goal_assum $ drule_at Any >>
  Cases >> simp[] >> rpt strip_tac >>
  metis_tac[current_token_name_append_stable]
QED

Theorem current_wf_list_rel_flat[local]:
  !xss yss. LIST_REL (LIST_REL R) xss yss ==>
    LIST_REL R (FLAT xss) (FLAT yss)
Proof
  Induct >> Cases_on `yss` >> simp[] >> rpt strip_tac >>
  irule LIST_REL_APPEND_suff >> simp[]
QED

Theorem current_wf_local_outputs_distinct:
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  current_annotations_ok V H (FLAT annss) /\ current_history_valid V H' ==>
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) insts'))
Proof
  strip_tac >> drule_all current_wf_local_output_relation >> strip_tac >>
  drule current_wf_list_rel_flat >> strip_tac >>
  drule current_wf_named_outputs_distinct >>
  gvs[current_annotations_ok_def, EVERY_MEM, pairTheory.FORALL_PROD] >>
  disch_then (qspec_then `V` mp_tac) >>
  (impl_tac >- metis_tac[]) >> simp[]
QED

Theorem current_wf_events_annotations_distinct:
  !events.
  ALL_DISTINCT (MAP current_event_label events) /\
  EVERY (current_event_valid A V) events /\ current_annotation_separation A ==>
  ALL_DISTINCT (MAP FST
    (FLAT (MAP (\ev. FLAT (A (current_event_label ev))) events)))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  simp[MAP_APPEND, ALL_DISTINCT_APPEND] >> conj_tac
  >- (qpat_x_assum `current_event_valid _ _ h` mp_tac >>
      PairCases_on `h` >>
      simp[current_event_valid_def, current_event_label_def,
        current_annotations_ok_def]) >>
  rpt strip_tac >> gvs[MEM_MAP, MEM_FLAT] >>
  `current_event_label h = current_event_label ev` by
    (irule (iffLR current_annotation_separation_def |> SPEC_ALL) >>
     goal_assum $ drule_at Any >> simp[MEM_MAP, MEM_FLAT] >> metis_tac[]) >>
  metis_tac[MEM_MAP]
QED

Theorem current_wf_events_output_relation:
  !events.
  EVERY (current_event_trace A H) events /\
  EVERY (current_event_valid A V) events ==>
  LIST_REL (\(t,v) n. current_token_name H t = SOME n)
    (FLAT (MAP (\ev. FLAT (A (current_event_label ev))) events))
    (FLAT (MAP (\ev. FLAT (MAP (\inst. inst.inst_outputs)
      (current_event_renamed_block ev).bb_instructions)) events))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  irule LIST_REL_APPEND_suff >> conj_tac
  >- (irule current_wf_list_rel_flat >>
      irule current_wf_event_output_relation >> metis_tac[]) >>
  first_x_assum irule >> simp[]
QED

Theorem current_wf_events_outputs_distinct:
  ALL_DISTINCT (MAP current_event_label events) /\
  EVERY (current_event_trace A H) events /\
  EVERY (current_event_valid A V) events /\
  current_annotation_separation A /\ current_history_valid V H ==>
  ALL_DISTINCT (FLAT (MAP (\ev. FLAT (MAP (\inst. inst.inst_outputs)
    (current_event_renamed_block ev).bb_instructions)) events))
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP FST
    (FLAT (MAP (\ev. FLAT (A (current_event_label ev))) events)))` by
    (irule current_wf_events_annotations_distinct >> metis_tac[]) >>
  drule_all current_wf_events_output_relation >> strip_tac >>
  drule current_wf_named_outputs_distinct >> simp[] >>
  disch_then (qspec_then `V` mp_tac) >> simp[] >>
  impl_tac >- (
    simp[EVERY_MEM, MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
    qpat_x_assum `EVERY (current_event_valid A V) events` mp_tac >>
    simp[EVERY_MEM] >> disch_then drule >>
    PairCases_on `ev` >> gvs[current_event_label_def] >> Cases_on `e` >>
    simp[current_event_valid_def, current_annotations_ok_def, EVERY_MEM] >>
    strip_tac >> qpat_x_assum `!e. MEM e _ ==> _`
      (qspec_then `(q,r)` mp_tac) >> simp[]) >> simp[]
QED

Theorem current_wf_output_family_disjoint[local]:
  !xs. ALL_DISTINCT (FLAT (MAP f xs)) ==>
  !x y v. MEM x xs /\ MEM y xs /\ x <> y /\ MEM v (f x) ==>
    ~MEM v (f y)
Proof
  Induct >> simp[ALL_DISTINCT_APPEND] >> rpt strip_tac >> gvs[] >>
  metis_tac[MEM_FLAT, MEM_MAP]
QED

Theorem current_wf_keyed_outputs_transport:
  !xs k f. ALL_DISTINCT (MAP k xs) /\ ALL_DISTINCT (FLAT (MAP f xs)) ==>
  !ys j G. ALL_DISTINCT (MAP j ys) /\
  (!y. MEM y ys ==> ?x. MEM x xs /\ k x = j y /\ ALL_DISTINCT (G y) /\
    (!v. MEM v (G y) ==> MEM v (f x))) ==>
  ALL_DISTINCT (FLAT (MAP G ys))
Proof
  rpt gen_tac >> strip_tac >> Induct >>
  simp[ALL_DISTINCT_APPEND] >> rpt strip_tac >>
  `?x. MEM x xs /\ k x = j h /\ ALL_DISTINCT (G h) /\
    (!v. MEM v (G h) ==> MEM v (f x))` by metis_tac[] >>
  `ALL_DISTINCT (FLAT (MAP G ys))` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> gvs[MEM_FLAT, MEM_MAP] >>
  `?z. MEM z xs /\ k z = j y /\ ALL_DISTINCT (G y) /\
    (!v. MEM v (G y) ==> MEM v (f z))` by metis_tac[] >>
  `x <> z` by metis_tac[MEM_MAP] >>
  metis_tac[current_wf_output_family_disjoint]
QED

Theorem current_wf_cleanup_inst_outputs[local]:
  !inst. (simplify_current_phi inst).inst_outputs = inst.inst_outputs \/
  (simplify_current_phi inst).inst_outputs = []
Proof
  `!inst. (simplify_current_phi_raw inst).inst_outputs = inst.inst_outputs \/
    (simplify_current_phi_raw inst).inst_outputs = []` by
    (gen_tac >> simp[simplify_current_phi_raw_def] >>
     Cases_on `inst.inst_opcode = PHI` >> simp[] >>
     Cases_on `current_phi_output inst.inst_outputs` >> simp[] >>
     Cases_on `current_phi_values (remove_current_phi_self x inst.inst_operands)` >>
     simp[] >> Cases_on `x'` >> simp[] >>
     Cases_on `EVERY (\w. w = h) t` >> simp[]) >>
  gen_tac >> simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem current_wf_reassign_outputs[local]:
  !ids insts. MAP (\inst. inst.inst_outputs) (reassign_current_inst_ids ids insts) =
    MAP (\inst. inst.inst_outputs) insts
Proof
  Induct >> Cases_on `insts` >> simp[reassign_current_inst_ids_def]
QED

Theorem current_wf_cleanup_parts_outputs[local]:
  !insts phis ordinary.
  simplify_current_phi_prefix_parts insts = (phis,ordinary) ==>
  (!v. MEM v (FLAT (MAP (\inst. inst.inst_outputs) (phis ++ ordinary))) ==>
       MEM v (FLAT (MAP (\inst. inst.inst_outputs) insts))) /\
  (ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) insts)) ==>
   ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) (phis ++ ordinary))))
Proof
  Induct >> simp[simplify_current_phi_prefix_parts_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[]
  >- (Cases_on `simplify_current_phi_prefix_parts insts` >> simp[] >>
      first_x_assum (qspecl_then [`q`, `r`] mp_tac) >> simp[] >> strip_tac >>
      qspec_then `h` strip_assume_tac current_wf_cleanup_inst_outputs >>
      Cases_on `(simplify_current_phi h).inst_opcode = PHI` >>
      simp[] >> strip_tac >> gvs[MAP_APPEND, FLAT_APPEND] >>
      gvs[ALL_DISTINCT_APPEND] >> metis_tac[MEM_APPEND]) >>
  strip_tac >> gvs[]
QED

Theorem current_wf_cleanup_prefix_outputs[local]:
  !insts. (!v. MEM v (FLAT (MAP (\inst. inst.inst_outputs)
       (simplify_current_phi_prefix insts))) ==>
       MEM v (FLAT (MAP (\inst. inst.inst_outputs) insts))) /\
  (ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) insts)) ==>
   ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs)
     (simplify_current_phi_prefix insts))))
Proof
  gen_tac >> Cases_on `simplify_current_phi_prefix_parts insts` >>
  drule current_wf_cleanup_parts_outputs >>
  simp[simplify_current_phi_prefix_def, current_wf_reassign_outputs] >> metis_tac[]
QED

Theorem current_wf_cleanup_block_output_member:
  MEM v (FLAT (MAP (\inst. inst.inst_outputs)
    (simplify_current_phi_block bb).bb_instructions)) ==>
  MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  Cases_on `bb.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  qspec_then `h::t` mp_tac current_wf_cleanup_prefix_outputs >> simp[] >> metis_tac[]
QED

Theorem current_wf_cleanup_block_outputs_distinct:
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions)) ==>
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs)
    (simplify_current_phi_block bb).bb_instructions))
Proof
  Cases_on `bb.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  qspec_then `h::t` mp_tac current_wf_cleanup_prefix_outputs >> simp[] >> metis_tac[]
QED

Definition current_wf_output_at_def:
  current_wf_output_at A H ev k t <=>
    k < LENGTH (A (current_event_label ev)) /\
    k < LENGTH (current_event_renamed_block ev).bb_instructions /\
    ?j. j < LENGTH (EL k (A (current_event_label ev))) /\
      FST (EL j (EL k (A (current_event_label ev)))) = t /\
      j < LENGTH (EL k (current_event_renamed_block ev).bb_instructions).inst_outputs /\
      current_token_name H t = SOME
        (EL j (EL k (current_event_renamed_block ev).bb_instructions).inst_outputs)
End

Theorem current_wf_event_output_at[local]:
  current_event_trace A H ev /\ current_event_valid A V ev /\
  k < LENGTH (A (current_event_label ev)) /\
  j < LENGTH (EL k (A (current_event_label ev))) ==>
  current_wf_output_at A H ev k
    (FST (EL j (EL k (A (current_event_label ev)))))
Proof
  PairCases_on `ev` >>
  simp[current_event_trace_def, current_event_valid_def,
    current_event_label_def, current_event_renamed_block_def,
    current_wf_output_at_def] >> strip_tac >>
  drule_all current_wf_local_output_name >> strip_tac >> simp[] >>
  qexists_tac `j` >> simp[] >>
  metis_tac[current_token_name_append_stable]
QED

Theorem current_wf_provenance_valid_events[local]:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) /\
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\
  ssa_vars_covered s (MAP FST defs) /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s (init_current_rename_state defs) bbs [] CurrentDefault []
    ctrs' s' bbs' H' visited' events ==>
  EVERY (current_event_valid (current_annotation_map bbs annsss)
    (FLAT (MAP block_ir_vars bbs))) events
Proof
  strip_tac >>
  `LENGTH bbs = LENGTH annsss` by (drule LIST_REL_LENGTH >> simp[]) >>
  `LIST_REL (\bb anns.
      LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns bb.bb_instructions)
      bbs annsss` by
    (irule current_provenance_map_owners >> metis_tac[]) >>
  `current_annotations_ok (FLAT (MAP block_ir_vars bbs))
      ([] : (current_token # string # string) list) (FLAT (FLAT annsss))` by
    (irule current_provenance_annotations_ok >> simp[] >> conj_tac
     >- (drule current_annotation_owners_in_vars >> simp[]) >>
     qexistsl_tac [`fn`, `ZIP (olds,bbs)`] >> simp[]) >>
  `current_pending_annotations (FLAT (MAP block_ir_vars bbs))
      (current_annotation_map bbs annsss) [] []` by
    metis_tac[current_annotation_map_pending] >>
  `current_annotation_separation (current_annotation_map bbs annsss)` by
    (irule current_annotation_map_separation >> fs[current_annotations_ok_def]) >>
  `current_allocation_consistent (FLAT (MAP block_ir_vars bbs))
      ([] : (current_token # string # string) list) s (init_current_rename_state defs) /\
    current_env_realizes ([] : (current_token # string # string) list)
      CurrentDefault (init_current_rename_state defs) (FLAT (MAP block_ir_vars bbs))` by
    (irule current_initial_state_valid >> simp[]) >>
  drule (cj 1 current_tree_trace_events_valid) >> simp[] >>
  disch_then irule >> simp[]
QED

(* Validity, concrete names and local projections share this single history. *)
Theorem current_wf_certificate_labels:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb ==>
  ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks) /\
  ALL_DISTINCT (MAP current_event_label events) /\
  (!b. MEM b fn'.fn_blocks ==>
    ?ev. MEM ev events /\ current_event_label ev = b.bb_label)
Proof
  strip_tac >>
  qpat_x_assum `current_structural_certificate _ _ _ _ _ _ _` mp_tac >>
  simp[current_structural_certificate_def] >> strip_tac >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks` by
    metis_tac[add_phi_nodes_supply_labels] >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==>
    IS_SOME (lookup_block l ins)` by
    metis_tac[current_actual_tree_lookup_coverage] >>
  `MAP current_event_label events = dom_tree_labels (current_dom_tree fn)` by
    metis_tac[cj 1 current_tree_trace_event_labels] >>
  `MAP (\b. b.bb_label) renamed = MAP (\b. b.bb_label) ins` by
    metis_tac[cj 1 current_tree_trace_labels] >>
  gvs[] >> conj_tac
  >- fs[wf_function_def, fn_labels_def] >> conj_tac
  >- metis_tac[current_actual_tree_labels_distinct] >>
  rpt strip_tac >>
  `MEM b.bb_label (MAP (\b. b.bb_label)
    (simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed))` by
    metis_tac[MEM_MAP] >>
  `MEM b.bb_label (fn_labels fn)` by
    (fs[fn_labels_def] >> metis_tac[]) >>
  `MEM b.bb_label (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_label_member] >>
  metis_tac[MEM_MAP]
QED

Theorem current_wf_certificate_block_outputs:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM b fn'.fn_blocks /\ MEM ev events /\ current_event_label ev = b.bb_label /\
  ALL_DISTINCT (FLAT (MAP instruction_inst_outputs
    (current_event_renamed_block ev).bb_instructions)) ==>
  ALL_DISTINCT (FLAT (MAP instruction_inst_outputs b.bb_instructions)) /\
  (!v. MEM v (FLAT (MAP instruction_inst_outputs b.bb_instructions)) ==>
    MEM v (FLAT (MAP instruction_inst_outputs
      (current_event_renamed_block ev).bb_instructions)))
Proof
  strip_tac >>
  `?before after. events = before ++ ev::after` by metis_tac[MEM_SPLIT] >>
  drule_all current_structural_certificate_final_event >> strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    metis_tac[current_wf_certificate_labels] >>
  `lookup_block b.bb_label fn'.fn_blocks = SOME b` by
    metis_tac[MEM_lookup_block] >>
  Cases_on `blocks_have_leading_phi fn.fn_blocks` >> gvs[]
  >- (conj_tac
      >- (irule (SRULE [SF ETA_ss] current_wf_cleanup_block_outputs_distinct) >>
          simp[current_replay_edges_outputs]) >>
      rpt strip_tac >> drule (SRULE [SF ETA_ss] current_wf_cleanup_block_output_member) >>
      simp[current_replay_edges_outputs]) >>
  simp[current_replay_edges_outputs]
QED

Theorem current_wf_certificate_output_coverage:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ALL_DISTINCT (FLAT (MAP (\ev. FLAT (MAP instruction_inst_outputs
    (current_event_renamed_block ev).bb_instructions)) events)) ==>
  !b. MEM b fn'.fn_blocks ==> ?ev. MEM ev events /\
    current_event_label ev = b.bb_label /\
    ALL_DISTINCT (FLAT (MAP instruction_inst_outputs b.bb_instructions)) /\
    (!v. MEM v (FLAT (MAP instruction_inst_outputs b.bb_instructions)) ==>
      MEM v (FLAT (MAP instruction_inst_outputs
        (current_event_renamed_block ev).bb_instructions)))
Proof
  strip_tac >> drule_all current_wf_certificate_labels >> strip_tac >>
  qx_gen_tac `b` >> strip_tac >>
  `?ev. MEM ev events /\ current_event_label ev = b.bb_label` by metis_tac[] >>
  `ALL_DISTINCT (FLAT (MAP instruction_inst_outputs
     (current_event_renamed_block ev).bb_instructions))` by
    (`?before after. events = before ++ ev::after` by metis_tac[MEM_SPLIT] >>
     gvs[MAP_APPEND, ALL_DISTINCT_APPEND]) >>
  qexists_tac `ev` >> simp[] >>
  metis_tac[current_wf_certificate_block_outputs]
QED

Theorem current_wf_certificate_ssa_form:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ALL_DISTINCT (FLAT (MAP (\ev. FLAT (MAP instruction_inst_outputs
    (current_event_renamed_block ev).bb_instructions)) events)) ==>
  ssa_form fn'
Proof
  strip_tac >>
  drule_all current_wf_certificate_labels >> strip_tac >>
  `!b. MEM b fn'.fn_blocks ==> ?ev. MEM ev events /\
    current_event_label ev = b.bb_label /\
    ALL_DISTINCT (FLAT (MAP instruction_inst_outputs b.bb_instructions)) /\
    (!v. MEM v (FLAT (MAP instruction_inst_outputs b.bb_instructions)) ==>
      MEM v (FLAT (MAP instruction_inst_outputs
        (current_event_renamed_block ev).bb_instructions)))` by
    metis_tac[current_wf_certificate_output_coverage] >>
  simp[ssa_form_def, fn_insts_def, fn_insts_blocks_flat,
    MAP_FLAT, FLAT_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  qspecl_then [`events`, `current_event_label`,
    `\ev. FLAT (MAP instruction_inst_outputs
      (current_event_renamed_block ev).bb_instructions)`]
    mp_tac (INST_TYPE [``:'d`` |-> ``:basic_block``]
      current_wf_keyed_outputs_transport) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`fn'.fn_blocks`, `\b. b.bb_label`,
    `\b. FLAT (MAP instruction_inst_outputs b.bb_instructions)`] mp_tac) >>
  simp[SF ETA_ss]
QED

Theorem current_wf_named_structural_certificate:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  ?A H events V.
    current_structural_certificate s fn fn' s' A H events /\
    current_history_valid V H /\ current_annotation_separation A /\
    ALL_DISTINCT (MAP current_event_label events) /\
    EVERY (current_event_valid A V) events /\
    EVERY (current_event_names H V) events /\
    EVERY (current_event_trace A H) events /\
    (!ev k j. MEM ev events /\
      k < LENGTH (A (current_event_label ev)) /\
      j < LENGTH (EL k (A (current_event_label ev))) ==>
      current_wf_output_at A H ev k
        (FST (EL j (EL k (A (current_event_label ev))))))
Proof
  strip_tac >> drule_all current_make_ssa_stages >> strip_tac >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks /\
    ssa_vars_covered si (FLAT (MAP block_ir_vars ins)) /\
    ssa_vars_covered si (MAP FST defs)` by
    (irule current_insertion_initial_supply >> metis_tac[]) >>
  `LENGTH fn.fn_blocks = LENGTH ins` by metis_tac[LENGTH_MAP] >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  qpat_x_assum `defs = _` SUBST_ALL_TAC >>
  drule_all current_actual_tree_trace >>
  disch_then (qspecl_then [`[]`, `CurrentDefault`] strip_assume_tac) >>
  `EVERY (current_event_valid (current_annotation_map ins annsss)
    (FLAT (MAP block_ir_vars ins))) events` by
    (drule_all current_wf_provenance_valid_events >> simp[]) >>
  drule_all current_provenance_initial_tree_names >> strip_tac >>
  `current_history_valid (FLAT (MAP block_ir_vars ins)) H'` by
    fs[current_allocation_consistent_def] >>
  `current_annotation_separation (current_annotation_map ins annsss)` by
    (irule current_annotation_map_separation >>
     metis_tac[LIST_REL_LENGTH, LENGTH_ZIP]) >>
  `ALL_DISTINCT (MAP current_event_label events)` by
    metis_tac[cj 1 current_trace_event_labels_distinct] >>
  `EVERY (current_event_trace (current_annotation_map ins annsss) H') events` by
    metis_tac[cj 1 current_tree_trace_events] >>
  qexistsl_tac [`current_annotation_map ins annsss`, `H'`, `events`,
    `FLAT (MAP block_ir_vars ins)`] >> simp[] >> conj_tac
  >- (simp[current_structural_certificate_def] >> metis_tac[]) >>
  rpt strip_tac >> irule current_wf_event_output_at >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem current_wf_run_ssa_form:
  wf_function fn /\ all_reachable fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==> ssa_form fn'
Proof
  strip_tac >> Cases_on `entry_block fn`
  >- (gvs[entry_block_def, fn_entry_label_def, make_ssa_current_fn_def,
        ssa_form_def, fn_insts_def, fn_insts_blocks_flat, NULL_EQ]) >>
  drule_all current_wf_named_structural_certificate >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\ev. FLAT (MAP instruction_inst_outputs
    (current_event_renamed_block ev).bb_instructions)) events))` by
    (irule (SRULE [SF ETA_ss] current_wf_events_outputs_distinct) >>
     metis_tac[]) >>
  irule current_wf_certificate_ssa_form >> metis_tac[]
QED

Theorem current_wf_path_annotation_origin:
  !path E v. current_path_env A E path v = E v \/
    ?l k. MEM l path /\ k < LENGTH (A l) /\
      MEM (current_path_env A E path v,v) (EL k (A l))
Proof
  Induct >> simp[current_path_env_def] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`current_advance_annotations A h E`, `v`] mp_tac) >>
  strip_tac
  >- (qspec_then `FLAT (A h)` (qspecl_then [`E`, `v`] mp_tac) current_wf_fold_origin >>
      fs[current_advance_annotations_def, MEM_FLAT, MEM_EL] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem current_wf_event_entry_origin:
  current_event_path A tree E ev ==>
  ?path. current_tree_ancestor_path tree (current_event_label ev) path /\
    (current_event_entry_env ev v = E v \/
     ?l k. MEM l path /\ k < LENGTH (A l) /\
       MEM (current_event_entry_env ev v,v) (EL k (A l)))
Proof
  strip_tac >> fs[current_event_path_def] >> qexists_tac `path` >> simp[] >>
  metis_tac[current_wf_path_annotation_origin]
QED

Theorem current_wf_prefix_annotation_lookup[local]:
  !(olds : basic_block list) (news : basic_block list) annsss l old.
  LENGTH olds = LENGTH news /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,news)) annsss /\
  LIST_REL (\old new. ?pre.
    new = old with bb_instructions := pre ++ old.bb_instructions /\ P old pre)
    olds news /\ lookup_block l olds = SOME old ==>
  ?pre. P old pre /\
    lookup_block l news = SOME (old with bb_instructions := pre ++ old.bb_instructions) /\
    current_annotation_map news annsss l = current_block_annotations old pre
Proof
  Induct_on `olds` >> Cases_on `news` >> Cases_on `annsss` >>
  simp[lookup_block_def, FIND_thm, current_annotation_map_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `current_block_provenance _ _ _ _` mp_tac >>
  simp[current_block_provenance_def] >> strip_tac >>
  gvs[basic_block_component_equality] >>
  IF_CASES_TAC >> gvs[]
  >- (qexists_tac `pre` >> simp[]) >>
  qpat_x_assum `!news annsss l old. _`
    (assume_tac o SRULE [lookup_block_def, current_annotation_map_def]) >>
  first_x_assum irule >> simp[]
QED

Theorem current_wf_certificate_actual_prefix:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM ev events /\ lookup_block (current_event_label ev) fn.fn_blocks = SOME old ==>
  ?pre. A (current_event_label ev) = current_block_annotations old pre /\
    EVERY (\inst. inst.inst_opcode = PHI) pre /\
    (!v. current_actual_inserted fn v (current_event_label ev) <=>
      ?inst. MEM inst pre /\ MEM v inst.inst_outputs) /\
    current_edge_shape (old with bb_instructions := pre ++ old.bb_instructions)
      (current_event_input_block ev) /\ current_event_trace A H ev
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks` by
    metis_tac[add_phi_nodes_supply_labels] >>
  `LENGTH fn.fn_blocks = LENGTH ins` by metis_tac[LENGTH_MAP] >>
  drule current_actual_insertion_prefix >> strip_tac >>
  drule_all (BETA_RULE (Q.INST [`P` |-> `\old pre.
    EVERY (\i. ?id v. i = build_phi_inst_supply id v
      (case ALOOKUP (current_pred_map fn) old.bb_label of
        SOME ps => ps | NONE => [])) pre /\
    (!v. current_actual_inserted fn v old.bb_label <=>
      ?i. MEM i pre /\ MEM v i.inst_outputs)`]
    current_wf_prefix_annotation_lookup)) >> strip_tac >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  `ALL_DISTINCT (MAP current_event_label events)` by
    metis_tac[cj 1 current_trace_event_labels_distinct] >>
  `old.bb_label = current_event_label ev` by metis_tac[lookup_block_label] >>
  drule (cj 1 current_tree_trace_events) >>
  simp[EVERY_MEM] >> strip_tac >>
  drule_all (cj 1 current_trace_event_input_shape) >> strip_tac >>
  qexists_tac `pre` >> simp[] >> conj_tac
  >- (gvs[EVERY_MEM] >> rpt strip_tac >>
      qpat_x_assum `!i. MEM i pre ==> ?id v. _` drule >>
      simp[build_phi_inst_supply_def] >> strip_tac >> gvs[]) >>
  metis_tac[]
QED

Theorem current_wf_certificate_static_entry:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM ev events ==>
  ?path. current_tree_ancestor_path (current_dom_tree fn) (current_event_label ev) path /\
    (!v. current_event_entry_env ev v =
      current_inherited_token fn (current_actual_inserted fn) v path) /\
    (!v. current_event_exit_env ev v =
      current_block_token fn (current_actual_inserted fn) v (current_event_label ev)
        (current_inherited_token fn (current_actual_inserted fn) v path))
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks` by
    metis_tac[add_phi_nodes_supply_labels] >>
  `LENGTH fn.fn_blocks = LENGTH ins` by metis_tac[LENGTH_MAP] >>
  `!old. MEM old fn.fn_blocks ==> lookup_block old.bb_label fn.fn_blocks = SOME old` by
    (rpt strip_tac >> irule MEM_lookup_block >>
     gvs[wf_function_def, fn_labels_def]) >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==>
    IS_SOME (lookup_block l ins)` by
    metis_tac[current_actual_tree_lookup_coverage] >>
  gvs[] >> drule_all current_provenance_tree_static_env >> metis_tac[]
QED

Theorem current_wf_nondefault_cut_output:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  current_structural_certificate s fn fn' s' A H events /\
  (!dev k j. MEM dev events /\ k < LENGTH (A (current_event_label dev)) /\
    j < LENGTH (EL k (A (current_event_label dev))) ==>
    current_wf_output_at A H dev k
      (FST (EL j (EL k (A (current_event_label dev)))))) /\
  MEM ev events /\ current_source_cut A ev n rs E /\ E v <> CurrentDefault v ==>
  ?dev k. MEM dev events /\ current_wf_output_at A H dev k (E v) /\
    ((dev = ev /\ k < n) \/
     (current_event_label dev <> current_event_label ev /\
      fn_dominates fn (current_event_label dev) (current_event_label ev)))
Proof
  strip_tac >>
  `current_event_path A (current_dom_tree fn) CurrentDefault ev` by
    (fs[current_structural_certificate_def] >>
     metis_tac[cj 1 current_tree_trace_paths, EVERY_MEM]) >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==>
    ?dev. MEM dev events /\ current_event_label dev = l` by
    (fs[current_structural_certificate_def] >>
     `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks` by
       metis_tac[add_phi_nodes_supply_labels] >>
     metis_tac[current_tree_trace_event_coverage, current_actual_tree_lookup_coverage]) >>
  drule current_wf_source_cut_origin >> disch_then (qspec_then `v` strip_assume_tac)
  >- (drule current_wf_event_entry_origin >>
      disch_then (qspec_then `v` strip_assume_tac) >> gvs[] >>
      `?dev. MEM dev events /\ current_event_label dev = l` by
        metis_tac[current_tree_ancestor_path_labels] >>
      `?j. j < LENGTH (EL k (A l)) /\ EL j (EL k (A l)) = (E v,v)` by
        metis_tac[MEM_EL] >>
      `current_wf_output_at A H dev k (E v)` by metis_tac[pairTheory.FST] >>
      `MEM (current_event_label ev) (fn_labels fn)` by
        metis_tac[current_tree_ancestor_path_labels, current_actual_tree_label_member] >>
      `fn_dominates fn l (current_event_label ev)` by
        metis_tac[current_wf_tree_ancestor_dominates] >>
      drule_all current_actual_path_chain >> strip_tac >>
      `strict_dominates (dom_analyze (cfg_analyze fn) fn) l (current_event_label ev)` by
        metis_tac[current_actual_chain_membership, MEM_REVERSE] >>
      fs[strict_dominates_def] >> metis_tac[]) >>
  `?j. j < LENGTH (EL k (A (current_event_label ev))) /\
    EL j (EL k (A (current_event_label ev))) = (E v,v)` by metis_tac[MEM_EL] >>
  metis_tac[pairTheory.FST]
QED

Theorem current_wf_entry_unavailable:
  fn_entry_label fn = SOME l ==> ~current_available fn v l 0
Proof
  strip_tac >> simp[current_available_def] >> rpt strip_tac >>
  qexists_tac `[l]` >> simp[is_fn_path_def]
QED

Theorem current_wf_selected_live_nondefault:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  first_block_no_phi fn /\ entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME bb /\
  current_tree_ancestor_path (current_dom_tree fn) l path /\
  (!pb phi. MEM pb fn.fn_blocks /\ MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) /\
  ~current_actual_inserted fn v l /\ current_phi_cut_clear fn v l /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) l = SOME vs /\ MEM v vs) ==>
  current_inherited_token fn (current_actual_inserted fn) v path <> CurrentDefault v
Proof
  strip_tac >> spose_not_then assume_tac >>
  `MEM l (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  drule_all current_actual_path_chain >> strip_tac >>
  `fn_reachable fn l` by
    (gvs[all_reachable_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `fn_entry_label fn = SOME eb.bb_label` by simp[fn_entry_label_def] >>
  `?route. is_fn_path fn route /\ route <> [] /\
     HD route = eb.bb_label /\ LAST route = l` by
    (gvs[fn_reachable_def] >> metis_tac[rtc_to_fn_path]) >>
  `LRC (fn_cfg_edge fn) (FRONT route) eb.bb_label l` by
    metis_tac[current_wf_path_lrc] >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) eb.bb_label = SOME vs /\ MEM v vs` by
    (mp_tac current_wf_live_default_route >>
     disch_then (qspecl_then [`FRONT route`, `eb.bb_label`, `l`] mp_tac) >>
     simp[] >> (impl_tac >- (conj_tac >- metis_tac[] >>
       qexists `REVERSE path` >> simp[])) >> metis_tac[]) >>
  `lookup_block eb.bb_label fn.fn_blocks = SOME eb` by
    (irule MEM_lookup_block >>
     gvs[entry_block_def, wf_function_def, fn_labels_def] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  `collect_phis eb.bb_instructions = []` by
    (gvs[first_block_no_phi_def, entry_block_def] >>
     Cases_on `fn.fn_blocks` >> gvs[] >>
     rename1 `EVERY _ hb.bb_instructions` >>
     Cases_on `hb.bb_instructions` >> gvs[livenessDefsTheory.collect_phis_def]) >>
  `MEM v (live_vars_at (liveness_analyze fn) eb.bb_label 0)` by
    metis_tac[current_selected_live_iff, listTheory.LENGTH] >>
  `current_available fn v eb.bb_label 0` by
    (irule current_live_post_phi_available >> simp[] >> metis_tac[]) >>
  metis_tac[current_wf_entry_unavailable]
QED

Theorem current_wf_demanded_cut_nondefault:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  first_block_no_phi fn /\ entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME bb /\
  current_tree_ancestor_path (current_dom_tree fn) l path /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\
  i <= LENGTH bb.bb_instructions /\ current_demand fn v l i ==>
  current_original_scan v l 0 (TAKE i bb.bb_instructions)
    (if current_actual_inserted fn v l then CurrentInserted v l
     else current_inherited_token fn (current_actual_inserted fn) v path)
    <> CurrentDefault v
Proof
  strip_tac >>
  Cases_on `?pb phi. MEM pb fn.fn_blocks /\
    MEM phi (collect_phis pb.bb_instructions) /\
    MEM v (MAP SND (phi_pairs phi.inst_operands))`
  >- (irule current_wf_single_available_nondefault >> simp[] >>
      metis_tac[current_phi_operand_single_bound, current_demand_available]) >>
  `!pb phi. MEM pb fn.fn_blocks /\ MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))` by metis_tac[] >>
  spose_not_then assume_tac >>
  gvs[current_wf_original_scan_default] >>
  Cases_on `current_actual_inserted fn v l` >> gvs[] >>
  `!k. k < i ==> ~MEM v (inst_defs (EL k bb.bb_instructions))` by
    (fs[EVERY_MEM, inst_defs_def] >> rpt strip_tac >>
     `MEM (EL k bb.bb_instructions) (TAKE i bb.bb_instructions)` by
       (simp[MEM_EL] >> qexists `k` >> simp[EL_TAKE]) >> metis_tac[]) >>
  `current_phi_cut_clear fn v l` by
    (simp[current_phi_cut_clear_def] >> rpt strip_tac >> gvs[] >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `MEM v (live_vars_at (liveness_analyze fn) l i)` by
    metis_tac[current_wf_demand_live] >>
  `MEM l (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `MEM l (cfg_analyze fn).cfg_dfs_pre` by metis_tac[current_all_labels_dfs_pre] >>
  `MEM v (live_vars_at (liveness_analyze fn) l
    (LENGTH (collect_phis bb.bb_instructions)))` by
    (drule live_vars_at_propagate_range >> simp[] >> disch_then irule >>
     simp[] >> qexists `i` >> simp[]) >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) l = SOME vs /\ MEM v vs` by
    metis_tac[current_selected_live_iff] >>
  metis_tac[current_wf_selected_live_nondefault]
QED

Theorem current_wf_demanded_source_cut_nondefault:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  first_block_no_phi fn /\ entry_block fn = SOME eb /\
  MEM ev events /\ lookup_block (current_event_label ev) fn.fn_blocks = SOME old /\
  A (current_event_label ev) = current_block_annotations old pre /\
  (!v. current_actual_inserted fn v (current_event_label ev) <=>
    ?inst. MEM inst pre /\ MEM v inst.inst_outputs) /\
  LENGTH (collect_phis old.bb_instructions) <= i /\
  i <= LENGTH old.bb_instructions /\
  current_demand fn v (current_event_label ev) i /\
  current_source_cut A ev (LENGTH pre + i) rs E ==>
  E v <> CurrentDefault v
Proof
  strip_tac >>
  `old.bb_label = current_event_label ev` by metis_tac[lookup_block_label] >>
  drule_all current_wf_certificate_static_entry >> strip_tac >>
  drule_all current_wf_demanded_cut_nondefault >> strip_tac >>
  `current_event_label ev = old.bb_label` by simp[] >>
  `A old.bb_label = current_block_annotations old pre` by metis_tac[] >>
  drule_all current_wf_source_cut_original_scan >>
  disch_then (qspec_then `v` mp_tac) >>
  qpat_x_assum `current_event_label ev = old.bb_label` kall_tac >>
  qpat_x_assum `!v. current_actual_inserted fn v _ <=> _`
    (fn th => rewrite_tac[GSYM th]) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem current_wf_demanded_source_cut_output:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  first_block_no_phi fn /\ entry_block fn = SOME eb /\
  (!dev k j. MEM dev events /\ k < LENGTH (A (current_event_label dev)) /\
    j < LENGTH (EL k (A (current_event_label dev))) ==>
    current_wf_output_at A H dev k
      (FST (EL j (EL k (A (current_event_label dev)))))) /\
  MEM ev events /\ lookup_block (current_event_label ev) fn.fn_blocks = SOME old /\
  A (current_event_label ev) = current_block_annotations old pre /\
  (!v. current_actual_inserted fn v (current_event_label ev) <=>
    ?inst. MEM inst pre /\ MEM v inst.inst_outputs) /\
  LENGTH (collect_phis old.bb_instructions) <= i /\
  i <= LENGTH old.bb_instructions /\
  current_demand fn v (current_event_label ev) i /\
  current_source_cut A ev (LENGTH pre + i) rs E ==>
  ?dev k. MEM dev events /\ current_wf_output_at A H dev k (E v) /\
    ((dev = ev /\ k < LENGTH pre + i) \/
     (current_event_label dev <> current_event_label ev /\
      fn_dominates fn (current_event_label dev) (current_event_label ev)))
Proof
  strip_tac >>
  `E v <> CurrentDefault v` by
    (irule current_wf_demanded_source_cut_nondefault >> metis_tac[]) >>
  irule current_wf_nondefault_cut_output >> metis_tac[]
QED

Definition current_wf_precleanup_certificate_def:
  current_wf_precleanup_certificate s fn renamed s' A H events <=>
  ?defs ins si annsss ctrs visited.
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
      ctrs s' renamed H visited events
End

Theorem current_wf_precleanup_certificate_stages:
  current_structural_certificate s fn fn' s' A H events <=>
  ?renamed. current_wf_precleanup_certificate s fn renamed s' A H events /\
    fn' = fn with fn_blocks :=
      simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed
Proof
  simp[current_structural_certificate_def, current_wf_precleanup_certificate_def] >>
  metis_tac[]
QED

Theorem current_wf_precleanup_names:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s ==>
  ?defs ins si.
    defs = compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))) /\
    add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
      (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
        (liveness_analyze fn) fn) fn.fn_blocks defs = (ins,si) /\
    current_history_valid (FLAT (MAP block_ir_vars ins)) H /\
    EVERY (current_event_names H (FLAT (MAP block_ir_vars ins))) events /\
    EVERY (current_event_valid A (FLAT (MAP block_ir_vars ins))) events /\
    EVERY (current_event_trace A H) events
Proof
  simp[current_wf_precleanup_certificate_def] >> rpt strip_tac >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks /\
    ssa_vars_covered si (FLAT (MAP block_ir_vars ins)) /\
    ssa_vars_covered si (MAP FST (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn))))))` by
    (irule current_insertion_initial_supply >> metis_tac[]) >>
  `LENGTH fn.fn_blocks = LENGTH ins` by metis_tac[LENGTH_MAP] >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  `ALL_DISTINCT (MAP FST (FLAT (FLAT annsss)))` by
    (irule current_provenance_global_distinct >>
     qexistsl_tac [`fn`, `fn.fn_blocks`] >> conj_tac
     >- fs[wf_function_def, fn_labels_def] >>
     fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
     qexists_tac `EL n ins` >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[EL_ZIP]) >>
  gvs[] >>
  drule_all current_provenance_initial_tree_names >> strip_tac >>
  drule_all current_wf_provenance_valid_events >> strip_tac >>
  drule (cj 1 current_tree_trace_events) >> strip_tac >>
  fs[current_allocation_consistent_def]
QED

Theorem current_wf_precleanup_event:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM ev events ==>
  ?bb. lookup_block (current_event_label ev) renamed = SOME bb /\
    current_edge_shape (current_event_renamed_block ev) bb
Proof
  simp[current_wf_precleanup_certificate_def] >> rpt strip_tac >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  `?before after. events = before ++ ev::after` by metis_tac[MEM_SPLIT] >>
  drule_all current_trace_final_event >> strip_tac >>
  goal_assum (drule_at Any) >> simp[current_replay_edges_shape]
QED

Theorem current_wf_rename_operand_labels[local]:
  !ops. MAP get_label (rename_current_operands rs ops) = MAP get_label ops
Proof
  Induct >> simp[rename_current_operands_def] >>
  Cases_on `h` >> simp[rename_current_operands_def, venomStateTheory.get_label_def]
QED

Theorem current_wf_inst_trace_successors:
  current_inst_trace aa inst s rs H E inst' s' rs' H' E' ==>
  get_successors inst' = get_successors inst
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `inst.inst_opcode = PHI` >>
  simp[get_successors_def, current_wf_rename_operand_labels]
QED

Theorem current_wf_local_trace_successors:
  !aa xs s rs H E ys s' rs' H' E'.
  current_local_trace aa xs s rs H E ys s' rs' H' E' ==>
  MAP get_successors ys = MAP get_successors xs
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >> gvs[] >>
  drule current_wf_inst_trace_successors >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem current_wf_bb_successors:
  MAP get_successors new.bb_instructions = MAP get_successors old.bb_instructions ==>
  bb_succs new = bb_succs old
Proof
  strip_tac >>
  `LENGTH new.bb_instructions = LENGTH old.bb_instructions` by
    metis_tac[LENGTH_MAP] >>
  qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `LAST`) >>
  Cases_on `new.bb_instructions` >> Cases_on `old.bb_instructions` >>
  gvs[bb_succs_def, LAST_MAP]
QED

Theorem current_wf_edge_shape_successors:
  current_edge_shape old new ==> bb_succs new = bb_succs old
Proof
  strip_tac >> irule current_wf_bb_successors >>
  fs[current_edge_shape_def, LIST_REL_EL_EQN] >>
  irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  Cases_on `(EL x old.bb_instructions).inst_opcode = PHI` >>
  gvs[get_successors_def, is_terminator_def]
QED

Theorem current_wf_event_trace_successors:
  current_event_trace A H ev ==>
  bb_succs (current_event_renamed_block ev) = bb_succs (current_event_input_block ev)
Proof
  PairCases_on `ev` >>
  simp[current_event_trace_def, current_event_renamed_block_def,
    current_event_input_block_def] >> strip_tac >>
  irule current_wf_bb_successors >> simp[] >>
  drule current_wf_local_trace_successors >> simp[]
QED

Theorem current_wf_event_lookup_successors[local]:
  (!ev. MEM ev events ==>
    OPTION_MAP bb_succs (lookup_block (current_event_label ev) bbs) =
      SOME (bb_succs (current_event_renamed_block ev))) ==>
  !prior. OPTION_MAP bb_succs prior = OPTION_MAP bb_succs (lookup_block q bbs) ==>
  OPTION_MAP bb_succs (FOLDL (current_event_lookup sm q) prior events) =
    OPTION_MAP bb_succs (lookup_block q bbs)
Proof
  Induct_on `events` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  simp[current_event_lookup_def] >> Cases_on `q = current_event_label h` >> simp[]
  >- metis_tac[current_event_edge_shape, current_wf_edge_shape_successors] >>
  Cases_on `prior` >> gvs[] >>
  metis_tac[current_event_edge_shape, current_wf_edge_shape_successors]
QED

Theorem current_wf_trace_successors:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  (!l. MEM l (dom_tree_labels tree) ==> IS_SOME (lookup_block l bbs)) /\
  ALL_DISTINCT (dom_tree_labels tree) ==>
  !q. OPTION_MAP bb_succs (lookup_block q bbs') =
    OPTION_MAP bb_succs (lookup_block q bbs)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP current_event_label events)` by
    metis_tac[current_tree_trace_event_labels_distinct] >>
  `EVERY (current_event_trace A H') events` by
    metis_tac[cj 1 current_tree_trace_events] >>
  drule (cj 1 current_trace_lookup_fold) >> strip_tac >> simp[] >>
  gen_tac >> irule current_wf_event_lookup_successors >>
  simp[] >> rpt strip_tac >>
  `MEM (current_event_label ev) (dom_tree_labels tree)` by
    metis_tac[cj 1 makeSsaCurrentFinalBlockTheory.current_trace_event_labels, MEM_MAP] >>
  `IS_SOME (lookup_block (current_event_label ev) bbs)` by metis_tac[] >>
  Cases_on `lookup_block (current_event_label ev) bbs` >> gvs[] >>
  `current_edge_shape x (current_event_input_block ev)` by
    metis_tac[cj 1 current_trace_event_input_shape] >>
  `current_event_trace A H' ev` by metis_tac[EVERY_MEM] >>
  metis_tac[current_wf_edge_shape_successors, current_wf_event_trace_successors]
QED

Theorem current_wf_insertion_successors:
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) fn.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn))))) = (ins,si) /\
  wf_function fn ==>
  !q. OPTION_MAP bb_succs (lookup_block q ins) =
    OPTION_MAP bb_succs (lookup_block q fn.fn_blocks)
Proof
  strip_tac >> drule current_actual_insertion_prefix >> strip_tac >>
  `MAP (\bb. bb.bb_label) ins = MAP (\bb. bb.bb_label) fn.fn_blocks` by
    metis_tac[add_phi_nodes_supply_labels] >>
  `phi_extends fn.fn_blocks ins` by
    (fs[phi_extends_def, LIST_REL_EL_EQN] >> rpt strip_tac >>
     first_x_assum (qspec_then `j` mp_tac) >> impl_tac >- simp[] >>
     strip_tac >> qexists_tac `pre` >>
     fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
     simp[build_phi_inst_supply_def]) >>
  `succs_preserved fn.fn_blocks ins` by
    (irule phi_extends_succs_preserved >> fs[wf_function_def, fn_labels_def]) >>
  gen_tac >> Cases_on `lookup_block q ins` >>
  Cases_on `lookup_block q fn.fn_blocks` >> gvs[succs_preserved_def]
  >- (drule lookup_block_MEM >> strip_tac >>
      `x.bb_label = q` by metis_tac[lookup_block_label] >>
      `ALL_DISTINCT (MAP (\bb. bb.bb_label) ins)` by fs[wf_function_def, fn_labels_def] >>
      `MEM q (MAP (\bb. bb.bb_label) ins)` by
        (asm_rewrite_tac[] >> simp[MEM_MAP] >> metis_tac[]) >>
      gvs[MEM_MAP] >>
      `ALL_DISTINCT (MAP (\bb. bb.bb_label) ins)` by metis_tac[] >>
      `lookup_block bb.bb_label ins = SOME bb` by
        (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  qpat_x_assum `!lbl bb. _` (qspec_then `q` mp_tac) >>
  disch_then (qspec_then `x` mp_tac) >> simp[]
QED

Theorem current_wf_cfg_lookup:
  ALL_DISTINCT (fn_labels f) ==>
  (fn_cfg_edge f a b <=>
    ?ss. OPTION_MAP bb_succs (lookup_block a f.fn_blocks) = SOME ss /\ MEM b ss)
Proof
  simp[fn_labels_def, fn_cfg_edge_def] >> strip_tac >> eq_tac >> rpt strip_tac
  >- (drule_all MEM_lookup_block >> strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> drule lookup_block_MEM >> strip_tac >> metis_tac[lookup_block_label]
QED

Theorem current_wf_precleanup_labels:
  current_wf_precleanup_certificate s fn renamed s' A H events ==>
  MAP (\bb. bb.bb_label) renamed = MAP (\bb. bb.bb_label) fn.fn_blocks
Proof
  simp[current_wf_precleanup_certificate_def] >> rpt strip_tac >>
  drule (cj 1 current_tree_trace_projection) >> strip_tac >>
  drule (cj 1 rename_current_blocks_labels) >>
  drule add_phi_nodes_supply_labels >> simp[]
QED

Theorem current_wf_precleanup_entry:
  current_wf_precleanup_certificate s fn renamed s' A H events ==>
  fn_entry_label (fn with fn_blocks := renamed) = fn_entry_label fn
Proof
  strip_tac >> drule current_wf_precleanup_labels >>
  Cases_on `renamed` >> Cases_on `fn.fn_blocks` >>
  simp[fn_entry_label_def, entry_block_def]
QED

Theorem current_wf_precleanup_successors:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb ==>
  !q. OPTION_MAP bb_succs (lookup_block q renamed) =
    OPTION_MAP bb_succs (lookup_block q fn.fn_blocks)
Proof
  simp[current_wf_precleanup_certificate_def] >> rpt strip_tac >>
  `MAP (\bb. bb.bb_label) ins = MAP (\bb. bb.bb_label) fn.fn_blocks` by
    metis_tac[add_phi_nodes_supply_labels] >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l ins)` by
    metis_tac[current_actual_tree_lookup_coverage] >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  drule_all current_wf_trace_successors >> strip_tac >>
  drule_all current_wf_insertion_successors >> simp[]
QED

Theorem current_wf_precleanup_cfg:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb ==>
  fn_entry_label (fn with fn_blocks := renamed) = fn_entry_label fn /\
  (!a b. fn_cfg_edge (fn with fn_blocks := renamed) a b <=> fn_cfg_edge fn a b)
Proof
  strip_tac >> conj_tac >- metis_tac[current_wf_precleanup_entry] >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  `ALL_DISTINCT (fn_labels (fn with fn_blocks := renamed))` by
    (drule current_wf_precleanup_labels >> fs[fn_labels_def]) >>
  drule_all current_wf_precleanup_successors >> strip_tac >>
  `!q. OPTION_MAP bb_succs (lookup_block q (fn with fn_blocks := renamed).fn_blocks) =
    OPTION_MAP bb_succs (lookup_block q fn.fn_blocks)` by simp[] >>
  metis_tac[current_wf_cfg_lookup]
QED

Theorem current_wf_precleanup_coverage:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM bb renamed ==>
  ?ev. MEM ev events /\ current_event_label ev = bb.bb_label
Proof
  strip_tac >>
  `MAP (\bb. bb.bb_label) renamed = MAP (\bb. bb.bb_label) fn.fn_blocks` by
    metis_tac[current_wf_precleanup_labels] >>
  `MEM bb.bb_label (fn_labels fn)` by
    (fs[fn_labels_def] >> metis_tac[MEM_MAP]) >>
  `MEM bb.bb_label (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_label_member] >>
  fs[current_wf_precleanup_certificate_def] >>
  `MAP (\bb. bb.bb_label) ins = MAP (\bb. bb.bb_label) fn.fn_blocks` by
    metis_tac[add_phi_nodes_supply_labels] >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l ins)` by
    metis_tac[current_actual_tree_lookup_coverage] >>
  drule_all current_tree_trace_event_coverage >> simp[]
QED

Theorem current_wf_precleanup_output:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM ev events /\ current_wf_output_at A H ev k tok /\
  current_token_name H tok = SOME v ==>
  ?bb. lookup_block (current_event_label ev) renamed = SOME bb /\
    bb.bb_label = current_event_label ev /\
    LENGTH bb.bb_instructions = LENGTH (current_event_renamed_block ev).bb_instructions /\
    k < LENGTH bb.bb_instructions /\ MEM v (EL k bb.bb_instructions).inst_outputs
Proof
  strip_tac >> drule_all current_wf_precleanup_event >> strip_tac >>
  qexists_tac `bb` >>
  fs[current_wf_output_at_def, current_edge_shape_def, LIST_REL_EL_EQN] >>
  conj_tac >- metis_tac[lookup_block_label] >>
  metis_tac[MEM_EL]
QED

Theorem current_wf_event_source_cut_exists:
  current_event_trace A H ev /\
  n <= LENGTH (current_event_input_block ev).bb_instructions ==>
  ?rs E. current_source_cut A ev n rs E
Proof
  PairCases_on `ev` >>
  simp[current_event_input_block_def] >>
  metis_tac[current_source_cut_exists]
QED

Theorem current_wf_event_source_cut_step:
  current_source_cut A ev n rs E /\
  n < LENGTH (current_event_input_block ev).bb_instructions ==>
  ?sm Hm sn rn Hn En.
    current_inst_trace (EL n (A (current_event_label ev)))
      (EL n (current_event_input_block ev).bb_instructions)
      sm rs Hm E (EL n (current_event_renamed_block ev).bb_instructions)
      sn rn Hn En /\
    current_source_cut A ev (SUC n) rn En
Proof
  PairCases_on `ev` >>
  simp[current_event_input_block_def, current_event_label_def,
    current_event_renamed_block_def] >>
  metis_tac[current_source_cut_step]
QED

Theorem current_wf_source_cut_name:
  current_event_valid A V ev /\ current_event_trace A H ev /\
  current_source_cut A ev n rs E /\ MEM u V ==>
  current_token_name H (E u) = SOME (latest_current_name rs u)
Proof
  PairCases_on `ev` >>
  simp[current_event_valid_def, current_event_trace_def,
    current_source_cut_def] >> rpt strip_tac >>
  `current_annotations_ok V ev5 (FLAT ap)` by
    metis_tac[current_annotations_split, FLAT_APPEND] >>
  `current_env_realizes Hm E rs V` by
    metis_tac[current_local_trace_preserves] >>
  `current_token_name Hm (E u) = SOME (latest_current_name rs u)` by
    fs[current_env_realizes_def] >>
  drule current_local_trace_history >> strip_tac >> gvs[] >>
  metis_tac[current_token_name_append_stable, APPEND_ASSOC]
QED

Theorem current_wf_rename_operands_var:
  !ops. MEM (Var v) (rename_current_operands rs ops) <=>
    ?u. MEM (Var u) ops /\ v = latest_current_name rs u
Proof
  Induct >> simp[rename_current_operands_def] >>
  Cases_on `h` >> simp[rename_current_operands_def] >> metis_tac[]
QED

Theorem current_wf_inst_trace_use:
  current_inst_trace aa inst s rs H E inst' s' rs' H' E' /\
  inst'.inst_opcode <> PHI /\ MEM (Var v) inst'.inst_operands ==>
  ?u. MEM (Var u) inst.inst_operands /\ v = latest_current_name rs u
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[current_wf_rename_operands_var] >>
  metis_tac[]
QED

Theorem current_wf_edge_shape_ordinary_index:
  current_edge_shape (old with bb_instructions := pre ++ old.bb_instructions) bb /\
  i < LENGTH old.bb_instructions /\ (EL i old.bb_instructions).inst_opcode <> PHI ==>
  LENGTH pre + i < LENGTH bb.bb_instructions /\
  EL (LENGTH pre + i) bb.bb_instructions = EL i old.bb_instructions
Proof
  simp[current_edge_shape_def, LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum (qspec_then `LENGTH pre + i` mp_tac) >>
  simp[EL_APPEND_EQN]
QED

Theorem current_wf_event_ordinary_cut:
  current_event_trace A H ev /\
  current_edge_shape (old with bb_instructions := pre ++ old.bb_instructions)
    (current_event_input_block ev) /\
  i < LENGTH old.bb_instructions /\ (EL i old.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (EL (LENGTH pre + i)
    (current_event_renamed_block ev).bb_instructions).inst_operands ==>
  ?rs E u. current_source_cut A ev (LENGTH pre + i) rs E /\
    MEM (Var u) (EL i old.bb_instructions).inst_operands /\
    v = latest_current_name rs u
Proof
  strip_tac >> drule_all current_wf_edge_shape_ordinary_index >> strip_tac >>
  `?rs E. current_source_cut A ev (LENGTH pre + i) rs E` by
    metis_tac[current_wf_event_source_cut_exists, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  drule_all current_wf_event_source_cut_step >> strip_tac >>
  ` (EL (LENGTH pre + i)
      (current_event_renamed_block ev).bb_instructions).inst_opcode <> PHI` by
    metis_tac[current_inst_trace_opcode] >>
  drule_all current_wf_inst_trace_use >> strip_tac >>
  metis_tac[]
QED

Theorem current_wf_edge_shape_ordinary_member:
  current_edge_shape old bb /\ MEM inst bb.bb_instructions /\ inst.inst_opcode <> PHI ==>
  ?n. n < LENGTH old.bb_instructions /\
    EL n old.bb_instructions = inst /\ EL n bb.bb_instructions = inst
Proof
  simp[current_edge_shape_def, LIST_REL_EL_EQN] >> strip_tac >>
  `?n. n < LENGTH bb.bb_instructions /\ inst = EL n bb.bb_instructions` by
    metis_tac[MEM_EL] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `n` >> gvs[] >> metis_tac[]
QED

Theorem current_wf_event_ordinary_source_index:
  current_event_trace A H ev /\
  current_edge_shape (old with bb_instructions := pre ++ old.bb_instructions)
    (current_event_input_block ev) /\ EVERY (\inst. inst.inst_opcode = PHI) pre /\
  n < LENGTH (current_event_renamed_block ev).bb_instructions /\
  (EL n (current_event_renamed_block ev).bb_instructions).inst_opcode <> PHI ==>
  ?i. n = LENGTH pre + i /\ i < LENGTH old.bb_instructions /\
    (EL i old.bb_instructions).inst_opcode <> PHI
Proof
  strip_tac >>
  `MAP instruction_inst_opcode (current_event_renamed_block ev).bb_instructions =
    MAP instruction_inst_opcode (current_event_input_block ev).bb_instructions` by
    (PairCases_on `ev` >>
     fs[current_event_trace_def, current_event_renamed_block_def,
       current_event_input_block_def] >>
     metis_tac[current_local_trace_opcodes]) >>
  drule current_edge_shape_opcodes >> simp[] >> strip_tac >>
  `LENGTH (current_event_renamed_block ev).bb_instructions =
     LENGTH pre + LENGTH old.bb_instructions` by
    metis_tac[LENGTH_MAP, LENGTH_APPEND] >>
  `MAP instruction_inst_opcode (current_event_renamed_block ev).bb_instructions =
     MAP instruction_inst_opcode (pre ++ old.bb_instructions)` by simp[] >>
  ` (EL n (current_event_renamed_block ev).bb_instructions).inst_opcode =
     (EL n (pre ++ old.bb_instructions)).inst_opcode` by
    (fs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `n >= LENGTH pre` by
    (spose_not_then assume_tac >>
     `n < LENGTH pre` by decide_tac >>
     ` (EL n pre).inst_opcode = PHI` by
       (qpat_x_assum `EVERY _ pre` mp_tac >> rewrite_tac[EVERY_EL] >>
        disch_then (qspec_then `n` mp_tac) >> simp[]) >>
     fs[EL_APPEND_EQN]) >>
  qexists_tac `n - LENGTH pre` >>
  fs[EL_APPEND_EQN]
QED

Theorem current_wf_precleanup_structural:
  current_wf_precleanup_certificate s fn renamed s' A H events ==>
  ?fn'. current_structural_certificate s fn fn' s' A H events
Proof
  strip_tac >>
  qexists_tac `fn with fn_blocks := simplify_current_phis_if
    (blocks_have_leading_phi fn.fn_blocks) renamed` >>
  metis_tac[current_wf_precleanup_certificate_stages]
QED

Theorem current_wf_precleanup_block_shape:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\ MEM bb renamed ==>
  ?ev. MEM ev events /\ current_event_label ev = bb.bb_label /\
    current_edge_shape (current_event_renamed_block ev) bb
Proof
  strip_tac >> drule_all current_wf_precleanup_coverage >> strip_tac >>
  drule_all current_wf_precleanup_event >> strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) renamed)` by
    (drule current_wf_precleanup_labels >>
     fs[wf_function_def, fn_labels_def]) >>
  `lookup_block bb.bb_label renamed = SOME bb` by
    (irule MEM_lookup_block >> simp[]) >>
  qexists_tac `ev` >> gvs[]
QED

Theorem current_wf_precleanup_ordinary_cut:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM bb renamed /\ MEM inst bb.bb_instructions /\ inst.inst_opcode <> PHI /\
  MEM (Var v) inst.inst_operands ==>
  ?ev old pre i rs E u.
    MEM ev events /\ current_event_label ev = bb.bb_label /\
    lookup_block (current_event_label ev) fn.fn_blocks = SOME old /\
    A (current_event_label ev) = current_block_annotations old pre /\
    EVERY (\inst. inst.inst_opcode = PHI) pre /\
    (!w. current_actual_inserted fn w (current_event_label ev) <=>
      ?phi. MEM phi pre /\ MEM w phi.inst_outputs) /\
    i < LENGTH old.bb_instructions /\ (EL i old.bb_instructions).inst_opcode <> PHI /\
    LENGTH pre + i < LENGTH bb.bb_instructions /\
    EL (LENGTH pre + i) bb.bb_instructions = inst /\
    current_source_cut A ev (LENGTH pre + i) rs E /\
    MEM (Var u) (EL i old.bb_instructions).inst_operands /\
    v = latest_current_name rs u
Proof
  strip_tac >> drule_all current_wf_precleanup_block_shape >> strip_tac >>
  `?old. MEM old fn.fn_blocks /\ old.bb_label = current_event_label ev` by
    (drule current_wf_precleanup_labels >>
     strip_tac >> `MEM bb.bb_label (MAP (\b. b.bb_label) fn.fn_blocks)` by
       metis_tac[MEM_MAP] >> gvs[MEM_MAP] >> metis_tac[]) >>
  `lookup_block (current_event_label ev) fn.fn_blocks = SOME old` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  drule current_wf_precleanup_structural >> strip_tac >>
  drule_all current_wf_certificate_actual_prefix >> strip_tac >>
  drule_all current_wf_edge_shape_ordinary_member >> strip_tac >>
  ` (EL n (current_event_renamed_block ev).bb_instructions).inst_opcode <> PHI` by
    simp[] >>
  drule_all current_wf_event_ordinary_source_index >> strip_tac >>
  gvs[] >>
  `?rs E u. current_source_cut A ev (LENGTH pre + i) rs E /\
      MEM (Var u) (EL i old.bb_instructions).inst_operands /\
      v = latest_current_name rs u` by
    (irule current_wf_event_ordinary_cut >> simp[] >> metis_tac[]) >>
  `LENGTH bb.bb_instructions =
    LENGTH (current_event_renamed_block ev).bb_instructions` by
    (qpat_x_assum `current_edge_shape (current_event_renamed_block ev) bb` mp_tac >>
     simp[current_edge_shape_def, LIST_REL_EL_EQN]) >>
  qexistsl_tac [`ev`, `old`, `pre`, `i`, `rs`, `E`, `u`] >>
  fs[arithmeticTheory.ADD_COMM]
QED

Theorem current_wf_prefix_vars:
  !olds news. LIST_REL (\old new. ?pre.
    new = old with bb_instructions := pre ++ old.bb_instructions)
    olds news ==>
  !u. MEM u (FLAT (MAP block_ir_vars olds)) ==>
    MEM u (FLAT (MAP block_ir_vars news))
Proof
  Induct >> Cases_on `news` >> simp[] >> rpt strip_tac >> gvs[] >>
  fs[block_ir_vars_def, MAP_APPEND, FLAT_APPEND] >> metis_tac[]
QED

Theorem current_wf_ordinary_demand:
  lookup_block l fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode <> PHI /\
  MEM (Var u) (EL i old.bb_instructions).inst_operands ==>
  current_demand fn u l i /\ MEM u (FLAT (MAP block_ir_vars fn.fn_blocks))
Proof
  strip_tac >>
  `MEM u (inst_uses (EL i old.bb_instructions))` by
    fs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
  conj_tac >- metis_tac[current_demand_rules] >>
  `MEM old fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  simp[MEM_FLAT, MEM_MAP] >> qexists_tac `block_ir_vars old` >>
  conj_tac >- metis_tac[] >>
  simp[block_ir_vars_def, MEM_FLAT, MEM_MAP] >>
  qexists_tac `inst_ir_vars (EL i old.bb_instructions)` >>
  simp[inst_ir_vars_def] >> metis_tac[EL_MEM]
QED

Theorem current_wf_precleanup_cut_name:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM ev events /\ current_source_cut A ev n rs E /\
  MEM u (FLAT (MAP block_ir_vars fn.fn_blocks)) ==>
  current_token_name H (E u) = SOME (latest_current_name rs u)
Proof
  strip_tac >> drule_all current_wf_precleanup_names >> strip_tac >> gvs[] >>
  drule current_actual_insertion_prefix >> strip_tac >>
  `MEM u (FLAT (MAP block_ir_vars ins))` by
    (irule current_wf_prefix_vars >> qexists_tac `fn.fn_blocks` >> simp[] >>
     irule LIST_REL_mono >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  irule current_wf_source_cut_name >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem current_wf_entry_undemanded:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_entry_label fn = SOME l ==> ~current_demand fn v l 0
Proof
  metis_tac[current_wf_entry_unavailable, current_demand_available]
QED

Theorem current_wf_path_last_edge[local]:
  !pre p target. is_fn_path fn (pre ++ [p;target]) ==>
    is_fn_path fn (pre ++ [p]) /\ fn_cfg_edge fn p target
Proof
  Induct >> simp[is_fn_path_def] >> rpt gen_tac >>
  Cases_on `pre` >> gvs[is_fn_path_def] >> metis_tac[]
QED

Theorem current_wf_first_visit_decomposition:
  !path. is_fn_path fn path /\ path <> [] /\ LAST path = target ==>
  ?pre suffix. path = pre ++ target::suffix /\
    is_fn_path fn (pre ++ [target]) /\
    HD (pre ++ [target]) = HD path /\ ~MEM target pre
Proof
  Induct >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `h = target`
  >- (qexistsl_tac [`[]`, `path`] >> simp[is_fn_path_def]) >>
  Cases_on `path` >> gvs[is_fn_path_def] >>
  qexistsl_tac [`h::pre`, `suffix`] >> simp[] >>
  Cases_on `pre` >> gvs[is_fn_path_def]
QED

Theorem current_wf_first_entry_path:
  fn_reachable fn target /\ fn_entry_label fn = SOME entry /\ entry <> target ==>
  ?path pred. is_fn_path fn path /\ path <> [] /\
    HD path = entry /\ LAST path = pred /\
    fn_cfg_edge fn pred target /\ ~MEM target path
Proof
  simp[fn_reachable_def] >> strip_tac >>
  drule rtc_to_fn_path >> strip_tac >>
  drule_all current_wf_first_visit_decomposition >> strip_tac >>
  `pre <> []` by (Cases_on `pre` >> gvs[]) >>
  Cases_on `pre` using SNOC_CASES >> gvs[SNOC_APPEND] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  drule current_wf_path_last_edge >> strip_tac >>
  qexists_tac `l ++ [x]` >> simp[] >>
  Cases_on `l` >> gvs[]
QED

Theorem current_wf_unique_output_block[local]:
  ssa_form fn /\
  MEM bb1 fn.fn_blocks /\ MEM inst1 bb1.bb_instructions /\ MEM v inst1.inst_outputs /\
  MEM bb2 fn.fn_blocks /\ MEM inst2 bb2.bb_instructions /\ MEM v inst2.inst_outputs ==>
  bb1 = bb2
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP
    (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) fn.fn_blocks))` by
    fs[ssa_form_def, fn_insts_def, fn_insts_blocks_flat,
      MAP_FLAT, FLAT_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  irule (INST_TYPE [beta |-> ``:string``] all_distinct_flat_map_unique) >>
  qexistsl_tac [`\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)`,
    `fn.fn_blocks`, `v`] >> simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem current_wf_phi_first_source[local]:
  ssa_form fn /\ MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  MEM out inst.inst_outputs /\ phi_edge_uses_wf fn bb inst /\
  is_fn_path fn path /\ path <> [] /\
  (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
  fn_cfg_edge fn (LAST path) bb.bb_label /\ ~MEM bb.bb_label path ==>
  ?src db di. MEM (LAST path,src) (phi_pairs inst.inst_operands) /\
    src <> out /\ MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM src di.inst_outputs /\ MEM db.bb_label path /\
    fn_dominates fn db.bb_label (LAST path)
Proof
  strip_tac >>
  `?src. MEM (LAST path,src) (phi_pairs inst.inst_operands)` by
    (fs[phi_edge_uses_wf_def, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = LAST path /\
    def_available_at fn pb NONE src` by metis_tac[phi_edge_uses_wf_def] >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  `MEM def_bb.bb_label path` by
    (fs[fn_dominates_def] >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  `src <> out` by
    (strip_tac >> gvs[] >>
     `def_bb = bb` by metis_tac[current_wf_unique_output_block] >> gvs[]) >>
  qexistsl_tac [`src`, `def_bb`, `def_inst`] >> fs[]
QED

Theorem current_wf_phi_nonself_source:
  ssa_form fn /\ MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  MEM out inst.inst_outputs /\ phi_edge_uses_wf fn bb inst /\
  fn_reachable fn bb.bb_label /\ fn_entry_label fn = SOME entry /\
  entry <> bb.bb_label ==>
  ?pred src. MEM (pred,src) (phi_pairs inst.inst_operands) /\ src <> out
Proof
  strip_tac >> drule_all current_wf_first_entry_path >> strip_tac >>
  `?src db di. MEM (LAST path,src) (phi_pairs inst.inst_operands) /\
    src <> out /\ MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM src di.inst_outputs /\ MEM db.bb_label path /\
    fn_dominates fn db.bb_label (LAST path)` by
    (irule current_wf_phi_first_source >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem current_wf_phi_constant_source:
  ssa_form fn /\ MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  MEM out inst.inst_outputs /\ phi_edge_uses_wf fn bb inst /\
  fn_reachable fn bb.bb_label /\ fn_entry_label fn = SOME entry /\
  entry <> bb.bb_label /\
  (!p w. MEM (p,w) (phi_pairs inst.inst_operands) /\ w <> out ==> w = src) ==>
  ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM src di.inst_outputs /\ db.bb_label <> bb.bb_label /\
    fn_dominates fn db.bb_label bb.bb_label
Proof
  strip_tac >> drule_all current_wf_first_entry_path >> strip_tac >>
  `?src0 db di. MEM (LAST path,src0) (phi_pairs inst.inst_operands) /\
    src0 <> out /\ MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM src0 di.inst_outputs /\ MEM db.bb_label path /\
    fn_dominates fn db.bb_label (LAST path)` by
    (irule current_wf_phi_first_source >> simp[] >> metis_tac[]) >>
  `src0 = src` by metis_tac[] >> gvs[] >>
  qexistsl_tac [`db`, `di`] >> simp[] >> conj_tac
  >- metis_tac[] >>
  simp[fn_dominates_def] >> rpt strip_tac >>
  drule_all current_wf_first_visit_decomposition >> strip_tac >>
  `pre <> []` by (Cases_on `pre` >> gvs[]) >>
  Cases_on `pre` using SNOC_CASES >> gvs[SNOC_APPEND] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  drule current_wf_path_last_edge >> strip_tac >>
  `?w db' di'. MEM (LAST (l ++ [x]),w) (phi_pairs inst.inst_operands) /\
    w <> out /\ MEM db' fn.fn_blocks /\ MEM di' db'.bb_instructions /\
    MEM w di'.inst_outputs /\ MEM db'.bb_label (l ++ [x]) /\
    fn_dominates fn db'.bb_label (LAST (l ++ [x]))` by
    (irule current_wf_phi_first_source >> simp[] >>
     Cases_on `l` >> gvs[] >> metis_tac[]) >>
  `w = src` by metis_tac[] >> gvs[] >>
  `db' = db` by metis_tac[current_wf_unique_output_block] >> gvs[]
QED

Theorem current_wf_phi_slots[local]:
  !ops. phi_well_formed ops ==> ops = current_phi_slots (phi_pairs ops)
Proof
  recInduct phi_well_formed_ind >> simp[phi_well_formed_def,
    phi_pairs_def, current_phi_slots_def]
QED

Theorem current_wf_phi_cleanup_cases[local]:
  inst.inst_opcode = PHI /\ inst.inst_outputs = [out] /\
  inst.inst_operands = current_phi_slots slots /\
  (?p w. MEM (p,w) slots /\ w <> out) ==>
  simplify_current_phi inst = inst \/
  ?src. simplify_current_phi inst =
      inst with <|inst_opcode := ASSIGN; inst_operands := [Var src]|> /\
    (!p w. MEM (p,w) slots /\ w <> out ==> w = src)
Proof
  strip_tac >>
  qabbrev_tac `vals = MAP SND (FILTER (\slot. SND slot <> out) slots)` >>
  `MEM w vals` by (simp[Abbr `vals`, MEM_MAP, MEM_FILTER] >> metis_tac[pairTheory.SND]) >>
  Cases_on `vals` >- fs[] >>
  qpat_x_assum `MEM _ (h::t)` kall_tac >> fs[] >>
  Cases_on `EVERY (\w. w = h) t`
  >- (disj2_tac >> qexists_tac `h` >> conj_tac
      >- (irule current_phi_slots_constant >> metis_tac[]) >>
      rpt strip_tac >>
      `MEM w' (h::t)` by
        (qpat_x_assum `_ = h::t` (SUBST1_TAC o SYM) >>
         simp[MEM_MAP, MEM_FILTER] >> metis_tac[pairTheory.SND]) >>
      fs[EVERY_MEM] >> metis_tac[]) >>
  disj1_tac >> fs[EVERY_MEM, EXISTS_MEM] >>
  simp[simplify_current_phi_def, simplify_current_phi_raw_def,
    current_phi_output_def, current_phi_slots_remove_self, current_phi_slots_values,
    keep_current_phi_vars_def, EVERY_MEM] >>
  Cases_on `!w. MEM w t ==> w = h` >> gvs[] >> metis_tac[]
QED

Theorem current_wf_phi_cleanup_classification:
  ssa_form fn /\ MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  inst.inst_opcode = PHI /\ inst.inst_outputs = [out] /\
  phi_edge_uses_wf fn bb inst /\ fn_reachable fn bb.bb_label /\
  fn_entry_label fn = SOME entry /\ entry <> bb.bb_label ==>
  simplify_current_phi inst = inst \/
  ?src db di.
    simplify_current_phi inst =
      inst with <|inst_opcode := ASSIGN; inst_operands := [Var src]|> /\
    MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM src di.inst_outputs /\ db.bb_label <> bb.bb_label /\
    fn_dominates fn db.bb_label bb.bb_label
Proof
  strip_tac >>
  `MEM out inst.inst_outputs` by simp[] >>
  `inst.inst_operands = current_phi_slots (phi_pairs inst.inst_operands)` by
    metis_tac[phi_edge_uses_wf_def, current_wf_phi_slots] >>
  drule_all current_wf_phi_nonself_source >> strip_tac >>
  `simplify_current_phi inst = inst \/
   ?v. simplify_current_phi inst =
       inst with <|inst_opcode := ASSIGN; inst_operands := [Var v]|> /\
     (!p w. MEM (p,w) (phi_pairs inst.inst_operands) /\ w <> out ==> w = v)` by
    metis_tac[current_wf_phi_cleanup_cases]
  >- simp[] >>
  disj2_tac >> qexists_tac `v` >> simp[] >>
  irule current_wf_phi_constant_source >> metis_tac[]
QED

Theorem current_wf_no_id_split[local]:
  !pre tail ys.
    MAP current_inst_no_id ys = MAP current_inst_no_id (pre ++ tail) ==>
    ?pre' tail'. ys = pre' ++ tail' /\ LENGTH pre' = LENGTH pre /\
      MAP current_inst_no_id pre' = MAP current_inst_no_id pre /\
      LIST_REL (\x y. current_inst_no_id x = current_inst_no_id y) tail tail'
Proof
  Induct >- (rpt strip_tac >> qexistsl_tac [`[]`, `ys`] >>
    simp[] >> fs[LIST_REL_EL_EQN] >>
    metis_tac[LENGTH_MAP, EL_MAP]) >>
  rpt gen_tac >> Cases_on `ys` >> simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`tail`, `t`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`h'::pre'`, `tail'`] >> simp[]
QED

Theorem current_wf_partition_outputs[local]:
  !xs. PERM
    (FLAT (MAP (\i. i.inst_outputs)
      (FILTER (\i. i.inst_opcode = PHI) xs ++
       FILTER (\i. i.inst_opcode <> PHI) xs)))
    (FLAT (MAP (\i. i.inst_outputs) xs))
Proof
  Induct >> simp[] >> gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[MAP_APPEND, FLAT_APPEND]
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[PERM_APPEND_IFF]) >>
  qmatch_goalsub_abbrev_tac `PERM (a ++ h.inst_outputs ++ b) _` >>
  irule PERM_TRANS >> qexists_tac `h.inst_outputs ++ (a ++ b)` >>
  conj_tac
  >- (simp[APPEND_ASSOC, PERM_APPEND_IFF, PERM_APPEND]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[PERM_APPEND_IFF] >>
  fs[Abbr `a`, Abbr `b`]
QED

Theorem current_wf_cleanup_no_id[local]:
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) ==>
  MAP current_inst_no_id (simplify_current_phi_prefix (pre ++ tail)) =
  MAP current_inst_no_id
    ((FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre) ++
      FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre)) ++ tail)
Proof
  disch_tac >>
  qspecl_then [`pre`, `tail`] mp_tac
    makeSsaCurrentCleanupShapeTheory.current_cleanup_partition >>
  impl_tac >- fs[] >> strip_tac >>
  simp[simplify_current_phi_prefix_def] >>
  pure_rewrite_tac[GSYM MAP_APPEND] >>
  irule makeSsaCurrentCleanupShapeTheory.current_reassign_no_id >>
  qspec_then `MAP simplify_current_phi pre` mp_tac
    makeSsaCurrentCleanupShapeTheory.current_cleanup_partition_length >>
  simp[]
QED

Theorem current_wf_cleanup_block_no_id[local]:
  bb.bb_instructions = pre ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) ==>
  MAP current_inst_no_id (simplify_current_phi_block bb).bb_instructions =
  MAP current_inst_no_id
    ((FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre) ++
      FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre)) ++ tail)
Proof
  disch_tac >>
  mp_tac (Q.INST [`pre` |-> `pre`, `tail` |-> `tail`] current_wf_cleanup_no_id) >>
  (impl_tac >- fs[]) >> disch_tac >>
  Cases_on `pre`
  >- (Cases_on `tail` >> gvs[simplify_current_phi_block_def]) >>
  gvs[simplify_current_phi_block_def]
QED

Theorem current_wf_no_id_outputs[local]:
  !xs ys. MAP current_inst_no_id xs = MAP current_inst_no_id ys ==>
    MAP (\i. i.inst_outputs) xs = MAP (\i. i.inst_outputs) ys
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  gvs[current_inst_no_id_def] >>
  qpat_x_assum `_ with inst_id := 0 = _` (mp_tac o Q.AP_TERM `\i. i.inst_outputs`) >>
  simp[]
QED

Theorem current_wf_cleanup_block_split:
  bb.bb_instructions = pre ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  (!i. MEM i pre ==> (simplify_current_phi i).inst_outputs = i.inst_outputs) ==>
  ?pre' tail'.
    (simplify_current_phi_block bb).bb_instructions = pre' ++ tail' /\
    LENGTH pre' = LENGTH pre /\
    LIST_REL (\x y. current_inst_no_id x = current_inst_no_id y) tail tail' /\
    PERM (FLAT (MAP (\i. i.inst_outputs) pre'))
         (FLAT (MAP (\i. i.inst_outputs) pre)) /\
    (!i'. MEM i' pre' ==> ?i. MEM i pre /\
       current_inst_no_id i' = current_inst_no_id (simplify_current_phi i))
Proof
  disch_tac >>
  `MAP current_inst_no_id (simplify_current_phi_block bb).bb_instructions =
   MAP current_inst_no_id
     ((FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre) ++
       FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre)) ++ tail)` by
    metis_tac[current_wf_cleanup_block_no_id] >>
  drule current_wf_no_id_split >> strip_tac >>
  qexistsl_tac [`pre'`, `tail'`] >> simp[] >>
  `LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre)) +
   LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre)) =
   LENGTH pre` by
    (qspec_then `MAP simplify_current_phi pre` mp_tac
      makeSsaCurrentCleanupShapeTheory.current_cleanup_partition_length >> simp[]) >>
  simp[] >> conj_tac
  >- (drule current_wf_no_id_outputs >> disch_tac >>
      `MAP (\i. i.inst_outputs) (MAP simplify_current_phi pre) =
       MAP (\i. i.inst_outputs) pre` by
        (simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >> metis_tac[]) >>
      qspec_then `MAP simplify_current_phi pre` mp_tac current_wf_partition_outputs >>
      fs[]) >>
  rpt strip_tac >>
  `MEM (current_inst_no_id i') (MAP current_inst_no_id pre')` by
    (simp[MEM_MAP] >> qexists_tac `i'` >> simp[]) >>
  qpat_x_assum `MEM (current_inst_no_id i') _` mp_tac >>
  asm_rewrite_tac[] >> simp[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

(* Retained PHIs precede every generated ordinary instruction, even when
   their relative order in the input prefix was the opposite. *)
Theorem current_wf_partition_order:
  MAP current_inst_no_id xs = MAP current_inst_no_id ((phis ++ ordinary) ++ tail) /\
  MEM d phis /\ MEM c ordinary ==>
  ?j k. j < k /\ k < LENGTH xs /\
    current_inst_no_id (EL j xs) = current_inst_no_id d /\
    current_inst_no_id (EL k xs) = current_inst_no_id c
Proof
  simp[MEM_EL] >> strip_tac >>
  rename1 `d = EL j phis` >> rename1 `c = EL k ordinary` >>
  qexistsl [`j`, `LENGTH phis + k`] >>
  `LENGTH xs = LENGTH phis + LENGTH ordinary + LENGTH tail` by
    metis_tac[LENGTH_MAP, LENGTH_APPEND] >>
  simp[] >>
  `EL j (MAP current_inst_no_id xs) =
   EL j (MAP current_inst_no_id ((phis ++ ordinary) ++ tail))` by simp[] >>
  `EL (LENGTH phis + k) (MAP current_inst_no_id xs) =
   EL (LENGTH phis + k)
     (MAP current_inst_no_id ((phis ++ ordinary) ++ tail))` by simp[] >>
  gvs[EL_MAP, EL_APPEND_EQN]
QED

Theorem current_wf_partition_source_available:
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MAP current_inst_no_id bb.bb_instructions =
    MAP current_inst_no_id ((phis ++ ordinary) ++ tail) /\
  MEM d phis /\ MEM c ordinary /\ MEM v d.inst_outputs ==>
  ?k. k < LENGTH bb.bb_instructions /\
    current_inst_no_id (EL k bb.bb_instructions) = current_inst_no_id c /\
    def_available_at fn bb (SOME (EL k bb.bb_instructions)) v
Proof
  strip_tac >> drule_all current_wf_partition_order >> strip_tac >>
  qexists `k` >> simp[] >>
  `MEM v (EL j bb.bb_instructions).inst_outputs` by
    (qpat_x_assum `current_inst_no_id (EL j _) = _`
      (mp_tac o Q.AP_TERM `\i. i.inst_outputs`) >>
     simp[current_inst_no_id_def]) >>
  simp[def_available_at_def] >>
  qexistsl [`bb`, `EL j bb.bb_instructions`] >>
  simp[EL_MEM, fn_dominates_def] >> conj_tac
  >- (rpt strip_tac >> metis_tac[LAST_MEM]) >>
  qexistsl [`j`, `k`] >> simp[]
QED

Theorem current_wf_cleanup_same_prefix_source:
  old.bb_instructions = pre ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  bb = simplify_current_phi_block old /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM d pre /\ MEM c pre /\
  (simplify_current_phi d).inst_opcode = PHI /\
  MEM v (simplify_current_phi d).inst_outputs /\
  (simplify_current_phi c).inst_opcode <> PHI ==>
  ?k. k < LENGTH bb.bb_instructions /\
    current_inst_no_id (EL k bb.bb_instructions) =
      current_inst_no_id (simplify_current_phi c) /\
    def_available_at fn bb (SOME (EL k bb.bb_instructions)) v
Proof
  strip_tac >>
  `MAP current_inst_no_id bb.bb_instructions =
   MAP current_inst_no_id
     ((FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre) ++
       FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre)) ++ tail)` by
    metis_tac[current_wf_cleanup_block_no_id] >>
  `MEM (simplify_current_phi d)
    (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre))` by
    (simp[MEM_FILTER, MEM_MAP] >> metis_tac[]) >>
  `MEM (simplify_current_phi c)
    (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre))` by
    (simp[MEM_FILTER, MEM_MAP] >> metis_tac[]) >>
  drule_all current_wf_partition_source_available >> simp[]
QED

Theorem current_wf_cfg_paths:
  (!a b. fn_cfg_edge g a b <=> fn_cfg_edge f a b) ==>
  !path. is_fn_path g path <=> is_fn_path f path
Proof
  disch_tac >> Induct >> simp[is_fn_path_def] >>
  Cases_on `path` >> simp[is_fn_path_def]
QED

Theorem current_wf_cfg_dominance:
  fn_entry_label g = fn_entry_label f /\
  (!a b. fn_cfg_edge g a b <=> fn_cfg_edge f a b) ==>
  (fn_reachable g l <=> fn_reachable f l) /\
  (fn_dominates g d n <=> fn_dominates f d n)
Proof
  strip_tac >>
  `fn_cfg_edge g = fn_cfg_edge f` by simp[FUN_EQ_THM] >>
  `!path. is_fn_path g path <=> is_fn_path f path` by
    (irule current_wf_cfg_paths >> simp[]) >>
  simp[fn_reachable_def, fn_dominates_def]
QED

Theorem current_wf_precleanup_dominance:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb ==>
  (fn_reachable (fn with fn_blocks := renamed) l <=> fn_reachable fn l) /\
  (fn_dominates (fn with fn_blocks := renamed) d n <=> fn_dominates fn d n)
Proof
  strip_tac >> irule current_wf_cfg_dominance >>
  metis_tac[current_wf_precleanup_cfg]
QED

Theorem current_wf_precleanup_output_available:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM dev events /\ current_wf_output_at A H dev k tok /\
  current_token_name H tok = SOME v /\
  MEM bb renamed /\
  (use_opt = NONE \/ ?n inst. use_opt = SOME inst /\
    n < LENGTH bb.bb_instructions /\ EL n bb.bb_instructions = inst /\
    (current_event_label dev = bb.bb_label ==> k < n)) /\
  fn_dominates fn (current_event_label dev) bb.bb_label ==>
  def_available_at (fn with fn_blocks := renamed) bb use_opt v
Proof
  strip_tac >> drule_all current_wf_precleanup_output >> strip_tac >>
  rename1 `lookup_block (current_event_label dev) renamed = SOME db` >>
  `MEM db renamed` by metis_tac[lookup_block_MEM] >>
  `fn_dominates (fn with fn_blocks := renamed) db.bb_label bb.bb_label` by
    metis_tac[current_wf_precleanup_dominance] >>
  simp[def_available_at_def] >>
  qexistsl_tac [`db`, `EL k db.bb_instructions`] >>
  simp[EL_MEM] >> strip_tac >> gvs[] >>
  qexistsl_tac [`k`, `n`] >> simp[]
QED

Theorem current_wf_precleanup_output_sites:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s ==>
  !ev k j. MEM ev events /\ k < LENGTH (A (current_event_label ev)) /\
    j < LENGTH (EL k (A (current_event_label ev))) ==>
    current_wf_output_at A H ev k (FST (EL j (EL k (A (current_event_label ev)))))
Proof
  strip_tac >> drule_all current_wf_precleanup_names >> strip_tac >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  irule current_wf_event_output_at >> metis_tac[]
QED

Definition current_wf_probe_defs_def:
  current_wf_probe_defs = compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl current_probe_loop.fn_blocks)
      (current_dom_postorder current_probe_loop))))
End

Definition current_wf_probe_insertion_def:
  current_wf_probe_insertion = add_phi_nodes_supply current_probe_supply
    (current_frontier_map current_probe_loop) (current_pred_map current_probe_loop)
    (select_current_live_in (blocks_have_leading_phi current_probe_loop.fn_blocks)
      (liveness_analyze current_probe_loop) current_probe_loop)
    current_probe_loop.fn_blocks current_wf_probe_defs
End

Definition current_wf_probe_renamed_def:
  current_wf_probe_renamed = SND (SND (rename_current_blocks
    (SND current_wf_probe_insertion) (init_current_rename_state current_wf_probe_defs)
    (FST current_wf_probe_insertion) (current_succ_map current_probe_loop)
    (current_dom_tree current_probe_loop)))
End

Theorem current_wf_probe_precleanup_header:
  (EL 1 current_wf_probe_renamed).bb_instructions =
  [current_probe_inst 10 PHI
     [Label "E"; Var "v"; Label "D"; Var "formal_var_0"] ["v"];
   current_probe_inst 2 PHI
     [Label "E"; Var "a"; Label "D"; Var "b"] ["formal_var_0"];
   current_probe_inst 3 ASSIGN [Lit 2w] ["b"];
   current_probe_inst 4 JNZ [Var "formal_var_0"; Label "D"; Label "X"] []]
Proof
  EVAL_TAC
QED

(* The historical simulation fixture is not a frozen-contract input: its
   supply omits function-level names.  In addition its final output is SSA,
   despite the unavailable slot observed before cleanup below. *)
Theorem current_wf_probe_input_structural_contract:
  fn_inst_wf current_probe_loop /\ wf_function current_probe_loop /\
  first_block_no_preds current_probe_loop /\ first_block_no_phi current_probe_loop /\
  ~ir_supply_covers_fn current_probe_supply current_probe_loop /\
  ir_supply_inst_ok current_probe_supply
Proof
  EVAL_TAC
QED

Theorem current_wf_probe_final_ssa:
  wf_ssa (FST (make_ssa_current_fn current_probe_supply current_probe_loop))
Proof
  rewrite_tac[wf_ssa_def] >> EVAL_TAC
QED

Theorem current_wf_probe_precleanup_unavailable:
  ~def_available_at (current_probe_loop with fn_blocks := current_wf_probe_renamed)
    (EL 0 current_wf_probe_renamed) NONE "v"
Proof
  spose_not_then assume_tac >>
  fs[def_available_at_def] >>
  qpat_x_assum `MEM def_bb _` mp_tac >> EVAL_TAC >> strip_tac >>
  gvs[] >>
  fs[fn_dominates_def] >>
  first_x_assum (qspec_then `["E"]` mp_tac) >> EVAL_TAC
QED

Theorem current_wf_tree_phi_slot_shape:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  (!p ss. ALOOKUP sm p = SOME ss ==> ALL_DISTINCT ss) /\
  lookup_block h bbs = SOME old /\ k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_operands = current_phi_slots slots ==>
  ?new slots'. lookup_block h bbs' = SOME new /\
    LENGTH new.bb_instructions = LENGTH old.bb_instructions /\
    k < LENGTH new.bb_instructions /\ (EL k new.bb_instructions).inst_opcode = PHI /\
    (EL k new.bb_instructions).inst_operands = current_phi_slots slots' /\
    MAP FST slots' = MAP FST slots
Proof
  strip_tac >> drule_all current_tree_trace_phi_lookup >> strip_tac >>
  drule_all current_phi_view_fold_instruction >> strip_tac >>
  qexistsl_tac [`new`, `MAP (\slot.
    FOLDL (\slot ev. current_event_pair_action sm h ev slot) slot events) slots`] >>
  simp[current_event_fold_slots, MAP_MAP_o, combinTheory.o_DEF, ETA_THM]
QED

Theorem current_wf_event_exit_cut:
  current_event_trace A H ev ==>
  current_source_cut A ev (LENGTH (current_event_input_block ev).bb_instructions)
    (current_event_exit_rs ev) (current_event_exit_env ev)
Proof
  PairCases_on `ev` >>
  simp[current_event_trace_def, current_event_input_block_def,
    current_event_exit_rs_def, current_event_exit_env_def, current_source_cut_end]
QED

Theorem current_wf_precleanup_exit_owner:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM ev events /\ lookup_block (current_event_label ev) fn.fn_blocks = SOME old ==>
  current_wf_token_owner fn (current_event_exit_env ev v) v
Proof
  strip_tac >> drule current_wf_precleanup_structural >> strip_tac >>
  drule_all current_wf_certificate_actual_prefix >> strip_tac >>
  drule_all current_wf_certificate_static_entry >> strip_tac >>
  `current_wf_token_owner fn (current_event_entry_env ev v) v` by
    metis_tac[current_wf_inherited_token_owner] >>
  `LENGTH (current_event_input_block ev).bb_instructions =
    LENGTH pre + LENGTH old.bb_instructions` by
    (qpat_x_assum `current_edge_shape _ (current_event_input_block ev)` mp_tac >>
     simp[current_edge_shape_def, LIST_REL_EL_EQN]) >>
  `current_source_cut A ev (LENGTH pre + LENGTH old.bb_instructions)
    (current_event_exit_rs ev) (current_event_exit_env ev)` by
    metis_tac[current_wf_event_exit_cut] >>
  irule current_wf_source_cut_owner >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem current_wf_precleanup_exit_nondefault:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  first_block_no_phi fn /\ entry_block fn = SOME eb /\
  MEM ev events /\ lookup_block (current_event_label ev) fn.fn_blocks = SOME old /\
  current_demand fn v (current_event_label ev) (LENGTH old.bb_instructions) ==>
  !w. current_event_exit_env ev v <> CurrentDefault w
Proof
  strip_tac >> drule current_wf_precleanup_structural >> strip_tac >>
  drule_all current_wf_certificate_actual_prefix >> strip_tac >>
  `LENGTH (current_event_input_block ev).bb_instructions =
    LENGTH pre + LENGTH old.bb_instructions` by
    (qpat_x_assum `current_edge_shape _ (current_event_input_block ev)` mp_tac >>
     simp[current_edge_shape_def, LIST_REL_EL_EQN]) >>
  `current_source_cut A ev (LENGTH pre + LENGTH old.bb_instructions)
    (current_event_exit_rs ev) (current_event_exit_env ev)` by
    metis_tac[current_wf_event_exit_cut] >>
  `LENGTH (collect_phis old.bb_instructions) <= LENGTH old.bb_instructions` by
    simp[current_collect_phis_length] >>
  `LENGTH old.bb_instructions <= LENGTH old.bb_instructions` by simp[] >>
  `current_event_exit_env ev v <> CurrentDefault v` by
    (drule_all current_wf_demanded_source_cut_nondefault >> simp[]) >>
  drule_all current_wf_precleanup_exit_owner >>
  disch_then (qspec_then `v` assume_tac) >>
  Cases_on `current_event_exit_env ev v` >> gvs[current_wf_token_owner_def]
QED

Theorem current_wf_original_phi_demand:
  wf_function fn /\ lookup_block h fn.fn_blocks = SOME old /\
  k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  MEM (p,v) (phi_pairs (EL k old.bb_instructions).inst_operands) /\
  fn_cfg_edge fn p h /\ lookup_block p fn.fn_blocks = SOME pred ==>
  current_demand fn v p (LENGTH pred.bb_instructions)
Proof
  strip_tac >>
  `MEM old fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb_well_formed old` by metis_tac[wf_function_def] >>
  `MEM (EL k old.bb_instructions) (collect_phis old.bb_instructions)` by
    (irule current_phi_in_prefix >> gvs[bb_well_formed_def] >> metis_tac[]) >>
  `MEM h (bb_succs pred)` by
    (fs[fn_cfg_edge_def] >>
     `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
       fs[wf_function_def, fn_labels_def] >>
     `lookup_block p fn.fn_blocks = SOME bb` by
       (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  metis_tac[current_demand_rules]
QED

Theorem current_wf_precleanup_exit_available:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  first_block_no_phi fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM ev events /\ lookup_block (current_event_label ev) fn.fn_blocks = SOME old /\
  current_demand fn v (current_event_label ev) (LENGTH old.bb_instructions) /\
  current_token_name H (current_event_exit_env ev v) = SOME n /\
  MEM bb renamed /\ bb.bb_label = current_event_label ev ==>
  def_available_at (fn with fn_blocks := renamed) bb NONE n
Proof
  strip_tac >> drule current_wf_precleanup_structural >> strip_tac >>
  drule_all current_wf_certificate_actual_prefix >> strip_tac >>
  `LENGTH (current_event_input_block ev).bb_instructions =
    LENGTH pre + LENGTH old.bb_instructions` by
    (qpat_x_assum `current_edge_shape _ (current_event_input_block ev)` mp_tac >>
     simp[current_edge_shape_def, LIST_REL_EL_EQN]) >>
  `current_source_cut A ev (LENGTH pre + LENGTH old.bb_instructions)
    (current_event_exit_rs ev) (current_event_exit_env ev)` by
    metis_tac[current_wf_event_exit_cut] >>
  `!dev k j. MEM dev events /\ k < LENGTH (A (current_event_label dev)) /\
     j < LENGTH (EL k (A (current_event_label dev))) ==>
     current_wf_output_at A H dev k (FST (EL j (EL k (A (current_event_label dev)))))` by
    metis_tac[current_wf_precleanup_output_sites] >>
  `LENGTH (collect_phis old.bb_instructions) <= LENGTH old.bb_instructions` by
    simp[current_collect_phis_length] >>
  `?dev k. MEM dev events /\ current_wf_output_at A H dev k (current_event_exit_env ev v) /\
    ((dev = ev /\ k < LENGTH pre + LENGTH old.bb_instructions) \/
     (current_event_label dev <> current_event_label ev /\
      fn_dominates fn (current_event_label dev) (current_event_label ev)))` by
    (irule current_wf_demanded_source_cut_output >> simp[] >> metis_tac[]) >>
  `fn_reachable fn (current_event_label ev)` by
    (drule lookup_block_MEM >> strip_tac >>
     drule lookup_block_label >> strip_tac >> fs[all_reachable_def] >> metis_tac[]) >>
  `fn_dominates fn (current_event_label ev) (current_event_label ev)` by
    (simp[fn_dominates_def] >> metis_tac[LAST_MEM]) >>
  irule current_wf_precleanup_output_available >> simp[] >> metis_tac[]
QED

Theorem current_wf_precleanup_static_slot:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  defs = compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))) /\
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) fn.fn_blocks defs = (ins,si) /\
  lookup_block h ins = SOME old /\ fn_cfg_edge fn p h /\
  k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_operands = current_phi_slots slots /\
  i < LENGTH slots /\ EL i slots = (p,v) ==>
  ?new path n. lookup_block h renamed = SOME new /\
    current_tree_ancestor_path (current_dom_tree fn) p path /\
    current_token_name H
      (current_block_token fn (current_actual_inserted fn) v p
        (current_inherited_token fn (current_actual_inserted fn) v path)) = SOME n /\
    LENGTH new.bb_instructions = LENGTH old.bb_instructions /\
    k < LENGTH new.bb_instructions /\ (EL k new.bb_instructions).inst_opcode = PHI /\
    EL (2 * i) (EL k new.bb_instructions).inst_operands = Label p /\
    EL (2 * i + 1) (EL k new.bb_instructions).inst_operands = Var n
Proof
  strip_tac >> drule_all current_wf_precleanup_names >> strip_tac >>
  gvs[current_wf_precleanup_certificate_def] >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks /\
    ssa_vars_covered si (FLAT (MAP block_ir_vars ins)) /\
    ssa_vars_covered si (MAP FST (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn))))))` by
    (irule current_insertion_initial_supply >> metis_tac[]) >>
  `LENGTH fn.fn_blocks = LENGTH ins` by metis_tac[LENGTH_MAP] >>
  `!old. MEM old fn.fn_blocks ==> lookup_block old.bb_label fn.fn_blocks = SOME old` by
    (rpt strip_tac >> irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l ins)` by
    metis_tac[current_actual_tree_lookup_coverage] >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  `MEM p (fn_labels fn)` by
    (fs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `MEM p (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_label_member] >>
  `MEM h (case ALOOKUP (current_succ_map fn) p of NONE => [] | SOME ss => ss)` by
    simp[ALOOKUP_current_succ_map, GSYM current_cfg_edge_succs] >>
  `MEM v (FLAT (MAP block_ir_vars ins))` by
    metis_tac[current_initial_slot_var_covered] >>
  irule current_provenance_tree_static_slot >>
  metis_tac[current_actual_succs_distinct]
QED

Theorem current_wf_precleanup_named_slot:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  defs = compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))) /\
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) fn.fn_blocks defs = (ins,si) /\
  lookup_block h ins = SOME old /\ fn_cfg_edge fn p h /\
  k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_operands = current_phi_slots slots /\
  i < LENGTH slots /\ EL i slots = (p,v) ==>
  ?new ev n. lookup_block h renamed = SOME new /\
    MEM ev events /\ current_event_label ev = p /\
    current_token_name H (current_event_exit_env ev v) = SOME n /\
    LENGTH new.bb_instructions = LENGTH old.bb_instructions /\
    k < LENGTH new.bb_instructions /\ (EL k new.bb_instructions).inst_opcode = PHI /\
    EL (2 * i) (EL k new.bb_instructions).inst_operands = Label p /\
    EL (2 * i + 1) (EL k new.bb_instructions).inst_operands = Var n
Proof
  strip_tac >> drule_all current_wf_precleanup_names >> strip_tac >>
  gvs[current_wf_precleanup_certificate_def] >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks` by
    metis_tac[add_phi_nodes_supply_labels] >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l ins)` by
    metis_tac[current_actual_tree_lookup_coverage] >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  `MEM p (fn_labels fn)` by
    (fs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `MEM p (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_label_member] >>
  `MEM h (case ALOOKUP (current_succ_map fn) p of NONE => [] | SOME ss => ss)` by
    simp[ALOOKUP_current_succ_map, GSYM current_cfg_edge_succs] >>
  `MEM v (FLAT (MAP block_ir_vars ins))` by
    metis_tac[current_initial_slot_var_covered] >>
  drule_all current_tree_trace_event_coverage >> strip_tac >>
  `ALL_DISTINCT (MAP current_event_label events)` by
    metis_tac[cj 1 current_trace_event_labels_distinct] >>
  `!p ss. ALOOKUP (current_succ_map fn) p = SOME ss ==> ALL_DISTINCT ss` by
    metis_tac[current_actual_succs_distinct] >>
  `FST (EL i slots) = current_event_label ev` by simp[] >>
  `MEM h (case ALOOKUP (current_succ_map fn) (current_event_label ev) of
     NONE => [] | SOME ss => ss)` by simp[] >>
  drule_all current_tree_trace_phi_slot >> strip_tac >>
  qexistsl_tac [`new`, `ev`, `latest_current_name (current_event_exit_rs ev) v`] >>
  fs[EVERY_MEM] >> metis_tac[current_event_names_accessors]
QED

Theorem current_wf_precleanup_slot_shape:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\
  defs = compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))) /\
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) fn.fn_blocks defs = (ins,si) /\
  lookup_block h ins = SOME old /\ k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_operands = current_phi_slots slots ==>
  ?new pairs. lookup_block h renamed = SOME new /\
    LENGTH new.bb_instructions = LENGTH old.bb_instructions /\
    k < LENGTH new.bb_instructions /\ (EL k new.bb_instructions).inst_opcode = PHI /\
    (EL k new.bb_instructions).inst_operands = current_phi_slots pairs /\
    MAP FST pairs = MAP FST slots
Proof
  simp[current_wf_precleanup_certificate_def] >> rpt strip_tac >> gvs[] >>
  irule current_wf_tree_phi_slot_shape >>
  metis_tac[current_actual_succs_distinct]
QED

Definition current_wf_phi_context_def:
  current_wf_phi_context s fn renamed s' A H events <=>
    current_wf_precleanup_certificate s fn renamed s' A H events /\
    fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
    fn_phis_cover_preds fn /\
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = PHI ==>
      ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
      !l v. MEM (l,v) (phi_pairs inst.inst_operands) ==>
        fn_cfg_edge fn l bb.bb_label) /\
    fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
    all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
    first_block_no_preds fn /\ first_block_no_phi fn /\
    ir_supply_covers_fn s fn /\ ir_supply_inst_ok s
End

Theorem current_wf_phi_context_intro:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  fn_phis_cover_preds fn /\
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI ==>
    ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
    !l v. MEM (l,v) (phi_pairs inst.inst_operands) ==>
      fn_cfg_edge fn l bb.bb_label) /\
  fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s ==>
  current_wf_phi_context s fn renamed s' A H events
Proof
  rewrite_tac[current_wf_phi_context_def] >> strip_tac >> asm_rewrite_tac[]
QED

Theorem current_wf_precleanup_insertion_lookup:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  lookup_block h fn.fn_blocks = SOME old ==>
  ?defs ins si pre.
    defs = compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))) /\
    add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
      (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
        (liveness_analyze fn) fn) fn.fn_blocks defs = (ins,si) /\
    lookup_block h ins = SOME (old with bb_instructions := pre ++ old.bb_instructions) /\
    A h = current_block_annotations old pre /\
    EVERY (\i. ?id w. i = build_phi_inst_supply id w
      (case ALOOKUP (current_pred_map fn) old.bb_label of
        SOME ps => ps | NONE => [])) pre /\
    (!v. current_actual_inserted fn v old.bb_label <=>
      ?i. MEM i pre /\ MEM v i.inst_outputs)
Proof
  simp[current_wf_precleanup_certificate_def] >> rpt strip_tac >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks` by
    metis_tac[add_phi_nodes_supply_labels] >>
  `LENGTH fn.fn_blocks = LENGTH ins` by metis_tac[LENGTH_MAP] >>
  drule current_actual_insertion_prefix >> strip_tac >>
  drule_all (BETA_RULE (Q.INST [`P` |-> `\old pre.
    EVERY (\i. ?id v. i = build_phi_inst_supply id v
      (case ALOOKUP (current_pred_map fn) old.bb_label of
        SOME ps => ps | NONE => [])) pre /\
    (!v. current_actual_inserted fn v old.bb_label <=>
      ?i. MEM i pre /\ MEM v i.inst_outputs)`]
    current_wf_prefix_annotation_lookup)) >> strip_tac >>
  qexistsl_tac [`ins`, `si`, `pre`] >> simp[]
QED

Definition current_wf_original_phi_at_def:
  current_wf_original_phi_at fn A renamed h k q slots <=>
    ?old pre new.
      lookup_block h fn.fn_blocks = SOME old /\
      k < LENGTH old.bb_instructions /\
      (EL k old.bb_instructions).inst_opcode = PHI /\
      (EL k old.bb_instructions).inst_operands = current_phi_slots slots /\
      slots = phi_pairs (EL k old.bb_instructions).inst_operands /\
      A h = current_block_annotations old pre /\
      lookup_block h renamed = SOME new /\
      q = LENGTH pre + k /\ q < LENGTH new.bb_instructions /\
      (EL q new.bb_instructions).inst_opcode = PHI
End

Theorem current_wf_original_outputs_index[local]:
  !vs j r. r < LENGTH vs ==>
    EL r (current_original_outputs l k j vs) = (CurrentOriginal l k (j + r), EL r vs)
Proof
  Induct >> simp[current_original_outputs_def] >> rpt gen_tac >>
  Cases_on `r` >> simp[current_original_outputs_def, arithmeticTheory.ADD_CLAUSES]
QED

Theorem current_wf_original_annotations_index[local]:
  !xs k r. r < LENGTH xs ==>
    EL r (current_original_annotations l k xs) =
      current_original_outputs l (k + r) 0 (EL r xs).inst_outputs
Proof
  Induct >> simp[current_original_annotations_def] >> rpt gen_tac >>
  Cases_on `r` >> simp[current_original_annotations_def, arithmeticTheory.ADD_CLAUSES]
QED

Theorem current_wf_original_annotation_index:
  k < LENGTH old.bb_instructions /\ j < LENGTH (EL k old.bb_instructions).inst_outputs ==>
  LENGTH pre + k < LENGTH (current_block_annotations old pre) /\
  j < LENGTH (EL (LENGTH pre + k) (current_block_annotations old pre)) /\
  EL j (EL (LENGTH pre + k) (current_block_annotations old pre)) =
    (CurrentOriginal old.bb_label k j, EL j (EL k old.bb_instructions).inst_outputs)
Proof
  strip_tac >>
  `LENGTH (current_original_annotations old.bb_label 0 old.bb_instructions) =
    LENGTH old.bb_instructions` by
    metis_tac[current_original_annotations_owners, LIST_REL_LENGTH] >>
  `LENGTH (current_original_outputs old.bb_label k 0
    (EL k old.bb_instructions).inst_outputs) =
    LENGTH (EL k old.bb_instructions).inst_outputs` by
    metis_tac[current_original_outputs_owners, LENGTH_MAP] >>
  simp[current_block_annotations_def, current_inserted_annotations_def,
    EL_APPEND_EQN, current_wf_original_annotations_index,
    current_wf_original_outputs_index]
QED

Theorem current_wf_original_phi_index_unique:
  current_wf_original_phi_at fn A renamed h k q slots /\
  current_wf_original_phi_at fn A renamed h k r slots' ==> q = r
Proof
  rewrite_tac[current_wf_original_phi_at_def] >> strip_tac >>
  rpt (qpat_x_assum `_.inst_operands = _` kall_tac) >>
  gvs[] >>
  `LENGTH pre = LENGTH pre'` by
    (qpat_x_assum `current_block_annotations old pre' = current_block_annotations old pre`
       (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[current_block_annotations_def, current_inserted_annotations_def]) >>
  simp[]
QED

Theorem current_wf_original_phi_slot:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  slots = phi_pairs (EL k old.bb_instructions).inst_operands /\
  i < LENGTH slots /\ EL i slots = (p,v) ==>
  ?q new ev n.
    current_wf_original_phi_at fn A renamed h k q slots /\
    lookup_block h renamed = SOME new /\
    MEM ev events /\ current_event_label ev = p /\
    current_wf_token_owner fn (current_event_exit_env ev v) v /\
    (!w. current_event_exit_env ev v <> CurrentDefault w) /\
    current_token_name H (current_event_exit_env ev v) = SOME n /\
    EL (2 * i) (EL q new.bb_instructions).inst_operands = Label p /\
    EL (2 * i + 1) (EL q new.bb_instructions).inst_operands = Var n
Proof
  rewrite_tac[current_wf_phi_context_def] >> strip_tac >>
  `MEM old fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM (EL k old.bb_instructions) old.bb_instructions` by metis_tac[MEM_EL] >>
  `inst_wf (EL k old.bb_instructions)` by metis_tac[fn_inst_wf_def] >>
  ` (EL k old.bb_instructions).inst_operands = current_phi_slots slots` by
    (gvs[inst_wf_def] >> metis_tac[current_wf_phi_slots]) >>
  `MEM (p,v) (phi_pairs (EL k old.bb_instructions).inst_operands)` by
    metis_tac[MEM_EL] >>
  `old.bb_label = h` by metis_tac[lookup_block_label] >>
  `fn_cfg_edge fn p h` by metis_tac[] >>
  drule_all current_wf_precleanup_insertion_lookup >> strip_tac >>
  `LENGTH pre + k < LENGTH (old with bb_instructions := pre ++ old.bb_instructions).bb_instructions /\
    (EL (LENGTH pre + k) (old with bb_instructions := pre ++ old.bb_instructions).bb_instructions).inst_opcode = PHI /\
    (EL (LENGTH pre + k) (old with bb_instructions := pre ++ old.bb_instructions).bb_instructions).inst_operands = current_phi_slots slots` by
    simp[IgnAsm `slots = _`, EL_APPEND_EQN] >>
  drule_all current_wf_precleanup_named_slot >> strip_tac >>
  `?pred. lookup_block p fn.fn_blocks = SOME pred` by
    (fs[fn_cfg_edge_def] >>
     `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
       fs[wf_function_def, fn_labels_def] >>
     metis_tac[MEM_lookup_block]) >>
  `current_demand fn v p (LENGTH pred.bb_instructions)` by
    (irule current_wf_original_phi_demand >> metis_tac[]) >>
  `current_wf_token_owner fn (current_event_exit_env ev v) v` by
    (irule current_wf_precleanup_exit_owner >> metis_tac[]) >>
  `!w. current_event_exit_env ev v <> CurrentDefault w` by
    (irule current_wf_precleanup_exit_nondefault >> metis_tac[]) >>
  qexistsl_tac [`LENGTH pre + k`, `new`, `ev`, `n`] >>
  conj_tac
  >- (rewrite_tac[current_wf_original_phi_at_def] >>
      qexistsl_tac [`old`, `pre`, `new`] >>
      rpt conj_tac >> FIRST [REFL_TAC, first_assum ACCEPT_TAC]) >>
  simp[IgnAsm `slots = _`]
QED

Theorem current_wf_original_phi_output:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_wf_original_phi_at fn A renamed h k q slots /\
  lookup_block h fn.fn_blocks = SOME old /\
  j < LENGTH (EL k old.bb_instructions).inst_outputs ==>
  ?new n.
    lookup_block h renamed = SOME new /\ q < LENGTH new.bb_instructions /\
    current_wf_token_owner fn (CurrentOriginal h k j)
      (EL j (EL k old.bb_instructions).inst_outputs) /\
    current_token_name H (CurrentOriginal h k j) = SOME n /\
    MEM n (EL q new.bb_instructions).inst_outputs
Proof
  rewrite_tac[current_wf_phi_context_def, current_wf_original_phi_at_def] >>
  strip_tac >> gvs[] >>
  `old.bb_label = h` by metis_tac[lookup_block_label] >>
  `MEM new renamed` by metis_tac[lookup_block_MEM] >>
  drule_all current_wf_precleanup_block_shape >> strip_tac >>
  `new.bb_label = h` by metis_tac[lookup_block_label] >>
  `LENGTH pre + k < LENGTH (A (current_event_label ev)) /\
    j < LENGTH (EL (LENGTH pre + k) (A (current_event_label ev))) /\
    EL j (EL (LENGTH pre + k) (A (current_event_label ev))) =
      (CurrentOriginal h k j, EL j (EL k old.bb_instructions).inst_outputs)` by
    (drule_all current_wf_original_annotation_index >> simp[] >> metis_tac[]) >>
  `current_wf_output_at A H ev (LENGTH pre + k) (CurrentOriginal h k j)` by
    metis_tac[current_wf_precleanup_output_sites, pairTheory.FST] >>
  `?n. current_token_name H (CurrentOriginal h k j) = SOME n` by
    metis_tac[current_wf_output_at_def] >>
  drule_all current_wf_precleanup_output >> strip_tac >>
  qexists_tac `n` >> simp[current_wf_token_owner_def] >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem current_wf_precleanup_output_alignment:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h renamed = SOME new ==>
  MAP (\inst. LENGTH inst.inst_outputs) new.bb_instructions =
    MAP LENGTH (A h)
Proof
  rewrite_tac[current_wf_phi_context_def] >> strip_tac >>
  `MEM new renamed` by metis_tac[lookup_block_MEM] >>
  `new.bb_label = h` by metis_tac[lookup_block_label] >>
  drule_all current_wf_precleanup_block_shape >> strip_tac >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  `current_event_trace A H ev /\
    current_event_valid A (FLAT (MAP block_ir_vars ins)) ev` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all current_wf_event_output_relation >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  fs[current_edge_shape_def, LIST_REL_EL_EQN] >>
  simp[LIST_EQ_REWRITE, EL_MAP] >> rpt strip_tac >>
  metis_tac[EL_MAP]
QED

Theorem current_wf_original_phi_output_length:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_wf_original_phi_at fn A renamed h k q slots /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new ==>
  LENGTH (EL q new.bb_instructions).inst_outputs =
    LENGTH (EL k old.bb_instructions).inst_outputs
Proof
  strip_tac >> drule_all current_wf_precleanup_output_alignment >> strip_tac >>
  qpat_x_assum `current_wf_original_phi_at _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[current_wf_original_phi_at_def] >> strip_tac >>
  rpt (qpat_x_assum `_.inst_operands = _` kall_tac) >> gvs[] >>
  `LENGTH (current_original_annotations old.bb_label 0 old.bb_instructions) =
    LENGTH old.bb_instructions` by
    metis_tac[current_original_annotations_owners, LIST_REL_LENGTH] >>
  `LENGTH (current_original_outputs old.bb_label k 0
      (EL k old.bb_instructions).inst_outputs) =
    LENGTH (EL k old.bb_instructions).inst_outputs` by
    metis_tac[current_original_outputs_owners, LENGTH_MAP] >>
  qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `\xs. EL (LENGTH pre + k) xs`) >>
  simp[EL_MAP, current_block_annotations_def, current_inserted_annotations_def,
    EL_APPEND_EQN, current_wf_original_annotations_index]
QED

Theorem current_wf_original_phi_input_witnesses:
  current_wf_phi_context s fn renamed s' A H events /\
  current_wf_original_phi_at fn A renamed h k q slots /\
  lookup_block h fn.fn_blocks = SOME old ==>
  ?out i1 p1 v1 i2 p2 v2.
    (EL k old.bb_instructions).inst_outputs = [out] /\
    i1 < LENGTH slots /\ EL i1 slots = (p1,v1) /\
    i2 < LENGTH slots /\ EL i2 slots = (p2,v2) /\
    v1 <> out /\ v2 <> out /\ v1 <> v2
Proof
  rewrite_tac[current_wf_phi_context_def, current_wf_original_phi_at_def] >>
  strip_tac >>
  rpt (qpat_x_assum `_.inst_operands = current_phi_slots _` kall_tac) >> gvs[] >>
  `MEM old fn.fn_blocks /\ MEM (EL k old.bb_instructions) old.bb_instructions` by
    metis_tac[lookup_block_MEM, MEM_EL] >>
  `inst_wf (EL k old.bb_instructions)` by metis_tac[fn_inst_wf_def] >>
  `?out. (EL k old.bb_instructions).inst_outputs = [out]` by
    (qpat_x_assum `inst_wf _` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `MEM (EL k old.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  fs[fn_phis_non_degenerate_def] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  gvs[MEM_EL] >> metis_tac[]
QED

Theorem current_wf_original_phi_shape:
  current_wf_phi_context s fn renamed s' A H events /\
  current_wf_original_phi_at fn A renamed h k q slots /\
  lookup_block h renamed = SOME new ==>
  ?pairs. (EL q new.bb_instructions).inst_operands = current_phi_slots pairs /\
    MAP FST pairs = MAP FST slots
Proof
  rewrite_tac[current_wf_phi_context_def, current_wf_original_phi_at_def] >>
  strip_tac >> gvs[] >>
  drule_all current_wf_precleanup_insertion_lookup >> strip_tac >>
  `LENGTH pre = LENGTH pre'` by
    (`current_block_annotations old pre = current_block_annotations old pre'` by
       metis_tac[] >>
     pop_assum (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[current_block_annotations_def, current_inserted_annotations_def]) >>
  `LENGTH pre' + k < LENGTH (old with bb_instructions := pre' ++ old.bb_instructions).bb_instructions /\
    (EL (LENGTH pre' + k) (old with bb_instructions := pre' ++ old.bb_instructions).bb_instructions).inst_opcode = PHI /\
    (EL (LENGTH pre' + k) (old with bb_instructions := pre' ++ old.bb_instructions).bb_instructions).inst_operands = current_phi_slots (phi_pairs (EL k old.bb_instructions).inst_operands)` by
    simp[EL_APPEND_EQN] >>
  drule_all current_wf_precleanup_slot_shape >> strip_tac >>
  rpt (qpat_x_assum `_.inst_operands = current_phi_slots (phi_pairs _)` kall_tac) >>
  gvs[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Theorem current_wf_original_phi_pair:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_wf_original_phi_at fn A renamed h k q slots /\
  lookup_block h renamed = SOME new /\
  (EL q new.bb_instructions).inst_operands = current_phi_slots pairs /\
  MAP FST pairs = MAP FST slots /\ i < LENGTH slots /\ EL i slots = (p,v) ==>
  ?ev n. MEM ev events /\ current_event_label ev = p /\
    current_wf_token_owner fn (current_event_exit_env ev v) v /\
    (!w. current_event_exit_env ev v <> CurrentDefault w) /\
    current_token_name H (current_event_exit_env ev v) = SOME n /\
    EL i pairs = (p,n)
Proof
  strip_tac >>
  qpat_assum `current_wf_original_phi_at _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[current_wf_original_phi_at_def] >> strip_tac >>
  drule_all current_wf_original_phi_slot >> strip_tac >>
  `q' = q` by metis_tac[current_wf_original_phi_index_unique] >>
  `i < LENGTH pairs` by metis_tac[LENGTH_MAP] >>
  `EL (2 * i) (current_phi_slots pairs) = Label (FST (EL i pairs)) /\
    EL (2 * i + 1) (current_phi_slots pairs) = Var (SND (EL i pairs))` by
    metis_tac[current_phi_slots_index] >>
  rpt (qpat_x_assum `_.inst_operands = current_phi_slots slots` kall_tac) >>
  qexistsl_tac [`ev`, `n`] >> gvs[] >>
  Cases_on `EL i pairs` >> gvs[]
QED

Theorem current_wf_original_phi_witnesses:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_wf_original_phi_at fn A renamed h k q slots /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new ==>
  ?out pairs p1 n1 p2 n2.
    (EL q new.bb_instructions).inst_outputs = [out] /\
    (EL q new.bb_instructions).inst_operands = current_phi_slots pairs /\
    MEM (p1,n1) pairs /\ MEM (p2,n2) pairs /\
    n1 <> out /\ n2 <> out /\ n1 <> n2
Proof
  strip_tac >> drule_all current_wf_original_phi_input_witnesses >> strip_tac >>
  drule_all current_wf_original_phi_shape >> strip_tac >>
  mp_tac (Q.INST [`i` |-> `i1`, `p` |-> `p1`, `v` |-> `v1`]
    (SPEC_ALL current_wf_original_phi_pair)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  mp_tac (Q.INST [`i` |-> `i2`, `p` |-> `p2`, `v` |-> `v2`]
    (SPEC_ALL current_wf_original_phi_pair)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `0 < LENGTH (EL k old.bb_instructions).inst_outputs` by simp[] >>
  drule_all (Q.INST [`j` |-> `0`] current_wf_original_phi_output) >> strip_tac >>
  drule_all current_wf_original_phi_output_length >> strip_tac >>
  ` (EL q new.bb_instructions).inst_outputs = [n'']` by
    (gvs[LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
    wf_function fn /\ all_reachable fn /\
    ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  `current_wf_token_owner fn (CurrentOriginal h k 0) out /\
    (!x. CurrentOriginal h k 0 <> CurrentDefault x)` by
    (qpat_x_assum `current_wf_token_owner fn (CurrentOriginal _ _ _) _` mp_tac >>
     simp[]) >>
  `n <> n' /\ n <> n'' /\ n' <> n''` by
    metis_tac[current_wf_owned_names_distinct] >>
  qexistsl_tac [`n''`, `pairs`, `p1`, `n`, `p2`, `n'`] >> simp[] >>
  `LENGTH pairs = LENGTH slots` by metis_tac[LENGTH_MAP] >>
  metis_tac[MEM_EL]
QED

Theorem current_wf_original_phi_retained:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_wf_original_phi_at fn A renamed h k q slots /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new ==>
  simplify_current_phi (EL q new.bb_instructions) = EL q new.bb_instructions
Proof
  strip_tac >> drule_all current_wf_original_phi_witnesses >> strip_tac >>
  irule current_phi_slots_retained >>
  ` (EL q new.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_original_phi_at_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem current_wf_original_phi_pair_available:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_wf_original_phi_at fn A renamed h k q slots /\
  lookup_block h renamed = SOME new /\
  (EL q new.bb_instructions).inst_operands = current_phi_slots pairs /\
  MAP FST pairs = MAP FST slots /\ i < LENGTH slots /\ EL i slots = (p,v) ==>
  ?pb n. MEM pb renamed /\ pb.bb_label = p /\ EL i pairs = (p,n) /\
    fn_cfg_edge (fn with fn_blocks := renamed) p h /\
    def_available_at (fn with fn_blocks := renamed) pb NONE n
Proof
  strip_tac >> drule_all current_wf_original_phi_pair >> strip_tac >>
  qpat_assum `current_wf_phi_context _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[current_wf_phi_context_def] >> strip_tac >>
  qpat_assum `current_wf_original_phi_at _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[current_wf_original_phi_at_def] >> strip_tac >>
  rpt (qpat_x_assum `_.inst_operands = current_phi_slots slots` kall_tac) >>
  `MEM old fn.fn_blocks /\ MEM (EL k old.bb_instructions) old.bb_instructions /\
    old.bb_label = h` by metis_tac[lookup_block_MEM, lookup_block_label, MEM_EL] >>
  `MEM (p,v) (phi_pairs (EL k old.bb_instructions).inst_operands)` by
    metis_tac[MEM_EL] >>
  `fn_cfg_edge fn p h` by metis_tac[] >>
  `?pred. lookup_block p fn.fn_blocks = SOME pred` by
    (fs[fn_cfg_edge_def] >>
     `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
       fs[wf_function_def, fn_labels_def] >>
     metis_tac[MEM_lookup_block]) >>
  `current_demand fn v p (LENGTH pred.bb_instructions)` by
    (irule current_wf_original_phi_demand >> metis_tac[]) >>
  `?pb. MEM pb renamed /\ pb.bb_label = p` by
    (drule current_wf_precleanup_labels >> strip_tac >>
     `MEM p (MAP (\b. b.bb_label) fn.fn_blocks)` by
       metis_tac[lookup_block_MEM, lookup_block_label, MEM_MAP] >>
     metis_tac[MEM_MAP]) >>
  qexistsl_tac [`pb`, `n`] >> simp[] >> conj_tac
  >- metis_tac[current_wf_precleanup_cfg] >>
  irule current_wf_precleanup_exit_available >> metis_tac[]
QED

Theorem current_wf_slots_shape[local]:
  !slots. phi_well_formed (current_phi_slots slots) /\
    phi_pairs (current_phi_slots slots) = slots
Proof
  Induct >> simp[current_phi_slots_def, phi_well_formed_def, phi_pairs_def] >>
  gen_tac >> PairCases_on `h` >>
  fs[current_phi_slots_def, phi_well_formed_def, phi_pairs_def]
QED

Theorem current_wf_original_phi_edge_wf:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  current_wf_original_phi_at fn A renamed h k q slots /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new ==>
  phi_edge_uses_wf (fn with fn_blocks := renamed) new (EL q new.bb_instructions)
Proof
  strip_tac >> drule_all current_wf_original_phi_shape >> strip_tac >>
  `new.bb_label = h` by metis_tac[lookup_block_label] >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
    wf_function fn /\ all_reachable fn /\ fn_phis_cover_preds fn` by
    fs[current_wf_phi_context_def] >>
  `ALL_DISTINCT (MAP FST slots) /\
    (!p. fn_cfg_edge fn p h <=> MEM p (MAP FST slots))` by
    (qpat_assum `current_wf_original_phi_at _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[current_wf_original_phi_at_def] >> strip_tac >>
     rpt (qpat_x_assum `_.inst_operands = current_phi_slots _` kall_tac) >>
     gvs[] >>
     `MEM old fn.fn_blocks /\ MEM (EL k old.bb_instructions) old.bb_instructions /\
       old.bb_label = new.bb_label` by
       metis_tac[lookup_block_MEM, lookup_block_label, MEM_EL] >>
     qpat_x_assum `current_wf_phi_context _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[current_wf_phi_context_def] >> strip_tac >>
     fs[fn_phis_cover_preds_def, MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  simp[phi_edge_uses_wf_def, current_wf_slots_shape] >> conj_tac
  >- (drule_all current_wf_precleanup_cfg >> strip_tac >>
      `!p. fn_cfg_edge (fn with fn_blocks := renamed) p h <=>
        MEM p (MAP FST pairs)` by metis_tac[] >>
      metis_tac[MEM_MAP]) >>
  rpt strip_tac >>
  `?i. i < LENGTH pairs /\ EL i pairs = (pred,v)` by metis_tac[MEM_EL] >>
  `i < LENGTH slots` by metis_tac[LENGTH_MAP] >>
  Cases_on `EL i slots` >>
  drule_all current_wf_original_phi_pair_available >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem current_wf_blocks_distinct_instructions:
  !bbs. ALL_DISTINCT (FLAT (MAP block_ir_inst_ids bbs)) ==>
    !bb. MEM bb bbs ==> ALL_DISTINCT bb.bb_instructions
Proof
  Induct >> simp[ALL_DISTINCT_APPEND] >> rpt strip_tac >> gvs[] >>
  fs[block_ir_inst_ids_def] >> metis_tac[ALL_DISTINCT_MAP]
QED

Theorem current_wf_original_phi_single_site:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
  di.inst_opcode = PHI /\ MEM v di.inst_outputs ==>
  !l. current_changing_site fn (current_actual_inserted fn) v l ==> l = db.bb_label
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
    all_reachable fn /\ first_block_no_preds fn /\
    fn_phi_outputs_single_def fn` by fs[current_wf_phi_context_def] >>
  `LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1` by
    metis_tac[fn_phi_outputs_single_def_def] >>
  `blocks_have_leading_phi fn.fn_blocks` by
    (`MEM di (collect_phis db.bb_instructions)` by
       (`bb_well_formed db` by metis_tac[wf_function_def] >>
        fs[bb_well_formed_def] >> metis_tac[current_phi_in_prefix, MEM_EL]) >>
     metis_tac[current_phi_operand_has_leading_phi]) >>
  simp[current_changing_site_def] >> rpt strip_tac
  >- (irule current_actual_inserted_single_local >> metis_tac[]) >>
  metis_tac[current_single_def_occurrence]
QED

Theorem current_wf_original_scan_single:
  !xs i k t. k < LENGTH xs /\ (EL k xs).inst_outputs = [v] /\
    (!r. r < LENGTH xs /\ r <> k ==> ~MEM v (EL r xs).inst_outputs) ==>
    current_original_scan v l i xs t = CurrentOriginal l (i + k) 0
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `k` >> simp[] >> strip_tac
  >- (`EVERY (\inst. ~MEM v inst.inst_outputs) xs` by
        (simp[EVERY_EL] >> rpt strip_tac >>
         first_x_assum (qspec_then `SUC n` mp_tac) >> simp[]) >>
      simp[current_original_scan_def, current_output_token_def,
        current_original_scan_absent]) >>
  `~MEM v h.inst_outputs` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[current_original_scan_def, current_output_token_absent] >>
  `current_original_scan v l (SUC i) xs t = CurrentOriginal l (SUC i + n) 0` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `SUC r` mp_tac) >> simp[]) >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem current_wf_single_site_chain:
  !ls t. wf_function fn /\ MEM d (fn_labels fn) /\
    current_changing_site fn ins v d /\
    (!l. current_changing_site fn ins v l ==> l = d) ==>
    current_chain_token fn ins v ls t =
      if MEM d ls then current_block_token fn ins v d (CurrentDefault v) else t
Proof
  Induct >- simp[current_chain_token_def] >> rpt strip_tac >>
  simp[current_chain_token_def] >>
  Cases_on `h = d` >> gvs[]
  >- (Cases_on `MEM d ls` >> simp[] >>
      metis_tac[current_site_block_constant]) >>
  `~current_changing_site fn ins v h` by metis_tac[] >>
  simp[current_non_site_block_token]
QED

Theorem current_wf_single_site_endpoint:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM p (fn_labels fn) /\ MEM d (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps p /\
  current_changing_site fn ins v d /\
  (!l. current_changing_site fn ins v l ==> l = d) ==>
  current_block_token fn ins v p
    (current_inherited_token fn ins v (REVERSE ps)) =
  if d = p \/ strict_dominates (dom_analyze (cfg_analyze fn) fn) d p
  then current_block_token fn ins v d (CurrentDefault v)
  else CurrentDefault v
Proof
  strip_tac >>
  drule_all current_actual_chain_membership >> strip_tac >>
  `!ls t. current_chain_token fn ins v ls t =
    if MEM d ls then current_block_token fn ins v d (CurrentDefault v) else t`
    by metis_tac[current_wf_single_site_chain] >>
  once_rewrite_tac[GSYM current_inherited_token_step] >>
  simp[current_inherited_token_def] >>
  metis_tac[]
QED

Theorem current_wf_original_phi_block_token:
  current_wf_phi_context s fn renamed s' A H events /\
  lookup_block h fn.fn_blocks = SOME old /\ k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_outputs = [v] ==>
  current_block_token fn ins v h t = CurrentOriginal h k 0
Proof
  strip_tac >>
  `wf_function fn /\ fn_phi_outputs_single_def fn` by
    fs[current_wf_phi_context_def] >>
  `MEM old fn.fn_blocks /\ old.bb_label = h` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `MEM (EL k old.bb_instructions) old.bb_instructions` by metis_tac[MEM_EL] >>
  `LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1` by
    metis_tac[fn_phi_outputs_single_def_def, MEM] >>
  `ALL_DISTINCT old.bb_instructions` by
    (irule current_wf_blocks_distinct_instructions >>
     qexists_tac `fn.fn_blocks` >>
     fs[wf_function_def, fn_inst_ids_distinct_def,
        GSYM block_ir_inst_ids_def, ETA_THM]) >>
  `!r. r < LENGTH old.bb_instructions /\ r <> k ==>
    ~MEM v (EL r old.bb_instructions).inst_outputs` by
    (rpt strip_tac >>
     `EL r old.bb_instructions = EL k old.bb_instructions` by
       (irule (cj 2 current_single_def_occurrence) >> metis_tac[MEM_EL, MEM]) >>
     metis_tac[ALL_DISTINCT_EL_IMP]) >>
  simp[current_block_token_def] >>
  drule_all current_wf_original_scan_single >> simp[]
QED

Theorem current_wf_original_phi_exit_token:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ MEM ev events /\
  lookup_block h fn.fn_blocks = SOME old /\ k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_outputs = [v] ==>
  current_event_exit_env ev v =
    if h = current_event_label ev \/
       strict_dominates (dom_analyze (cfg_analyze fn) fn) h (current_event_label ev)
    then CurrentOriginal h k 0 else CurrentDefault v
Proof
  strip_tac >>
  `wf_function fn /\ all_reachable fn /\
   current_wf_precleanup_certificate s fn renamed s' A H events` by
    fs[current_wf_phi_context_def] >>
  drule current_wf_precleanup_structural >> strip_tac >>
  drule_all current_wf_certificate_static_entry >> strip_tac >>
  `MEM old fn.fn_blocks /\ old.bb_label = h` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `MEM h (fn_labels fn)` by (simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `MEM (current_event_label ev) (fn_labels fn)` by
    metis_tac[current_tree_ancestor_path_labels, current_actual_tree_label_member] >>
  `current_changing_site fn (current_actual_inserted fn) v h` by
    (simp[current_changing_site_def] >> disj2_tac >>
     qexistsl_tac [`old`, `EL k old.bb_instructions`] >> simp[] >>
     metis_tac[MEM_EL]) >>
  `!l. current_changing_site fn (current_actual_inserted fn) v l ==> l = h` by
    (metis_tac[current_wf_original_phi_single_site, MEM_EL, MEM]) >>
  drule_all current_actual_path_chain >> strip_tac >>
  drule_all current_wf_single_site_endpoint >> simp[] >>
  `current_block_token fn (current_actual_inserted fn) v h (CurrentDefault v) =
     CurrentOriginal h k 0` by metis_tac[current_wf_original_phi_block_token] >>
  simp[]
QED

Theorem current_wf_original_phi_inserted_frontier:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  MEM old fn.fn_blocks /\ MEM inst old.bb_instructions /\
  inst.inst_opcode = PHI /\ MEM v inst.inst_outputs /\
  current_actual_inserted fn v old.bb_label ==>
  current_frontier_edge (current_frontier_map fn) old.bb_label old.bb_label
Proof
  strip_tac >>
  `wf_function fn /\ all_reachable fn /\ fn_phi_outputs_single_def fn` by
    fs[current_wf_phi_context_def] >>
  `LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts fn)) <= 1` by
    metis_tac[fn_phi_outputs_single_def_def] >>
  `!l. current_changing_site fn (current_actual_inserted fn) v l ==>
     l = old.bb_label` by metis_tac[current_wf_original_phi_single_site] >>
  qpat_x_assum `current_actual_inserted fn v old.bb_label` mp_tac >>
  rewrite_tac[current_actual_inserted_def] >> strip_tac >>
  `!d. MEM d roots ==> d = old.bb_label` by
    metis_tac[current_compute_defs_single_support] >>
  `!d. current_pruned_reach (current_frontier_map fn)
     (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
        (liveness_analyze fn) fn) v roots d ==> d = old.bb_label` by
    (rpt strip_tac >>
     `current_actual_inserted fn v d` by metis_tac[current_actual_inserted_def] >>
     metis_tac[current_changing_site_def]) >>
  qpat_x_assum `current_pruned_reach _ _ _ _ old.bb_label` mp_tac >>
  once_rewrite_tac[current_pruned_reach_cases] >> metis_tac[]
QED

Theorem current_wf_original_phi_inserted_return:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  MEM old fn.fn_blocks /\ MEM inst old.bb_instructions /\
  inst.inst_opcode = PHI /\ MEM v inst.inst_outputs /\
  current_actual_inserted fn v old.bb_label ==>
  ?p. fn_cfg_edge fn p old.bb_label /\
      dominates (dom_analyze (cfg_analyze fn) fn) old.bb_label p
Proof
  strip_tac >>
  drule_all current_wf_original_phi_inserted_frontier >>
  rewrite_tac[current_frontier_edge_def] >> strip_tac >>
  `wf_function fn /\ all_reachable fn /\ first_block_no_preds fn` by
    fs[current_wf_phi_context_def] >>
  `MEM old.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  drule_all current_frontier_elim >>
  simp[current_cfg_edge_preds] >> metis_tac[]
QED

Theorem current_wf_outputs_history_owners:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' ==>
  MAP (\e. (FST e,FST (SND e))) H' =
    MAP (\e. (FST e,FST (SND e))) H ++ anns
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[APPEND_ASSOC]
QED

Theorem current_wf_local_history_owners:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  MAP (\e. (FST e,FST (SND e))) H' =
    MAP (\e. (FST e,FST (SND e))) H ++ FLAT annss
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >>
  drule current_inst_trace_projection >> strip_tac >>
  qpat_x_assum `current_inst_trace _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[current_inst_trace_def] >> strip_tac >>
  drule current_wf_outputs_history_owners >> strip_tac >>
  first_x_assum drule >> simp[APPEND_ASSOC]
QED

Definition current_wf_history_provenance_def:
  current_wf_history_provenance A visited H <=>
    !t v n. MEM (t,v,n) H ==>
      ?l. MEM l visited /\ MEM (t,v) (FLAT (A l))
End

Theorem current_wf_local_history_provenance:
  current_local_trace (A l) insts s rs H E insts' s' rs' H' E' /\
  current_wf_history_provenance A visited H ==>
  current_wf_history_provenance A (l::visited) H'
Proof
  strip_tac >> drule current_wf_local_history_owners >> strip_tac >>
  simp[current_wf_history_provenance_def] >> rpt strip_tac >>
  `MEM (t,v) (MAP (\e. (FST e,FST (SND e))) H')` by
    (simp[MEM_MAP] >> qexists_tac `(t,v,n)` >> simp[]) >>
  qpat_x_assum `MEM (t,v) (MAP _ H')` mp_tac >>
  pure_asm_rewrite_tac[MEM_APPEND] >>
  simp[MEM_MAP, pairTheory.EXISTS_PROD] >> strip_tac
  >- (fs[current_wf_history_provenance_def] >> metis_tac[]) >>
  qexists_tac `l` >> simp[]
QED

Theorem current_wf_tree_history_provenance:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    current_wf_history_provenance A visited H ==>
    current_wf_history_provenance A visited' H') /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    current_wf_history_provenance A visited H ==>
    current_wf_history_provenance A visited' H')
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      first_x_assum irule >> metis_tac[current_wf_local_history_provenance])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED

Definition current_wf_event_history_provenance_def:
  current_wf_event_history_provenance A
    (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,
      (bbs1 : basic_block list),(bbs2 : basic_block list)) <=>
    ?visited. ~MEM l visited /\ current_wf_history_provenance A visited H
End

Theorem current_wf_tree_event_history_provenance:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    ALL_DISTINCT (dom_tree_labels tree) /\
    (!l. MEM l (dom_tree_labels tree) ==> ~MEM l visited) /\
    current_wf_history_provenance A visited H ==>
    EVERY (current_wf_event_history_provenance A) events) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l visited) /\
    current_wf_history_provenance A visited H ==>
    EVERY (current_wf_event_history_provenance A) events)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def, dom_tree_labels_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      conj_tac
      >- (simp[current_wf_event_history_provenance_def] >> metis_tac[]) >>
      first_x_assum irule >>
      metis_tac[current_wf_local_history_provenance, MEM])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def, ALL_DISTINCT_APPEND] >> strip_tac >> gvs[] >>
  simp[EVERY_APPEND] >> conj_tac
  >- (last_x_assum irule >> metis_tac[MEM_APPEND]) >>
  `current_wf_history_provenance A visited1 H1` by
    metis_tac[cj 1 current_wf_tree_history_provenance] >>
  `!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l visited1` by
    (drule (cj 1 current_tree_trace_visited) >> metis_tac[MEM_APPEND]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem current_wf_event_single_owner_absent:
  current_wf_event_history_provenance A
    (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,bbs1,bbs2) /\
  (!q t. MEM (t,v) (FLAT (A q)) ==> q = l) ==>
  current_owner_count H v = 0
Proof
  simp[current_wf_event_history_provenance_def,
    current_wf_history_provenance_def] >> strip_tac >>
  `EVERY (\e. FST (SND e) <> v) H` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  fs[current_owner_count_def, FILTER_EQ_NIL]
QED

Theorem current_wf_precleanup_event_history:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb ==>
  EVERY (current_wf_event_history_provenance A) events
Proof
  strip_tac >> drule current_wf_precleanup_structural >>
  simp[current_structural_certificate_def] >> strip_tac >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  gvs[] >> drule (cj 1 current_wf_tree_event_history_provenance) >>
  simp[current_wf_history_provenance_def]
QED

Theorem current_wf_annotation_map_lookup:
  !bbs annsss l t v. LENGTH bbs = LENGTH annsss /\
  MEM (t,v) (FLAT (current_annotation_map bbs annsss l)) ==>
  ?bb. lookup_block l bbs = SOME bb
Proof
  Induct >> Cases_on `annsss` >>
  simp[current_annotation_map_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h'.bb_label = l` >> gvs[] >>
  qpat_x_assum `!annsss l t v. _`
    (mp_tac o SRULE [lookup_block_def, current_annotation_map_def]) >>
  metis_tac[]
QED

Theorem current_wf_block_annotation_owner:
  MEM (t,v) (FLAT (current_block_annotations old pre)) ==>
  ?inst. MEM inst (pre ++ old.bb_instructions) /\ MEM v inst.inst_outputs
Proof
  strip_tac >>
  mp_tac (Q.INST [`new` |-> `old with bb_instructions := pre ++ old.bb_instructions`]
    current_block_annotations_owners) >> simp[] >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  qpat_x_assum `MEM (t,v) (FLAT _)`
    (strip_assume_tac o REWRITE_RULE [MEM_FLAT, MEM_EL]) >>
  `n < LENGTH (pre ++ old.bb_instructions)` by simp[] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `EL n (pre ++ old.bb_instructions)` >> conj_tac
  >- metis_tac[EL_MEM, MEM_APPEND] >>
  qpat_x_assum `MAP SND _ = _` (SUBST1_TAC o SYM) >>
  simp[MEM_MAP] >> qexists_tac `EL n' l` >>
  conj_tac >- metis_tac[pairTheory.SND] >>
  metis_tac[EL_MEM]
QED

Theorem current_wf_precleanup_annotation_lookup:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  MEM (t,v) (FLAT (A l)) ==>
  ?old. lookup_block l fn.fn_blocks = SOME old
Proof
  simp[current_wf_precleanup_certificate_def] >> rpt strip_tac >>
  `MAP (\bb. bb.bb_label) ins = MAP (\bb. bb.bb_label) fn.fn_blocks` by
    metis_tac[add_phi_nodes_supply_labels] >>
  `LENGTH ins = LENGTH fn.fn_blocks` by metis_tac[LENGTH_MAP] >>
  `LENGTH ins = LENGTH annsss` by metis_tac[LIST_REL_LENGTH, LENGTH_ZIP] >>
  gvs[] >>
  `?bb. lookup_block l ins = SOME bb` by
    metis_tac[current_wf_annotation_map_lookup] >>
  drule venomExecProofsTheory.lookup_block_labels_agree >>
  disch_then (qspec_then `l` mp_tac) >> simp[] >>
  Cases_on `lookup_block l fn.fn_blocks` >> simp[]
QED

Theorem current_wf_precleanup_annotation_changing:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  MEM (t,v) (FLAT (A l)) ==>
  current_changing_site fn (current_actual_inserted fn) v l
Proof
  strip_tac >> drule_all current_wf_precleanup_annotation_lookup >> strip_tac >>
  drule_all current_wf_precleanup_insertion_lookup >> strip_tac >>
  `old.bb_label = l` by metis_tac[lookup_block_label] >>
  `?inst. MEM inst (pre ++ old.bb_instructions) /\ MEM v inst.inst_outputs` by
    metis_tac[current_wf_block_annotation_owner] >>
  fs[MEM_APPEND] >> simp[current_changing_site_def]
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> metis_tac[lookup_block_MEM]
QED

Theorem current_wf_original_phi_annotation_locality:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ MEM db fn.fn_blocks /\
  MEM di db.bb_instructions /\ di.inst_opcode = PHI /\ MEM v di.inst_outputs ==>
  !l t. MEM (t,v) (FLAT (A l)) ==> l = db.bb_label
Proof
  strip_tac >>
  `!l. current_changing_site fn (current_actual_inserted fn) v l ==> l = db.bb_label`
    by metis_tac[current_wf_original_phi_single_site] >>
  `current_wf_precleanup_certificate s fn renamed s' A H events` by
    fs[current_wf_phi_context_def] >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[current_wf_precleanup_annotation_changing]
QED

Theorem current_wf_inserted_annotation_tokens:
  EVERY (\(t,v). t = CurrentInserted v l)
    (FLAT (current_inserted_annotations l pre))
Proof
  simp[current_inserted_annotations_def, EVERY_FLAT, EVERY_MAP, combinTheory.o_DEF]
QED

Theorem current_wf_inserted_annotation_first:
  ALL_DISTINCT (MAP FST (FLAT (current_block_annotations old pre))) /\
  MEM inst pre /\ MEM v inst.inst_outputs ==>
  ?before after.
    FLAT (current_block_annotations old pre) =
      before ++ (CurrentInserted v old.bb_label,v)::after /\
    EVERY (\a. SND a <> v) before
Proof
  strip_tac >>
  `MEM (CurrentInserted v old.bb_label,v)
    (FLAT (current_inserted_annotations old.bb_label pre))` by
    (simp[current_inserted_annotations_def, MEM_FLAT, MEM_MAP] >>
     qexists_tac `MAP (\w. (CurrentInserted w old.bb_label,w)) inst.inst_outputs` >>
     conj_tac >- (qexists_tac `inst` >> simp[]) >>
     simp[MEM_MAP]) >>
  `?before after. FLAT (current_inserted_annotations old.bb_label pre) =
    before ++ (CurrentInserted v old.bb_label,v)::after` by metis_tac[MEM_SPLIT] >>
  qexistsl_tac [`before`, `after ++ FLAT (current_original_annotations old.bb_label 0 old.bb_instructions)`] >>
  conj_tac >- simp[current_block_annotations_def, FLAT_APPEND, APPEND_ASSOC] >>
  mp_tac (Q.INST [`l` |-> `old.bb_label`] current_wf_inserted_annotation_tokens) >>
  fs[current_block_annotations_def, FLAT_APPEND, MAP_APPEND, ALL_DISTINCT_APPEND] >>
  simp[EVERY_MEM] >> rpt strip_tac >> PairCases_on `a` >> gvs[] >>
  qpat_x_assum `!e. MEM e before ==> _` drule >> simp[] >> strip_tac >>
  gvs[MEM_MAP] >> metis_tac[pairTheory.FST]
QED

Theorem current_wf_outputs_trace_append:
  !anns s rs H E names s1 rs1 H1 E1 rest more s' rs' H' E'.
  current_outputs_trace anns s rs H E names s1 rs1 H1 E1 /\
  current_outputs_trace rest s1 rs1 H1 E1 more s' rs' H' E' ==>
  current_outputs_trace (anns ++ rest) s rs H E (names ++ more) s' rs' H' E'
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem current_wf_local_outputs_trace:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  ?names. current_outputs_trace (FLAT annss) s rs H E names s' rs' H' E'
Proof
  Induct >> simp[current_local_trace_def, current_outputs_trace_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  fs[current_inst_trace_def] >> metis_tac[current_wf_outputs_trace_append]
QED

Theorem current_wf_outputs_first_owner:
  !pre t v post s rs H E names s' rs' H' E' V tail.
  current_outputs_trace (pre ++ (t,v)::post) s rs H E
    names s' rs' H' E' /\
  current_annotations_ok V H (pre ++ (t,v)::post) /\
  current_allocation_consistent V H s rs /\
  EVERY (\a. SND a <> v) pre /\ current_owner_count H v = 0 ==>
  current_token_name (H' ++ tail) t = SOME v
Proof
  Induct
  >- (simp[current_outputs_trace_def] >> rpt strip_tac >>
      `(!w. t <> CurrentDefault w) /\ ~MEM t (MAP FST H)` by
        fs[current_annotations_ok_def] >>
      drule_all current_first_allocation_alias >> strip_tac >>
      drule current_outputs_trace_history >> strip_tac >> gvs[] >>
      metis_tac[current_token_name_append_stable, current_token_name_default]) >>
  gen_tac >> PairCases_on `h` >>
  simp[current_outputs_trace_def] >> rpt gen_tac >> strip_tac >>
  `(!w. h0 <> CurrentDefault w) /\ ~MEM h0 (MAP FST H) /\ MEM h1 V` by
    fs[current_annotations_ok_def] >>
  `current_allocation_consistent V (H ++ [(h0,h1,n)]) s1 rs1` by
    (irule current_push_consistent >> metis_tac[]) >>
  `current_annotations_ok V (H ++ [(h0,h1,n)]) (pre ++ (t,v)::post)` by
    metis_tac[current_annotations_tail] >>
  first_x_assum irule >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem current_wf_local_first_owner:
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  FLAT annss = pre ++ (t,v)::post /\
  current_annotations_ok V H (FLAT annss) /\
  current_allocation_consistent V H s rs /\
  EVERY (\a. SND a <> v) pre /\ current_owner_count H v = 0 ==>
  current_token_name (H' ++ tail) t = SOME v
Proof
  strip_tac >> drule current_wf_local_outputs_trace >> strip_tac >>
  qpat_x_assum `FLAT annss = _` SUBST_ALL_TAC >>
  drule_all current_wf_outputs_first_owner >> simp[]
QED

Theorem current_wf_event_first_owner:
  current_event_valid A V ev /\ current_event_trace A H ev /\
  current_wf_event_history_provenance A ev /\
  (!l u. MEM (u,v) (FLAT (A l)) ==> l = current_event_label ev) /\
  FLAT (A (current_event_label ev)) = pre ++ (t,v)::post /\
  EVERY (\a. SND a <> v) pre ==>
  current_token_name H t = SOME v
Proof
  PairCases_on `ev` >>
  pure_rewrite_tac[current_event_valid_def, current_event_trace_def, current_event_label_def] >>
  strip_tac >>
  `current_owner_count ev5 v = 0` by
    (drule current_wf_event_single_owner_absent >>
     disch_then (qspec_then `v` mp_tac) >> metis_tac[]) >>
  drule current_wf_local_outputs_trace >> strip_tac >>
  qpat_x_assum `FLAT (A ev0) = _` SUBST_ALL_TAC >>
  drule_all current_wf_outputs_first_owner >> gvs[]
QED

Theorem current_wf_exceptional_inserted_spelling:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ MEM db fn.fn_blocks /\
  MEM di db.bb_instructions /\ di.inst_opcode = PHI /\ MEM v di.inst_outputs /\
  current_actual_inserted fn v db.bb_label ==>
  current_token_name H (CurrentInserted v db.bb_label) = SOME v
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\
   ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  `lookup_block db.bb_label fn.fn_blocks = SOME db` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  drule_all current_wf_precleanup_insertion_lookup >> strip_tac >>
  `?bb. MEM bb renamed /\ bb.bb_label = db.bb_label` by
    (`MEM db.bb_label (MAP (\bb. bb.bb_label) renamed)` by
       (drule current_wf_precleanup_labels >> disch_then SUBST1_TAC >>
        simp[MEM_MAP] >> metis_tac[]) >>
     fs[MEM_MAP] >> metis_tac[]) >>
  `?ev. MEM ev events /\ current_event_label ev = db.bb_label` by
    metis_tac[current_wf_precleanup_coverage] >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  drule_all current_wf_precleanup_event_history >> strip_tac >>
  `current_event_valid A (FLAT (MAP block_ir_vars ins')) ev /\
   current_event_trace A H ev /\ current_wf_event_history_provenance A ev` by
    fs[EVERY_MEM] >>
  `ALL_DISTINCT (MAP FST (FLAT (A db.bb_label)))` by
    (PairCases_on `ev` >> fs[current_event_valid_def, current_event_label_def,
      current_annotations_ok_def] >> metis_tac[]) >>
  `?inst. MEM inst pre /\ MEM v inst.inst_outputs` by metis_tac[] >>
  `ALL_DISTINCT (MAP FST (FLAT (current_block_annotations db pre)))` by
    metis_tac[] >>
  drule_all current_wf_inserted_annotation_first >> strip_tac >>
  irule current_wf_event_first_owner >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  metis_tac[current_wf_original_phi_annotation_locality]
QED

Theorem current_wf_exceptional_inserted_tokens:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block h fn.fn_blocks = SOME old /\ k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_outputs = [v] /\
  current_actual_inserted fn v h ==>
  current_token_name H (CurrentInserted v h) = SOME v /\
  (!ev. MEM ev events ==>
    current_event_exit_env ev v = CurrentDefault v \/
    current_event_exit_env ev v = CurrentOriginal h k 0) /\
  (?ev. MEM ev events /\ fn_cfg_edge fn (current_event_label ev) h /\
    current_event_exit_env ev v = CurrentOriginal h k 0)
Proof
  strip_tac >>
  `MEM old fn.fn_blocks /\ old.bb_label = h` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `MEM (EL k old.bb_instructions) old.bb_instructions` by simp[EL_MEM] >>
  conj_tac >- metis_tac[current_wf_exceptional_inserted_spelling, MEM] >>
  conj_tac
  >- (rpt strip_tac >> drule_all current_wf_original_phi_exit_token >>
      IF_CASES_TAC >> simp[]) >>
  `?p. fn_cfg_edge fn p h /\
    dominates (dom_analyze (cfg_analyze fn) fn) h p` by
    metis_tac[current_wf_original_phi_inserted_return, MEM] >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn` by fs[current_wf_phi_context_def] >>
  `MEM p (MAP (\bb. bb.bb_label) renamed)` by
    (drule current_wf_precleanup_labels >> disch_then SUBST1_TAC >>
     fs[fn_cfg_edge_def, MEM_MAP] >> metis_tac[]) >>
  `?bb. MEM bb renamed /\ bb.bb_label = p` by
    (fs[MEM_MAP] >> metis_tac[]) >>
  `?ev. MEM ev events /\ current_event_label ev = p` by
    metis_tac[current_wf_precleanup_coverage] >>
  qexists_tac `ev` >> simp[] >>
  drule_all current_wf_original_phi_exit_token >>
  simp[strict_dominates_def] >> metis_tac[]
QED

Definition current_wf_inserted_phi_at_def:
  current_wf_inserted_phi_at A renamed h q v <=>
    ?new. lookup_block h renamed = SOME new /\
      q < LENGTH new.bb_instructions /\ q < LENGTH (A h) /\
      EL q (A h) = [(CurrentInserted v h,v)] /\
      (EL q new.bb_instructions).inst_opcode = PHI
End

Theorem current_wf_inserted_annotation_index:
  q < LENGTH (current_block_annotations old pre) /\
  EL q (current_block_annotations old pre) = [(CurrentInserted v h,v)] ==>
  q < LENGTH pre /\ (EL q pre).inst_outputs = [v] /\ old.bb_label = h
Proof
  strip_tac >>
  `q < LENGTH pre` by
    (spose_not_then assume_tac >>
     `MEM (CurrentInserted v h) (MAP FST
       (FLAT (current_original_annotations old.bb_label 0 old.bb_instructions)))` by
       (simp[MEM_MAP] >> qexists_tac `(CurrentInserted v h,v)` >> simp[] >>
        simp[MEM_FLAT] >> qexists_tac `[(CurrentInserted v h,v)]` >> simp[] >>
        `q - LENGTH pre < LENGTH (current_original_annotations old.bb_label 0 old.bb_instructions) /\
         EL (q - LENGTH pre) (current_original_annotations old.bb_label 0 old.bb_instructions) =
           [(CurrentInserted v h,v)]` by
          fs[current_block_annotations_def, current_inserted_annotations_def, EL_APPEND_EQN] >>
        metis_tac[EL_MEM]) >>
     drule current_original_annotations_key >> simp[]) >>
  fs[current_block_annotations_def, current_inserted_annotations_def,
    EL_APPEND_EQN, EL_MAP] >>
  qpat_x_assum `MAP _ _ = _` (mp_tac o Q.AP_TERM `MAP SND`) >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem current_wf_inserted_phi_prefix:
  current_wf_phi_context s fn renamed s' A H events /\
  current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old ==>
  ?defs ins si pre.
    defs = compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))) /\
    add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
      (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
        (liveness_analyze fn) fn) fn.fn_blocks defs = (ins,si) /\
    lookup_block h ins = SOME (old with bb_instructions := pre ++ old.bb_instructions) /\
    A h = current_block_annotations old pre /\ q < LENGTH pre /\
    (EL q pre).inst_outputs = [v] /\ current_actual_inserted fn v h /\
    ?id. EL q pre = build_phi_inst_supply id v
      (case ALOOKUP (current_pred_map fn) h of SOME ps => ps | NONE => [])
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events` by
    fs[current_wf_phi_context_def] >>
  drule_all current_wf_precleanup_insertion_lookup >> strip_tac >>
  `q < LENGTH (current_block_annotations old pre) /\
   EL q (current_block_annotations old pre) = [(CurrentInserted v h,v)]` by
    fs[current_wf_inserted_phi_at_def] >>
  drule_all current_wf_inserted_annotation_index >> strip_tac >>
  `?id w. EL q pre = build_phi_inst_supply id w
    (case ALOOKUP (current_pred_map fn) old.bb_label of SOME ps => ps | NONE => [])` by
    (qpat_x_assum `EVERY _ pre` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `EL q pre` mp_tac) >> simp[EL_MEM]) >>
  `w = v` by fs[build_phi_inst_supply_def] >>
  qexistsl_tac [`defs`, `ins`, `si`, `pre`] >> simp[] >> metis_tac[EL_MEM, MEM]
QED

Theorem current_wf_inserted_phi_output:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h renamed = SOME new ==>
  ?out. current_token_name H (CurrentInserted v h) = SOME out /\
    (EL q new.bb_instructions).inst_outputs = [out]
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\
   ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by fs[current_wf_phi_context_def] >>
  `MEM new renamed /\ new.bb_label = h` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  drule_all current_wf_precleanup_coverage >> strip_tac >>
  `q < LENGTH new.bb_instructions /\ q < LENGTH (A h) /\
   EL q (A h) = [(CurrentInserted v h,v)]` by
    fs[current_wf_inserted_phi_at_def] >>
  `current_wf_output_at A H ev q (CurrentInserted v h)` by
    (mp_tac current_wf_precleanup_output_sites >>
     impl_tac >- metis_tac[] >>
     disch_then (qspecl_then [`ev`, `q`, `0`] mp_tac) >> simp[]) >>
  `?out. current_token_name H (CurrentInserted v h) = SOME out` by
    fs[current_wf_output_at_def] >>
  drule_all current_wf_precleanup_output >> strip_tac >>
  `bb = new` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `bb = new` SUBST_ALL_TAC >>
  qpat_x_assum `new.bb_label = current_event_label ev` kall_tac >>
  `LENGTH (EL q new.bb_instructions).inst_outputs = 1` by
    (drule_all current_wf_precleanup_output_alignment >>
     disch_then (mp_tac o Q.AP_TERM `\xs. EL q xs`) >> simp[EL_MAP]) >>
  qexists_tac `out` >> simp[] >>
  Cases_on `(EL q new.bb_instructions).inst_outputs` >> gvs[LENGTH_EQ_NUM]
QED

Theorem current_wf_inserted_phi_slots:
  current_wf_phi_context s fn renamed s' A H events /\
  current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new ==>
  ?pairs. (EL q new.bb_instructions).inst_operands = current_phi_slots pairs /\
    MAP FST pairs =
      (case ALOOKUP (current_pred_map fn) h of SOME ps => ps | NONE => [])
Proof
  strip_tac >> drule_all current_wf_inserted_phi_prefix >> strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\ wf_function fn` by
    fs[current_wf_phi_context_def] >>
  `q < LENGTH (old with bb_instructions := pre ++ old.bb_instructions).bb_instructions /\
   (EL q (old with bb_instructions := pre ++ old.bb_instructions).bb_instructions).inst_opcode = PHI /\
   (EL q (old with bb_instructions := pre ++ old.bb_instructions).bb_instructions).inst_operands =
     current_phi_slots (MAP (\p. (p,v))
       (case ALOOKUP (current_pred_map fn) h of SOME ps => ps | NONE => []))` by
    simp[EL_APPEND_EQN, build_phi_inst_supply_def, current_phi_slots_def, MAP_MAP_o,
      combinTheory.o_DEF] >>
  drule_all current_wf_precleanup_slot_shape >> strip_tac >>
  `new' = new` by metis_tac[optionTheory.SOME_11] >>
  qexists_tac `pairs` >> fs[MAP_MAP_o, combinTheory.o_DEF, MAP_ID]
QED

Theorem current_wf_inserted_phi_slot:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  ps = (case ALOOKUP (current_pred_map fn) h of SOME ps => ps | NONE => []) /\
  i < LENGTH ps /\ EL i ps = p ==>
  ?ev n. MEM ev events /\ current_event_label ev = p /\
    fn_cfg_edge fn p h /\ current_token_name H (current_event_exit_env ev v) = SOME n /\
    EL (2 * i) (EL q new.bb_instructions).inst_operands = Label p /\
    EL (2 * i + 1) (EL q new.bb_instructions).inst_operands = Var n
Proof
  strip_tac >> drule_all current_wf_inserted_phi_prefix >> strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  `MEM h (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `ps = cfg_preds_of (cfg_analyze fn) h` by
    (drule ALOOKUP_current_pred_map >> disch_tac >>
     qpat_x_assum `ps = _` mp_tac >> simp[]) >>
  `fn_cfg_edge fn p h` by
    (simp[current_cfg_edge_preds] >> metis_tac[EL_MEM]) >>
  `q < LENGTH (old with bb_instructions := pre ++ old.bb_instructions).bb_instructions /\
   (EL q (old with bb_instructions := pre ++ old.bb_instructions).bb_instructions).inst_opcode = PHI /\
   (EL q (old with bb_instructions := pre ++ old.bb_instructions).bb_instructions).inst_operands =
     current_phi_slots (MAP (\p. (p,v)) ps)` by
    simp[EL_APPEND_EQN, build_phi_inst_supply_def, current_phi_slots_def, MAP_MAP_o,
      combinTheory.o_DEF, ALOOKUP_current_pred_map] >>
  `i < LENGTH (MAP (\p. (p,v)) ps) /\ EL i (MAP (\p. (p,v)) ps) = (p,v)` by
    (ntac 2 (qpat_x_assum `ps = _` kall_tac) >> simp[EL_MAP]) >>
  drule_all current_wf_precleanup_named_slot >> strip_tac >>
  qexistsl_tac [`ev`, `n`] >> metis_tac[optionTheory.SOME_11]
QED

Theorem current_wf_inserted_pred_demand:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ current_actual_inserted fn v h /\
  lookup_block h fn.fn_blocks = SOME old /\
  (!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==> ~MEM v di.inst_outputs) /\
  fn_cfg_edge fn p h /\ lookup_block p fn.fn_blocks = SOME pred ==>
  current_demand fn v p (LENGTH pred.bb_instructions)
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
   fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn` by
    fs[current_wf_phi_context_def] >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
     (liveness_analyze fn) fn) h = SOME vs /\ MEM v vs` by
    (fs[current_actual_inserted_def] >> drule current_pruned_reach_live >>
     simp[current_placement_live_def]) >>
  `MEM v (live_vars_at (liveness_analyze fn) h
     (LENGTH (collect_phis old.bb_instructions)))` by
    metis_tac[current_selected_live_iff] >>
  `!phi. MEM phi (collect_phis old.bb_instructions) ==>
     ~MEM v (MAP SND (phi_pairs phi.inst_operands))` by
    (rpt strip_tac >>
     `MEM old fn.fn_blocks /\ old.bb_label = h` by
       metis_tac[lookup_block_MEM, lookup_block_label] >>
     `blocks_have_leading_phi fn.fn_blocks` by
       metis_tac[current_phi_operand_has_leading_phi] >>
     `LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1` by
       metis_tac[current_phi_operand_single_bound] >>
     `fn_reachable fn h` by metis_tac[all_reachable_def] >>
     `ALOOKUP (select_current_live_in T (liveness_analyze fn) fn) h = SOME vs` by
       (qpat_x_assum `ALOOKUP _ h = SOME vs` mp_tac >> simp[]) >>
     drule_all current_selected_live_single_definition >> strip_tac >>
     `h = db.bb_label` by metis_tac[current_actual_inserted_single_local] >>
     `lookup_block h fn.fn_blocks = SOME db` by
       (qpat_x_assum `h = db.bb_label` SUBST_ALL_TAC >>
        irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
     `db = old` by metis_tac[optionTheory.SOME_11] >>
     `?j. j < LENGTH (collect_phis old.bb_instructions) /\
          MEM v (EL j old.bb_instructions).inst_outputs` by metis_tac[] >>
     `j < LENGTH old.bb_instructions` by
       metis_tac[current_collect_phis_length, arithmeticTheory.LESS_LESS_EQ_TRANS] >>
     `(EL j old.bb_instructions).inst_opcode = PHI` by
       metis_tac[current_wf_nonphi_after_collect, arithmeticTheory.NOT_LESS] >>
     metis_tac[EL_MEM]) >>
  `!k. k < LENGTH (collect_phis old.bb_instructions) ==>
     ~MEM v (inst_defs (EL k old.bb_instructions))` by
    (rpt strip_tac >>
     `k < LENGTH old.bb_instructions` by
       metis_tac[current_collect_phis_length, arithmeticTheory.LESS_LESS_EQ_TRANS] >>
     `(EL k old.bb_instructions).inst_opcode = PHI` by
       metis_tac[current_wf_nonphi_after_collect, arithmeticTheory.NOT_LESS] >>
     fs[inst_defs_def] >> metis_tac[EL_MEM]) >>
  `MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pred.bb_instructions))` by
    (irule current_live_cut_to_pred_exit >> goal_assum (drule_at Any) >>
     simp[] >> qexistsl_tac [`h`, `old`] >> simp[]) >>
  irule current_live_post_phi_demand >>
  goal_assum (drule_at Any) >> simp[current_collect_phis_length]
QED

Theorem current_wf_inserted_phi_pair:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  (EL q new.bb_instructions).inst_operands = current_phi_slots pairs /\
  MAP FST pairs = (case ALOOKUP (current_pred_map fn) h of SOME ps => ps | NONE => []) /\
  i < LENGTH pairs /\ EL i pairs = (p,n) ==>
  ?ev. MEM ev events /\ current_event_label ev = p /\ fn_cfg_edge fn p h /\
    current_token_name H (current_event_exit_env ev v) = SOME n
Proof
  strip_tac >>
  `i < LENGTH (MAP FST pairs) /\ EL i (MAP FST pairs) = p` by simp[EL_MAP] >>
  drule_all current_wf_inserted_phi_slot >> strip_tac >>
  `EL (2 * i + 1) (current_phi_slots pairs) = Var n` by
    metis_tac[current_phi_slots_index, pairTheory.SND] >>
  `n' = n` by
    (qpat_x_assum `EL (2 * i + 1) (EL q new.bb_instructions).inst_operands = _` mp_tac >>
     simp[]) >>
  qexists_tac `ev` >> simp[]
QED

Theorem current_wf_inserted_phi_pair_available:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  (!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==> ~MEM v di.inst_outputs) /\
  (EL q new.bb_instructions).inst_operands = current_phi_slots pairs /\
  MAP FST pairs = (case ALOOKUP (current_pred_map fn) h of SOME ps => ps | NONE => []) /\
  i < LENGTH pairs /\ EL i pairs = (p,n) ==>
  ?pb. MEM pb renamed /\ pb.bb_label = p /\
    fn_cfg_edge (fn with fn_blocks := renamed) p h /\
    def_available_at (fn with fn_blocks := renamed) pb NONE n
Proof
  strip_tac >> drule_all current_wf_inserted_phi_pair >> strip_tac >>
  drule_all current_wf_inserted_phi_prefix >> strip_tac >>
  qpat_assum `current_wf_phi_context _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[current_wf_phi_context_def] >> strip_tac >>
  `?pred. lookup_block p fn.fn_blocks = SOME pred` by
    (fs[fn_cfg_edge_def] >>
     `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
       fs[wf_function_def, fn_labels_def] >>
     metis_tac[MEM_lookup_block]) >>
  `current_demand fn v p (LENGTH pred.bb_instructions)` by
    (irule current_wf_inserted_pred_demand >> metis_tac[]) >>
  `?pb. MEM pb renamed /\ pb.bb_label = p` by
    (drule current_wf_precleanup_labels >> strip_tac >>
     `MEM p (MAP (\b. b.bb_label) fn.fn_blocks)` by
       metis_tac[lookup_block_MEM, lookup_block_label, MEM_MAP] >>
     metis_tac[MEM_MAP]) >>
  qexists_tac `pb` >> simp[] >> conj_tac
  >- metis_tac[current_wf_precleanup_cfg] >>
  irule current_wf_precleanup_exit_available >> metis_tac[]
QED

Theorem current_wf_ordered_insert_distinct[local]:
  !x xs. ALL_DISTINCT xs ==> ALL_DISTINCT (ordered_set_insert x xs)
Proof
  simp[ordered_set_insert_def] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[ALL_DISTINCT_APPEND]
QED

Theorem current_wf_map_update_distinct[local]:
  (!k. ALL_DISTINCT (fmap_lookup_list m k)) /\ ALL_DISTINCT xs ==>
  !k. ALL_DISTINCT (fmap_lookup_list (m |+ (l,xs)) k)
Proof
  simp[fmap_lookup_list_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem current_wf_init_fold_distinct[local]:
  !bbs m. (!k. ALL_DISTINCT (fmap_lookup_list m k)) ==>
  !k. ALL_DISTINCT (fmap_lookup_list
    (FOLDL (\m bb. m |+ (bb.bb_label, [])) m bbs) k)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  irule current_wf_map_update_distinct >> simp[]
QED

Theorem current_wf_pred_inner_distinct[local]:
  !ls m l. (!k. ALL_DISTINCT (fmap_lookup_list m k)) ==>
  !k. ALL_DISTINCT (fmap_lookup_list
    (FOLDR (\succ m2. m2 |+ (succ, ordered_set_insert l (fmap_lookup_list m2 succ))) m ls) k)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  irule current_wf_map_update_distinct >>
  simp[current_wf_ordered_insert_distinct]
QED

Theorem current_wf_pred_outer_distinct[local]:
  !bbs m succs. (!k. ALL_DISTINCT (fmap_lookup_list m k)) ==>
  !k. ALL_DISTINCT (fmap_lookup_list
    (FOLDL (\m bb. FOLDR (\succ m2.
       m2 |+ (succ, ordered_set_insert bb.bb_label (fmap_lookup_list m2 succ)))
       m (fmap_lookup_list succs bb.bb_label)) m bbs) k)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  irule current_wf_pred_inner_distinct >> simp[]
QED

Theorem current_wf_build_preds_distinct:
  !bbs succs h. ALL_DISTINCT (fmap_lookup_list (build_preds bbs succs) h)
Proof
  rpt gen_tac >> simp[build_preds_def] >>
  irule current_wf_pred_outer_distinct >>
  simp[init_preds_def] >> irule current_wf_init_fold_distinct >>
  simp[fmap_lookup_list_def]
QED

Theorem cfg_analyze_preds_distinct:
  !fn h. ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) h)
Proof
  simp[cfg_analyze_preds, current_wf_build_preds_distinct]
QED

Theorem current_wf_inserted_phi_edge_wf:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  (!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==> ~MEM v di.inst_outputs) ==>
  phi_edge_uses_wf (fn with fn_blocks := renamed) new (EL q new.bb_instructions)
Proof
  strip_tac >> drule_all current_wf_inserted_phi_slots >> strip_tac >>
  `new.bb_label = h` by metis_tac[lookup_block_label] >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn` by
    fs[current_wf_phi_context_def] >>
  `MEM h (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `MAP FST pairs = cfg_preds_of (cfg_analyze fn) h` by
    (drule ALOOKUP_current_pred_map >> disch_tac >>
     qpat_x_assum `MAP FST pairs = _` mp_tac >> simp[]) >>
  `ALL_DISTINCT (MAP FST pairs)` by
    simp[cfg_analyze_preds_distinct] >>
  simp[phi_edge_uses_wf_def, current_wf_slots_shape, cfg_analyze_preds_distinct] >> conj_tac
  >- (drule current_wf_precleanup_cfg >> strip_tac >>
      `!p. fn_cfg_edge (fn with fn_blocks := renamed) p h <=>
        MEM p (MAP FST pairs)` by metis_tac[current_cfg_edge_preds] >>
      metis_tac[MEM_MAP]) >>
  rpt strip_tac >>
  `?i. i < LENGTH pairs /\ EL i pairs = (pred,v')` by metis_tac[MEM_EL] >>
  drule_all current_wf_inserted_phi_pair_available >> strip_tac >>
  metis_tac[]
QED

Theorem current_wf_phi_context_event_labels_distinct:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb ==>
  ALL_DISTINCT (MAP current_event_label events)
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn` by fs[current_wf_phi_context_def] >>
  gvs[current_wf_precleanup_certificate_def] >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  metis_tac[cj 1 current_trace_event_labels_distinct]
QED

Theorem current_wf_exceptional_inserted_pair_values:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  k < LENGTH old.bb_instructions /\ (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_outputs = [v] /\
  current_token_name H (CurrentOriginal h k 0) = SOME n /\
  (EL q new.bb_instructions).inst_operands = current_phi_slots pairs /\
  MAP FST pairs = (case ALOOKUP (current_pred_map fn) h of SOME ps => ps | NONE => []) ==>
  (EL q new.bb_instructions).inst_outputs = [v] /\ n <> v /\
  (!p w. MEM (p,w) pairs ==> w = v \/ w = n)
Proof
  strip_tac >> drule_all current_wf_inserted_phi_prefix >> strip_tac >>
  drule_all current_wf_exceptional_inserted_tokens >> strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  `(EL q new.bb_instructions).inst_outputs = [v]` by
    (drule_all current_wf_inserted_phi_output >> strip_tac >>
     metis_tac[optionTheory.SOME_11]) >>
  `n <> v` by
    (drule_all current_wf_precleanup_names >> strip_tac >>
     strip_tac >>
     `CurrentInserted v h = CurrentOriginal h k 0` by
       (irule current_allocated_name_injective >> simp[] >> metis_tac[]) >>
     fs[]) >>
  simp[] >> rpt strip_tac >>
  `?i. i < LENGTH pairs /\ EL i pairs = (p,w)` by metis_tac[MEM_EL] >>
  drule_all current_wf_inserted_phi_pair >> strip_tac >>
  `current_event_exit_env ev' v = CurrentDefault v \/
   current_event_exit_env ev' v = CurrentOriginal h k 0` by metis_tac[] >>
  fs[current_token_name_def] >> metis_tac[optionTheory.SOME_11]
QED

Theorem current_wf_exceptional_inserted_pair_exists:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  k < LENGTH old.bb_instructions /\ (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_outputs = [v] /\
  current_token_name H (CurrentOriginal h k 0) = SOME n /\
  (EL q new.bb_instructions).inst_operands = current_phi_slots pairs /\
  MAP FST pairs = (case ALOOKUP (current_pred_map fn) h of SOME ps => ps | NONE => []) ==>
  ?p. MEM (p,n) pairs
Proof
  strip_tac >> drule_all current_wf_inserted_phi_prefix >> strip_tac >>
  drule_all current_wf_exceptional_inserted_tokens >> strip_tac >>
  `MEM h (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `MAP FST pairs = cfg_preds_of (cfg_analyze fn) h` by
    (drule ALOOKUP_current_pred_map >> disch_tac >>
     qpat_x_assum `MAP FST pairs = _` mp_tac >> simp[]) >>
  `wf_function fn` by fs[current_wf_phi_context_def] >>
  `MEM (current_event_label ev) (MAP FST pairs)` by
    metis_tac[current_cfg_edge_preds] >>
  `?w. MEM (current_event_label ev,w) pairs` by
    (fs[MEM_MAP] >> metis_tac[pairTheory.PAIR]) >>
  `?i. i < LENGTH pairs /\ EL i pairs = (current_event_label ev,w)` by
    metis_tac[MEM_EL] >>
  drule_all current_wf_inserted_phi_pair >> strip_tac >>
  `ALL_DISTINCT (MAP current_event_label events)` by
    metis_tac[current_wf_phi_context_event_labels_distinct] >>
  `ev' = ev` by
    (gvs[MEM_EL] >> metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP, EL_MAP]) >>
  gvs[] >> metis_tac[optionTheory.SOME_11]
QED

Theorem current_wf_exceptional_original_source:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_outputs = [v] ==>
  ?r slots n. current_wf_original_phi_at fn A renamed h k r slots /\
    current_token_name H (CurrentOriginal h k 0) = SOME n /\
    MEM n (EL r new.bb_instructions).inst_outputs /\
    simplify_current_phi (EL r new.bb_instructions) = EL r new.bb_instructions
Proof
  strip_tac >>
  `fn_phis_non_degenerate fn` by fs[current_wf_phi_context_def] >>
  `MEM (EL k old.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
     metis_tac[lookup_block_MEM, EL_MEM]) >>
  `?p w. MEM (p,w) (phi_pairs (EL k old.bb_instructions).inst_operands)` by
    (fs[fn_phis_non_degenerate_def] >> metis_tac[]) >>
  `?i. i < LENGTH (phi_pairs (EL k old.bb_instructions).inst_operands) /\
    EL i (phi_pairs (EL k old.bb_instructions).inst_operands) = (p,w)` by
    metis_tac[MEM_EL] >>
  mp_tac (Q.INST [`slots` |-> `phi_pairs (EL k old.bb_instructions).inst_operands`,
    `v` |-> `w`] (SPEC_ALL current_wf_original_phi_slot)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `0 < LENGTH (EL k old.bb_instructions).inst_outputs` by simp[] >>
  drule_all current_wf_original_phi_output >> strip_tac >>
  qexistsl_tac [`q`, `phi_pairs (EL k old.bb_instructions).inst_operands`, `n'`] >>
  simp[] >> metis_tac[current_wf_original_phi_retained, optionTheory.SOME_11]
QED

Theorem current_wf_exceptional_inserted_copy:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  k < LENGTH old.bb_instructions /\ (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_outputs = [v] ==>
  ?r slots n. current_wf_original_phi_at fn A renamed h k r slots /\
    MEM n (EL r new.bb_instructions).inst_outputs /\ n <> v /\
    simplify_current_phi (EL r new.bb_instructions) = EL r new.bb_instructions /\
    (EL q new.bb_instructions).inst_outputs = [v] /\
    simplify_current_phi (EL q new.bb_instructions) =
      (EL q new.bb_instructions) with <|inst_opcode := ASSIGN; inst_operands := [Var n]|>
Proof
  strip_tac >> drule_all current_wf_exceptional_original_source >> strip_tac >>
  drule_all current_wf_inserted_phi_slots >> strip_tac >>
  drule_all current_wf_exceptional_inserted_pair_values >> strip_tac >>
  drule_all current_wf_exceptional_inserted_pair_exists >> strip_tac >>
  `(EL q new.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_inserted_phi_at_def] >> metis_tac[optionTheory.SOME_11]) >>
  qexistsl_tac [`r`, `slots`, `n`] >> simp[] >>
  qabbrev_tac `vals = MAP SND (FILTER (\slot. SND slot <> v) pairs)` >>
  `MEM n vals` by
    (simp[Abbr `vals`, MEM_MAP, MEM_FILTER] >> metis_tac[pairTheory.SND]) >>
  `EVERY (\w. w = n) vals` by
    (simp[Abbr `vals`, EVERY_MEM, MEM_MAP, MEM_FILTER] >>
     rpt strip_tac >> PairCases_on `y` >> gvs[] >> metis_tac[]) >>
  Cases_on `vals` >- fs[] >>
  fs[] >> irule current_phi_slots_constant >> metis_tac[]
QED

Theorem current_wf_inserted_phi_producer:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new ==>
  phi_edge_uses_wf (fn with fn_blocks := renamed) new (EL q new.bb_instructions) \/
  ?k r slots n. current_wf_original_phi_at fn A renamed h k r slots /\
    MEM n (EL r new.bb_instructions).inst_outputs /\ n <> v /\
    simplify_current_phi (EL r new.bb_instructions) = EL r new.bb_instructions /\
    (EL q new.bb_instructions).inst_outputs = [v] /\
    simplify_current_phi (EL q new.bb_instructions) =
      (EL q new.bb_instructions) with <|inst_opcode := ASSIGN; inst_operands := [Var n]|>
Proof
  strip_tac >>
  Cases_on `!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==> ~MEM v di.inst_outputs`
  >- (disj1_tac >> metis_tac[current_wf_inserted_phi_edge_wf]) >>
  gvs[NOT_FORALL_THM] >> disj2_tac >>
  `?k. k < LENGTH old.bb_instructions /\ EL k old.bb_instructions = di` by
    metis_tac[MEM_EL] >>
  `fn_inst_wf fn` by fs[current_wf_phi_context_def] >>
  `inst_wf di` by metis_tac[fn_inst_wf_def, lookup_block_MEM] >>
  `di.inst_outputs = [v]` by
    (qpat_x_assum `inst_wf di` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> strip_tac >> gvs[]) >>
  `?r slots n. current_wf_original_phi_at fn A renamed h k r slots /\
    MEM n (EL r new.bb_instructions).inst_outputs /\ n <> v /\
    simplify_current_phi (EL r new.bb_instructions) = EL r new.bb_instructions /\
    (EL q new.bb_instructions).inst_outputs = [v] /\
    simplify_current_phi (EL q new.bb_instructions) =
      (EL q new.bb_instructions) with <|inst_opcode := ASSIGN; inst_operands := [Var n]|>` by
    (irule current_wf_exceptional_inserted_copy >> metis_tac[]) >>
  metis_tac[]
QED

Theorem current_wf_phi_context_block_opcodes:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new ==>
  ?pre. A h = current_block_annotations old pre /\
    EVERY (\i. i.inst_opcode = PHI) pre /\
    EVERY (\i. ?id w. i = build_phi_inst_supply id w
      (case ALOOKUP (current_pred_map fn) old.bb_label of SOME ps => ps | NONE => [])) pre /\
    MAP instruction_inst_opcode new.bb_instructions =
      MAP instruction_inst_opcode (pre ++ old.bb_instructions)
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  drule_all current_wf_precleanup_insertion_lookup >> strip_tac >>
  `EVERY (\i. i.inst_opcode = PHI) pre` by
    (fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
     strip_tac >> simp[build_phi_inst_supply_def]) >>
  `MEM new renamed /\ new.bb_label = h` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  drule_all current_wf_precleanup_block_shape >> strip_tac >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  `current_event_trace A H ev` by metis_tac[EVERY_MEM] >>
  `ALL_DISTINCT (MAP current_event_label events)` by
    metis_tac[current_wf_phi_context_event_labels_distinct] >>
  `current_edge_shape (old with bb_instructions := pre ++ old.bb_instructions)
    (current_event_input_block ev)` by
    (gvs[current_wf_precleanup_certificate_def] >>
     metis_tac[cj 1 current_trace_event_input_shape]) >>
  `MAP instruction_inst_opcode (current_event_renamed_block ev).bb_instructions =
    MAP instruction_inst_opcode (current_event_input_block ev).bb_instructions` by
    (PairCases_on `ev` >> fs[current_event_trace_def,
       current_event_renamed_block_def, current_event_input_block_def] >>
     metis_tac[current_local_trace_opcodes]) >>
  qexists_tac `pre` >> simp[] >>
  imp_res_tac current_edge_shape_opcodes >> fs[]
QED

Theorem current_wf_phi_occurrence_provenance:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ q < LENGTH new.bb_instructions /\
  (EL q new.bb_instructions).inst_opcode = PHI ==>
  (?v. current_wf_inserted_phi_at A renamed h q v) \/
  (?k slots. current_wf_original_phi_at fn A renamed h k q slots)
Proof
  strip_tac >> drule_all current_wf_phi_context_block_opcodes >> strip_tac >>
  `LENGTH new.bb_instructions = LENGTH pre + LENGTH old.bb_instructions` by
    metis_tac[LENGTH_MAP, LENGTH_APPEND] >>
  `old.bb_label = h` by metis_tac[lookup_block_label] >>
  Cases_on `q < LENGTH pre`
  >- (disj1_tac >>
      `?id w. EL q pre = build_phi_inst_supply id w
        (case ALOOKUP (current_pred_map fn) h of SOME ps => ps | NONE => [])` by
        (fs[EVERY_MEM] >> metis_tac[EL_MEM]) >>
      qexists_tac `w` >> simp[current_wf_inserted_phi_at_def] >>
      simp[current_block_annotations_def, current_inserted_annotations_def,
        EL_APPEND_EQN, EL_MAP, build_phi_inst_supply_def]) >>
  disj2_tac >>
  `q - LENGTH pre < LENGTH old.bb_instructions /\ q = LENGTH pre + (q - LENGTH pre)` by
    decide_tac >>
  `(EL (q - LENGTH pre) old.bb_instructions).inst_opcode = PHI` by
    (qpat_x_assum `MAP instruction_inst_opcode _ = _`
       (mp_tac o Q.AP_TERM `\xs. EL q xs`) >>
     simp[EL_MAP, EL_APPEND_EQN]) >>
  `fn_inst_wf fn` by fs[current_wf_phi_context_def] >>
  `inst_wf (EL (q - LENGTH pre) old.bb_instructions)` by
    metis_tac[fn_inst_wf_def, lookup_block_MEM, EL_MEM] >>
  `(EL (q - LENGTH pre) old.bb_instructions).inst_operands =
    current_phi_slots (phi_pairs (EL (q - LENGTH pre) old.bb_instructions).inst_operands)` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def] >>
     metis_tac[current_wf_phi_slots]) >>
  qexistsl_tac [`q - LENGTH pre`,
    `phi_pairs (EL (q - LENGTH pre) old.bb_instructions).inst_operands`] >>
  simp[current_wf_original_phi_at_def] >>
  qexists_tac `pre` >> simp[]
QED

Theorem current_wf_phi_occurrence_producer:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ q < LENGTH new.bb_instructions /\
  (EL q new.bb_instructions).inst_opcode = PHI ==>
  phi_edge_uses_wf (fn with fn_blocks := renamed) new (EL q new.bb_instructions) \/
  ?k r slots n v. current_wf_original_phi_at fn A renamed h k r slots /\
    MEM n (EL r new.bb_instructions).inst_outputs /\ n <> v /\
    simplify_current_phi (EL r new.bb_instructions) = EL r new.bb_instructions /\
    (EL q new.bb_instructions).inst_outputs = [v] /\
    simplify_current_phi (EL q new.bb_instructions) =
      (EL q new.bb_instructions) with <|inst_opcode := ASSIGN; inst_operands := [Var n]|>
Proof
  strip_tac >> drule_all current_wf_phi_occurrence_provenance >> strip_tac
  >- (drule_all current_wf_inserted_phi_producer >> metis_tac[]) >>
  disj1_tac >> metis_tac[current_wf_original_phi_edge_wf]
QED

Theorem current_wf_inserted_nonentry:
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  current_actual_inserted fn v h ==> fn_entry_label fn <> SOME h
Proof
  simp[current_actual_inserted_def] >> strip_tac >>
  qpat_x_assum `current_pruned_reach _ _ _ _ _` mp_tac >>
  once_rewrite_tac[current_pruned_reach_cases] >> strip_tac >>
  fs[current_frontier_edge_def] >>
  `MEM d (fn_labels fn)` by
    (imp_res_tac alistTheory.ALOOKUP_MEM >>
     gvs[current_frontier_map_def, current_query_map_def, MEM_MAP] >> metis_tac[]) >>
  drule_all current_frontier_target_support >> simp[]
QED

Theorem current_wf_phi_occurrence_nonentry:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ q < LENGTH new.bb_instructions /\
  (EL q new.bb_instructions).inst_opcode = PHI ==>
  fn_entry_label fn <> SOME h
Proof
  strip_tac >> drule_all current_wf_phi_occurrence_provenance >> strip_tac
  >- (drule_all current_wf_inserted_phi_prefix >> strip_tac >>
      irule current_wf_inserted_nonentry >>
      fs[current_wf_phi_context_def] >> metis_tac[]) >>
  `k < LENGTH old.bb_instructions /\
   (EL k old.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_original_phi_at_def] >> gvs[]) >>
  `first_block_no_phi fn` by fs[current_wf_phi_context_def] >>
  simp[fn_entry_label_def] >> strip_tac >>
  `old = eb` by
    (gvs[entry_block_def] >> Cases_on `fn.fn_blocks` >>
     gvs[lookup_block_def, FIND_thm]) >>
  gvs[first_block_no_phi_def, entry_block_def] >>
  Cases_on `fn.fn_blocks` >> gvs[EVERY_MEM] >> metis_tac[EL_MEM]
QED

Theorem current_wf_phi_occurrence_single_output:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ q < LENGTH new.bb_instructions /\
  (EL q new.bb_instructions).inst_opcode = PHI ==>
  ?out. (EL q new.bb_instructions).inst_outputs = [out]
Proof
  strip_tac >> drule_all current_wf_phi_occurrence_provenance >> strip_tac
  >- metis_tac[current_wf_inserted_phi_output] >>
  drule_all current_wf_original_phi_output_length >> strip_tac >>
  `k < LENGTH old.bb_instructions /\
   (EL k old.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_original_phi_at_def] >> gvs[]) >>
  `inst_wf (EL k old.bb_instructions)` by
    (fs[current_wf_phi_context_def] >>
     metis_tac[fn_inst_wf_def, lookup_block_MEM, EL_MEM]) >>
  `LENGTH (EL k old.bb_instructions).inst_outputs = 1` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  metis_tac[LENGTH_EQ_1]
QED

Theorem current_wf_edge_shape_outputs:
  current_edge_shape old new ==>
  MAP instruction_inst_outputs old.bb_instructions =
  MAP instruction_inst_outputs new.bb_instructions
Proof
  simp[current_edge_shape_def, LIST_REL_EL_EQN] >> strip_tac >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >> simp[EL_MAP]
QED

Theorem current_wf_precleanup_ssa_form:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s ==>
  ssa_form (fn with fn_blocks := renamed)
Proof
  strip_tac >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  `ALL_DISTINCT (MAP current_event_label events) /\
   current_annotation_separation A` by
    (qpat_x_assum `current_wf_precleanup_certificate _ _ _ _ _ _ _` mp_tac >>
     simp[current_wf_precleanup_certificate_def] >> strip_tac >>
     `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
       metis_tac[current_actual_tree_labels_distinct] >>
     conj_tac
     >- metis_tac[cj 1 current_trace_event_labels_distinct] >>
     gvs[] >>
     `LENGTH fn.fn_blocks = LENGTH ins` by
       (drule add_phi_nodes_supply_labels >> metis_tac[LENGTH_MAP]) >>
     irule current_annotation_map_separation >>
     reverse conj_tac
     >- (drule LIST_REL_LENGTH >>
         drule add_phi_nodes_supply_labels >>
         metis_tac[LENGTH_ZIP, LENGTH_MAP]) >>
     irule current_provenance_global_distinct >>
     qexistsl_tac [`fn`, `fn.fn_blocks`] >> conj_tac
     >- fs[wf_function_def, fn_labels_def] >>
     fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
     qexists_tac `EL n ins` >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[EL_ZIP]) >>
  `ALL_DISTINCT (FLAT (MAP (\ev. FLAT (MAP instruction_inst_outputs
    (current_event_renamed_block ev).bb_instructions)) events))` by
    (irule (SRULE [SF ETA_ss] current_wf_events_outputs_distinct) >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) renamed)` by
    (drule current_wf_precleanup_labels >> fs[wf_function_def, fn_labels_def]) >>
  `!b. MEM b renamed ==> ?ev. MEM ev events /\
    current_event_label ev = b.bb_label /\
    ALL_DISTINCT (FLAT (MAP instruction_inst_outputs b.bb_instructions)) /\
    (!v. MEM v (FLAT (MAP instruction_inst_outputs b.bb_instructions)) ==>
      MEM v (FLAT (MAP instruction_inst_outputs
        (current_event_renamed_block ev).bb_instructions)))` by
    (rpt strip_tac >> drule_all current_wf_precleanup_block_shape >> strip_tac >>
     drule current_wf_edge_shape_outputs >> strip_tac >>
     qexists_tac `ev` >> simp[] >>
     `?before after. events = before ++ ev::after` by metis_tac[MEM_SPLIT] >>
     gvs[MAP_APPEND, ALL_DISTINCT_APPEND]) >>
  simp[ssa_form_def, fn_insts_def, fn_insts_blocks_flat,
    MAP_FLAT, FLAT_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  qspecl_then [`events`, `current_event_label`,
    `\ev. FLAT (MAP instruction_inst_outputs
      (current_event_renamed_block ev).bb_instructions)`]
    mp_tac (INST_TYPE [``:'d`` |-> ``:basic_block``]
      current_wf_keyed_outputs_transport) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`renamed`, `\b. b.bb_label`,
    `\b. FLAT (MAP instruction_inst_outputs b.bb_instructions)`] mp_tac) >>
  simp[SF ETA_ss]
QED

Theorem current_wf_phi_context_ssa_form:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb ==> ssa_form (fn with fn_blocks := renamed)
Proof
  strip_tac >> irule current_wf_precleanup_ssa_form >>
  fs[current_wf_phi_context_def] >> metis_tac[]
QED

Theorem current_wf_leading_phi_split[local]:
  !insts. ?pre tail. insts = pre ++ tail /\
    EVERY (\i. i.inst_opcode = PHI) pre /\
    (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
    collect_phis insts = pre
Proof
  Induct >- (qexistsl_tac [`[]`, `[]`] >> simp[livenessDefsTheory.collect_phis_def]) >> gen_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (qpat_x_assum `?pre tail. _` strip_assume_tac >>
      qexistsl_tac [`h::pre`, `tail`] >> simp[livenessDefsTheory.collect_phis_def]) >>
  qexistsl_tac [`[]`, `h::insts`] >> simp[livenessDefsTheory.collect_phis_def]
QED

Theorem current_wf_phi_prefix_order:
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (!i j. i < j /\ j < LENGTH tail /\ (EL j tail).inst_opcode = PHI ==>
    (EL i tail).inst_opcode = PHI) /\
  MAP instruction_inst_opcode ys = MAP instruction_inst_opcode (pre ++ tail) ==>
  !i j. i < j /\ j < LENGTH ys /\ (EL j ys).inst_opcode = PHI ==>
    (EL i ys).inst_opcode = PHI
Proof
  strip_tac >>
  `LENGTH ys = LENGTH pre + LENGTH tail` by metis_tac[LENGTH_MAP, LENGTH_APPEND] >>
  rpt strip_tac >>
  `(EL j (pre ++ tail)).inst_opcode = PHI /\
   (EL i ys).inst_opcode = (EL i (pre ++ tail)).inst_opcode` by
    (qpat_x_assum `MAP _ ys = _` mp_tac >>
     disch_then (fn th => mp_tac (Q.AP_TERM `\xs. EL j xs` th) >>
       mp_tac (Q.AP_TERM `\xs. EL i xs` th)) >> simp[EL_MAP]) >>
  Cases_on `i < LENGTH pre`
  >- (simp[EL_APPEND_EQN] >> fs[EVERY_MEM] >> metis_tac[EL_MEM]) >>
  `~(j < LENGTH pre)` by decide_tac >>
  fs[EL_APPEND_EQN] >> first_x_assum irule >>
  qexists_tac `j - LENGTH pre` >> simp[] >> decide_tac
QED

Theorem current_wf_phi_context_prefix_order:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new ==>
  !i j. i < j /\ j < LENGTH new.bb_instructions /\
    (EL j new.bb_instructions).inst_opcode = PHI ==>
    (EL i new.bb_instructions).inst_opcode = PHI
Proof
  strip_tac >> drule_all current_wf_phi_context_block_opcodes >> strip_tac >>
  rpt strip_tac >> irule current_wf_phi_prefix_order >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`pre`, `old.bb_instructions`] >> simp[] >>
  `wf_function fn` by fs[current_wf_phi_context_def] >>
  `bb_well_formed old` by metis_tac[wf_function_def, lookup_block_MEM] >>
  fs[bb_well_formed_def]
QED

Theorem current_wf_phi_occurrence_cleanup_cases:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ q < LENGTH new.bb_instructions /\
  (EL q new.bb_instructions).inst_opcode = PHI ==>
  simplify_current_phi (EL q new.bb_instructions) = EL q new.bb_instructions \/
  (?src db di.
    simplify_current_phi (EL q new.bb_instructions) =
      (EL q new.bb_instructions) with <|inst_opcode := ASSIGN; inst_operands := [Var src]|> /\
    MEM db renamed /\ MEM di db.bb_instructions /\ MEM src di.inst_outputs /\
    db.bb_label <> new.bb_label /\
    fn_dominates (fn with fn_blocks := renamed) db.bb_label new.bb_label) \/
  ?k r slots n v. current_wf_original_phi_at fn A renamed h k r slots /\
    MEM n (EL r new.bb_instructions).inst_outputs /\ n <> v /\
    simplify_current_phi (EL r new.bb_instructions) = EL r new.bb_instructions /\
    (EL q new.bb_instructions).inst_outputs = [v] /\
    simplify_current_phi (EL q new.bb_instructions) =
      (EL q new.bb_instructions) with <|inst_opcode := ASSIGN; inst_operands := [Var n]|>
Proof
  strip_tac >> drule_all current_wf_phi_occurrence_producer >> strip_tac
  >- (`ssa_form (fn with fn_blocks := renamed)` by
        metis_tac[current_wf_phi_context_ssa_form] >>
      `?out. (EL q new.bb_instructions).inst_outputs = [out]` by
        metis_tac[current_wf_phi_occurrence_single_output] >>
      `fn_entry_label fn <> SOME h` by
        metis_tac[current_wf_phi_occurrence_nonentry] >>
      `current_wf_precleanup_certificate s fn renamed s' A H events /\
       wf_function fn /\ all_reachable fn` by fs[current_wf_phi_context_def] >>
      `MEM new renamed /\ new.bb_label = h` by
        metis_tac[lookup_block_MEM, lookup_block_label] >>
      `fn_reachable fn h` by
        (fs[all_reachable_def, fn_labels_def, MEM_MAP] >>
         metis_tac[lookup_block_MEM, lookup_block_label]) >>
      `fn_reachable (fn with fn_blocks := renamed) h` by
        metis_tac[current_wf_precleanup_dominance] >>
      `fn_entry_label (fn with fn_blocks := renamed) = SOME eb.bb_label` by
        metis_tac[current_wf_precleanup_entry, fn_entry_label_def, optionTheory.option_CLAUSES] >>
      `eb.bb_label <> h` by fs[fn_entry_label_def] >>
      `MEM new (fn with fn_blocks := renamed).fn_blocks /\
       MEM (EL q new.bb_instructions) new.bb_instructions /\
       fn_reachable (fn with fn_blocks := renamed) new.bb_label /\
       eb.bb_label <> new.bb_label` by simp[EL_MEM] >>
      drule_all current_wf_phi_cleanup_classification >> simp[] >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem current_wf_phi_context_same_prefix_source:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  q < LENGTH new.bb_instructions /\ r < LENGTH new.bb_instructions /\
  (EL q new.bb_instructions).inst_opcode = PHI /\
  (EL r new.bb_instructions).inst_opcode = PHI /\
  simplify_current_phi (EL r new.bb_instructions) = EL r new.bb_instructions /\
  MEM v (EL r new.bb_instructions).inst_outputs /\
  (simplify_current_phi (EL q new.bb_instructions)).inst_opcode <> PHI /\
  bb = simplify_current_phi_block new /\
  MEM bb f.fn_blocks /\ fn_reachable f bb.bb_label ==>
  ?k. k < LENGTH bb.bb_instructions /\
    current_inst_no_id (EL k bb.bb_instructions) =
      current_inst_no_id (simplify_current_phi (EL q new.bb_instructions)) /\
    def_available_at f bb (SOME (EL k bb.bb_instructions)) v
Proof
  strip_tac >>
  `!i j. i < j /\ j < LENGTH new.bb_instructions /\
    (EL j new.bb_instructions).inst_opcode = PHI ==>
    (EL i new.bb_instructions).inst_opcode = PHI` by
    metis_tac[current_wf_phi_context_prefix_order] >>
  `MEM (EL q new.bb_instructions) (collect_phis new.bb_instructions) /\
   MEM (EL r new.bb_instructions) (collect_phis new.bb_instructions)` by
    metis_tac[current_phi_in_prefix] >>
  qspec_then `new.bb_instructions` strip_assume_tac current_wf_leading_phi_split >>
  irule current_wf_cleanup_same_prefix_source >> simp[] >>
  qexistsl_tac [`EL r new.bb_instructions`, `new`, `pre`, `tail`] >> gvs[]
QED

Theorem current_wf_original_phi_copy_available:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ q < LENGTH new.bb_instructions /\
  (EL q new.bb_instructions).inst_opcode = PHI /\
  current_wf_original_phi_at fn A renamed h k r slots /\
  MEM n (EL r new.bb_instructions).inst_outputs /\
  simplify_current_phi (EL r new.bb_instructions) = EL r new.bb_instructions /\
  simplify_current_phi (EL q new.bb_instructions) =
    (EL q new.bb_instructions) with <|inst_opcode := ASSIGN; inst_operands := [Var n]|> /\
  bb = simplify_current_phi_block new /\
  MEM bb f.fn_blocks /\ fn_reachable f bb.bb_label ==>
  ?j. j < LENGTH bb.bb_instructions /\
    current_inst_no_id (EL j bb.bb_instructions) =
      current_inst_no_id (simplify_current_phi (EL q new.bb_instructions)) /\
    def_available_at f bb (SOME (EL j bb.bb_instructions)) n
Proof
  strip_tac >>
  `r < LENGTH new.bb_instructions /\
   (EL r new.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_original_phi_at_def] >> gvs[]) >>
  `(simplify_current_phi (EL q new.bb_instructions)).inst_opcode <> PHI` by simp[] >>
  irule current_wf_phi_context_same_prefix_source >> metis_tac[]
QED

Theorem current_wf_phi_occurrence_cleanup_ready:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ q < LENGTH new.bb_instructions /\
  (EL q new.bb_instructions).inst_opcode = PHI /\
  bb = simplify_current_phi_block new /\ MEM bb f.fn_blocks /\
  fn_reachable f bb.bb_label ==>
  simplify_current_phi (EL q new.bb_instructions) = EL q new.bb_instructions \/
  (?src db di.
    simplify_current_phi (EL q new.bb_instructions) =
      (EL q new.bb_instructions) with <|inst_opcode := ASSIGN; inst_operands := [Var src]|> /\
    MEM db renamed /\ MEM di db.bb_instructions /\ MEM src di.inst_outputs /\
    db.bb_label <> new.bb_label /\
    fn_dominates (fn with fn_blocks := renamed) db.bb_label new.bb_label) \/
  ?k r slots n v j. current_wf_original_phi_at fn A renamed h k r slots /\
    MEM n (EL r new.bb_instructions).inst_outputs /\ n <> v /\
    simplify_current_phi (EL r new.bb_instructions) = EL r new.bb_instructions /\
    (EL q new.bb_instructions).inst_outputs = [v] /\
    simplify_current_phi (EL q new.bb_instructions) =
      (EL q new.bb_instructions) with <|inst_opcode := ASSIGN; inst_operands := [Var n]|> /\
    j < LENGTH bb.bb_instructions /\
    current_inst_no_id (EL j bb.bb_instructions) =
      current_inst_no_id (simplify_current_phi (EL q new.bb_instructions)) /\
    def_available_at f bb (SOME (EL j bb.bb_instructions)) n
Proof
  strip_tac >> drule_all current_wf_phi_occurrence_cleanup_cases >> strip_tac
  >- simp[]
  >- metis_tac[] >>
  drule_all current_wf_original_phi_copy_available >> metis_tac[]
QED

Theorem current_wf_precleanup_ordinary_available:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  first_block_no_phi fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM bb renamed /\ MEM inst bb.bb_instructions /\ inst.inst_opcode <> PHI /\
  MEM (Var v) inst.inst_operands ==>
  def_available_at (fn with fn_blocks := renamed) bb (SOME inst) v
Proof
  strip_tac >> drule_all current_wf_precleanup_ordinary_cut >> strip_tac >>
  drule_all current_wf_ordinary_demand >> strip_tac >>
  `current_token_name H (E u) = SOME v` by
    (drule_all current_wf_precleanup_cut_name >> simp[]) >>
  `LENGTH (collect_phis old.bb_instructions) <= i` by
    metis_tac[current_wf_nonphi_after_collect] >>
  drule current_wf_precleanup_structural >> strip_tac >>
  `!dev k j. MEM dev events /\ k < LENGTH (A (current_event_label dev)) /\
     j < LENGTH (EL k (A (current_event_label dev))) ==>
     current_wf_output_at A H dev k (FST (EL j (EL k (A (current_event_label dev)))))` by
    metis_tac[current_wf_precleanup_output_sites] >>
  `fn_reachable fn (current_event_label ev)` by
    (drule lookup_block_MEM >> strip_tac >>
     drule lookup_block_label >> strip_tac >> fs[all_reachable_def] >> metis_tac[]) >>
  `fn_dominates fn (current_event_label ev) (current_event_label ev)` by
    (simp[fn_dominates_def] >> metis_tac[LAST_MEM]) >>
  `?dev k. MEM dev events /\ current_wf_output_at A H dev k (E u) /\
    ((dev = ev /\ k < LENGTH pre + i) \/
     (current_event_label dev <> current_event_label ev /\
      fn_dominates fn (current_event_label dev) (current_event_label ev)))` by
    (irule current_wf_demanded_source_cut_output >>
     fs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  irule current_wf_precleanup_output_available >>
  fs[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Definition current_wf_block_replacement_def:
  current_wf_block_replacement bb bb' <=>
    ?pre tail pre' tail'.
      bb.bb_instructions = pre ++ tail /\
      bb'.bb_instructions = pre' ++ tail' /\
      EVERY (\i. i.inst_opcode = PHI) pre /\
      LENGTH pre' = LENGTH pre /\
      PERM (FLAT (MAP (\i. i.inst_outputs) pre'))
           (FLAT (MAP (\i. i.inst_outputs) pre)) /\
      LIST_REL (\x y. current_inst_no_id x = current_inst_no_id y) tail tail'
End

Theorem current_wf_no_id_list_rel[local]:
  !xs ys. LIST_REL (\x y. current_inst_no_id x = current_inst_no_id y) xs ys ==>
    MAP current_inst_no_id xs = MAP current_inst_no_id ys
Proof
  Induct >> Cases_on `ys` >> simp[LIST_REL_def] >> metis_tac[]
QED

Theorem current_wf_block_replacement_outputs:
  current_wf_block_replacement bb bb' ==>
  PERM (FLAT (MAP (\i. i.inst_outputs) bb'.bb_instructions))
       (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  simp[current_wf_block_replacement_def] >> strip_tac >>
  drule current_wf_no_id_list_rel >> disch_tac >>
  drule current_wf_no_id_outputs >> disch_tac >>
  simp[PERM_APPEND_IFF]
QED

Theorem current_wf_replacement_outputs:
  !bbs. (!bb. MEM bb bbs ==> current_wf_block_replacement bb (B bb)) ==>
  PERM
    (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) (B bb).bb_instructions)) bbs))
    (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) bbs))
Proof
  Induct >- simp[] >> gen_tac >> strip_tac >>
  `current_wf_block_replacement h (B h)` by metis_tac[MEM] >>
  drule current_wf_block_replacement_outputs >> strip_tac >>
  qpat_x_assum `(_ ==> PERM _ _)` mp_tac >>
  (impl_tac >- metis_tac[MEM]) >> strip_tac >>
  simp[] >> metis_tac[PERM_CONG]
QED

Theorem current_wf_replacement_ssa_form:
  g.fn_blocks = MAP B f.fn_blocks /\
  (!bb. MEM bb f.fn_blocks ==> current_wf_block_replacement bb (B bb)) /\
  ssa_form f ==> ssa_form g
Proof
  strip_tac >>
  `PERM
    (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) (B bb).bb_instructions)) f.fn_blocks))
    (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) f.fn_blocks))` by
    (irule current_wf_replacement_outputs >> simp[]) >>
  fs[ssa_form_def, fn_insts_def, fn_insts_blocks_flat,
     MAP_FLAT, FLAT_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  metis_tac[ALL_DISTINCT_PERM, PERM_SYM]
QED

Theorem current_wf_block_replacement_defines:
  current_wf_block_replacement bb bb' ==>
  ((?i. MEM i bb'.bb_instructions /\ MEM v i.inst_outputs) <=>
   (?i. MEM i bb.bb_instructions /\ MEM v i.inst_outputs))
Proof
  strip_tac >> drule current_wf_block_replacement_outputs >>
  disch_then (mp_tac o MATCH_MP PERM_MEM_EQ) >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem current_wf_replacement_endpoint:
  g.fn_blocks = MAP B f.fn_blocks /\
  (!bb. MEM bb f.fn_blocks ==> current_wf_block_replacement bb (B bb) /\
     (B bb).bb_label = bb.bb_label) /\
  fn_entry_label g = fn_entry_label f /\
  (!a b. fn_cfg_edge g a b <=> fn_cfg_edge f a b) /\
  MEM bb f.fn_blocks /\ def_available_at f bb NONE v ==>
  def_available_at g (B bb) NONE v
Proof
  strip_tac >>
  `!d n. fn_dominates g d n <=> fn_dominates f d n` by
    metis_tac[current_wf_cfg_dominance] >>
  gvs[def_available_at_def] >>
  `current_wf_block_replacement def_bb (B def_bb)` by metis_tac[] >>
  `?di. MEM di (B def_bb).bb_instructions /\ MEM v di.inst_outputs` by
    metis_tac[current_wf_block_replacement_defines] >>
  qexistsl_tac [`B def_bb`, `di`] >> simp[MEM_MAP] >> metis_tac[]
QED

Theorem current_wf_prefix_output_before[local]:
  LENGTH pre' = LENGTH pre /\
  PERM (FLAT (MAP (\i. i.inst_outputs) pre'))
       (FLAT (MAP (\i. i.inst_outputs) pre)) /\
  LIST_REL (\x y. current_inst_no_id x = current_inst_no_id y) tail tail' /\
  d < LENGTH pre + k /\ k < LENGTH tail /\
  MEM v (EL d (pre ++ tail)).inst_outputs ==>
  ?d'. d' < LENGTH pre' + k /\
       MEM v (EL d' (pre' ++ tail')).inst_outputs
Proof
  strip_tac >> Cases_on `d < LENGTH pre`
  >- (`MEM v (FLAT (MAP (\i. i.inst_outputs) pre))` by
        (simp[MEM_FLAT, MEM_MAP] >> qexists_tac `(EL d pre).inst_outputs` >>
         conj_tac
         >- (qexists_tac `EL d pre` >> simp[EL_MEM]) >>
         fs[EL_APPEND_EQN]) >>
      `MEM v (FLAT (MAP (\i. i.inst_outputs) pre'))` by metis_tac[PERM_MEM_EQ] >>
      fs[MEM_FLAT, MEM_MAP] >>
      rename1 `MEM inst pre'` >>
      qpat_x_assum `MEM inst pre'` mp_tac >> rewrite_tac[MEM_EL] >>
      strip_tac >> qexists_tac `n` >>
      gvs[EL_APPEND_EQN, GSYM MEM_EL]) >>
  qexists_tac `d` >>
  drule current_wf_no_id_list_rel >> disch_tac >>
  drule current_wf_no_id_outputs >> disch_tac >>
  `d - LENGTH pre < LENGTH tail` by decide_tac >>
  `EL (d - LENGTH pre) (MAP (\i. i.inst_outputs) tail') =
   EL (d - LENGTH pre) (MAP (\i. i.inst_outputs) tail)` by simp[] >>
  `LENGTH tail = LENGTH tail'` by metis_tac[LIST_REL_LENGTH] >>
  `d - LENGTH pre < LENGTH tail /\ d - LENGTH pre < LENGTH tail'` by decide_tac >>
  fs[EL_MAP, EL_APPEND_EQN]
QED

Theorem current_wf_replacement_suffix:
  g.fn_blocks = MAP B f.fn_blocks /\
  (!b. MEM b f.fn_blocks ==> current_wf_block_replacement b (B b) /\
     (B b).bb_label = b.bb_label) /\
  fn_entry_label g = fn_entry_label f /\
  (!a b. fn_cfg_edge g a b <=> fn_cfg_edge f a b) /\
  ALL_DISTINCT (fn_labels f) /\ MEM bb f.fn_blocks /\
  bb.bb_instructions = pre ++ tail /\
  (B bb).bb_instructions = pre' ++ tail' /\
  LENGTH pre' = LENGTH pre /\
  PERM (FLAT (MAP (\i. i.inst_outputs) pre'))
       (FLAT (MAP (\i. i.inst_outputs) pre)) /\
  LIST_REL (\x y. current_inst_no_id x = current_inst_no_id y) tail tail' /\
  ALL_DISTINCT bb.bb_instructions /\ k < LENGTH tail /\
  def_available_at f bb (SOME (EL k tail)) v ==>
  def_available_at g (B bb) (SOME (EL k tail')) v
Proof
  strip_tac >>
  `!d n. fn_dominates g d n <=> fn_dominates f d n` by
    metis_tac[current_wf_cfg_dominance] >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  Cases_on `def_bb = bb`
  >- (qpat_x_assum `MEM def_inst _` kall_tac >> gvs[] >>
      `EL (LENGTH pre + k) (pre ++ tail) = EL k tail` by
        simp[EL_APPEND_EQN] >>
      `LENGTH pre + k < LENGTH (pre ++ tail)` by simp[] >>
      `j < LENGTH (pre ++ tail)` by simp[] >>
      `j = LENGTH pre + k` by metis_tac[ALL_DISTINCT_EL_IMP] >>
      `?d'. d' < LENGTH pre' + k /\
         MEM v (EL d' (pre' ++ tail')).inst_outputs` by
        (irule current_wf_prefix_output_before >> metis_tac[]) >>
      `LENGTH tail = LENGTH tail'` by metis_tac[LIST_REL_LENGTH] >>
      `MEM (EL d' (pre' ++ tail')) (pre' ++ tail')` by
        (irule EL_MEM >> simp[] >> decide_tac) >>
      qexistsl_tac [`B bb`, `EL d' (pre' ++ tail')`] >>
      simp[MEM_MAP] >> conj_tac
      >- metis_tac[] >>
      conj_tac >- metis_tac[MEM_APPEND] >>
      qexistsl_tac [`d'`, `LENGTH pre' + k`] >> simp[EL_APPEND_EQN]) >>
  `current_wf_block_replacement def_bb (B def_bb)` by metis_tac[] >>
  `?di. MEM di (B def_bb).bb_instructions /\ MEM v di.inst_outputs` by
    metis_tac[current_wf_block_replacement_defines] >>
  `B def_bb <> B bb` by
    (strip_tac >>
     `def_bb.bb_label = bb.bb_label` by metis_tac[] >>
     fs[fn_labels_def, MEM_EL] >>
     metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP, EL_MAP]) >>
  qexistsl_tac [`B def_bb`, `di`] >> simp[MEM_MAP] >> metis_tac[]
QED

Theorem current_wf_no_id_fields[local]:
  current_inst_no_id i = current_inst_no_id j ==>
  i.inst_opcode = j.inst_opcode /\ i.inst_operands = j.inst_operands /\
  i.inst_outputs = j.inst_outputs
Proof
  simp[current_inst_no_id_def] >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `_ with inst_id := 0 = _` (mp_tac o Q.AP_TERM `\i. i.inst_opcode`) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `_ with inst_id := 0 = _` (mp_tac o Q.AP_TERM `\i. i.inst_operands`) >> simp[]) >>
  qpat_x_assum `_ with inst_id := 0 = _` (mp_tac o Q.AP_TERM `\i. i.inst_outputs`) >> simp[]
QED

Theorem current_wf_replacement_phi:
  g.fn_blocks = MAP B f.fn_blocks /\
  (!b. MEM b f.fn_blocks ==> current_wf_block_replacement b (B b) /\
     (B b).bb_label = b.bb_label) /\
  fn_entry_label g = fn_entry_label f /\
  (!a b. fn_cfg_edge g a b <=> fn_cfg_edge f a b) /\
  MEM bb f.fn_blocks /\ current_inst_no_id i' = current_inst_no_id i /\
  phi_edge_uses_wf f bb i ==>
  phi_edge_uses_wf g (B bb) i'
Proof
  strip_tac >> drule current_wf_no_id_fields >> strip_tac >>
  fs[phi_edge_uses_wf_def] >>
  rpt strip_tac >>
  qpat_x_assum `!pred v. _` drule >> strip_tac >>
  `def_available_at g (B pred_bb) NONE v` by
    (irule current_wf_replacement_endpoint >> metis_tac[]) >>
  qexists_tac `B pred_bb` >> simp[MEM_MAP] >> metis_tac[]
QED

Theorem current_wf_replacement_strict_source:
  g.fn_blocks = MAP B f.fn_blocks /\
  (!b. MEM b f.fn_blocks ==> current_wf_block_replacement b (B b) /\
     (B b).bb_label = b.bb_label) /\
  fn_entry_label g = fn_entry_label f /\
  (!a b. fn_cfg_edge g a b <=> fn_cfg_edge f a b) /\
  MEM bb f.fn_blocks /\ MEM db f.fn_blocks /\
  db.bb_label <> bb.bb_label /\ fn_dominates f db.bb_label bb.bb_label /\
  MEM di db.bb_instructions /\ MEM v di.inst_outputs ==>
  def_available_at g (B bb) (SOME i) v
Proof
  strip_tac >>
  `?di'. MEM di' (B db).bb_instructions /\ MEM v di'.inst_outputs` by
    metis_tac[current_wf_block_replacement_defines] >>
  `fn_dominates g (B db).bb_label (B bb).bb_label` by
    metis_tac[current_wf_cfg_dominance] >>
  `B db <> B bb` by metis_tac[] >>
  simp[def_available_at_def] >> qexistsl_tac [`B db`, `di'`] >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem current_wf_ssa_no_id_available:
  ssa_form f /\ MEM bb f.fn_blocks /\
  MEM i bb.bb_instructions /\ MEM j bb.bb_instructions /\
  current_inst_no_id i = current_inst_no_id j /\ i.inst_outputs <> [] /\
  def_available_at f bb (SOME j) v ==>
  def_available_at f bb (SOME i) v
Proof
  strip_tac >> drule current_wf_no_id_fields >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP instruction_inst_outputs bb.bb_instructions))` by
    (fs[ssa_form_def, fn_insts_def, fn_insts_blocks_flat,
        MAP_FLAT, FLAT_FLAT, MAP_MAP_o, combinTheory.o_DEF, ETA_THM] >>
     drule all_distinct_flat_map_member >> simp[] >>
     disch_then (qspec_then `bb` mp_tac) >> simp[]) >>
  `?out. MEM out i.inst_outputs` by (Cases_on `i.inst_outputs` >> fs[] >> metis_tac[]) >>
  `i = j` by
    (irule (INST_TYPE [beta |-> ``:string``] all_distinct_flat_map_unique) >>
     qexistsl [`instruction_inst_outputs`, `bb.bb_instructions`, `out`] >> gvs[]) >>
  simp[]
QED

Theorem current_wf_replacement_wf_ssa:
  g.fn_blocks = MAP B f.fn_blocks /\
  fn_entry_label g = fn_entry_label f /\
  (!a b. fn_cfg_edge g a b <=> fn_cfg_edge f a b) /\
  ALL_DISTINCT (fn_labels f) /\ wf_ssa f /\
  (!bb. MEM bb f.fn_blocks ==>
    (B bb).bb_label = bb.bb_label /\ ALL_DISTINCT bb.bb_instructions /\
    ?pre tail pre' tail'.
      bb.bb_instructions = pre ++ tail /\
      (B bb).bb_instructions = pre' ++ tail' /\
      EVERY (\i. i.inst_opcode = PHI) pre /\
      LENGTH pre' = LENGTH pre /\
      PERM (FLAT (MAP (\i. i.inst_outputs) pre'))
           (FLAT (MAP (\i. i.inst_outputs) pre)) /\
      LIST_REL (\x y. current_inst_no_id x = current_inst_no_id y) tail tail' /\
      (!i'. MEM i' pre' ==>
        (i'.inst_opcode = PHI ==>
           ?i. MEM i pre /\ current_inst_no_id i' = current_inst_no_id i) /\
        (i'.inst_opcode <> PHI ==> !v. MEM (Var v) i'.inst_operands ==>
           ?db di. MEM db f.fn_blocks /\ MEM di db.bb_instructions /\
             MEM v di.inst_outputs /\ db.bb_label <> bb.bb_label /\
             fn_dominates f db.bb_label bb.bb_label))) ==>
  wf_ssa g
Proof
  strip_tac >>
  `!bb. MEM bb f.fn_blocks ==> current_wf_block_replacement bb (B bb) /\
      (B bb).bb_label = bb.bb_label` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     simp[current_wf_block_replacement_def] >> metis_tac[]) >>
  fs[wf_ssa_def] >> conj_tac
  >- (irule current_wf_replacement_ssa_form >> metis_tac[]) >>
  simp[def_dominates_uses_def] >> rpt gen_tac >> strip_tac >>
  gvs[MEM_MAP] >> rename1 `MEM bb f.fn_blocks` >>
  qpat_x_assum `!bb. MEM bb _ ==> ALL_DISTINCT _ /\ _` drule >>
  strip_tac >>
  Cases_on `MEM inst pre'`
  >- (Cases_on `inst.inst_opcode = PHI` >> simp[]
      >- (`?i. MEM i pre /\ current_inst_no_id inst = current_inst_no_id i` by metis_tac[] >>
          `phi_edge_uses_wf f bb i` by
            (fs[def_dominates_uses_def, EVERY_MEM] >> metis_tac[MEM_APPEND]) >>
          irule current_wf_replacement_phi >> metis_tac[]) >>
      rpt strip_tac >> irule current_wf_replacement_strict_source >> metis_tac[]) >>
  `MEM inst tail'` by metis_tac[MEM_APPEND] >>
  qpat_x_assum `MEM inst tail'` mp_tac >> rewrite_tac[MEM_EL] >> strip_tac >>
  `n < LENGTH tail` by metis_tac[LIST_REL_LENGTH] >>
  `current_inst_no_id (EL n tail) = current_inst_no_id inst` by
    (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  drule current_wf_no_id_fields >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> simp[]
  >- (`phi_edge_uses_wf f bb (EL n tail)` by
        (fs[def_dominates_uses_def] >> metis_tac[MEM_APPEND, EL_MEM]) >>
      irule current_wf_replacement_phi >> metis_tac[]) >>
  rpt strip_tac >>
  `def_available_at f bb (SOME (EL n tail)) v` by
    (fs[def_dominates_uses_def] >> metis_tac[MEM_APPEND, EL_MEM]) >>
  irule current_wf_replacement_suffix >> metis_tac[]
QED

Theorem current_wf_precleanup_ids_distinct:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  defs = compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) labels))) /\
  add_phi_nodes_supply s df pm li fn.fn_blocks defs = (ins,si) /\
  rename_current_blocks si rs ins sm tree = (ctrs,s',renamed) ==>
  ALL_DISTINCT (FLAT (MAP block_ir_inst_ids renamed))
Proof
  strip_tac >>
  `ssa_vars_covered s (FLAT (MAP block_ir_vars fn.fn_blocks))` by
    fs[ir_supply_covers_fn_def, list_subset_def, fn_ir_vars_def, ssa_vars_covered_def] >>
  `ssa_vars_covered s (MAP FST defs)` by
    (simp[] >> irule compute_defs_lookup_blocks_vars_covered >> simp[]) >>
  `ALL_DISTINCT (FLAT (MAP block_ir_inst_ids fn.fn_blocks))` by
    (fs[wf_function_def, fn_inst_ids_distinct_def] >>
     qpat_x_assum `ALL_DISTINCT (FLAT _)` mp_tac >>
     simp[GSYM block_ir_inst_ids_def, ETA_THM]) >>
  `EVERY (\id. MEM id s.irs_used_inst_ids) (FLAT (MAP block_ir_inst_ids fn.fn_blocks))` by
    fs[ir_supply_covers_fn_def, list_subset_def, fn_ir_inst_ids_def] >>
  `ALL_DISTINCT (MAP basic_block_bb_label fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  drule_all add_phi_nodes_supply_ok >> strip_tac >>
  `ALL_DISTINCT (MAP basic_block_bb_label ins)` by metis_tac[] >>
  drule_all (CONJUNCT1 rename_current_blocks_inst_ids) >>
  fs[ssa_ids_supply_ok_def]
QED

Theorem current_wf_cleanup_prefix_semantics:
  ssa_form fn /\ MEM bb fn.fn_blocks /\
  bb.bb_instructions = pre ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  fn_reachable fn bb.bb_label /\ fn_entry_label fn = SOME entry /\
  entry <> bb.bb_label /\
  (!i. MEM i pre ==> (?out. i.inst_outputs = [out]) /\ phi_edge_uses_wf fn bb i) ==>
  ?pre' tail'.
    (simplify_current_phi_block bb).bb_instructions = pre' ++ tail' /\
    LENGTH pre' = LENGTH pre /\
    PERM (FLAT (MAP (\i. i.inst_outputs) pre'))
         (FLAT (MAP (\i. i.inst_outputs) pre)) /\
    LIST_REL (\x y. current_inst_no_id x = current_inst_no_id y) tail tail' /\
    (!i'. MEM i' pre' ==>
      (i'.inst_opcode = PHI ==>
         ?i. MEM i pre /\ current_inst_no_id i' = current_inst_no_id i) /\
      (i'.inst_opcode <> PHI ==> !v. MEM (Var v) i'.inst_operands ==>
         ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
           MEM v di.inst_outputs /\ db.bb_label <> bb.bb_label /\
           fn_dominates fn db.bb_label bb.bb_label))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!i. MEM i pre ==> simplify_current_phi i = i \/
    ?src db di. simplify_current_phi i =
       i with <|inst_opcode := ASSIGN; inst_operands := [Var src]|> /\
       MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
       MEM src di.inst_outputs /\ db.bb_label <> bb.bb_label /\
       fn_dominates fn db.bb_label bb.bb_label` by
    (rpt strip_tac >> irule current_wf_phi_cleanup_classification >>
     fs[EVERY_MEM] >> metis_tac[MEM_APPEND]) >>
  `!i. MEM i pre ==> (simplify_current_phi i).inst_outputs = i.inst_outputs` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[]) >>
  mp_tac (Q.INST [`bb` |-> `bb`, `pre` |-> `pre`, `tail` |-> `tail`]
    current_wf_cleanup_block_split) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`pre'`, `tail'`] >> simp[] >> rpt strip_tac
  >- (qpat_x_assum `!i'. MEM i' _ ==> ?i. _` drule >> strip_tac >>
      `simplify_current_phi i = i \/
        ?src db di. simplify_current_phi i =
           i with <|inst_opcode := ASSIGN; inst_operands := [Var src]|> /\
           MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
           MEM src di.inst_outputs /\ db.bb_label <> bb.bb_label /\
           fn_dominates fn db.bb_label bb.bb_label` by metis_tac[]
      >- metis_tac[] >>
      drule current_wf_no_id_fields >> simp[]) >>
  qpat_x_assum `!i'. MEM i' _ ==> ?i. _` drule >> strip_tac >>
  drule current_wf_no_id_fields >> strip_tac >>
  qpat_x_assum `!i. MEM i _ ==> simplify_current_phi i = i \/ _` drule >>
  strip_tac
  >- (fs[EVERY_MEM] >> metis_tac[]) >>
  gvs[] >> qexistsl_tac [`db`, `di`] >> simp[]
QED

Theorem current_wf_cleanup_phi_successors[local]:
  i.inst_opcode = PHI ==> get_successors (simplify_current_phi i) = []
Proof
  strip_tac >>
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[get_successors_def, is_terminator_def] >>
  simp[simplify_current_phi_raw_def] >>
  Cases_on `current_phi_output i.inst_outputs` >> simp[get_successors_def, is_terminator_def] >>
  Cases_on `current_phi_values (remove_current_phi_self x i.inst_operands)` >>
  simp[get_successors_def, is_terminator_def] >>
  Cases_on `x'` >> simp[get_successors_def, is_terminator_def] >>
  Cases_on `EVERY (\w. w = h) t` >> simp[get_successors_def, is_terminator_def]
QED

Definition current_wf_list_succs_def:
  current_wf_list_succs insts =
    if insts = [] then [] else get_successors (LAST insts)
End

Theorem current_wf_list_succs_no_id[local]:
  !xs ys. MAP current_inst_no_id xs = MAP current_inst_no_id ys ==>
    current_wf_list_succs xs = current_wf_list_succs ys
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `xs = []` >> Cases_on `ys = []` >> gvs[current_wf_list_succs_def] >>
  `current_inst_no_id (LAST xs) = current_inst_no_id (LAST ys)` by
    metis_tac[LAST_MAP] >>
  drule current_wf_no_id_fields >> simp[get_successors_def]
QED

Theorem current_wf_list_succs_prefix[local]:
  EVERY (\i. get_successors i = []) pre ==>
  current_wf_list_succs (pre ++ tail) = current_wf_list_succs tail
Proof
  strip_tac >> Cases_on `tail = []` >> simp[current_wf_list_succs_def, LAST_APPEND_NOT_NIL] >>
  Cases_on `pre = []` >> simp[] >> fs[EVERY_MEM] >> metis_tac[LAST_MEM]
QED

Theorem current_wf_cleanup_block_succs:
  bb_succs (simplify_current_phi_block bb) = bb_succs bb
Proof
  qspec_then `bb.bb_instructions` strip_assume_tac current_wf_leading_phi_split >>
  `MAP current_inst_no_id (simplify_current_phi_block bb).bb_instructions =
    MAP current_inst_no_id
      ((FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre) ++
        FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre)) ++ tail)` by
    (irule current_wf_cleanup_block_no_id >> metis_tac[]) >>
  drule current_wf_list_succs_no_id >> disch_tac >>
  `EVERY (\i. get_successors i = []) pre` by
    (fs[EVERY_MEM] >> simp[get_successors_def, is_terminator_def]) >>
  `EVERY (\i. get_successors i = [])
    (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre) ++
     FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre))` by
    (fs[EVERY_MEM, MEM_FILTER, MEM_MAP] >> rpt strip_tac >> gvs[] >>
     irule current_wf_cleanup_phi_successors >> metis_tac[]) >>
  `current_wf_list_succs (simplify_current_phi_block bb).bb_instructions =
    current_wf_list_succs bb.bb_instructions` by
    metis_tac[current_wf_list_succs_prefix] >>
  `!b. bb_succs b = nub (REVERSE (current_wf_list_succs b.bb_instructions))` by
    (gen_tac >> Cases_on `b.bb_instructions` >>
     simp[bb_succs_def, current_wf_list_succs_def]) >>
  simp[]
QED

Theorem current_wf_cleanup_cfg:
  g.fn_blocks = MAP simplify_current_phi_block f.fn_blocks ==>
  fn_entry_label g = fn_entry_label f /\
  (!a b. fn_cfg_edge g a b <=> fn_cfg_edge f a b)
Proof
  strip_tac >> conj_tac
  >- (Cases_on `f.fn_blocks` >>
      simp[fn_entry_label_def, entry_block_def]) >>
  simp[fn_cfg_edge_def, MEM_MAP] >>
  metis_tac[current_wf_cleanup_block_succs, current_cleanup_block_label]
QED

Theorem current_wf_entry_phi_free[local]:
  ALL_DISTINCT (fn_labels f) /\ first_block_no_phi f /\
  MEM bb f.fn_blocks /\ fn_entry_label f = SOME bb.bb_label ==>
  EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions
Proof
  strip_tac >> Cases_on `f.fn_blocks` >>
  gvs[fn_entry_label_def, entry_block_def, first_block_no_phi_def,
      fn_labels_def, ALL_DISTINCT, MEM_MAP] >> metis_tac[]
QED

Theorem current_wf_cleanup_preserves_wf_ssa:
  wf_ssa f /\ ALL_DISTINCT (fn_labels f) /\ all_reachable f /\
  first_block_no_phi f /\ fn_inst_wf f /\
  (!bb. MEM bb f.fn_blocks ==> ALL_DISTINCT bb.bb_instructions) /\
  g.fn_blocks = simplify_current_phis f.fn_blocks ==>
  wf_ssa g
Proof
  strip_tac >>
  `g.fn_blocks = MAP simplify_current_phi_block f.fn_blocks` by
    metis_tac[current_cleanup_phis_map] >>
  drule current_wf_cleanup_cfg >> strip_tac >>
  irule current_wf_replacement_wf_ssa >>
  qexistsl_tac [`simplify_current_phi_block`, `f`] >> simp[] >>
  qx_gen_tac `bb` >> strip_tac >>
  Cases_on `fn_entry_label f = SOME bb.bb_label`
  >- (`EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions` by
        (irule current_wf_entry_phi_free >> qexists_tac `f` >> simp[]) >>
      `simplify_current_phi_block bb = bb` by
        (Cases_on `bb.bb_instructions` >>
         fs[simplify_current_phi_block_def]) >>
      qexistsl_tac [`[]`, `bb.bb_instructions`, `[]`, `bb.bb_instructions`] >>
      simp[LIST_REL_EL_EQN]) >>
  `fn_reachable f bb.bb_label` by fs[all_reachable_def] >>
  `?entry. fn_entry_label f = SOME entry /\ entry <> bb.bb_label` by
    (fs[fn_reachable_def] >> metis_tac[]) >>
  qspec_then `bb.bb_instructions`
    (qx_choose_then `pre` (qx_choose_then `tail` assume_tac)) current_wf_leading_phi_split >>
  `!i. MEM i pre ==> (?out. i.inst_outputs = [out]) /\ phi_edge_uses_wf f bb i` by
    (gen_tac >> disch_tac >>
     `MEM i bb.bb_instructions /\ i.inst_opcode = PHI` by fs[EVERY_MEM] >>
     conj_tac
     >- (`inst_wf i` by metis_tac[fn_inst_wf_def] >>
         qpat_x_assum `inst_wf i` mp_tac >>
         simp[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
     fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  `ssa_form f` by fs[wf_ssa_def] >>
  qpat_x_assum `_ = pre ++ tail /\ _` (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all current_wf_cleanup_prefix_semantics >> strip_tac >>
  qexistsl_tac [`pre`, `tail`, `pre'`, `tail'`] >> fs[] >> metis_tac[]
QED

Theorem current_wf_phi_context_lookup:
  current_wf_phi_context s fn renamed s' A H events /\ MEM new renamed ==>
  lookup_block new.bb_label renamed = SOME new /\
  ?old. lookup_block new.bb_label fn.fn_blocks = SOME old
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\ wf_function fn` by
    fs[current_wf_phi_context_def] >>
  drule current_wf_precleanup_labels >>
  disch_then (assume_tac o PURE_REWRITE_RULE [ETA_THM]) >>
  `ALL_DISTINCT (MAP basic_block_bb_label fn.fn_blocks)` by
    (qpat_x_assum `wf_function fn` mp_tac >>
     pure_rewrite_tac[wf_function_def, fn_labels_def, ETA_THM] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `ALL_DISTINCT (MAP basic_block_bb_label renamed)` by metis_tac[] >>
  conj_tac >- metis_tac[MEM_lookup_block] >>
  `MEM new.bb_label (MAP basic_block_bb_label fn.fn_blocks)` by
    metis_tac[MEM_MAP] >>
  qpat_x_assum `MEM new.bb_label (MAP _ fn.fn_blocks)` mp_tac >>
  pure_rewrite_tac[MEM_MAP] >> strip_tac >>
  metis_tac[MEM_lookup_block]
QED

Theorem current_wf_phi_context_cleanup_split:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ MEM new renamed ==>
  ?pre tail pre' tail'.
    new.bb_instructions = pre ++ tail /\
    EVERY (\i. i.inst_opcode = PHI) pre /\
    EVERY (\i. i.inst_opcode <> PHI) tail /\
    (simplify_current_phi_block new).bb_instructions = pre' ++ tail' /\
    LENGTH pre' = LENGTH pre /\
    PERM (FLAT (MAP (\i. i.inst_outputs) pre'))
         (FLAT (MAP (\i. i.inst_outputs) pre)) /\
    LIST_REL (\x y. current_inst_no_id x = current_inst_no_id y) tail tail' /\
    (!i'. MEM i' pre' ==> ?i. MEM i pre /\
       current_inst_no_id i' = current_inst_no_id (simplify_current_phi i))
Proof
  strip_tac >> drule_all current_wf_phi_context_lookup >> strip_tac >>
  `!i j. i < j /\ j < LENGTH new.bb_instructions /\
    (EL j new.bb_instructions).inst_opcode = PHI ==>
    (EL i new.bb_instructions).inst_opcode = PHI` by
    metis_tac[current_wf_phi_context_prefix_order] >>
  qspec_then `new.bb_instructions`
    (qx_choose_then `pre` (qx_choose_then `tail`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac))) current_wf_leading_phi_split >>
  qpat_x_assum `collect_phis _ = pre` kall_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) tail` by
    (rewrite_tac[EVERY_EL] >> qx_gen_tac `n` >> disch_tac >>
     `tail <> []` by (strip_tac >> gvs[]) >>
     `HD tail = EL 0 tail` by (Cases_on `tail` >> simp[]) >>
     Cases_on `n = 0` >- metis_tac[] >>
     BETA_TAC >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`LENGTH pre`, `LENGTH pre + n`] mp_tac) >>
     qpat_x_assum `new.bb_instructions = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, EL_APPEND_EQN] >>
     `0 < n` by decide_tac >> metis_tac[]) >>
  `!i. MEM i pre ==> (simplify_current_phi i).inst_outputs = i.inst_outputs` by
    (rpt strip_tac >>
     `?q. q < LENGTH new.bb_instructions /\ i = EL q new.bb_instructions` by
       (simp[GSYM MEM_EL] >> metis_tac[MEM_APPEND]) >>
     `i.inst_opcode = PHI` by
       (qpat_x_assum `EVERY (\i. i.inst_opcode = PHI) pre` mp_tac >>
        pure_rewrite_tac[EVERY_MEM] >> disch_then (qspec_then `i` mp_tac) >>
        simp[]) >>
     qpat_x_assum `i = EL q _` SUBST_ALL_TAC >>
     drule_all current_wf_phi_occurrence_cleanup_cases >> strip_tac >> gvs[]) >>
  drule_all current_wf_cleanup_block_split >> strip_tac >>
  qexistsl [`pre`, `tail`, `pre'`, `tail'`] >> simp[]
QED

Theorem current_wf_phi_context_replacement:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ MEM bb renamed ==>
  current_wf_block_replacement bb (simplify_current_phi_block bb) /\
  (simplify_current_phi_block bb).bb_label = bb.bb_label
Proof
  strip_tac >> drule_all current_wf_phi_context_cleanup_split >> strip_tac >>
  simp[current_wf_block_replacement_def] >> metis_tac[]
QED

Theorem current_wf_phi_context_cleanup_ssa_form:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  g.fn_blocks = MAP simplify_current_phi_block renamed ==>
  ssa_form g
Proof
  strip_tac >> irule current_wf_replacement_ssa_form >>
  qexistsl [`simplify_current_phi_block`, `fn with fn_blocks := renamed`] >>
  simp[] >> conj_tac
  >- metis_tac[current_wf_phi_context_replacement] >>
  metis_tac[current_wf_phi_context_ssa_form]
QED

Theorem current_wf_phi_context_retained_edge:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ q < LENGTH new.bb_instructions /\
  (EL q new.bb_instructions).inst_opcode = PHI /\
  simplify_current_phi (EL q new.bb_instructions) = EL q new.bb_instructions ==>
  phi_edge_uses_wf (fn with fn_blocks := renamed) new (EL q new.bb_instructions)
Proof
  strip_tac >> drule_all current_wf_phi_occurrence_producer >> strip_tac >> simp[] >>
  qpat_x_assum `_ = _ with <|inst_opcode := ASSIGN; inst_operands := _|>`
    (mp_tac o Q.AP_TERM `\i. i.inst_opcode`) >> simp[]
QED

Theorem current_wf_phi_context_cleaned_occurrence:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ MEM new renamed /\
  q < LENGTH new.bb_instructions /\ (EL q new.bb_instructions).inst_opcode = PHI /\
  g.fn_blocks = MAP simplify_current_phi_block renamed /\
  MEM i' (simplify_current_phi_block new).bb_instructions /\
  current_inst_no_id i' = current_inst_no_id (simplify_current_phi (EL q new.bb_instructions)) /\
  fn_reachable g new.bb_label ==>
  (i'.inst_opcode = PHI ==> phi_edge_uses_wf g (simplify_current_phi_block new) i') /\
  (i'.inst_opcode <> PHI ==> !v. MEM (Var v) i'.inst_operands ==>
    def_available_at g (simplify_current_phi_block new) (SOME i') v)
Proof
  strip_tac >> drule_all current_wf_phi_context_lookup >> strip_tac >>
  `!b. MEM b (fn with fn_blocks := renamed).fn_blocks ==>
    current_wf_block_replacement b (simplify_current_phi_block b) /\
    (simplify_current_phi_block b).bb_label = b.bb_label` by
    (simp[] >> metis_tac[current_wf_phi_context_replacement]) >>
  `g.fn_blocks = MAP simplify_current_phi_block (fn with fn_blocks := renamed).fn_blocks` by simp[] >>
  drule current_wf_cleanup_cfg >> strip_tac >>
  `MEM (simplify_current_phi_block new) g.fn_blocks` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  `fn_reachable g (simplify_current_phi_block new).bb_label` by simp[] >>
  mp_tac (Q.INST [`f` |-> `g`, `bb` |-> `simplify_current_phi_block new`,
    `h` |-> `new.bb_label`] current_wf_phi_occurrence_cleanup_ready) >>
  (impl_tac >- metis_tac[]) >> strip_tac
  >- (`phi_edge_uses_wf (fn with fn_blocks := renamed) new (EL q new.bb_instructions)` by
        metis_tac[current_wf_phi_context_retained_edge] >>
      `current_inst_no_id i' = current_inst_no_id (EL q new.bb_instructions)` by metis_tac[] >>
      drule current_wf_no_id_fields >> strip_tac >> simp[] >>
      irule current_wf_replacement_phi >>
      qexistsl [`fn with fn_blocks := renamed`, `EL q new.bb_instructions`] >>
      simp[])
  >- (drule current_wf_no_id_fields >> strip_tac >> gvs[] >>
      irule current_wf_replacement_strict_source >>
      qexistsl [`db`, `di`, `fn with fn_blocks := renamed`] >> simp[]) >>
  qpat_assum `current_inst_no_id i' = _`
    (strip_assume_tac o MATCH_MP current_wf_no_id_fields) >> gvs[] >>
  `ssa_form g` by metis_tac[current_wf_phi_context_cleanup_ssa_form] >>
  irule current_wf_ssa_no_id_available >> simp[] >>
  qexists_tac `EL j (simplify_current_phi_block new).bb_instructions` >>
  simp[EL_MEM] >> metis_tac[]
QED

Theorem current_wf_phi_context_instructions_distinct:
  current_wf_phi_context s fn renamed s' A H events ==>
  !bb. MEM bb renamed ==> ALL_DISTINCT bb.bb_instructions
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP block_ir_inst_ids renamed))` suffices_by
    metis_tac[current_wf_blocks_distinct_instructions] >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  qpat_x_assum `current_wf_precleanup_certificate _ _ _ _ _ _ _` mp_tac >>
  simp[current_wf_precleanup_certificate_def] >> strip_tac >>
  drule (cj 1 current_tree_trace_projection) >> strip_tac >>
  irule current_wf_precleanup_ids_distinct >> metis_tac[]
QED

Theorem current_wf_phi_context_cleanup_reachable:
  current_wf_phi_context s fn renamed s' A H events /\ entry_block fn = SOME eb /\
  g.fn_blocks = MAP simplify_current_phi_block renamed /\ MEM bb renamed ==>
  fn_reachable g bb.bb_label
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn` by fs[current_wf_phi_context_def] >>
  drule_all current_wf_phi_context_lookup >> strip_tac >>
  `fn_reachable fn bb.bb_label` by
    (qpat_x_assum `all_reachable fn` mp_tac >>
     simp[all_reachable_def, fn_labels_def, MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `fn_reachable (fn with fn_blocks := renamed) bb.bb_label` by
    metis_tac[current_wf_precleanup_dominance] >>
  `g.fn_blocks = MAP simplify_current_phi_block (fn with fn_blocks := renamed).fn_blocks` by simp[] >>
  drule current_wf_cleanup_cfg >> strip_tac >>
  metis_tac[current_wf_cfg_dominance]
QED

Theorem current_wf_phi_context_cleanup_dominates:
  current_wf_phi_context s fn renamed s' A H events /\ entry_block fn = SOME eb /\
  g.fn_blocks = MAP simplify_current_phi_block renamed ==>
  def_dominates_uses g
Proof
  strip_tac >>
  `!b. MEM b (fn with fn_blocks := renamed).fn_blocks ==>
    current_wf_block_replacement b (simplify_current_phi_block b) /\
    (simplify_current_phi_block b).bb_label = b.bb_label` by
    (simp[] >> metis_tac[current_wf_phi_context_replacement]) >>
  `g.fn_blocks = MAP simplify_current_phi_block (fn with fn_blocks := renamed).fn_blocks` by simp[] >>
  drule current_wf_cleanup_cfg >> strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
   fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
   first_block_no_phi fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  `ALL_DISTINCT (fn_labels (fn with fn_blocks := renamed))` by
    (drule current_wf_precleanup_labels >>
     disch_then (assume_tac o PURE_REWRITE_RULE [ETA_THM]) >>
     qpat_x_assum `wf_function fn` mp_tac >>
     pure_rewrite_tac[wf_function_def, fn_labels_def, ETA_THM] >>
     strip_tac >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
  simp[def_dominates_uses_def] >> rpt gen_tac >> strip_tac >>
  gvs[MEM_MAP] >> rename1 `MEM new renamed` >>
  drule_all current_wf_phi_context_cleanup_split >> strip_tac >>
  Cases_on `MEM inst pre'`
  >- (`?i. MEM i pre /\ current_inst_no_id inst = current_inst_no_id (simplify_current_phi i)` by
        metis_tac[] >>
      `i.inst_opcode = PHI` by
        (qpat_x_assum `EVERY (\i. i.inst_opcode = PHI) pre` mp_tac >>
         pure_rewrite_tac[EVERY_MEM] >> disch_then (qspec_then `i` mp_tac) >> simp[]) >>
      `?q. q < LENGTH new.bb_instructions /\ i = EL q new.bb_instructions` by
        (simp[GSYM MEM_EL] >> metis_tac[MEM_APPEND]) >>
      `fn_reachable g new.bb_label` by metis_tac[current_wf_phi_context_cleanup_reachable] >>
      qpat_x_assum `i = EL q _` SUBST_ALL_TAC >>
      drule_all current_wf_phi_context_cleaned_occurrence >>
      Cases_on `inst.inst_opcode = PHI` >> simp[]) >>
  `MEM inst tail'` by metis_tac[MEM_APPEND] >>
  qpat_x_assum `MEM inst tail'` mp_tac >> pure_rewrite_tac[MEM_EL] >> strip_tac >>
  `n < LENGTH tail` by metis_tac[LIST_REL_LENGTH] >>
  `current_inst_no_id (EL n tail) = current_inst_no_id inst` by
    (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  drule current_wf_no_id_fields >> strip_tac >>
  `MEM (EL n tail) tail` by simp[EL_MEM] >>
  `(EL n tail).inst_opcode <> PHI` by
    (qpat_x_assum `EVERY (\i. i.inst_opcode <> PHI) tail` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >> disch_then (qspec_then `EL n tail` mp_tac) >> simp[]) >>
  gvs[] >> rpt strip_tac >>
  `def_available_at (fn with fn_blocks := renamed) new (SOME (EL n tail)) v` by
    (irule current_wf_precleanup_ordinary_available >> simp[] >> metis_tac[MEM_APPEND, EL_MEM]) >>
  irule current_wf_replacement_suffix >>
  conj_tac >- metis_tac[current_wf_phi_context_instructions_distinct] >>
  qexistsl [`fn with fn_blocks := renamed`, `pre`, `pre'`, `tail`] >>
  simp[]
QED

Theorem current_wf_no_leading_phi_member[local]:
  !bbs bb. ~blocks_have_leading_phi bbs /\ MEM bb bbs ==>
    !i. i < LENGTH bb.bb_instructions /\
      (EL i bb.bb_instructions).inst_opcode = PHI ==> ~bb_well_formed bb
Proof
  Induct >- simp[] >> gen_tac >> simp[blocks_have_leading_phi_def] >>
  Cases_on `h.bb_instructions` >> simp[]
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `bb = h`
  >- (gvs[bb_well_formed_def] >> Cases_on `i` >> gvs[] >>
      qpat_x_assum `!i j. _` (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  metis_tac[]
QED

Theorem current_wf_phi_context_no_cleanup_dominates:
  current_wf_phi_context s fn renamed s' A H events /\ entry_block fn = SOME eb /\
  ~blocks_have_leading_phi fn.fn_blocks ==>
  def_dominates_uses (fn with fn_blocks := renamed)
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
   fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
   first_block_no_phi fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  `!h k r slots. ~current_wf_original_phi_at fn A renamed h k r slots` by
    (rpt strip_tac >> fs[current_wf_original_phi_at_def] >>
     `MEM old fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
     metis_tac[current_wf_no_leading_phi_member, wf_function_def]) >>
  simp[def_dominates_uses_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (simp[] >>
      `?q. q < LENGTH bb.bb_instructions /\ inst = EL q bb.bb_instructions` by
        metis_tac[MEM_EL] >>
      drule_all current_wf_phi_context_lookup >> strip_tac >>
      qpat_x_assum `inst = EL q _` SUBST_ALL_TAC >>
      drule_all current_wf_phi_occurrence_producer >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  irule current_wf_precleanup_ordinary_available >> simp[] >>
  metis_tac[EL_MEM]
QED

(* Bounded cleanup probe: two backedge predecessors of an original PHI. *)
Definition current_wf_probe_fork_def:
  current_wf_probe_fork = mk_raw_function "fork"
    [<| bb_label := "E"; bb_instructions :=
        [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
         current_probe_inst 1 JMP [Label "H"] []] |>;
     <| bb_label := "H"; bb_instructions :=
        [current_probe_inst 2 PHI
          [Label "E"; Var "a"; Label "D"; Var "b"; Label "F"; Var "c"] ["v"];
         current_probe_inst 3 JNZ [Var "v"; Label "D"; Label "F"] []] |>;
     <| bb_label := "D"; bb_instructions :=
        [current_probe_inst 4 ASSIGN [Lit 2w] ["b"];
         current_probe_inst 5 JNZ [Var "v"; Label "H"; Label "X"] []] |>;
     <| bb_label := "F"; bb_instructions :=
        [current_probe_inst 6 ASSIGN [Lit 3w] ["c"];
         current_probe_inst 7 JMP [Label "H"] []] |>;
     <| bb_label := "X"; bb_instructions :=
        [current_probe_inst 8 STOP [] []] |>]
End

Definition current_wf_probe_supply_def:
  current_wf_probe_supply fn =
    <| irs_next_inst := 20; irs_next_var := 0; irs_next_label := 0;
       irs_used_inst_ids := fn_ir_inst_ids fn;
       irs_used_vars := fn_ir_vars fn; irs_used_labels := fn_ir_labels fn |>
End

Theorem current_wf_probe_fork_structural:
  wf_function current_wf_probe_fork /\ fn_inst_wf current_wf_probe_fork /\
  first_block_no_preds current_wf_probe_fork /\ first_block_no_phi current_wf_probe_fork /\
  ir_supply_covers_fn (current_wf_probe_supply current_wf_probe_fork) current_wf_probe_fork /\
  ir_supply_inst_ok (current_wf_probe_supply current_wf_probe_fork)
Proof
  EVAL_TAC
QED

Theorem current_wf_probe_fork_final:
  wf_ssa (FST (make_ssa_current_fn (current_wf_probe_supply current_wf_probe_fork)
    current_wf_probe_fork))
Proof
  rewrite_tac[wf_ssa_def] >> EVAL_TAC
QED

(* Nested header: the inner original PHI reads the outer PHI's output. *)
Definition current_wf_probe_nested_def:
  current_wf_probe_nested = mk_raw_function "nested"
    [<| bb_label := "E"; bb_instructions :=
        [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
         current_probe_inst 1 JMP [Label "H"] []] |>;
     <| bb_label := "H"; bb_instructions :=
        [current_probe_inst 2 PHI
          [Label "E"; Var "a"; Label "F"; Var "b"] ["v"];
         current_probe_inst 3 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        [current_probe_inst 4 PHI
          [Label "H"; Var "v"; Label "D"; Var "c"] ["w"];
         current_probe_inst 5 JNZ [Var "w"; Label "D"; Label "F"] []] |>;
     <| bb_label := "D"; bb_instructions :=
        [current_probe_inst 6 ASSIGN [Lit 2w] ["c"];
         current_probe_inst 7 JMP [Label "J"] []] |>;
     <| bb_label := "F"; bb_instructions :=
        [current_probe_inst 8 ASSIGN [Lit 3w] ["b"];
         current_probe_inst 9 JNZ [Var "w"; Label "H"; Label "X"] []] |>;
     <| bb_label := "X"; bb_instructions :=
        [current_probe_inst 10 ASSIGN [Var "v"] ["z"];
         current_probe_inst 11 STOP [] []] |>]
End

Theorem current_wf_probe_fork_header:
  (EL 1 (FST (make_ssa_current_fn
    (current_wf_probe_supply current_wf_probe_fork) current_wf_probe_fork)).fn_blocks).
    bb_instructions =
  [current_probe_inst 20 PHI
    [Label "E"; Var "a"; Label "D"; Var "b"; Label "F"; Var "c"] ["formal_var_0"];
   current_probe_inst 2 ASSIGN [Var "formal_var_0"] ["v"];
   current_probe_inst 3 JNZ [Var "formal_var_0"; Label "D"; Label "F"] []]
Proof
  EVAL_TAC
QED

Theorem current_wf_probe_nested_structural:
  wf_function current_wf_probe_nested /\ fn_inst_wf current_wf_probe_nested /\
  first_block_no_preds current_wf_probe_nested /\ first_block_no_phi current_wf_probe_nested /\
  ir_supply_covers_fn (current_wf_probe_supply current_wf_probe_nested) current_wf_probe_nested /\
  ir_supply_inst_ok (current_wf_probe_supply current_wf_probe_nested)
Proof
  EVAL_TAC
QED

Theorem current_wf_probe_nested_final:
  wf_ssa (FST (make_ssa_current_fn (current_wf_probe_supply current_wf_probe_nested)
    current_wf_probe_nested))
Proof
  rewrite_tac[wf_ssa_def] >> EVAL_TAC
QED

Theorem current_wf_probe_nested_shape:
  MAP (\bb. (bb.bb_label, MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs))
     bb.bb_instructions))
    (FST (make_ssa_current_fn (current_wf_probe_supply current_wf_probe_nested)
       current_wf_probe_nested)).fn_blocks =
  [("E",[(ASSIGN,[Lit 1w],["a"]); (JMP,[Label "H"],[])]);
   ("H",[(PHI,[Label "E"; Var "a"; Label "F"; Var "b"],["formal_var_0"]);
         (ASSIGN,[Var "formal_var_0"],["v"]); (JMP,[Label "J"],[])]);
   ("J",[(PHI,[Label "H"; Var "formal_var_0"; Label "D"; Var "c"],["formal_var_1"]);
         (ASSIGN,[Var "formal_var_1"],["w"]);
         (JNZ,[Var "formal_var_1"; Label "D"; Label "F"],[])]);
   ("D",[(ASSIGN,[Lit 2w],["c"]); (JMP,[Label "J"],[])]);
   ("F",[(ASSIGN,[Lit 3w],["b"]); (JNZ,[Var "formal_var_1"; Label "H"; Label "X"],[])]);
   ("X",[(ASSIGN,[Var "formal_var_0"],["z"]); (STOP,[],[])])]
Proof
  EVAL_TAC
QED

Theorem current_wf_probe_phi_contract:
  !fn. MEM fn [current_wf_probe_fork; current_wf_probe_nested] ==>
  fn_phi_operands_single_def fn /\ fn_phis_cover_preds fn /\
  fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = PHI ==>
     ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
     !l v. MEM (l,v) (phi_pairs inst.inst_operands) ==>
       fn_cfg_edge fn l bb.bb_label)
Proof
  simp[fn_phi_operands_single_def_def, fn_phis_cover_preds_def,
       fn_phi_outputs_single_def_def, fn_phis_non_degenerate_def,
       current_wf_probe_fork_def, current_wf_probe_nested_def,
       mk_raw_function_def, fn_insts_def, fn_cfg_edge_def,
       current_probe_inst_def, phi_pairs_def] >>
  rpt strip_tac >> gvs[phi_pairs_def] >>
  rule_assum_tac (CONV_RULE EVAL) >> gvs[] >>
  EVAL_TAC >>
  simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC
QED

Theorem current_wf_probe_input_ssa:
  wf_ssa current_wf_probe_fork /\ wf_ssa current_wf_probe_nested
Proof
  rewrite_tac[wf_ssa_def] >> EVAL_TAC
QED

Theorem current_wf_probe_input_definite_assignment:
  fn_defs_reach_uses current_wf_probe_fork /\
  fn_defs_reach_uses current_wf_probe_nested
Proof
  conj_tac >> irule wf_ssa_defs_reach_uses_distinct >>
  metis_tac[current_wf_probe_input_ssa, current_wf_probe_fork_structural,
            current_wf_probe_nested_structural, wf_function_def]
QED

Theorem current_wf_probe_input_reachable:
  all_reachable current_wf_probe_fork /\ all_reachable current_wf_probe_nested
Proof
  conj_tac >>
  simp[all_reachable_def, fn_reachable_cfg_analyze,
       current_wf_probe_fork_structural, current_wf_probe_nested_structural] >>
  EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

(* Negative control for self-only deletion.  The non-degeneracy premise
   excludes this input; it must not be reported as a task counterexample. *)
Definition current_wf_probe_self_only_def:
  current_wf_probe_self_only = mk_raw_function "self_only"
    [<| bb_label := "E"; bb_instructions :=
        [current_probe_inst 0 JMP [Label "H"] []] |>;
     <| bb_label := "H"; bb_instructions :=
        [current_probe_inst 1 PHI
          [Label "E"; Var "v"; Label "H"; Var "v"] ["v"];
         current_probe_inst 2 JNZ [Var "v"; Label "H"; Label "X"] []] |>;
     <| bb_label := "X"; bb_instructions :=
        [current_probe_inst 3 ASSIGN [Var "v"] ["z"];
         current_probe_inst 4 STOP [] []] |>]
End

Theorem current_wf_probe_self_only_rejected:
  ~fn_phis_non_degenerate current_wf_probe_self_only
Proof
  simp[fn_phis_non_degenerate_def, current_wf_probe_self_only_def,
       mk_raw_function_def, fn_insts_def, current_probe_inst_def,
       phi_pairs_def] >>
  qexistsl [`current_probe_inst 1 PHI
    [Label "E"; Var "v"; Label "H"; Var "v"] ["v"]`, `"v"`] >>
  simp[current_probe_inst_def, phi_pairs_def] >> EVAL_TAC >> metis_tac[]
QED

Theorem current_wf_probe_self_only_shape:
  MAP (\bb. (bb.bb_label, MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs))
     bb.bb_instructions))
    (FST (make_ssa_current_fn (current_wf_probe_supply current_wf_probe_self_only)
       current_wf_probe_self_only)).fn_blocks =
  [("E",[(JMP,[Label "H"],[])]);
   ("H",[(ASSIGN,[Var "formal_var_0"],["v"]);
         (ASSIGN,[Var "v"],["formal_var_0"]);
         (JNZ,[Var "formal_var_0"; Label "H"; Label "X"],[])]);
   ("X",[(ASSIGN,[Var "formal_var_0"],["z"]); (STOP,[],[])])]
Proof
  EVAL_TAC
QED

Theorem make_ssa_current_fn_wf_ssa:
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  fn_phis_cover_preds fn /\
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = PHI ==>
     ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
     !l v. MEM (l,v) (phi_pairs inst.inst_operands) ==>
       fn_cfg_edge fn l bb.bb_label) /\
  fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  wf_ssa fn'
Proof
  strip_tac >> rewrite_tac[wf_ssa_def] >> conj_tac
  >- (irule current_wf_run_ssa_form >> metis_tac[]) >>
  Cases_on `entry_block fn`
  >- (gvs[entry_block_def, fn_entry_label_def, make_ssa_current_fn_def,
          def_dominates_uses_def, NULL_EQ]) >>
  drule_all current_wf_named_structural_certificate >> strip_tac >>
  qpat_x_assum `current_structural_certificate _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[current_wf_precleanup_certificate_stages] >> strip_tac >>
  `current_wf_phi_context s fn renamed s' A H events` by
    (irule current_wf_phi_context_intro >> asm_rewrite_tac[]) >>
  Cases_on `blocks_have_leading_phi fn.fn_blocks` >>
  gvs[simplify_current_phis_if_def]
  >- (irule current_wf_phi_context_cleanup_dominates >> simp[current_cleanup_phis_map] >> metis_tac[]) >>
  irule current_wf_phi_context_no_cleanup_dominates >> metis_tac[]
QED
