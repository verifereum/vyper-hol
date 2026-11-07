(*
 * Static facts about a lineage state (fnPlanLineage): the planner state a
 * run-time path reaches at a block's entry.  The block-entry prefix lemmas
 * (fnFrameSteps$phi_prefix_frame_sim, fnFrameSinglePred) and the block
 * body (fnBlockBody) need them of the state they start from.
 *
 * TOP-LEVEL:
 *   lineage_state_static - the state is well formed (repeated
 *                          dead_stack_marker slots allowed), and nothing on
 *                          its stack or in its spill map but the block's
 *                          PHI sources stands for a variable the block
 *                          defines (nothing at all with one predecessor);
 *                          it holds every live-in variable but the PHI
 *                          operands, and one source of each PHI
 *)

Theory fnLineageStatic
Ancestors
  fnPlanLineageJoin fnLineageInv fnLiveDefDom fnPlanPrefix fnPlanLineage
  stackPlanGen stackPlanTypes livenessDefs dfgDefs
  codegenReadyCompute venomExecProofs venomWf venomExecProps venomInst
  relation list finite_map dominatorProofs cfgAnalysisProps
  removeUnusedSsaProofs cfgNormBase livenessProofs livenessTransferProofs
  fnFrameStepsRevertForward dominatorAnalysisProps dfgAnalysisProps

Theorem lineage_state_entry_cases[local]:
  lineage_state liveness dfg cfg fn ps0 lbl ps ==>
  (fn_entry_label fn = SOME lbl /\ ps = ps0) \/
  (?pred. lineage_entry liveness dfg cfg fn ps0 pred lbl ps)
Proof
  simp[Once lineage_state_cases, lineage_entry_def] >> metis_tac[]
QED

Theorem lineage_state_reachable[local]:
  !liveness dfg cfg fn ps0 lbl ps.
    lineage_state liveness dfg cfg fn ps0 lbl ps ==>
    cfg = cfg_analyze fn /\ codegen_ready_fn fn ==>
    fn_reachable fn lbl
Proof
  rpt gen_tac >> qid_spec_tac `ps` >> qid_spec_tac `lbl` >>
  ho_match_mp_tac lineage_state_ind >> rpt strip_tac
  >- (simp[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL])
  >> irule fn_reachable_step >> qexists_tac `lbl` >>
  gvs[codegen_ready_fn_def] >>
  metis_tac[fn_cfg_edge_cfg_analyze]
QED

Theorem lineage_entry_edge[local]:
  lineage_entry liveness dfg (cfg_analyze fn) fn ps0 pred succ ps /\
  codegen_ready_fn fn ==>
  (?bb. lookup_block pred fn.fn_blocks = SOME bb) /\
  fn_cfg_edge fn pred succ /\ fn_reachable fn pred /\
  fn_reachable fn succ
Proof
  strip_tac >>
  `fn_reachable fn succ` by
    metis_tac[lineage_entry_lineage_state, lineage_state_reachable] >>
  gvs[lineage_entry_def] >>
  `fn_reachable fn pred` by metis_tac[lineage_state_reachable] >>
  gvs[codegen_ready_fn_def] >>
  metis_tac[fn_cfg_edge_cfg_analyze]
QED

Theorem ready_small_preds_no_phis[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <= 1 ==>
  collect_phis bb.bb_instructions = []
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  gvs[codegen_ready_fn_def, phis_at_joins_def, EVERY_MEM] >>
  metis_tac[NULL_EQ]
QED

Theorem ready_entry_no_phis[local]:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  collect_phis bb.bb_instructions = []
Proof
  strip_tac >>
  `?eb. entry_block fn = SOME eb /\ eb.bb_label = lbl` by
    gvs[fn_entry_label_def, AllCaseEqs()] >>
  `MEM eb fn.fn_blocks` by
    (gvs[entry_block_def, AllCaseEqs()] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  `ALL_DISTINCT (fn_labels fn)` by
    gvs[codegen_ready_fn_def, wf_function_def] >>
  `lookup_block lbl fn.fn_blocks = SOME eb` by
    metis_tac[MEM_lookup_block, fn_labels_def] >>
  gvs[codegen_ready_fn_def, block_entries_ready_def, NULL_EQ]
QED

Theorem initial_cleanup_empty[local]:
  (init_cleanup_plan_state ch growth spill_base lbl_ctr).ps_stack = [] /\
  (init_cleanup_plan_state ch growth spill_base lbl_ctr).ps_spilled = FEMPTY
Proof
  simp[init_cleanup_plan_state_def, init_plan_state_def]
QED

Theorem dominates_entry_label:
  fn_entry_label fn = SOME entry /\ fn_dominates fn dom entry ==>
  dom = entry
Proof
  rw[fn_dominates_def] >>
  first_x_assum (qspec_then `[entry]` mp_tac) >>
  simp[is_fn_path_def]
QED

Theorem ready_entry_no_preds[local]:
  codegen_ready_fn fn /\ entry_block fn = SOME eb ==>
  cfg_preds_of (cfg_analyze fn) eb.bb_label = []
Proof
  strip_tac >> gvs[codegen_ready_fn_def, block_entries_ready_def, NULL_EQ]
QED

Theorem small_preds_not_dominates_pred[local]:
  codegen_ready_fn fn /\ fn_reachable fn pred /\
  fn_cfg_edge fn pred succ /\
  LENGTH (cfg_preds_of (cfg_analyze fn) succ) <= 1 ==>
  ~fn_dominates fn succ pred
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `?eb. entry_block fn = SOME eb` by
    (gvs[wf_function_def, fn_has_entry_def, entry_block_def] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) succ)` by
    metis_tac[fn_cfg_edge_cfg_analyze, cfg_edge_symmetry_uncond] >>
  `succ <> eb.bb_label` by metis_tac[ready_entry_no_preds, MEM] >>
  `cfg_reachable_of (cfg_analyze fn) succ` by
    metis_tac[fn_reachable_step, fn_reachable_cfg_analyze] >>
  drule_all exists_pred_not_dominated >>
  disch_then (qx_choose_then `other` strip_assume_tac) >>
  `other = pred` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) succ` >> gvs[] >>
     rename1 `SUC (LENGTH rest) <= 1` >> Cases_on `rest` >> gvs[]) >>
  metis_tac[fn_dominates_cfg_analyze]
QED

Theorem dominating_def_excludes_outputs[local]:
  codegen_ready_fn fn /\
  MEM def_bb fn.fn_blocks /\ MEM inst def_bb.bb_instructions /\
  MEM v inst.inst_outputs /\ fn_dominates fn def_bb.bb_label pred /\
  MEM target fn.fn_blocks /\ ~fn_dominates fn target.bb_label pred ==>
  ~MEM v (FLAT (MAP (\i. i.inst_outputs) target.bb_instructions))
Proof
  strip_tac >> strip_tac >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  metis_tac[ssa_unique_output_block]
QED

Theorem strict_dominating_def_excludes_outputs[local]:
  codegen_ready_fn fn /\
  MEM def_bb fn.fn_blocks /\ MEM inst def_bb.bb_instructions /\
  MEM v inst.inst_outputs /\ fn_dominates fn def_bb.bb_label target.bb_label /\
  def_bb.bb_label <> target.bb_label /\ MEM target fn.fn_blocks ==>
  ~MEM v (FLAT (MAP (\i. i.inst_outputs) target.bb_instructions))
Proof
  strip_tac >> strip_tac >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  metis_tac[ssa_unique_output_block]
QED

Theorem ready_dominates_trans[local]:
  codegen_ready_fn fn /\ fn_dominates fn a b /\ fn_dominates fn b c ==>
  fn_dominates fn a c
Proof
  strip_tac >> `wf_function fn` by gvs[codegen_ready_fn_def] >>
  gvs[fn_dominates_cfg_analyze] >> metis_tac[dominates_trans]
QED

Theorem ready_dominates_antisym[local]:
  codegen_ready_fn fn /\ fn_dominates fn a b /\ fn_dominates fn b a ==>
  a = b
Proof
  strip_tac >> `wf_function fn` by gvs[codegen_ready_fn_def] >>
  gvs[fn_dominates_cfg_analyze] >> metis_tac[dominates_antisym]
QED

Theorem normalize_marker_not_var[local]:
  normalize_operand dfg visited dead_stack_marker <> Var v
Proof
  simp[dead_stack_marker_def, normalize_operand_def]
QED

Theorem normalize_var_invariant[local]:
  !P dfg visited op.
  (!u inst w. FLOOKUP dfg.dfg_defs u = SOME inst /\
     inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var w] /\ P u ==> P w) ==>
  !v.
    (case op of Var u => P u | _ => F) /\
    normalize_operand dfg visited op = Var v ==> P v
Proof
  gen_tac >> recInduct normalize_operand_ind >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >> gen_tac >>
      simp[NoAsms] >> strip_tac >>
      rename1 `normalize_operand dfg visited (Var src) = Var dst` >>
      qpat_x_assum `normalize_operand _ _ _ = _` mp_tac >>
      pure_once_rewrite_tac[normalize_operand_def] >>
      Cases_on `MEM src visited`
      >- (simp[NoAsms] >> strip_tac >> gvs[]) >>
      qpat_assum `~MEM src visited` (fn th => simp[NoAsms, th]) >>
      Cases_on `FLOOKUP dfg.dfg_defs src`
      >- (qpat_assum `FLOOKUP _ _ = NONE` (fn th => simp[NoAsms, th]) >>
          strip_tac >> gvs[]) >>
      rename1 `FLOOKUP dfg.dfg_defs src = SOME inst` >>
      qpat_assum `FLOOKUP _ _ = SOME inst` (fn th => simp[NoAsms, th]) >>
      Cases_on `inst.inst_opcode = ASSIGN`
      >- (qpat_assum `inst.inst_opcode = ASSIGN` (fn th => simp[NoAsms, th]) >>
          Cases_on `inst.inst_operands`
          >- (qpat_assum `inst.inst_operands = []` (fn th => simp[NoAsms, th]) >>
              strip_tac >> gvs[]) >>
          rename1 `inst.inst_operands = operand::rest` >>
          Cases_on `rest`
          >- (qpat_assum `inst.inst_operands = [operand]`
                (fn th => simp[NoAsms, th]) >>
              qpat_x_assum `!a b c. _ ==> _ ==> _`
                (qspecl_then [`inst`, `operand`, `[]`] mp_tac) >>
              (impl_tac >- simp[]) >>
              (impl_tac >- first_assum ACCEPT_TAC) >>
              Cases_on `operand`
              >- simp[normalize_operand_def]
              >- (rename1 `inst.inst_operands = [Var source]` >>
                  `P source` by metis_tac[] >> simp[]) >>
              simp[normalize_operand_def]) >>
          qpat_assum `inst.inst_operands = _::_::_`
            (fn th => simp[NoAsms, th]) >> strip_tac >> gvs[]) >>
      qpat_assum `inst.inst_opcode <> ASSIGN` (fn th => simp[NoAsms, th]) >>
      strip_tac >> gvs[]) >>
  simp[NoAsms]
QED

Theorem ready_assign_source_def[local]:
  codegen_ready_fn fn /\ MEM db fn.fn_blocks /\ MEM def db.bb_instructions /\
  MEM u def.inst_outputs /\
  FLOOKUP (dfg_build_function fn).dfg_defs u = SOME inst /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var w] ==>
  ?source_bb source_inst.
    MEM source_bb fn.fn_blocks /\ MEM source_inst source_bb.bb_instructions /\
    MEM w source_inst.inst_outputs /\
    fn_dominates fn source_bb.bb_label db.bb_label
Proof
  strip_tac >>
  `ssa_form fn /\ def_dominates_uses fn` by gvs[codegen_ready_fn_def] >>
  `MEM def (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `dfg_get_def (dfg_build_function fn) u = SOME def` by
    metis_tac[dfg_build_function_ssa_def] >>
  `def = inst` by gvs[dfg_get_def_def] >>
  `def_available_at fn db (SOME inst) w` by
    (gvs[def_dominates_uses_def] >>
     first_x_assum (qspecl_then [`db`, `def`] mp_tac) >> simp[]) >>
  gvs[def_available_at_def] >> metis_tac[]
QED

Theorem normalize_dominating_def[local]:
  codegen_ready_fn fn /\
  MEM db fn.fn_blocks /\ MEM inst db.bb_instructions /\ MEM u inst.inst_outputs /\
  fn_dominates fn db.bb_label target /\
  normalize_operand (dfg_build_function fn) visited (Var u) = Var v ==>
  ?vb vi. MEM vb fn.fn_blocks /\ MEM vi vb.bb_instructions /\
    MEM v vi.inst_outputs /\ fn_dominates fn vb.bb_label target
Proof
  strip_tac >>
  mp_tac (normalize_var_invariant |> Q.SPEC
    `\x. ?vb vi. MEM vb fn.fn_blocks /\ MEM vi vb.bb_instructions /\
       MEM x vi.inst_outputs /\ fn_dominates fn vb.bb_label target` |>
    Q.SPEC `dfg_build_function fn` |> Q.SPEC `visited` |> Q.SPEC `Var u`) >>
  (impl_tac >-
    (simp[NoAsms] >> rpt strip_tac >> drule_all ready_assign_source_def >> strip_tac >>
     metis_tac[ready_dominates_trans])) >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem normalize_strict_dominating_def[local]:
  codegen_ready_fn fn /\
  MEM db fn.fn_blocks /\ MEM inst db.bb_instructions /\ MEM u inst.inst_outputs /\
  fn_dominates fn db.bb_label target /\ db.bb_label <> target /\
  normalize_operand (dfg_build_function fn) visited (Var u) = Var v ==>
  ?vb vi. MEM vb fn.fn_blocks /\ MEM vi vb.bb_instructions /\
    MEM v vi.inst_outputs /\ fn_dominates fn vb.bb_label target /\
    vb.bb_label <> target
Proof
  strip_tac >>
  mp_tac (normalize_var_invariant |> Q.SPEC
    `\x. ?vb vi. MEM vb fn.fn_blocks /\ MEM vi vb.bb_instructions /\
       MEM x vi.inst_outputs /\ fn_dominates fn vb.bb_label target /\
       vb.bb_label <> target` |>
    Q.SPEC `dfg_build_function fn` |> Q.SPEC `visited` |> Q.SPEC `Var u`) >>
  (impl_tac >-
    (simp[NoAsms] >> rpt strip_tac >>
     drule_all ready_assign_source_def >> strip_tac >>
     metis_tac[ready_dominates_trans, ready_dominates_antisym])) >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem collect_phis_idempotent[local]:
  !instrs. collect_phis (collect_phis instrs) = collect_phis instrs
Proof
  Induct >> simp[collect_phis_def] >> gen_tac >>
  IF_CASES_TAC >> simp[collect_phis_def]
QED

Theorem phi_pair_updates_lookup:
  !pairs m idx v.
    FLOOKUP (FOLDL (\m (lbl,w). m |+ (w,idx)) m pairs) v =
    if MEM v (MAP SND pairs) then SOME idx else FLOOKUP m v
Proof
  Induct >> simp[] >> Cases >> rpt gen_tac >>
  simp[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem phi_owner_cons_witness[local]:
  !i p xs v owner.
    (MEM v (MAP SND (phi_pairs p.inst_operands)) ==> i = owner) ==>
    ((?q. MEM (owner,q) ((i,p)::xs) /\
           MEM v (MAP SND (phi_pairs q.inst_operands))) <=>
     (MEM v (MAP SND (phi_pairs p.inst_operands)) \/
      ?q. MEM (owner,q) xs /\ MEM v (MAP SND (phi_pairs q.inst_operands))))
Proof
  rpt gen_tac >> strip_tac >> simp[MEM, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  metis_tac[]
QED

Theorem indexed_phi_owner_lookup[local]:
  !indexed om mt pred v owner.
    (!idx phi. MEM (idx,phi) indexed /\
      MEM v (MAP SND (phi_pairs phi.inst_operands)) ==> idx = owner) ==>
    FLOOKUP (FST (FOLDL (\(om,mt) (idx,phi).
      (FOLDL (\m (lbl,w). m |+ (w,idx)) om (phi_pairs phi.inst_operands),
       case FIND (\(lbl,w). lbl = pred) (phi_pairs phi.inst_operands) of
         NONE => mt | SOME (lbl,w) => mt |+ (idx,w))) (om,mt) indexed)) v =
    if (?phi. MEM (owner,phi) indexed /\
          MEM v (MAP SND (phi_pairs phi.inst_operands)))
    then SOME owner else FLOOKUP om v
Proof
  Induct >- simp[] >>
  qx_gen_tac `head_pair` >>
  namedCases_on `head_pair` ["head_idx head_phi"] >>
  rpt gen_tac >> strip_tac >>
  `MEM v (MAP SND (phi_pairs head_phi.inst_operands)) ==> head_idx = owner`
    by metis_tac[MEM] >>
  drule phi_owner_cons_witness >>
  disch_then (qspecl_then [`indexed`] (fn th => pure_rewrite_tac[th])) >>
  `!idx phi. MEM (idx,phi) indexed /\
     MEM v (MAP SND (phi_pairs phi.inst_operands)) ==> idx = owner`
    by metis_tac[MEM] >>
  qpat_x_assum `!om mt pred v owner. _` drule >>
  simp[NoAsms, FOLDL] >>
  Cases_on `FIND (\(lbl,w). lbl = pred) (phi_pairs head_phi.inst_operands)`
  >- (simp[] >> strip_tac >>
      qpat_x_assum `!om mt pred. _` kall_tac >>
      Cases_on `MEM v (MAP SND (phi_pairs head_phi.inst_operands))` >>
      simp[phi_pair_updates_lookup] >>
      Cases_on `?phi. MEM (owner,phi) indexed /\
        MEM v (MAP SND (phi_pairs phi.inst_operands))` >> simp[]) >>
  rename1 `FIND _ _ = SOME selected` >> PairCases_on `selected` >>
  simp[] >> strip_tac >> qpat_x_assum `!om mt pred. _` kall_tac >>
  Cases_on `MEM v (MAP SND (phi_pairs head_phi.inst_operands))` >>
  simp[phi_pair_updates_lookup] >>
  Cases_on `?phi. MEM (owner,phi) indexed /\
    MEM v (MAP SND (phi_pairs phi.inst_operands))` >> simp[]
QED

Theorem build_phi_owner_at[local]:
  (!j phi. MEM (j,phi) (MAPi (\k p. (k,p)) phis) /\
    MEM v (MAP SND (phi_pairs phi.inst_operands)) ==> j = owner) ==>
  FLOOKUP (FST (build_phi_maps pred phis)) v =
    if owner < LENGTH phis /\
       MEM v (MAP SND (phi_pairs (EL owner phis).inst_operands))
    then SOME owner else NONE
Proof
  strip_tac >>
  drule indexed_phi_owner_lookup >>
  disch_then (qspecl_then [`FEMPTY`, `FEMPTY`, `pred`] mp_tac) >>
  simp[build_phi_maps_def, indexedListsTheory.MEM_MAPi]
QED

Theorem build_phi_owner_lookup[local]:
  (!i j v. i < LENGTH phis /\ j < LENGTH phis /\
    MEM v (MAP SND (phi_pairs (EL i phis).inst_operands)) /\
    MEM v (MAP SND (phi_pairs (EL j phis).inst_operands)) ==> i = j) ==>
  (FLOOKUP (FST (build_phi_maps pred phis)) v = SOME i <=>
   i < LENGTH phis /\
   MEM v (MAP SND (phi_pairs (EL i phis).inst_operands)))
Proof
  strip_tac >>
  Cases_on `?j. j < LENGTH phis /\
    MEM v (MAP SND (phi_pairs (EL j phis).inst_operands))`
  >- (pop_assum (qx_choose_then `owner` strip_assume_tac) >>
      `!j phi. MEM (j,phi) (MAPi (\k p. (k,p)) phis) /\
        MEM v (MAP SND (phi_pairs phi.inst_operands)) ==> j = owner`
        by (simp[indexedListsTheory.MEM_MAPi] >> metis_tac[]) >>
      drule build_phi_owner_at >> disch_then (qspec_then `pred` mp_tac) >>
      simp[] >> metis_tac[]) >>
  `!j phi. MEM (j,phi) (MAPi (\k p. (k,p)) phis) /\
    MEM v (MAP SND (phi_pairs phi.inst_operands)) ==> j = i`
    by (simp[indexedListsTheory.MEM_MAPi] >> metis_tac[]) >>
  drule build_phi_owner_at >> disch_then (qspec_then `pred` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem indexed_phi_selected_absent[local]:
  !indexed om mt pred i.
    ~MEM i (MAP FST indexed) ==>
    FLOOKUP (SND (FOLDL (\(om,mt) (idx,phi).
      (FOLDL (\m (lbl,w). m |+ (w,idx)) om (phi_pairs phi.inst_operands),
       case FIND (\(lbl,w). lbl = pred) (phi_pairs phi.inst_operands) of
         NONE => mt | SOME (lbl,w) => mt |+ (idx,w))) (om,mt) indexed)) i =
    FLOOKUP mt i
Proof
  Induct >- simp[] >>
  qx_gen_tac `head_pair` >>
  namedCases_on `head_pair` ["idx phi"] >>
  rpt gen_tac >> simp[] >> strip_tac >>
  simp[FOLDL] >>
  Cases_on `FIND (\(lbl,w). lbl = pred) (phi_pairs phi.inst_operands)`
  >- (simp[] >> first_x_assum irule >> simp[]) >>
  rename1 `FIND _ _ = SOME selected` >> PairCases_on `selected` >>
  simp[] >> first_x_assum (drule o SPEC_ALL) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem indexed_phi_selected_member[local]:
  !indexed om mt pred i phi.
    ALL_DISTINCT (MAP FST indexed) /\ MEM (i,phi) indexed ==>
    FLOOKUP (SND (FOLDL (\(om,mt) (idx,p).
      (FOLDL (\m (lbl,w). m |+ (w,idx)) om (phi_pairs p.inst_operands),
       case FIND (\(lbl,w). lbl = pred) (phi_pairs p.inst_operands) of
         NONE => mt | SOME (lbl,w) => mt |+ (idx,w))) (om,mt) indexed)) i =
    case FIND (\(lbl,w). lbl = pred) (phi_pairs phi.inst_operands) of
      NONE => FLOOKUP mt i | SOME (lbl,w) => SOME w
Proof
  Induct >- simp[] >>
  qx_gen_tac `head_pair` >>
  namedCases_on `head_pair` ["idx head_phi"] >>
  rpt gen_tac >> simp[] >> disch_tac >>
  `~MEM idx (MAP FST indexed) /\ ALL_DISTINCT (MAP FST indexed)`
    by metis_tac[] >>
  Cases_on `i = idx`
  >- (`phi = head_phi` by (gvs[] >> metis_tac[MEM_MAP, pairTheory.FST]) >>
      gvs[] >> simp[FOLDL] >>
      Cases_on `FIND (\(lbl,w). lbl = pred) (phi_pairs head_phi.inst_operands)`
      >- (simp[] >> irule indexed_phi_selected_absent >> simp[]) >>
      rename1 `FIND _ _ = SOME selected` >> PairCases_on `selected` >>
      simp[indexed_phi_selected_absent, FLOOKUP_UPDATE]) >>
  `MEM (i,phi) indexed` by gvs[] >>
  simp[FOLDL] >>
  Cases_on `FIND (\(lbl,w). lbl = pred) (phi_pairs head_phi.inst_operands)`
  >- (simp[] >> first_x_assum irule >> simp[]) >>
  rename1 `FIND _ _ = SOME selected` >> PairCases_on `selected` >>
  simp[] >>
  qpat_x_assum `!om mt pred i phi. _` (fn th => drule_all th) >>
  disch_then (fn th => rewrite_tac[th]) >> simp[FLOOKUP_UPDATE]
QED

Theorem build_phi_selected_lookup[local]:
  i < LENGTH phis ==>
  FLOOKUP (SND (build_phi_maps pred phis)) i =
    OPTION_MAP SND
      (FIND (\pair. FST pair = pred) (phi_pairs (EL i phis).inst_operands))
Proof
  strip_tac >>
  `MAP FST (MAPi (\k p. (k,p)) phis) = GENLIST I (LENGTH phis)` by
    (irule LIST_EQ >> simp[indexedListsTheory.LENGTH_MAPi,
      indexedListsTheory.EL_MAPi, EL_MAP]) >>
  `ALL_DISTINCT (MAP FST (MAPi (\k p. (k,p)) phis))` by
    simp[ALL_DISTINCT_GENLIST] >>
  `MEM (i, EL i phis) (MAPi (\k p. (k,p)) phis)` by
    simp[indexedListsTheory.MEM_MAPi] >>
  drule_all indexed_phi_selected_member >>
  disch_then (qspecl_then [`FEMPTY`, `FEMPTY`, `pred`] mp_tac) >>
  simp[build_phi_maps_def] >>
  Cases_on `FIND (\(lbl,w). lbl = pred) (phi_pairs (EL i phis).inst_operands)`
  >- simp[pairTheory.LAMBDA_PROD] >>
  rename1 `FIND _ _ = SOME selected` >> PairCases_on `selected` >>
  simp[pairTheory.LAMBDA_PROD]
QED

Definition phi_place_run_def:
  phi_place_run om mt acc (placed:num list) (xs:string list) =
    FOLDL (\(acc,placed) w.
      case FLOOKUP om w of
        SOME idx => if MEM idx placed then (acc,placed)
          else (case FLOOKUP mt idx of
            SOME src => (acc ++ [src],idx::placed) | NONE => (acc,placed))
      | NONE => (acc ++ [w],placed)) (acc,placed) xs
End

Theorem phi_place_run_mem[local]:
  !xs om mt acc placed v.
    MEM v (FST (phi_place_run om mt acc placed xs)) <=>
    MEM v acc \/ (MEM v xs /\ FLOOKUP om v = NONE) \/
    (?i w. MEM w xs /\ FLOOKUP om w = SOME i /\
      ~MEM i placed /\ FLOOKUP mt i = SOME v)
Proof
  Induct >- simp[phi_place_run_def] >>
  rpt gen_tac >>
  simp[Once phi_place_run_def, FOLDL] >>
  Cases_on `FLOOKUP om h`
  >- (simp[GSYM phi_place_run_def] >>
      qpat_x_assum `!om mt acc placed v. _` kall_tac >>
      simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
      Cases_on `v = h` >> gvs[] >> metis_tac[]) >>
  rename1 `FLOOKUP om h = SOME idx` >>
  Cases_on `MEM idx placed`
  >- (simp[GSYM phi_place_run_def] >>
      qpat_x_assum `!om mt acc placed v. _` kall_tac >>
      simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
      Cases_on `v = h` >> gvs[] >> metis_tac[]) >>
  Cases_on `FLOOKUP mt idx`
  >- (simp[GSYM phi_place_run_def] >>
      qpat_x_assum `!om mt acc placed v. _` kall_tac >>
      simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
      Cases_on `v = h` >> gvs[] >> metis_tac[]) >>
  rename1 `FLOOKUP mt idx = SOME chosen` >>
  simp[GSYM phi_place_run_def, MEM_APPEND] >>
  qpat_x_assum `!om mt acc placed v. _` kall_tac >>
  simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  Cases_on `v = chosen` >> gvs[] >>
  Cases_on `v = h` >> gvs[] >> metis_tac[optionTheory.SOME_11]
QED

Theorem input_vars_placement_mem[local]:
  ~NULL (collect_phis instrs) ==>
  (MEM v (input_vars_from pred instrs live) <=>
   (MEM v live /\ FLOOKUP (FST (build_phi_maps pred (collect_phis instrs))) v = NONE) \/
   ?i w. MEM w live /\
     FLOOKUP (FST (build_phi_maps pred (collect_phis instrs))) w = SOME i /\
     FLOOKUP (SND (build_phi_maps pred (collect_phis instrs))) i = SOME v)
Proof
  strip_tac >>
  Cases_on `build_phi_maps pred (collect_phis instrs)` >>
  simp[input_vars_from_def, GSYM phi_place_run_def,
       pairTheory.LAMBDA_PROD] >>
  pairarg_tac >> gvs[] >>
  rename1 `phi_place_run om mt [] [] live = (result,placed)` >>
  qspec_then `live` mp_tac phi_place_run_mem >>
  disch_then (qspecl_then [`om`, `mt`, `[]`, `[]`, `v`] mp_tac) >> simp[]
QED

Theorem phi_selected_exists[local]:
  !pairs pred. (?v. MEM (pred,v) pairs) ==>
    ?v. FIND (\pair. FST pair = pred) pairs = SOME (pred,v) /\
        MEM (pred,v) pairs
Proof
  Induct >- simp[] >> Cases >> rpt gen_tac >>
  simp[FIND_thm] >> strip_tac >> IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem input_vars_phi_exactly_one[local]:
  (!i j v. i < LENGTH (collect_phis instrs) /\ j < LENGTH (collect_phis instrs) /\
    MEM v (MAP SND (phi_pairs (EL i (collect_phis instrs)).inst_operands)) /\
    MEM v (MAP SND (phi_pairs (EL j (collect_phis instrs)).inst_operands)) ==> i = j) /\
  (!phi v. MEM phi (collect_phis instrs) ==>
    (MEM (Var v) phi.inst_operands <=> MEM v (MAP SND (phi_pairs phi.inst_operands)))) /\
  (!phi. MEM phi (collect_phis instrs) ==> ?v. MEM (pred,v) (phi_pairs phi.inst_operands)) /\
  (!phi. MEM phi (collect_phis instrs) ==> ?v. MEM v live /\
    MEM v (MAP SND (phi_pairs phi.inst_operands))) ==>
  EVERY (\phi. ?!v. MEM (Var v) phi.inst_operands /\
    MEM v (input_vars_from pred instrs live)) (collect_phis instrs)
Proof
  strip_tac >> simp[EVERY_MEM] >> qx_gen_tac `phi` >> strip_tac >>
  `?i. i < LENGTH (collect_phis instrs) /\ phi = EL i (collect_phis instrs)`
    by metis_tac[MEM_EL] >>
  `?chosen. FIND (\pair. FST pair = pred) (phi_pairs phi.inst_operands) =
      SOME (pred,chosen) /\ MEM (pred,chosen) (phi_pairs phi.inst_operands)`
    by metis_tac[phi_selected_exists] >>
  `MEM chosen (MAP SND (phi_pairs phi.inst_operands))`
    by (simp[MEM_MAP] >> metis_tac[pairTheory.SND]) >>
  `FLOOKUP (SND (build_phi_maps pred (collect_phis instrs))) i = SOME chosen`
    by (drule build_phi_selected_lookup >> disch_then (qspec_then `pred` mp_tac) >>
        qpat_x_assum `phi = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `!v j. FLOOKUP (FST (build_phi_maps pred (collect_phis instrs))) v = SOME j <=>
     j < LENGTH (collect_phis instrs) /\
     MEM v (MAP SND (phi_pairs (EL j (collect_phis instrs)).inst_operands))`
    by (rpt gen_tac >> match_mp_tac build_phi_owner_lookup >>
        first_assum ACCEPT_TAC) >>
  `?seed. MEM seed live /\ MEM seed (MAP SND (phi_pairs phi.inst_operands))`
    by metis_tac[] >>
  `~NULL (collect_phis instrs)` by (Cases_on `collect_phis instrs` >> gvs[]) >>
  `MEM chosen (input_vars_from pred instrs live)`
    by (drule input_vars_placement_mem >>
        disch_then (qspecl_then [`chosen`, `pred`, `live`] mp_tac) >>
        metis_tac[]) >>
  `!v. MEM (Var v) phi.inst_operands /\
       MEM v (input_vars_from pred instrs live) ==> v = chosen` suffices_by
    (simp[EXISTS_UNIQUE_THM] >> metis_tac[]) >>
  qx_gen_tac `v` >> strip_tac >>
  `MEM v (MAP SND (phi_pairs phi.inst_operands))` by metis_tac[] >>
  `FLOOKUP (FST (build_phi_maps pred (collect_phis instrs))) v = SOME i`
    by metis_tac[] >>
  drule_all input_vars_placement_mem >>
  disch_then (qspecl_then [`v`, `pred`, `live`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `j` (qx_choose_then `w` strip_assume_tac)) >>
  `j < LENGTH (collect_phis instrs)` by metis_tac[] >>
  drule build_phi_selected_lookup >> disch_then (qspec_then `pred` mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `FIND _ _ = SOME selected` >> PairCases_on `selected` >> gs[] >>
  drule venomExecPropsTheory.FIND_MEM >> strip_tac >>
  `MEM v (MAP SND (phi_pairs (EL j (collect_phis instrs)).inst_operands))`
    by (simp[MEM_MAP] >> metis_tac[pairTheory.SND]) >>
  `j = i` by metis_tac[] >> gvs[]
QED

Theorem ready_phi_edge_wf[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM phi (collect_phis bb.bb_instructions) ==>
  phi_edge_uses_wf fn bb phi
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  drule collect_phis_mem >> strip_tac >>
  gvs[codegen_ready_fn_def, def_dominates_uses_def] >> metis_tac[]
QED

Theorem ready_phi_var_pairs[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM phi (collect_phis bb.bb_instructions) ==>
  (MEM (Var v) phi.inst_operands <=>
   MEM v (MAP SND (phi_pairs phi.inst_operands)))
Proof
  strip_tac >> drule_all ready_phi_edge_wf >>
  simp[phi_edge_uses_wf_def] >> strip_tac >> eq_tac
  >- (strip_tac >> drule_all phi_well_formed_var_pair >>
      strip_tac >> simp[MEM_MAP] >> metis_tac[pairTheory.SND]) >>
  simp[MEM_MAP] >> strip_tac >>
  rename1 `MEM pair (phi_pairs phi.inst_operands)` >> PairCases_on `pair` >>
  gvs[] >> metis_tac[phi_pairs_mem_var]
QED

Theorem ready_phi_external_pred[local]:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM phi (collect_phis bb.bb_instructions) ==>
  ?p. fn_cfg_edge fn p lbl /\ ~fn_dominates fn lbl p
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `?eb. entry_block fn = SOME eb` by
    (gvs[wf_function_def, fn_has_entry_def, entry_block_def] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  `fn_entry_label fn = SOME eb.bb_label` by simp[fn_entry_label_def] >>
  `lbl <> eb.bb_label` by metis_tac[ready_entry_no_phis, MEM] >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by
    metis_tac[fn_reachable_cfg_analyze] >>
  drule_all exists_pred_not_dominated >>
  strip_tac >>
  metis_tac[fn_cfg_edge_cfg_analyze, cfg_edge_symmetry_uncond,
    fn_dominates_cfg_analyze]
QED

Theorem ready_phi_external_value[local]:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM phi (collect_phis bb.bb_instructions) ==>
  ?v. MEM (Var v) phi.inst_operands /\
    ~MEM v (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  strip_tac >> drule_all ready_phi_external_pred >>
  disch_then (qx_choose_then `p` strip_assume_tac) >>
  `bb.bb_label = lbl /\ MEM bb fn.fn_blocks` by
    metis_tac[lookup_block_label, lookup_block_MEM] >>
  drule_all ready_phi_edge_wf >>
  simp[phi_edge_uses_wf_def] >> strip_tac >>
  `?v. MEM (p,v) (phi_pairs phi.inst_operands)` by
    (qpat_x_assum `!pred. fn_cfg_edge _ _ _ <=> _`
       (qspec_then `p` mp_tac) >> simp[] >>
     disch_then (qx_choose_then `edge_pair` strip_assume_tac) >>
     PairCases_on `edge_pair` >> gvs[] >> metis_tac[]) >>
  rename1 `MEM (p,value) (phi_pairs phi.inst_operands)` >>
  qexists_tac `value` >>
  conj_tac >- metis_tac[phi_pairs_mem_var] >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = p /\
    def_available_at fn pb NONE value` by metis_tac[] >>
  gvs[def_available_at_def] >>
  irule dominating_def_excludes_outputs >> metis_tac[]
QED

Theorem ready_phi_live_seed[local]:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM phi (collect_phis bb.bb_instructions) ==>
  ?v. MEM (Var v) phi.inst_operands /\
    MEM v (live_vars_at (liveness_analyze fn) lbl 0)
Proof
  strip_tac >> drule_all ready_phi_external_value >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  qexists_tac `v` >> simp[] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[fn_reachable_in_cfg_dfs_pre] >>
  `MEM phi bb.bb_instructions` by metis_tac[collect_phis_mem] >>
  `?idx. idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = phi`
    by metis_tac[MEM_EL] >>
  `MEM v (inst_uses (EL idx bb.bb_instructions))` by
    metis_tac[operand_var_in_inst_uses] >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl idx)` by
    metis_tac[live_vars_at_uses] >>
  drule live_vars_at_propagate_range >> simp[] >> disch_then irule >> simp[] >>
  qexists_tac `idx` >> simp[] >>
  rpt strip_tac >>
  `MEM (EL k bb.bb_instructions) bb.bb_instructions` by
    (irule EL_MEM >> decide_tac) >>
  qpat_x_assum `~MEM v (FLAT _)` mp_tac >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[inst_defs_def]
QED

Theorem phi_disjoint_use_indices[local]:
  !phis i j v.
    phi_uses_disjoint phis /\ i < LENGTH phis /\ j < LENGTH phis /\
    MEM v (inst_uses (EL i phis)) /\ MEM v (inst_uses (EL j phis)) ==> i = j
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `i` >> Cases_on `j` >>
  gvs[phi_uses_disjoint_def, EVERY_MEM] >> metis_tac[EL_MEM]
QED

Theorem ready_phi_disjoint[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
  phi_uses_disjoint (collect_phis bb.bb_instructions)
Proof
  strip_tac >> `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `phi_operands_ready fn` by gvs[codegen_ready_fn_def] >>
  gvs[phi_operands_ready_def] >>
  Cases_on `EVERY (\bb. NULL (collect_phis bb.bb_instructions)) fn.fn_blocks`
  >- (gvs[EVERY_MEM, NULL_EQ] >> metis_tac[phi_uses_disjoint_def]) >>
  gvs[EVERY_MEM, phi_block_ready_def]
QED

Theorem ready_phi_pair_indices[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
  !i j v. i < LENGTH (collect_phis bb.bb_instructions) /\
    j < LENGTH (collect_phis bb.bb_instructions) /\
    MEM v (MAP SND (phi_pairs (EL i (collect_phis bb.bb_instructions)).inst_operands)) /\
    MEM v (MAP SND (phi_pairs (EL j (collect_phis bb.bb_instructions)).inst_operands))
    ==> i = j
Proof
  strip_tac >> drule_all ready_phi_disjoint >> strip_tac >> rpt strip_tac >>
  irule phi_disjoint_use_indices >>
  qexistsl_tac [`collect_phis bb.bb_instructions`, `v`] >> simp[] >>
  conj_tac >> irule operand_var_in_inst_uses >>
  gvs[MEM_MAP] >> metis_tac[phi_pairs_mem_var, pairTheory.PAIR]
QED

Theorem ready_phi_pred_pair[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM pred (cfg_preds_of (cfg_analyze fn) lbl) /\
  MEM phi (collect_phis bb.bb_instructions) ==>
  ?v. MEM (pred,v) (phi_pairs phi.inst_operands)
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  `fn_cfg_edge fn pred lbl` by
    metis_tac[fn_cfg_edge_cfg_analyze, cfg_edge_symmetry_uncond] >>
  drule_all ready_phi_edge_wf >> simp[phi_edge_uses_wf_def] >> strip_tac >>
  qpat_x_assum `!pred. fn_cfg_edge _ _ _ <=> _`
    (qspec_then `pred` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `edge_pair` strip_assume_tac) >>
  PairCases_on `edge_pair` >> gvs[] >> metis_tac[]
QED

Theorem ready_phi_input_hypotheses[local]:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM pred (cfg_preds_of (cfg_analyze fn) lbl) ==>
  (!i j v. i < LENGTH (collect_phis bb.bb_instructions) /\
    j < LENGTH (collect_phis bb.bb_instructions) /\
    MEM v (MAP SND (phi_pairs (EL i (collect_phis bb.bb_instructions)).inst_operands)) /\
    MEM v (MAP SND (phi_pairs (EL j (collect_phis bb.bb_instructions)).inst_operands))
    ==> i = j) /\
  (!phi v. MEM phi (collect_phis bb.bb_instructions) ==>
    (MEM (Var v) phi.inst_operands <=> MEM v (MAP SND (phi_pairs phi.inst_operands)))) /\
  (!phi. MEM phi (collect_phis bb.bb_instructions) ==>
    ?v. MEM (pred,v) (phi_pairs phi.inst_operands)) /\
  (!phi. MEM phi (collect_phis bb.bb_instructions) ==>
    ?v. MEM v (live_vars_at (liveness_analyze fn) lbl 0) /\
        MEM v (MAP SND (phi_pairs phi.inst_operands)))
Proof
  strip_tac >> conj_tac >- metis_tac[ready_phi_pair_indices] >>
  conj_tac >- metis_tac[ready_phi_var_pairs] >>
  conj_tac >- metis_tac[ready_phi_pred_pair] >>
  rpt strip_tac >> drule_all ready_phi_live_seed >> strip_tac >>
  metis_tac[ready_phi_var_pairs]
QED

Theorem ready_phi_input_exactly_one[local]:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM pred (cfg_preds_of (cfg_analyze fn) lbl) ==>
  EVERY (\phi. ?!v. MEM (Var v) phi.inst_operands /\
    MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0)))
    (collect_phis bb.bb_instructions)
Proof
  strip_tac >> drule_all ready_phi_input_hypotheses >> strip_tac >>
  irule input_vars_phi_exactly_one >> metis_tac[]
QED

Theorem input_vars_from_collect[local]:
  input_vars_from pred (collect_phis instrs) live =
  input_vars_from pred instrs live
Proof
  simp[input_vars_from_def, collect_phis_idempotent]
QED

Theorem input_vars_non_phi_iff[local]:
  ~MEM (Var v) (FLAT (MAP (\phi. phi.inst_operands)
                          (collect_phis instrs))) ==>
  (MEM v (input_vars_from pred instrs live) <=> MEM v live)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >>
      `MEM v (input_vars_from pred (collect_phis instrs) live)` by
        metis_tac[input_vars_from_collect] >>
      pop_assum (mp_tac o MATCH_MP input_vars_from_phi_correct_proof) >>
      strip_tac >> gvs[] >>
      `MEM (Var v) inst.inst_operands` by metis_tac[phi_pairs_mem_var] >>
      gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  strip_tac >> irule input_vars_from_non_phi >> simp[] >>
  rpt strip_tac >> gvs[MEM_MAP] >>
  rename1 `MEM pair (phi_pairs inst.inst_operands)` >>
  PairCases_on `pair` >> gvs[] >>
  rename1 `MEM (source, value) (phi_pairs inst.inst_operands)` >>
  `MEM (Var value) inst.inst_operands` by metis_tac[phi_pairs_mem_var] >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem phi_index_in_collect[local]:
  !instrs j.
    (!i k. i < k /\ k < LENGTH instrs /\
           (EL k instrs).inst_opcode = PHI ==>
           (EL i instrs).inst_opcode = PHI) /\
    j < LENGTH instrs /\ (EL j instrs).inst_opcode = PHI ==>
    MEM (EL j instrs) (collect_phis instrs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `j`
  >- gvs[collect_phis_def] >>
  rename1 `SUC idx < SUC (LENGTH instrs)` >>
  `h.inst_opcode = PHI` by
    (first_x_assum (qspecl_then [`0`, `SUC idx`] mp_tac) >> simp[]) >>
  simp[collect_phis_def] >> disj2_tac >> first_x_assum irule >>
  gvs[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`SUC i`, `SUC k`] mp_tac) >> simp[]
QED

Theorem ready_phi_index_in_collect[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  j < LENGTH bb.bb_instructions /\
  (EL j bb.bb_instructions).inst_opcode = PHI ==>
  MEM (EL j bb.bb_instructions) (collect_phis bb.bb_instructions)
Proof
  strip_tac >> irule phi_index_in_collect >> simp[] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  gvs[codegen_ready_fn_def, wf_function_def, bb_well_formed_def] >>
  metis_tac[]
QED

Theorem live_end_dominating_def[local]:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) ==>
  ?def_bb inst. MEM def_bb fn.fn_blocks /\ MEM inst def_bb.bb_instructions /\
    MEM v inst.inst_outputs /\ fn_dominates fn def_bb.bb_label lbl
Proof
  strip_tac >>
  mp_tac (live_def_dominates |> Q.SPEC `fn` |> Q.SPEC `lbl` |>
    Q.SPEC `bb` |> Q.SPEC `LENGTH bb.bb_instructions` |> Q.SPEC `v`) >>
  (impl_tac >- (simp[] >> rpt strip_tac >> decide_tac)) >>
  metis_tac[]
QED

Theorem live_start_strict_dominating_def[local]:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM v (live_vars_at (liveness_analyze fn) lbl 0) /\
  ~MEM (Var v) (FLAT (MAP (\phi. phi.inst_operands)
    (collect_phis bb.bb_instructions))) ==>
  ?def_bb inst. MEM def_bb fn.fn_blocks /\ MEM inst def_bb.bb_instructions /\
    MEM v inst.inst_outputs /\ fn_dominates fn def_bb.bb_label lbl /\
    def_bb.bb_label <> lbl
Proof
  strip_tac >>
  `!j. 0 <= j /\ j < LENGTH bb.bb_instructions /\
       (EL j bb.bb_instructions).inst_opcode = PHI ==>
       ~MEM (Var v) (EL j bb.bb_instructions).inst_operands` by
    (rpt strip_tac >> drule_all ready_phi_index_in_collect >>
     gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  mp_tac (live_def_dominates |> Q.SPEC `fn` |> Q.SPEC `lbl` |>
    Q.SPEC `bb` |> Q.SPEC `0` |> Q.SPEC `v`) >>
  simp[] >> metis_tac[]
QED

Theorem ready_entry_live_empty[local]:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  live_vars_at (liveness_analyze fn) lbl 0 = []
Proof
  strip_tac >>
  `collect_phis bb.bb_instructions = []` by metis_tac[ready_entry_no_phis] >>
  `fn_reachable fn lbl` by
    (simp[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]) >>
  Cases_on `live_vars_at (liveness_analyze fn) lbl 0` >> simp[] >>
  rename1 `live_vars_at (liveness_analyze fn) lbl 0 = v::vs` >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl 0)` by simp[] >>
  `~MEM (Var v) (FLAT (MAP (\phi. phi.inst_operands)
      (collect_phis bb.bb_instructions)))` by simp[] >>
  drule_all live_start_strict_dominating_def >>
  metis_tac[dominates_entry_label]
QED

Theorem initial_cleanup_wf_marked[local]:
  generated_plan_state_wf_marked spill_base
    (init_cleanup_plan_state ch growth spill_base lbl_ctr)
Proof
  simp[generated_plan_state_wf_marked_def,
       planSpillBoundsTheory.plan_slots_bounded_def,
       planSpillBoundsTheory.alloc_slots_bounded_def,
       doSwapSimTheory.spill_alloc_layout_wf_def,
       init_cleanup_plan_state_def, init_plan_state_def, init_spill_alloc_def]
QED

Theorem ready_join_pred_jmp[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block pred fn.fn_blocks = SOME pb /\ fn_cfg_edge fn pred lbl /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) ==>
  pb.bb_instructions <> [] /\ (LAST pb.bb_instructions).inst_opcode = JMP
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `wf_function fn /\ block_entries_ready (cfg_analyze fn) fn` by
    gvs[codegen_ready_fn_def] >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) lbl)` by
    metis_tac[fn_cfg_edge_cfg_analyze, cfg_edge_symmetry_uncond] >>
  gvs[block_entries_ready_def, EVERY_MEM] >>
  qpat_x_assum `!bb. MEM bb _ ==> _` (qspec_then `bb` mp_tac) >>
  simp[] >> strip_tac >> gvs[EVERY_MEM] >>
  qpat_x_assum `!p. MEM p _ ==> _` (qspec_then `pred` mp_tac) >> simp[NULL_EQ]
QED

Theorem ready_join_pred_succs[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block pred fn.fn_blocks = SOME pb /\ fn_cfg_edge fn pred lbl /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) ==>
  cfg_succs_of (cfg_analyze fn) pred = [lbl]
Proof
  strip_tac >> drule_all ready_join_pred_jmp >> strip_tac >>
  `MEM pb fn.fn_blocks /\ pb.bb_label = pred` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `wf_function fn /\ fn_inst_wf fn` by gvs[codegen_ready_fn_def] >>
  `MEM (LAST pb.bb_instructions) pb.bb_instructions` by
    (Cases_on `pb.bb_instructions` >> gvs[rich_listTheory.MEM_LAST]) >>
  `inst_wf (LAST pb.bb_instructions)` by
    metis_tac[fn_inst_wf_def] >>
  `?target. (LAST pb.bb_instructions).inst_operands = [Label target]` by
    gvs[inst_wf_def] >>
  `bb_succs pb = [target]` by
    (Cases_on `pb.bb_instructions` >>
     gvs[bb_succs_def, get_successors_def, is_terminator_def,
         venomStateTheory.get_label_def, listTheory.nub_def]) >>
  `cfg_succs_of (cfg_analyze fn) pred = [target]` by
    metis_tac[cfg_analyze_preserves_bb_succs] >>
  `MEM lbl (cfg_succs_of (cfg_analyze fn) pred)` by
    metis_tac[fn_cfg_edge_cfg_analyze] >> gvs[]
QED

Theorem ready_join_live_out[local]:
  codegen_ready_fn fn /\ fn_reachable fn pred /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block pred fn.fn_blocks = SOME pb /\ fn_cfg_edge fn pred lbl /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) ==>
  (MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions)) <=>
   MEM v (input_vars_from pred bb.bb_instructions
     (live_vars_at (liveness_analyze fn) lbl 0)))
Proof
  strip_tac >> drule_all ready_join_pred_succs >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `cfg_reachable_of (cfg_analyze fn) pred` by
    metis_tac[fn_reachable_cfg_analyze] >>
  drule_all liveness_convergence >>
  simp[livenessBlockProofsTheory.liveness_instrs_def,
       livenessBlockProofsTheory.liveness_out_def,
       liveness_edge_transfer_def, same_vars_set, pred_setTheory.EXTENSION,
       live_vars_at_def, list_union_mem]
QED

Theorem lineage_entry_small_fresh[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred lbl ps /\
  LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <= 1 /\
  (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (op = Var v \/ normalize_operand (dfg_build_function fn) [] op = Var v) ==>
  ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  strip_tac >>
  `op <> dead_stack_marker` by
    (strip_tac >> gvs[normalize_marker_not_var, dead_stack_marker_def,
                     normalize_operand_def]) >>
  drule_all lineage_entry_edge >> strip_tac >>
  rename1 `lookup_block pred fn.fn_blocks = SOME pb` >>
  drule_at (Pat `lineage_entry _ _ _ _ _ _ _ _`) lineage_entry_inventory >>
  disch_then (qspec_then `pb` mp_tac) >> simp[] >> strip_tac >>
  `?u. op = Var u /\ MEM u (live_vars_at (liveness_analyze fn) pred
    (LENGTH pb.bb_instructions))` by metis_tac[] >>
  drule_all live_end_dominating_def >> strip_tac >>
  `~fn_dominates fn lbl pred` by metis_tac[small_preds_not_dominates_pred] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `~MEM u (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
    metis_tac[dominating_def_excludes_outputs] >>
  gvs[] >> drule_all normalize_dominating_def >> strip_tac >>
  drule_all dominating_def_excludes_outputs >> simp[]
QED

Theorem lineage_entry_non_phi_fresh[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred lbl ps /\
  (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  ~MEM op (FLAT (MAP (\inst. inst.inst_operands) (collect_phis bb.bb_instructions))) /\
  (op = Var v \/ normalize_operand (dfg_build_function fn) [] op = Var v) ==>
  ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  rpt gen_tac >> disch_tac >>
  Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <= 1`
  >- metis_tac[lineage_entry_small_fresh] >>
  qpat_x_assum `_ /\ _` strip_assume_tac >>
  `op <> dead_stack_marker` by
    (strip_tac >> gvs[normalize_marker_not_var, dead_stack_marker_def,
                     normalize_operand_def]) >>
  drule_all lineage_entry_edge >> strip_tac >>
  rename1 `lookup_block pred fn.fn_blocks = SOME pb` >>
  drule_at (Pat `lineage_entry _ _ _ _ _ _ _ _`) lineage_entry_inventory >>
  disch_then (qspec_then `pb` mp_tac) >> simp[] >> strip_tac >>
  `?u. op = Var u /\ MEM u (live_vars_at (liveness_analyze fn) pred
    (LENGTH pb.bb_instructions))` by metis_tac[] >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl)` by decide_tac >>
  `MEM u (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0))` by metis_tac[ready_join_live_out] >>
  `MEM u (live_vars_at (liveness_analyze fn) lbl 0)` by
    metis_tac[input_vars_non_phi_iff] >>
  `~MEM (Var u) (FLAT (MAP (\inst. inst.inst_operands)
    (collect_phis bb.bb_instructions)))` by metis_tac[] >>
  drule_all live_start_strict_dominating_def >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `~MEM u (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
    metis_tac[strict_dominating_def_excludes_outputs] >>
  gvs[] >> drule_all normalize_strict_dominating_def >> strip_tac >>
  drule_all strict_dominating_def_excludes_outputs >> simp[]
QED

Theorem lineage_entry_marked[local]:
  codegen_ready_fn fn /\
  lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred lbl ps ==>
  generated_plan_state_wf_marked spill_base ps
Proof
  strip_tac >> drule_all lineage_entry_edge >> strip_tac >>
  rename1 `lookup_block pred fn.fn_blocks = SOME pb` >>
  drule_at (Pat `lineage_entry _ _ _ _ _ _ _ _`) lineage_entry_inventory >>
  disch_then (qspec_then `pb` mp_tac) >> simp[]
QED

Theorem lineage_entry_coverage[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred lbl ps /\
  MEM v (live_vars_at (liveness_analyze fn) lbl 0) /\
  ~MEM (Var v) (FLAT (MAP (\inst. inst.inst_operands)
    (collect_phis bb.bb_instructions))) ==>
  MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled
Proof
  strip_tac >> drule_all lineage_entry_edge >> strip_tac >>
  rename1 `lookup_block pred fn.fn_blocks = SOME pb` >>
  drule_at (Pat `lineage_entry _ _ _ _ _ _ _ _`) lineage_entry_inventory >>
  disch_then (qspec_then `pb` mp_tac) >> simp[] >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM pred (cfg_analyze fn).cfg_dfs_pre /\
   MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[fn_reachable_in_cfg_dfs_pre] >>
  `MEM lbl (cfg_succs_of (cfg_analyze fn) pred)` by
    metis_tac[fn_cfg_edge_cfg_analyze] >>
  `!inst. MEM inst (collect_phis bb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs inst.inst_operands))` by
    (rpt strip_tac >>
     qpat_x_assum `MEM v (MAP SND _)` mp_tac >>
     simp[MEM_MAP, pairTheory.EXISTS_PROD] >> rpt strip_tac >>
     drule phi_pairs_mem_var >> strip_tac >>
     qpat_x_assum `~MEM (Var v) _` mp_tac >>
     simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  drule_all (SIMP_RULE std_ss [LET_THM] live_vars_at_cross_block) >>
  metis_tac[]
QED

Theorem lineage_entry_phi_sources[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred lbl ps ==>
  EVERY (\phi. ?!v. MEM (Var v) phi.inst_operands /\
    (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled))
    (collect_phis bb.bb_instructions)
Proof
  strip_tac >>
  Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <= 1`
  >- (drule_all ready_small_preds_no_phis >> simp[]) >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl)` by decide_tac >>
  drule_all lineage_entry_edge >> strip_tac >>
  rename1 `lookup_block pred fn.fn_blocks = SOME pb` >>
  drule_at (Pat `lineage_entry _ _ _ _ _ _ _ _`) lineage_entry_inventory >>
  disch_then (qspec_then `pb` mp_tac) >> simp[] >> strip_tac >>
  `!v. (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) <=>
    MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0))` by
    (gen_tac >>
     `MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions)) <=>
      MEM v (input_vars_from pred bb.bb_instructions
        (live_vars_at (liveness_analyze fn) lbl 0))` by
       (irule ready_join_live_out >> metis_tac[]) >>
     `Var v <> dead_stack_marker` by simp[dead_stack_marker_def] >>
     eq_tac >- (strip_tac >>
       `?u. Var v = Var u /\ MEM u (live_vars_at (liveness_analyze fn) pred
         (LENGTH pb.bb_instructions))` by metis_tac[] >> gvs[]) >>
     metis_tac[]) >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) lbl)` by
    metis_tac[fn_cfg_edge_cfg_analyze, cfg_edge_symmetry_uncond] >>
  drule_all ready_phi_input_exactly_one >> simp[]
QED

(* Why it should hold.  Freshness: a join's entry stack is its JMP
   reorder's target, the predecessor-side PHI sources and the live-in
   variables; a source may be an output of the join itself (a loop header
   x = phi(a, v) whose body defines v), hence the exclusion of the PHI
   operands.  A live-in variable's definition strictly dominates the
   block, and so do the ASSIGN sources normalize_operand follows, so none
   is an output of the block.  A block with one predecessor P is entered
   with P's live-out variables (and markers), whose definitions dominate P
   and so the block, PHI sources included.  Well-formedness: a join is
   entered by a JMP, after which the spill map is empty (restore_spilled_plan,
   release_dead_spills), so only the successor's DFS allocator matters; a
   single-predecessor block is entered with the predecessor's spill map,
   which the lineage run allocates as the DFS run does (the stacks differ
   only in a bottom prefix of dead_stack_marker slots).  Coverage: the
   state holds every variable live at the end of the predecessor
   (fnLineageInv), and a live-in variable of the block that isn't a PHI
   operand is one of them; at the entry block nothing is live
   (fnLiveDefDom).  A PHI's operand from the entering edge is live at the
   end of that predecessor; its other operands are not (phi_uses_disjoint,
   phi_block_ready, and a join's predecessor has the join as its only
   successor).  A block with one predecessor has no PHIs
   (stackPlanGen$phis_at_joins). *)
Theorem lineage_state_static:
  !liveness dfg cfg ch growth spill_base lbl_ctr fn fn_ops ps_end lbl bb ps.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps
    ==>
    generated_plan_state_wf_marked spill_base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            ~MEM op (FLAT (MAP (\inst. inst.inst_operands)
                              (collect_phis bb.bb_instructions))) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    (LENGTH (cfg_preds_of cfg lbl) <= 1 ==>
     !op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    (!v. MEM v (live_vars_at liveness lbl 0) /\
         ~MEM (Var v) (FLAT (MAP (\inst. inst.inst_operands)
                              (collect_phis bb.bb_instructions))) ==>
         MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    EVERY (\phi. ?!v. MEM (Var v) phi.inst_operands /\
                      (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled))
      (collect_phis bb.bb_instructions)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule lineage_state_entry_cases >> strip_tac
  >- (gvs[] >>
      `live_vars_at (liveness_analyze fn) lbl 0 = []` by
        metis_tac[ready_entry_live_empty] >>
      `collect_phis bb.bb_instructions = []` by
        metis_tac[ready_entry_no_phis] >>
      simp[initial_cleanup_wf_marked, initial_cleanup_empty]) >>
  conj_tac >- metis_tac[lineage_entry_marked] >>
  conj_tac >- (rpt gen_tac >> disch_tac >>
    irule lineage_entry_non_phi_fresh >> metis_tac[]) >>
  conj_tac >- (disch_tac >> rpt gen_tac >> disch_tac >>
    irule lineage_entry_small_fresh >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> irule lineage_entry_coverage >> metis_tac[]) >>
  irule lineage_entry_phi_sources >> metis_tac[]
QED
