(*
 * CSE — Function-Level Correctness and Well-Formedness Preservation
 *
 * Lifts single-pass CSE correctness (cse_single_pass_correct) across the
 * OWHILE fixpoint iteration (cse_iterate) and trailing NOP cleanup
 * (clear_nops_function), proving structural invariant preservation
 * (wf_function, ssa_form, cse_reachable_wf_ssa, fn_inst_wf, ~is_alloca_op)
 * and cse_function_correct.
 *)

Theory cseCorrectness
Ancestors
  cseProofs cseBlockSimulationProps cseDefs cseCanonProps cseHistoryProps
  availExprDefs availExprProofs
  cfgDefs cfgAnalysisProps dfAnalyzeDefs dfAnalyzeProps
  venomInst venomWf venomWfProps venomExecProofs
  stateEquiv stateEquivProps
  passSharedDefs passSharedProps
  passTransform passSimulationDefs passSimulationProps analysisSimProps
  removeUnusedProofs
  indexedLists list rich_list relation While
Libs
  BasicProvers

(* ===== Shape of the per-instruction transform ===== *)

Theorem cse_inst_terminator[local]:
  !ids canon dav inst.
    is_terminator inst.inst_opcode ==> cse_inst ids canon dav inst = inst
Proof
  rpt gen_tac >> PairCases_on `dav` >> rw[cse_inst_def]
QED

Theorem cse_inst_props[local]:
  !ids canon dav inst.
    (cse_inst ids canon dav inst).inst_id = inst.inst_id /\
    (cse_inst ids canon dav inst).inst_outputs = inst.inst_outputs /\
    (~is_terminator inst.inst_opcode ==>
     ~is_terminator (cse_inst ids canon dav inst).inst_opcode) /\
    ((cse_inst ids canon dav inst).inst_opcode = PHI <=>
     inst.inst_opcode = PHI) /\
    (inst_wf inst ==> inst_wf (cse_inst ids canon dav inst)) /\
    (~is_alloca_op inst.inst_opcode ==>
     ~is_alloca_op (cse_inst ids canon dav inst).inst_opcode)
Proof
  rpt gen_tac >> PairCases_on `dav` >>
  qspecl_then [`ids`, `canon`, `dav0`, `dav1`, `inst`] strip_assume_tac
    cse_inst_replay_cases >>
  gvs[mk_assign_inst_def, mk_nop_inst_def, is_terminator_def,
      inst_wf_def, is_alloca_op_def]
QED

Theorem cse_single_pass_mapi[local]:
  !fn. ?g. (!bb i inst. ?ids canon dav. g bb i inst = cse_inst ids canon dav inst) /\
           cse_single_pass fn =
           function_map_transform
             (\bb. bb with bb_instructions := MAPi (g bb) bb.bb_instructions) fn
Proof
  gen_tac >>
  qexists_tac `\bb idx inst.
    cse_inst (set (MAP (\inst. inst.inst_id) bb.bb_instructions))
      (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
      (dfg_build_function fn, df_at NONE (avail_analyze fn) bb.bb_label idx)
      inst` >>
  simp[] >> conj_tac >- metis_tac[] >>
  simp[cse_single_pass_def, function_map_transform_def,
       ir_function_component_equality, MAP_EQ_f] >>
  simp[cse_block_transform_def, LET_THM]
QED

(* ===== Structural invariants of cse_single_pass ===== *)

Theorem cse_single_pass_preserves_ssa_form[local]:
  !fn. ssa_form fn ==> ssa_form (cse_single_pass fn)
Proof
  rw[ssa_form_def, fn_insts_def, fn_insts_blocks_flat,
     cse_single_pass_def, function_map_transform_def] >>
  `MAP (\i. i.inst_outputs)
     (FLAT (MAP (\bb. bb.bb_instructions)
       (MAP (cse_block_transform
               (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
               (dfg_build_function fn) (avail_analyze fn))
            fn.fn_blocks))) =
   MAP (\i. i.inst_outputs)
     (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks))`
    suffices_by simp[] >>
  Q.SPEC_TAC (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[] >> gen_tac >>
  simp[cse_block_transform_def, LET_THM, LIST_EQ_REWRITE, EL_MAP, EL_MAPi,
       cse_inst_props]
QED

Theorem cse_single_pass_preserves_wf_function[local]:
  !fn. wf_function fn ==> wf_function (cse_single_pass fn)
Proof
  rpt strip_tac >>
  qspec_then `fn` strip_assume_tac cse_single_pass_mapi >>
  pop_assum SUBST1_TAC >>
  irule mapi_transform_preserves_wf_bb >> simp[] >>
  metis_tac[cse_inst_props, cse_inst_terminator]
QED

Theorem cse_single_pass_preserves_fn_inst_wf[local]:
  !fn. fn_inst_wf fn ==> fn_inst_wf (cse_single_pass fn)
Proof
  rw[fn_inst_wf_def, cse_single_pass_def, function_map_transform_def,
     cse_block_transform_def, LET_THM, MEM_MAP] >>
  gvs[MEM_MAPi] >>
  irule (cj 5 (SPEC_ALL cse_inst_props)) >>
  first_x_assum irule >>
  metis_tac[EL_MEM]
QED

Theorem cse_single_pass_preserves_no_alloca[local]:
  !fn.
    EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) ==>
    EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts (cse_single_pass fn))
Proof
  rw[EVERY_MEM, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP,
     cse_single_pass_def, function_map_transform_def,
     cse_block_transform_def, LET_THM] >>
  gvs[MEM_MAPi] >>
  irule (cj 6 (SPEC_ALL cse_inst_props)) >>
  first_x_assum irule >>
  metis_tac[EL_MEM]
QED

(* ===== CFG and dominance invariance under cse_single_pass ===== *)

Theorem cse_block_transform_succs[local]:
  !canon dfg res bb.
    (cse_block_transform canon dfg res bb).bb_label = bb.bb_label /\
    bb_succs (cse_block_transform canon dfg res bb) = bb_succs bb
Proof
  rpt gen_tac >> simp[cse_block_transform_def, LET_THM] >>
  irule mapi_transform_bb_succs >>
  simp[cse_inst_terminator, cse_inst_props]
QED

Theorem foldl_map_eq[local]:
  !f bt bbs acc.
    (!bb m. f m (bt bb) = f m bb) ==>
    FOLDL f acc (MAP bt bbs) = FOLDL f acc bbs
Proof
  ntac 2 gen_tac >> Induct >> simp[]
QED

Theorem map_transform_cfg[local]:
  !bt fn.
    (!bb. (bt bb).bb_label = bb.bb_label /\ bb_succs (bt bb) = bb_succs bb) ==>
    fn_labels (function_map_transform bt fn) = fn_labels fn /\
    fn_entry_label (function_map_transform bt fn) = fn_entry_label fn /\
    cfg_analyze (function_map_transform bt fn) = cfg_analyze fn /\
    fn_cfg_edge (function_map_transform bt fn) = fn_cfg_edge fn /\
    is_fn_path (function_map_transform bt fn) = is_fn_path fn /\
    fn_reachable (function_map_transform bt fn) = fn_reachable fn /\
    fn_dominates (function_map_transform bt fn) = fn_dominates fn
Proof
  rpt strip_tac
  >- simp[fn_labels_def, function_map_transform_def, MAP_MAP_o, combinTheory.o_DEF]
  >- (Cases_on `fn.fn_blocks` >>
      simp[fn_entry_label_def, entry_block_def, function_map_transform_def])
  >- (
    `(function_map_transform bt fn).fn_blocks = MAP bt fn.fn_blocks` by
      simp[function_map_transform_def] >>
    `build_succs (MAP bt fn.fn_blocks) = build_succs fn.fn_blocks` by (
      rewrite_tac[build_succs_def] >>
      `init_succs (MAP bt fn.fn_blocks) : (string, string list) fmap =
       init_succs fn.fn_blocks` by
        (simp[init_succs_def] >> irule foldl_map_eq >> simp[]) >>
      pop_assum SUBST1_TAC >> irule foldl_map_eq >> simp[]) >>
    `!s. build_preds (MAP bt fn.fn_blocks) s = build_preds fn.fn_blocks s` by (
      gen_tac >> rewrite_tac[build_preds_def] >>
      `init_preds (MAP bt fn.fn_blocks) : (string, string list) fmap =
       init_preds fn.fn_blocks` by
        (simp[init_preds_def] >> irule foldl_map_eq >> simp[]) >>
      pop_assum SUBST1_TAC >> irule foldl_map_eq >> simp[LET_THM]) >>
    `MAP (\bb. bb.bb_label) (MAP bt fn.fn_blocks) =
     MAP (\bb. bb.bb_label) fn.fn_blocks` by
      simp[MAP_MAP_o, combinTheory.o_DEF] >>
    `(case entry_block (function_map_transform bt fn) of
        NONE => NONE | SOME bb => SOME bb.bb_label) =
     (case entry_block fn of
        NONE => NONE | SOME bb => SOME bb.bb_label)` by
      (Cases_on `fn.fn_blocks` >>
       simp[entry_block_def, function_map_transform_def]) >>
    rewrite_tac[cfg_analyze_def, LET_THM] >>
    BETA_TAC >> ASM_REWRITE_TAC[])
  >- (simp[FUN_EQ_THM, fn_cfg_edge_def, function_map_transform_def, MEM_MAP] >>
      metis_tac[])
  >- (
    `fn_cfg_edge (function_map_transform bt fn) = fn_cfg_edge fn` by
      (simp[FUN_EQ_THM, fn_cfg_edge_def, function_map_transform_def, MEM_MAP] >>
       metis_tac[]) >>
    simp[FUN_EQ_THM] >> Induct >> simp[is_fn_path_def] >>
    gen_tac >> Cases_on `x` >> simp[is_fn_path_def])
  >- (
    `fn_entry_label (function_map_transform bt fn) = fn_entry_label fn` by
      (Cases_on `fn.fn_blocks` >>
       simp[fn_entry_label_def, entry_block_def, function_map_transform_def]) >>
    `fn_cfg_edge (function_map_transform bt fn) = fn_cfg_edge fn` by
      (simp[FUN_EQ_THM, fn_cfg_edge_def, function_map_transform_def, MEM_MAP] >>
       metis_tac[]) >>
    simp[FUN_EQ_THM, fn_reachable_def])
  >- (
    `fn_entry_label (function_map_transform bt fn) = fn_entry_label fn` by
      (Cases_on `fn.fn_blocks` >>
       simp[fn_entry_label_def, entry_block_def, function_map_transform_def]) >>
    `fn_cfg_edge (function_map_transform bt fn) = fn_cfg_edge fn` by
      (simp[FUN_EQ_THM, fn_cfg_edge_def, function_map_transform_def, MEM_MAP] >>
       metis_tac[]) >>
    `is_fn_path (function_map_transform bt fn) = is_fn_path fn` by
      (simp[FUN_EQ_THM] >> Induct >> simp[is_fn_path_def] >>
       gen_tac >> Cases_on `x` >> simp[is_fn_path_def]) >>
    `fn_reachable (function_map_transform bt fn) = fn_reachable fn` by
      simp[FUN_EQ_THM, fn_reachable_def] >>
    simp[FUN_EQ_THM, fn_dominates_def])
QED

Theorem cse_single_pass_cfg[local]:
  !fn.
    fn_labels (cse_single_pass fn) = fn_labels fn /\
    fn_entry_label (cse_single_pass fn) = fn_entry_label fn /\
    cfg_analyze (cse_single_pass fn) = cfg_analyze fn /\
    fn_cfg_edge (cse_single_pass fn) = fn_cfg_edge fn /\
    is_fn_path (cse_single_pass fn) = is_fn_path fn /\
    fn_reachable (cse_single_pass fn) = fn_reachable fn /\
    fn_dominates (cse_single_pass fn) = fn_dominates fn
Proof
  gen_tac >> simp[cse_single_pass_def, LET_THM] >>
  irule map_transform_cfg >> simp[cse_block_transform_succs]
QED

(* ===== Preservation of cse_reachable_wf_ssa ===== *)

Theorem cfg_dfs_pre_imp_fn_reachable[local]:
  !fn lbl.
    wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    fn_reachable fn lbl
Proof
  rpt strip_tac >>
  drule cfg_analyze_reachable_sets >> strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by
    (fs[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `?ebb. entry_block fn = SOME ebb /\ fn_entry_label fn = SOME ebb.bb_label` by (
    fs[wf_function_def, fn_has_entry_def, fn_entry_label_def, entry_block_def] >>
    Cases_on `fn.fn_blocks` >> gvs[]) >>
  drule_all cfg_analyze_semantic_reachability >> strip_tac >>
  gvs[cfg_path_def] >>
  qpat_x_assum `fn_entry_label fn = SOME ebb.bb_label` mp_tac >>
  qpat_x_assum `RTC _ _ _` mp_tac >>
  Q.SPEC_TAC (`lbl`, `target`) >>
  Q.SPEC_TAC (`ebb.bb_label`, `start`) >>
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >> conj_tac
  >- simp[fn_reachable_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  drule_all fn_reachable_has_block >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = a` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `cfg_succs_of (cfg_analyze fn) a = bb_succs bb` by
    metis_tac[cfg_analyze_preserves_bb_succs] >>
  `fn_cfg_edge fn a target` by (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  gvs[fn_reachable_def] >>
  metis_tac[RTC_CASES2]
QED

Theorem fn_path_to_cse_static_trace[local]:
  !path fn entry.
    wf_function fn /\ is_fn_path fn path /\ path <> [] /\
    fn_entry_label fn = SOME entry /\ HD path = entry ==>
    ?ps. cse_static_trace fn ps /\
         LAST ps = (LAST path, 0) /\
         (!lbl0 k0. MEM (lbl0, k0) ps ==> MEM lbl0 path) /\
         (~MEM (LAST path) (FRONT path) ==>
          !k0. ~MEM (LAST path, k0) (FRONT ps))
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[] >> rpt strip_tac >>
  Cases_on `path = []`
  >- (
    gvs[] >>
    `fn_reachable fn x` by simp[fn_reachable_def] >>
    drule_all fn_reachable_has_block >> strip_tac >>
    qexists_tac `[(x, 0)]` >> simp[] >>
    irule (cj 1 cse_static_trace_rules) >> simp[] >>
    qexists_tac `bb` >> simp[]) >>
  `MEM (LAST path) path` by simp[MEM_LAST_NOT_NIL] >>
  `HD (SNOC x path) = HD path` by (Cases_on `path` >> gvs[SNOC]) >>
  gvs[] >>
  `is_fn_path fn path` by metis_tac[is_fn_path_init] >>
  `fn_cfg_edge fn (LAST path) x` by metis_tac[is_fn_path_last_edge] >>
  first_x_assum (qspec_then `fn` mp_tac) >> simp[] >> strip_tac >>
  `?rbb. lookup_block (LAST path) fn.fn_blocks = SOME rbb` by (
    qpat_x_assum `fn_cfg_edge _ _ _` mp_tac >> simp[fn_cfg_edge_def] >>
    strip_tac >> qexists_tac `bb` >> irule MEM_lookup_block >>
    gvs[wf_function_def, fn_labels_def]) >>
  `?xbb. lookup_block x fn.fn_blocks = SOME xbb` by
    metis_tac[fn_cfg_edge_target_block] >>
  qspecl_then [`LENGTH rbb.bb_instructions`, `ps`, `LAST path`, `0`, `rbb`, `fn`]
    mp_tac cse_static_trace_advance >>
  simp[] >> strip_tac >>
  qabbrev_tac `ps1 = ps ++ GENLIST (\i. (LAST path, SUC i)) (LENGTH rbb.bb_instructions)` >>
  `LAST ps1 = (LAST path, LENGTH rbb.bb_instructions)` by (
    simp[Abbr `ps1`] >>
    Cases_on `LENGTH rbb.bb_instructions` >> simp[GENLIST, LAST_SNOC]) >>
  `cse_static_trace fn (ps1 ++ [(x, 0)])` by (
    irule (cj 3 cse_static_trace_rules) >> simp[] >>
    qexistsl_tac [`LAST path`, `rbb`, `xbb`] >> simp[]) >>
  qexists_tac `ps1 ++ [(x, 0)]` >>
  simp[FRONT_SNOC, GSYM SNOC_APPEND] >>
  conj_tac
  >- (
    rpt strip_tac >> gvs[Abbr `ps1`, MEM_GENLIST] >>
    disj2_tac >> first_x_assum drule >> simp[]) >>
  strip_tac >> gen_tac >>
  simp[Abbr `ps1`, MEM_GENLIST] >>
  conj_tac
  >- (spose_not_then assume_tac >> first_x_assum drule >> simp[]) >>
  Cases_on `x = LAST path` >> gvs[]
QED

Theorem cse_avail_source_def_available[local]:
  !fn bb k expr srcs src src_var.
    wf_function fn /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    k < LENGTH bb.bb_instructions /\
    FLOOKUP (avail_unwrap (df_at NONE (avail_analyze fn) bb.bb_label k)) expr = SOME srcs /\
    MEM src srcs /\
    src.inst_outputs = [src_var] ==>
    def_available_at fn bb (SOME (EL k bb.bb_instructions)) src_var
Proof
  rpt strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def, MEM_MAP]) >>
  `fn_reachable fn bb.bb_label` by metis_tac[cfg_dfs_pre_imp_fn_reachable] >>
  `?entry path0. fn_entry_label fn = SOME entry /\
                 is_fn_path fn path0 /\ path0 <> [] /\
                 HD path0 = entry /\ LAST path0 = bb.bb_label` by (
    fs[fn_reachable_def] >> drule rtc_to_fn_path >> strip_tac >> metis_tac[]) >>
  `MEM bb.bb_label path0` by metis_tac[MEM_LAST_NOT_NIL] >>
  qpat_x_assum `MEM bb.bb_label path0`
    (mp_tac o MATCH_MP (iffLR MEM_SPLIT_APPEND_first)) >> strip_tac >>
  qabbrev_tac `spath = pfx ++ [bb.bb_label]` >>
  `spath <> [] /\ LAST spath = bb.bb_label /\ FRONT spath = pfx` by
    simp[Abbr `spath`, GSYM SNOC_APPEND, FRONT_SNOC] >>
  `HD spath = entry` by (Cases_on `pfx` >> gvs[Abbr `spath`]) >>
  `is_fn_path fn spath` by
    (simp[Abbr `spath`] >> irule cse_path_prefix_projection >>
     qexists_tac `sfx` >> gvs[APPEND_ASSOC]) >>
  qspecl_then [`spath`, `fn`, `entry`] mp_tac fn_path_to_cse_static_trace >>
  simp[] >> strip_tac >>
  qspecl_then [`k`, `ps`, `bb.bb_label`, `0`, `bb`, `fn`]
    mp_tac cse_static_trace_advance >>
  simp[] >> strip_tac >>
  qabbrev_tac `ps' = ps ++ GENLIST (\i. (bb.bb_label, SUC i)) k` >>
  `LAST ps' = (bb.bb_label, k)` by (
    simp[Abbr `ps'`] >> Cases_on `k` >> simp[GENLIST, LAST_SNOC]) >>
  drule cse_static_trace_avail_inst >> simp[] >> strip_tac >>
  gvs[avail_unwrap_def] >>
  first_x_assum (qspecl_then [`expr`, `src`] mp_tac) >>
  impl_tac >- (qexists_tac `srcs` >> simp[]) >> strip_tac >>
  `MEM bb0 fn.fn_blocks /\ bb0.bb_label = lbl0` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `cse_point_has_id fn (lbl0, k0) src.inst_id` by
    simp[cse_point_has_id_def] >>
  simp[def_available_at_def] >>
  qexistsl_tac [`bb0`, `src`] >>
  `MEM src bb0.bb_instructions` by metis_tac[EL_MEM] >>
  simp[] >> reverse conj_tac
  >- (
    strip_tac >> gvs[] >>
    qexistsl_tac [`k0`, `k`] >> simp[] >>
    Cases_on `k`
    >- gvs[Abbr `ps'`, GENLIST] >>
    `ps' = SNOC (bb.bb_label, SUC n) (ps ++ GENLIST (\i. (bb.bb_label, SUC i)) n)` by
      simp[Abbr `ps'`, GENLIST, SNOC_APPEND] >>
    `FRONT ps' = ps ++ GENLIST (\i. (bb.bb_label, SUC i)) n` by
      simp[FRONT_SNOC] >>
    `MEM (bb.bb_label, k0) ps \/ MEM (bb.bb_label, k0) (GENLIST (\i. (bb.bb_label, SUC i)) n)` by
      metis_tac[MEM_APPEND]
    >- (
      qspec_then `ps` strip_assume_tac SNOC_CASES >- gvs[cse_static_trace_nonempty] >>
      gvs[FRONT_SNOC, LAST_SNOC] >>
      Cases_on `(bb.bb_label, k0) = (bb.bb_label, 0)` >> gvs[] >>
      metis_tac[MEM_SNOC])
    >- (gvs[MEM_GENLIST])) >>
  simp[fn_dominates_def] >> rpt strip_tac >> gvs[] >>
  qspecl_then [`path`, `fn`, `HD path`] mp_tac fn_path_to_cse_static_trace >>
  simp[] >> disch_then (qx_choose_then `qps` strip_assume_tac) >>
  qspecl_then [`k`, `qps`, `bb.bb_label`, `0`, `bb`, `fn`]
    mp_tac cse_static_trace_advance >>
  simp[] >> strip_tac >>
  qabbrev_tac `qps' = qps ++ GENLIST (\i. (bb.bb_label, SUC i)) k` >>
  `LAST qps' = (bb.bb_label, k)` by (
    simp[Abbr `qps'`] >> Cases_on `k` >> simp[GENLIST, LAST_SNOC]) >>
  drule cse_static_trace_availability >> simp[] >> strip_tac >>
  gvs[] >>
  first_x_assum (qspecl_then [`expr`, `EL k0 bb0.bb_instructions`] mp_tac) >>
  impl_tac >- (qexists_tac `srcs` >> simp[]) >> strip_tac >>
  `q = (bb0.bb_label, k0)` by (
    irule cse_point_has_id_injective >>
    qexistsl_tac [`fn`, `(EL k0 bb0.bb_instructions).inst_id`] >> simp[]) >>
  gvs[] >>
  `MEM (bb0.bb_label, k0) qps'` by (
    qspec_then `qps'` strip_assume_tac SNOC_CASES >- gvs[cse_static_trace_nonempty] >>
    gvs[FRONT_SNOC, MEM_SNOC]) >>
  gvs[Abbr `qps'`, MEM_GENLIST]
  >- (qpat_x_assum `!lbl0 k0. MEM (lbl0, k0) qps ==> _` drule >> simp[])
  >- metis_tac[MEM_LAST_NOT_NIL]
QED

Theorem cse_single_pass_def_available_none[local]:
  !fn bb v.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    def_available_at fn bb NONE v ==>
    def_available_at (cse_single_pass fn)
      (cse_block_transform
         (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
         (dfg_build_function fn) (avail_analyze fn) bb) NONE v
Proof
  rpt strip_tac >>
  qabbrev_tac `bt = cse_block_transform
    (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
    (dfg_build_function fn) (avail_analyze fn)` >>
  gvs[def_available_at_def] >>
  `?idx. idx < LENGTH def_bb.bb_instructions /\
         EL idx def_bb.bb_instructions = def_inst` by metis_tac[MEM_EL] >>
  qexistsl_tac [`bt def_bb`, `EL idx (bt def_bb).bb_instructions`] >>
  `LENGTH (bt def_bb).bb_instructions = LENGTH def_bb.bb_instructions` by
    simp[Abbr `bt`, cse_block_transform_def, LET_THM] >>
  `(EL idx (bt def_bb).bb_instructions).inst_outputs =
   (EL idx def_bb.bb_instructions).inst_outputs` by
    simp[Abbr `bt`, cse_block_transform_def, LET_THM, EL_MAPi, cse_inst_props] >>
  `(bt def_bb).bb_label = def_bb.bb_label /\ (bt bb).bb_label = bb.bb_label` by
    simp[Abbr `bt`, cse_block_transform_succs] >>
  simp[EL_MEM, cse_single_pass_cfg] >>
  simp[cse_single_pass_def, function_map_transform_def, MEM_MAP] >>
  metis_tac[]
QED

Theorem cse_single_pass_def_available_some[local]:
  !fn bb k v.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    k < LENGTH bb.bb_instructions /\
    def_available_at fn bb (SOME (EL k bb.bb_instructions)) v ==>
    def_available_at (cse_single_pass fn)
      (cse_block_transform
         (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
         (dfg_build_function fn) (avail_analyze fn) bb)
      (SOME (EL k (cse_block_transform
                     (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
                     (dfg_build_function fn) (avail_analyze fn) bb).bb_instructions)) v
Proof
  rpt strip_tac >>
  qabbrev_tac `bt = cse_block_transform
    (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
    (dfg_build_function fn) (avail_analyze fn)` >>
  gvs[def_available_at_def] >>
  `?idx. idx < LENGTH def_bb.bb_instructions /\
         EL idx def_bb.bb_instructions = def_inst` by metis_tac[MEM_EL] >>
  qexistsl_tac [`bt def_bb`, `EL idx (bt def_bb).bb_instructions`] >>
  `LENGTH (bt def_bb).bb_instructions = LENGTH def_bb.bb_instructions /\
   LENGTH (bt bb).bb_instructions = LENGTH bb.bb_instructions` by
    simp[Abbr `bt`, cse_block_transform_def, LET_THM] >>
  `(EL idx (bt def_bb).bb_instructions).inst_outputs =
   (EL idx def_bb.bb_instructions).inst_outputs` by
    simp[Abbr `bt`, cse_block_transform_def, LET_THM, EL_MAPi, cse_inst_props] >>
  simp[EL_MEM, cse_single_pass_cfg] >>
  `(bt def_bb).bb_label = def_bb.bb_label /\ (bt bb).bb_label = bb.bb_label` by
    simp[Abbr `bt`, cse_block_transform_succs] >>
  simp[] >> conj_tac
  >- (simp[cse_single_pass_def, function_map_transform_def, MEM_MAP] >>
      metis_tac[]) >>
  strip_tac >>
  `def_bb.bb_label = bb.bb_label` by metis_tac[] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by (
    qpat_assum `wf_function fn` mp_tac >>
    rewrite_tac[wf_function_def, fn_labels_def] >>
    strip_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
   lookup_block def_bb.bb_label fn.fn_blocks = SOME def_bb` by
    (conj_tac >> irule MEM_lookup_block >> simp[]) >>
  `def_bb = bb` by (
    qpat_x_assum `lookup_block bb.bb_label _ = SOME bb` mp_tac >>
    qpat_x_assum `lookup_block def_bb.bb_label _ = SOME def_bb` mp_tac >>
    simp[]) >>
  qpat_x_assum `def_bb = bb` SUBST_ALL_TAC >>
  qpat_x_assum `bb = bb ==> _` mp_tac >> simp[] >> strip_tac >>
  `cse_point_has_id fn (bb.bb_label, idx) (EL idx bb.bb_instructions).inst_id /\
   cse_point_has_id fn (bb.bb_label, i) (EL idx bb.bb_instructions).inst_id` by
    (qpat_x_assum `_ = def_inst` (assume_tac o GSYM) >>
     simp[cse_point_has_id_def]) >>
  `(bb.bb_label, idx) = (bb.bb_label, i)` by (
    irule cse_point_has_id_injective >>
    qexistsl_tac [`fn`, `(EL idx bb.bb_instructions).inst_id`] >> simp[]) >>
  `cse_point_has_id fn (bb.bb_label, j) (EL k bb.bb_instructions).inst_id /\
   cse_point_has_id fn (bb.bb_label, k) (EL k bb.bb_instructions).inst_id` by
    simp[cse_point_has_id_def] >>
  `(bb.bb_label, j) = (bb.bb_label, k)` by (
    irule cse_point_has_id_injective >>
    qexistsl_tac [`fn`, `(EL k bb.bb_instructions).inst_id`] >> simp[]) >>
  `idx = i /\ j = k` by (
    qpat_x_assum `(_, idx) = (_, i)` mp_tac >>
    qpat_x_assum `(_, j) = (_, k)` mp_tac >> simp[]) >>
  qexistsl_tac [`i`, `k`] >> simp[]
QED

Theorem cse_single_pass_preserves_cse_reachable_wf_ssa[local]:
  !fn.
    wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn ==>
    cse_reachable_wf_ssa (cse_single_pass fn)
Proof
  rpt strip_tac >>
  `ssa_form (cse_single_pass fn)` by
    (irule cse_single_pass_preserves_ssa_form >> fs[cse_reachable_wf_ssa_def]) >>
  simp[cse_reachable_wf_ssa_def, cse_single_pass_cfg] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bt = cse_block_transform
    (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
    (dfg_build_function fn) (avail_analyze fn)` >>
  `?bb0. MEM bb0 fn.fn_blocks /\ bb = bt bb0` by (
    qpat_x_assum `MEM bb _` mp_tac >>
    simp[cse_single_pass_def, function_map_transform_def, MEM_MAP, Abbr `bt`] >>
    metis_tac[]) >>
  qpat_x_assum `bb = bt bb0` SUBST_ALL_TAC >>
  `(bt bb0).bb_label = bb0.bb_label` by
    simp[Abbr `bt`, cse_block_transform_succs] >>
  `MEM bb0.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (qpat_x_assum `MEM (bt bb0).bb_label _` mp_tac >> simp[]) >>
  `LENGTH (bt bb0).bb_instructions = LENGTH bb0.bb_instructions` by
    simp[Abbr `bt`, cse_block_transform_def, LET_THM] >>
  `?k. k < LENGTH bb0.bb_instructions /\
       inst = EL k (bt bb0).bb_instructions` by metis_tac[MEM_EL] >>
  qabbrev_tac `orig = EL k bb0.bb_instructions` >>
  `MEM orig bb0.bb_instructions` by simp[Abbr `orig`, EL_MEM] >>
  `inst = cse_inst (set (MAP (\i. i.inst_id) bb0.bb_instructions))
            (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
            (dfg_build_function fn,
             df_at NONE (avail_analyze fn) bb0.bb_label k) orig` by
    simp[Abbr `bt`, cse_block_transform_def, LET_THM, EL_MAPi, Abbr `orig`] >>
  IF_CASES_TAC
  >- (
    `orig.inst_opcode = PHI` by
      (qpat_x_assum `inst.inst_opcode = PHI` mp_tac >> simp[cse_inst_props]) >>
    `inst = orig` by (
      qspecl_then [`set (MAP (\i. i.inst_id) bb0.bb_instructions)`,
                   `compute_canon (dfg_build_function fn) (avail_analyze fn) fn`,
                   `dfg_build_function fn`,
                   `df_at NONE (avail_analyze fn) bb0.bb_label k`,
                   `orig`] strip_assume_tac cse_inst_replay_cases >>
      qpat_x_assum `orig.inst_opcode = PHI` mp_tac >>
      qpat_x_assum `inst = cse_inst _ _ _ _` mp_tac >> simp[]) >>
    qpat_x_assum `inst = cse_inst _ _ _ _` kall_tac >>
    qpat_x_assum `inst = EL k _` kall_tac >>
    `phi_edge_uses_wf fn bb0 orig` by (
      qpat_x_assum `cse_reachable_wf_ssa fn` mp_tac >>
      simp[cse_reachable_wf_ssa_def] >> strip_tac >>
      first_x_assum drule_all >> simp[]) >>
    qpat_x_assum `phi_edge_uses_wf _ _ _` mp_tac >>
    simp[phi_edge_uses_wf_def, cse_single_pass_cfg] >>
    strip_tac >> simp[] >> rpt strip_tac >>
    first_x_assum drule >> strip_tac >>
    qexists_tac `bt pred_bb` >>
    simp[Abbr `bt`, cse_block_transform_succs] >> conj_tac
    >- (simp[cse_single_pass_def, function_map_transform_def, MEM_MAP] >>
        metis_tac[]) >>
    conj_tac >- (qexists_tac `(pred, v)` >> simp[]) >>
    irule cse_single_pass_def_available_none >> simp[])
  >- (
    rpt strip_tac >>
    `orig.inst_opcode <> PHI` by
      (qpat_x_assum `inst.inst_opcode <> PHI` mp_tac >> simp[cse_inst_props]) >>
    qspecl_then [`set (MAP (\i. i.inst_id) bb0.bb_instructions)`,
                 `compute_canon (dfg_build_function fn) (avail_analyze fn) fn`,
                 `dfg_build_function fn`,
                 `df_at NONE (avail_analyze fn) bb0.bb_label k`,
                 `orig`] strip_assume_tac cse_inst_replay_cases
    >- (
      `inst = orig` by simp[] >>
      qpat_x_assum `inst = cse_inst _ _ _ _` kall_tac >>
      `def_available_at fn bb0 (SOME orig) v` by (
        qpat_x_assum `cse_reachable_wf_ssa fn` mp_tac >>
        simp[cse_reachable_wf_ssa_def] >> strip_tac >>
        first_x_assum drule_all >>
        qpat_x_assum `MEM (Var v) _` mp_tac >> simp[]) >>
      qspecl_then [`fn`, `bb0`, `k`, `v`] mp_tac
        cse_single_pass_def_available_some >>
      qpat_x_assum `inst = orig` kall_tac >>
      qpat_x_assum `inst = EL k _` (assume_tac o GSYM) >>
      simp[Abbr `orig`, Abbr `bt`])
    >- (
      `inst = mk_assign_inst orig (Var y)` by simp[] >>
      qpat_x_assum `inst = cse_inst _ _ _ _` kall_tac >>
      `v = y` by
        (qpat_x_assum `MEM (Var v) inst.inst_operands` mp_tac >>
         simp[mk_assign_inst_def]) >>
      qpat_x_assum `v = y` SUBST_ALL_TAC >>
      `def_available_at fn bb0 (SOME orig) y` by (
        unabbrev_all_tac >> irule cse_avail_source_def_available >>
        simp[] >>
        qexistsl_tac [`mk_expr (dfg_build_function fn) (EL k bb0.bb_instructions)`,
                      `src`, `xs`] >> simp[]) >>
      qspecl_then [`fn`, `bb0`, `k`, `y`] mp_tac
        cse_single_pass_def_available_some >>
      qpat_x_assum `inst = mk_assign_inst _ _` kall_tac >>
      qpat_x_assum `inst = EL k _` (assume_tac o GSYM) >>
      simp[Abbr `orig`, Abbr `bt`])
    >- (
      `inst = mk_nop_inst orig` by simp[] >>
      qpat_x_assum `inst = cse_inst _ _ _ _` kall_tac >>
      qpat_x_assum `MEM (Var v) inst.inst_operands` mp_tac >>
      simp[mk_nop_inst_def]))
QED

Theorem cse_iterate_inv[local]:
  !P fn fn'.
    P fn /\ (!x. P x ==> P (cse_single_pass x)) /\
    cse_iterate fn = SOME fn' ==> P fn'
Proof
  rpt strip_tac >> fs[cse_iterate_def] >>
  qpat_x_assum `OWHILE _ _ _ = _` mp_tac >>
  Q.SPEC_TAC (`fn'`, `fn'`) >>
  ho_match_mp_tac (GEN_ALL WhileTheory.OWHILE_INV_IND) >>
  simp[]
QED

(* ===== Top-Level Obligations ===== *)

Theorem cse_function_correct:
  !fuel ctx fn s.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
    s.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s.vs_current_bb ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (cse_function fn) s)
Proof
  rpt strip_tac >>
  simp[cse_function_def, GSYM stateEquivPropsTheory.result_equiv_is_lift_result] >>
  Cases_on `cse_iterate fn` >> simp[]
  >- (disj2_tac >> irule clear_nops_function_correct >> simp[]) >>
  qabbrev_tac `P = \f.
    wf_function f /\ cse_reachable_wf_ssa f /\ fn_inst_wf f /\
    EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts f) /\
    fn_entry_label f = SOME s.vs_current_bb` >>
  `P fn` by simp[Abbr `P`, wf_ssa_imp_cse_reachable_wf_ssa] >>
  `!g. P g ==> P (cse_single_pass g)` by (
    gen_tac >> simp[Abbr `P`] >> strip_tac >>
    simp[cse_single_pass_preserves_wf_function,
         cse_single_pass_preserves_cse_reachable_wf_ssa,
         cse_single_pass_preserves_fn_inst_wf,
         cse_single_pass_preserves_no_alloca,
         cse_single_pass_cfg]) >>
  `P x` by metis_tac[cse_iterate_inv] >>
  `wf_function x` by fs[Abbr `P`] >>
  qspecl_then [
    `\f. (cse_single_pass f).fn_blocks <> f.fn_blocks`,
    `cse_single_pass`,
    `state_equiv {}`,
    `execution_equiv {}`,
    `\f. run_blocks fuel ctx f s`,
    `P`
  ] mp_tac owhile_lift_result_compose >>
  impl_tac
  >- (
    simp[state_equiv_refl, execution_equiv_refl] >>
    conj_tac >- metis_tac[state_equiv_trans] >>
    conj_tac >- metis_tac[execution_equiv_trans] >>
    rpt strip_tac >> fs[Abbr `P`] >>
    qspecl_then [`fuel`, `ctx`, `x'`, `s`] mp_tac cse_single_pass_correct >>
    simp[]) >>
  disch_then (qspecl_then [`fn`, `x`] mp_tac) >>
  fs[cse_iterate_def, GSYM stateEquivPropsTheory.result_equiv_is_lift_result] >>
  strip_tac >- simp[] >>
  disj2_tac >>
  irule stateEquivPropsTheory.result_equiv_trans >>
  qexists_tac `run_blocks fuel ctx x s` >> simp[] >>
  irule clear_nops_function_correct >> simp[]
QED

Theorem cse_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (cse_function fn)
Proof
  rpt strip_tac >> simp[cse_function_def] >>
  Cases_on `cse_iterate fn` >> simp[] >>
  irule clear_nops_function_preserves_ssa >> fs[] >>
  irule (Q.SPEC `ssa_form` cse_iterate_inv) >>
  simp[cse_single_pass_preserves_ssa_form] >>
  qexists_tac `fn` >> simp[]
QED

Theorem cse_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (cse_function fn)
Proof
  rpt strip_tac >> simp[cse_function_def] >>
  Cases_on `cse_iterate fn` >> simp[] >>
  irule clear_nops_function_preserves_wf >> fs[] >>
  irule (Q.SPEC `wf_function` cse_iterate_inv) >>
  simp[cse_single_pass_preserves_wf_function] >>
  qexists_tac `fn` >> simp[]
QED
