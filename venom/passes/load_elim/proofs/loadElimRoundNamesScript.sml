Theory loadElimRoundNames
Ancestors
  loadElimDefs loadElimOriginHelpers loadElimPhiCapture
  loadElimAllBlockPopulation loadElimConvergence loadElimSolverHelpers
  loadElimSupportHelpers loadElimGeneratedSupport loadElimActionFreshness
  localPtrsProps
  dfgAnalysisProps cfgTransform removeUnusedSsaProofs venomWfProps livenessTransferProofs
  venomInst venomWf venomExecProps cfgDefs cfgAnalysisProps list rich_list finite_map pred_set

Theorem le_generated_var_source:
  Var v IN le_generated_operands (fn_insts fn) ==>
  MEM v (fn_all_vars fn)
Proof
  simp[le_generated_operands_def, fn_insts_def, fn_insts_blocks_flat,
       cfgTransformTheory.fn_all_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> gvs[MEM_MAP] >>
  qexistsl [`bb`, `i`] >> simp[] >> disj2_tac >>
  qexists `Var v` >> simp[]
QED

Theorem le_analyze_all_point_supported:
  wf_function fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  n <= LENGTH bb.bb_instructions ==>
  le_lattice_supported (le_generated_keys ctx (fn_insts fn))
    (le_generated_operands (fn_insts fn))
    (df_at NONE (load_analyze ctx fn) lbl n)
Proof
  strip_tac >> drule_all le_analyze_all_block_prefix >> disch_then (qspec_then `ctx` SUBST1_TAC) >>
  irule le_transfer_fold_supported >> conj_tac
  >- (simp[EVERY_MEM] >> rpt strip_tac >>
      `MEM i bb.bb_instructions` by metis_tac[MEM_TAKE] >>
      `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
      simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  irule le_boundary_joined_supported >> metis_tac[le_analyze_boundary_supported]
QED

Theorem le_analyze_point_var_source:
  wf_function fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  n <= LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) lbl n)) k = SOME vs /\
  MEM (Var v) vs ==> MEM v (fn_all_vars fn)
Proof
  strip_tac >> drule_all le_analyze_all_point_supported >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[le_lattice_supported_def, EVERY_MEM] >> strip_tac >>
  irule le_generated_var_source >> first_x_assum drule >> simp[]
QED

Theorem le_analyze_boundary_var_source:
  wf_function fn /\
  FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn) lbl)) k = SOME vs /\
  MEM (Var v) vs ==> MEM v (fn_all_vars fn)
Proof
  strip_tac >> drule le_analyze_boundary_supported >>
  disch_then (qspecl_then [`lbl`, `ctx`] mp_tac) >>
  simp[le_lattice_supported_def, EVERY_MEM] >> strip_tac >>
  irule le_generated_var_source >> first_x_assum drule >> simp[]
QED

Theorem le_phi_pairs_var_member:
  !pairs v. MEM (Var v) (mk_phi_ops_from_pairs pairs) <=>
    ?lbl. MEM (lbl,v) pairs
Proof
  Induct >> simp[mk_phi_ops_from_pairs_def] >>
  Cases_on `h` >> simp[mk_phi_ops_from_pairs_def] >> metis_tac[]
QED

Theorem le_collected_phi_operand_source:
  wf_function fn /\
  MEM pa (collect_phi_actions m ctx g (load_analyze ctx fn) fn) /\
  MEM (Var v) pa.pa_phi_ops ==> MEM v (fn_all_vars fn)
Proof
  strip_tac >> drule collect_phi_actions_member >> strip_tac >>
  drule le_compute_phi_action_certificate >> strip_tac >>
  gvs[le_phi_pairs_var_member, EVERY_MEM] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  irule le_analyze_boundary_var_source >> metis_tac[MEM]
QED

Theorem le_inst_other_opcode_origin:
  (load_elim_inst ctx actions ll i).inst_opcode <> ASSIGN /\
  (load_elim_inst ctx actions ll i).inst_opcode <> NOP ==>
  load_elim_inst ctx actions ll i = i
Proof
  strip_tac >> Cases_on `load_elim_inst ctx actions ll i = i` >- simp[] >>
  drule_at (Pat `transformed <> inst`) load_elim_inst_changed >>
  disch_then (qspecl_then [`ll`, `ctx`, `actions`] mp_tac) >>
  disch_then strip_assume_tac >>
  gvs[passSharedDefsTheory.mk_assign_inst_def, passSharedDefsTheory.mk_nop_inst_def]
QED

Theorem le_inst_var_bound:
  (!vs k v. FLOOKUP (unwrap_load_lattice ll) k = SOME vs /\ MEM (Var v) vs ==>
    v IN names) /\
  (!pa v. MEM pa actions /\ v = pa.pa_phi_out ==> v IN names) /\
  MEM v ((load_elim_inst ctx actions ll i).inst_outputs ++
    FLAT (MAP (\op. case op of Var u => [u] | _ => [])
      (load_elim_inst ctx actions ll i).inst_operands)) ==>
  MEM v (i.inst_outputs ++
    FLAT (MAP (\op. case op of Var u => [u] | _ => []) i.inst_operands)) \/
  v IN names
Proof
  strip_tac >> Cases_on `load_elim_inst ctx actions ll i = i` >- gvs[] >>
  drule_at (Pat `transformed <> inst`) load_elim_inst_changed >>
  disch_then (qspecl_then [`ll`, `ctx`, `actions`] mp_tac) >>
  disch_then strip_assume_tac >>
  gvs[passSharedDefsTheory.mk_assign_inst_def, passSharedDefsTheory.mk_nop_inst_def] >>
  gvs[MEM_FLAT, MEM_MAP, AllCaseEqs()]
  >- (Cases_on `v'` >> gvs[] >> disj2_tac >>
      first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  disj2_tac >> drule phi_action_lookup_member >> strip_tac >> metis_tac[]
QED

Theorem le_prepend_other_opcode_origin:
  MEM j (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
    (\ll i. [load_elim_inst ctx actions ll i]) bb).bb_instructions /\
  j.inst_opcode = op /\ op <> PHI /\ op <> ASSIGN /\ op <> NOP ==>
  MEM j bb.bb_instructions
Proof
  simp[passTransformTheory.analysis_block_transform_prepend_def,
       load_phi_prepend_def, passSimulationPropsTheory.flat_mapi_singleton,
       MEM_APPEND] >> rpt strip_tac
  >- (drule MEM_TAKE >> strip_tac >> gvs[indexedListsTheory.MEM_MAPi] >>
      drule_all le_inst_other_opcode_origin >> strip_tac >> gvs[] >>
      metis_tac[MEM_EL])
  >- (drule phis_for_block_member >> strip_tac >> gvs[]) >>
  drule MEM_DROP_IMP >> strip_tac >> gvs[indexedListsTheory.MEM_MAPi] >>
  drule_all le_inst_other_opcode_origin >> strip_tac >> gvs[] >> metis_tac[MEM_EL]
QED

Theorem le_round_other_opcode_origin:
  MEM j (fn_insts (load_elim_one ctx g fn)) /\
  j.inst_opcode = op /\ op <> PHI /\ op <> ASSIGN /\ op <> NOP ==>
  MEM j (fn_insts fn)
Proof
  simp[load_elim_one_def, passTransformTheory.analysis_function_transform_prepend_def,
       passTransformTheory.function_map_transform_def,
       fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> drule_all le_prepend_other_opcode_origin >> strip_tac >>
  metis_tac[]
QED

Theorem le_prepend_var_bound:
  (!n k vs v. n < LENGTH bb.bb_instructions /\
    FLOOKUP (unwrap_load_lattice (df_at NONE result bb.bb_label n)) k = SOME vs /\
    MEM (Var v) vs ==> v IN names) /\
  (!pa. MEM pa actions ==> pa.pa_phi_out IN names) /\
  (!pa v. MEM pa actions /\ MEM (Var v) pa.pa_phi_ops ==> v IN names) /\
  MEM v (FLAT (MAP (\i. i.inst_outputs ++
      FLAT (MAP (\op. case op of Var u => [u] | _ => []) i.inst_operands))
    (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
      (\ll i. [load_elim_inst ctx actions ll i]) bb).bb_instructions)) ==>
  MEM v (FLAT (MAP (\i. i.inst_outputs ++
      FLAT (MAP (\op. case op of Var u => [u] | _ => []) i.inst_operands))
      bb.bb_instructions)) \/ v IN names
Proof
  strip_tac >>
  `!idx u. idx < LENGTH bb.bb_instructions /\
    MEM u ((load_elim_inst ctx actions (df_at NONE result bb.bb_label idx)
      (EL idx bb.bb_instructions)).inst_outputs ++
      FLAT (MAP (\op. case op of Var w => [w] | _ => [])
        (load_elim_inst ctx actions (df_at NONE result bb.bb_label idx)
          (EL idx bb.bb_instructions)).inst_operands)) ==>
    MEM u ((EL idx bb.bb_instructions).inst_outputs ++
      FLAT (MAP (\op. case op of Var w => [w] | _ => [])
        (EL idx bb.bb_instructions).inst_operands)) \/ u IN names` by
    (rpt gen_tac >> strip_tac >> irule le_inst_var_bound >>
     qexistsl [`actions`, `ctx`, `df_at NONE result bb.bb_label idx`] >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `MEM v (FLAT _)` mp_tac >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS,
       passTransformTheory.analysis_block_transform_prepend_def,
       load_phi_prepend_def, passSimulationPropsTheory.flat_mapi_singleton,
       MEM_APPEND] >> rpt strip_tac
  >>~- ([`MEM _ (TAKE _ _)`],
    drule MEM_TAKE >> strip_tac >> gvs[indexedListsTheory.MEM_MAPi] >>
    qpat_x_assum `!idx u. _` (qspec_then `idx` mp_tac) >>
    simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[MEM_EL])
  >>~- ([`MEM _ (DROP _ _)`],
    drule MEM_DROP_IMP >> strip_tac >> gvs[indexedListsTheory.MEM_MAPi] >>
    qpat_x_assum `!idx u. _` (qspec_then `idx` mp_tac) >>
    simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[MEM_EL]) >>
  drule phis_for_block_member >> strip_tac >>
  gvs[MEM_FLAT, MEM_MAP, AllCaseEqs()] >>
  Cases_on `op` >> gvs[] >> metis_tac[]
QED

Theorem le_round_vars_bound:
  wf_function fn /\ MEM v (fn_all_vars (load_elim_one ctx g fn)) ==>
  MEM v (fn_all_vars fn) \/ v IN load_elim_one_fresh ctx g fn
Proof
  strip_tac >>
  qpat_x_assum `MEM v _` mp_tac >>
  simp[load_elim_one_def,
    passTransformTheory.analysis_function_transform_prepend_def,
    passTransformTheory.function_map_transform_def,
    cfgTransformTheory.fn_all_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> rename1 `MEM bb fn.fn_blocks` >>
  `(!n k vs u. n < LENGTH bb.bb_instructions /\
    FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) bb.bb_label n)) k = SOME vs /\
    MEM (Var u) vs ==> u IN set (fn_all_vars fn) UNION load_elim_one_fresh ctx g fn)` by
    (rpt strip_tac >> simp[] >> disj1_tac >>
     irule le_analyze_point_var_source >> simp[] >>
     qexistsl [`bb`, `ctx`, `k`, `bb.bb_label`, `n`, `vs`] >> simp[] >>
     irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  `(!pa. MEM pa (collect_phi_actions (fn_max_inst_id fn) ctx g (load_analyze ctx fn) fn) ==>
    pa.pa_phi_out IN set (fn_all_vars fn) UNION load_elim_one_fresh ctx g fn)` by
    (simp[load_elim_one_fresh_def, load_elim_fresh_vars_def, MEM_MAP] >> metis_tac[]) >>
  `(!pa u. MEM pa (collect_phi_actions (fn_max_inst_id fn) ctx g (load_analyze ctx fn) fn) /\
    MEM (Var u) pa.pa_phi_ops ==>
    u IN set (fn_all_vars fn) UNION load_elim_one_fresh ctx g fn)` by
    (simp[] >> metis_tac[le_collected_phi_operand_source]) >>
  drule le_prepend_var_bound >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  disch_then (qspecl_then [`v`, `ctx`,
    `collect_phi_actions (fn_max_inst_id fn) ctx g (load_analyze ctx fn) fn`] mp_tac) >>
  simp[] >>
  gvs[cfgTransformTheory.fn_all_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

(* Names are indexed by original load opcode, not by generated PHI IDs. *)
Definition le_opcode_names_def:
  le_opcode_names fn ops =
    {v | ?i. MEM i (fn_insts fn) /\ MEM i.inst_opcode ops /\
             v = fresh_phi_var i.inst_id}
End

Theorem le_round_fresh_origin:
  v IN load_elim_one_fresh ctx g fn ==>
  ?i. MEM i (fn_insts fn) /\ i.inst_opcode = ctx.lctx_config.lc_load /\
      v = fresh_phi_var i.inst_id
Proof
  simp[load_elim_one_fresh_def, load_elim_fresh_vars_def, MEM_MAP] >>
  strip_tac >> drule collect_phi_actions_member >> strip_tac >>
  drule compute_phi_action_origin >> strip_tac >>
  qexists `inst` >> simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  metis_tac[MEM_EL]
QED

Theorem le_opcode_names_disjoint:
  fn_inst_ids_distinct fn /\ DISJOINT (set ops1) (set ops2) ==>
  DISJOINT (le_opcode_names fn ops1) (le_opcode_names fn ops2)
Proof
  simp[DISJOINT_DEF, EXTENSION, le_opcode_names_def] >>
  rpt strip_tac >> spose_not_then strip_assume_tac >> gvs[] >>
  drule_all fn_inst_ids_distinct_inj >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem le_opcode_names_prefix:
  v IN le_opcode_names fn ops ==> isPREFIX "$le_phi_" v
Proof
  simp[le_opcode_names_def] >> strip_tac >> gvs[fresh_phi_var_def]
QED

Theorem le_opcode_names_source_disjoint:
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) ==>
  DISJOINT (le_opcode_names fn ops) (set (fn_all_vars fn))
Proof
  pure_rewrite_tac[EVERY_MEM] >> strip_tac >>
  simp[DISJOINT_DEF, EXTENSION] >> gen_tac >>
  spose_not_then strip_assume_tac >>
  drule le_opcode_names_prefix >>
  first_x_assum drule >> simp[]
QED

Definition le_round_name_bound_def:
  le_round_name_bound original fn ops <=>
    set (fn_all_vars fn) SUBSET
      set (fn_all_vars original) UNION le_opcode_names original ops /\
    (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> PHI /\
         i.inst_opcode <> ASSIGN /\ i.inst_opcode <> NOP ==>
         MEM i (fn_insts original))
End

Theorem le_round_name_bound_initial:
  le_round_name_bound fn fn []
Proof
  simp[le_round_name_bound_def, le_opcode_names_def, SUBSET_DEF]
QED

Theorem le_round_name_bound_fresh:
  le_round_name_bound original fn ops /\
  ctx.lctx_config.lc_load <> PHI /\ ctx.lctx_config.lc_load <> ASSIGN /\
  ctx.lctx_config.lc_load <> NOP ==>
  load_elim_one_fresh ctx g fn SUBSET
    le_opcode_names original [ctx.lctx_config.lc_load]
Proof
  simp[le_round_name_bound_def, SUBSET_DEF] >> rpt strip_tac >>
  drule le_round_fresh_origin >> strip_tac >>
  simp[le_opcode_names_def] >> metis_tac[]
QED

Theorem le_round_name_bound_step:
  le_round_name_bound original fn ops /\ wf_function fn /\
  ctx.lctx_config.lc_load <> PHI /\ ctx.lctx_config.lc_load <> ASSIGN /\
  ctx.lctx_config.lc_load <> NOP ==>
  le_round_name_bound original (load_elim_one ctx g fn)
    (ctx.lctx_config.lc_load::ops)
Proof
  strip_tac >>
  drule_all le_round_name_bound_fresh >> disch_then (qspec_then `g` assume_tac) >>
  gvs[le_round_name_bound_def, SUBSET_DEF] >> conj_tac
  >- (rpt strip_tac >> drule_all le_round_vars_bound >> strip_tac
      >- (first_x_assum drule >> simp[le_opcode_names_def] >> metis_tac[]) >>
      first_x_assum drule >> simp[le_opcode_names_def] >> metis_tac[]) >>
  rpt strip_tac >> metis_tac[le_round_other_opcode_origin]
QED

Theorem le_round_name_bound_disjoint:
  le_round_name_bound original fn ops /\ fn_inst_ids_distinct original /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars original) /\
  ~MEM ctx.lctx_config.lc_load ops /\
  ctx.lctx_config.lc_load <> PHI /\ ctx.lctx_config.lc_load <> ASSIGN /\
  ctx.lctx_config.lc_load <> NOP ==>
  DISJOINT (load_elim_one_fresh ctx g fn) (set (fn_all_vars fn))
Proof
  strip_tac >>
  drule_all le_round_name_bound_fresh >> disch_then (qspec_then `g` assume_tac) >>
  `DISJOINT (le_opcode_names original [ctx.lctx_config.lc_load])
            (le_opcode_names original ops)` by
    (irule le_opcode_names_disjoint >> simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  drule le_opcode_names_source_disjoint >>
  disch_then (qspec_then `[ctx.lctx_config.lc_load]` assume_tac) >>
  gvs[le_round_name_bound_def, SUBSET_DEF, DISJOINT_DEF, EXTENSION] >>
  metis_tac[]
QED

(* Intermediate well-formedness is the independent RoundWf obligation.
   CFG, BP and alias fields of the contexts need not be rebuilt here. *)
Theorem le_five_round_name_separation:
  wf_function fn /\ wf_function fn1 /\ wf_function fn2 /\ wf_function fn3 /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
  c1.lctx_config.lc_load = MLOAD /\ c2.lctx_config.lc_load = TLOAD /\
  c3.lctx_config.lc_load = SLOAD /\ c4.lctx_config.lc_load = DLOAD /\
  c5.lctx_config.lc_load = CALLDATALOAD /\
  fn1 = load_elim_one c1 g fn /\ fn2 = load_elim_one c2 g fn1 /\
  fn3 = load_elim_one c3 g fn2 /\ fn4 = load_elim_one c4 g fn3 ==>
  DISJOINT (load_elim_one_fresh c1 g fn) (set (fn_all_vars fn)) /\
  DISJOINT (load_elim_one_fresh c2 g fn1) (set (fn_all_vars fn1)) /\
  DISJOINT (load_elim_one_fresh c3 g fn2) (set (fn_all_vars fn2)) /\
  DISJOINT (load_elim_one_fresh c4 g fn3) (set (fn_all_vars fn3)) /\
  DISJOINT (load_elim_one_fresh c5 g fn4) (set (fn_all_vars fn4))
Proof
  strip_tac >>
  `le_round_name_bound fn fn []` by simp[le_round_name_bound_initial] >>
  `le_round_name_bound fn fn1 [MLOAD]` by
    (qpat_x_assum `fn1 = _` SUBST1_TAC >>
     ` [MLOAD] = c1.lctx_config.lc_load::[]` by simp[] >>
     pop_assum SUBST1_TAC >> irule le_round_name_bound_step >> simp[]) >>
  `le_round_name_bound fn fn2 [TLOAD; MLOAD]` by
    (qpat_x_assum `fn2 = _` SUBST1_TAC >>
     `[TLOAD; MLOAD] = c2.lctx_config.lc_load::[MLOAD]` by simp[] >>
     pop_assum SUBST1_TAC >> irule le_round_name_bound_step >> simp[]) >>
  `le_round_name_bound fn fn3 [SLOAD; TLOAD; MLOAD]` by
    (qpat_x_assum `fn3 = _` SUBST1_TAC >>
     `[SLOAD; TLOAD; MLOAD] = c3.lctx_config.lc_load::[TLOAD; MLOAD]` by simp[] >>
     pop_assum SUBST1_TAC >> irule le_round_name_bound_step >> simp[]) >>
  `le_round_name_bound fn fn4 [DLOAD; SLOAD; TLOAD; MLOAD]` by
    (qpat_x_assum `fn4 = _` SUBST1_TAC >>
     `[DLOAD; SLOAD; TLOAD; MLOAD] = c4.lctx_config.lc_load::[SLOAD; TLOAD; MLOAD]` by simp[] >>
     pop_assum SUBST1_TAC >> irule le_round_name_bound_step >> simp[]) >>
  `fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
  conj_tac
  >- (irule le_round_name_bound_disjoint >> simp[] >>
      qexistsl [`[]`, `fn`] >> gvs[]) >>
  conj_tac
  >- (irule le_round_name_bound_disjoint >> simp[] >>
      qexistsl [`[MLOAD]`, `fn`] >> gvs[]) >>
  conj_tac
  >- (irule le_round_name_bound_disjoint >> simp[] >>
      qexistsl [`[TLOAD; MLOAD]`, `fn`] >> gvs[]) >>
  conj_tac
  >- (irule le_round_name_bound_disjoint >> simp[] >>
      qexistsl [`[SLOAD; TLOAD; MLOAD]`, `fn`] >> gvs[]) >>
  irule le_round_name_bound_disjoint >> simp[] >>
  qexistsl [`[DLOAD; SLOAD; TLOAD; MLOAD]`, `fn`] >> gvs[]
QED
