(*
 * Static facts about the planner state partway through a block: the
 * state block_plan_state names at instruction index k, when the block is
 * planned from its lineage state (fnPlanLineage, fnLineageStatic).  The
 * block body's induction (fnBlockBody) needs them at each instruction for
 * the planner-only premises of the instruction frame lemmas (fnFrameDeep),
 * of revert forwarding (fnFrameStepsRevertForwardDeep) and of the alias
 * step (fnAliasStep).
 *
 * TOP-LEVEL:
 *   block_plan_state         - the planner state at an instruction index
 *   block_plan_state_static  - CHEATED: at an instruction past the PHI
 *                              prefix, the state is well formed, holds the
 *                              instruction's variable operands, and nothing
 *                              on its stack or in its spill map stands for
 *                              one of the instruction's outputs
 *)

Theory fnBlockPlanStatic
Ancestors
  fnLineageStatic fnPlanPrefix fnPlanLineage reorderSim contextCodegenRel
  stackPlanGen stackPlanOps stackPlanTypes venomExecSemantics venomWf
  livenessDefs dfgDefs cfgDefs fnBlockPlanStaticRetRegion fnBlockPlanStaticInventory
  fnBlockPlanStaticPromises fnBlockPlanStaticRegion fnBlockPlanStaticBodyPrefix
  fnBlockPlanStaticAccounting fnBlockPlanStaticBalance simplifyCfgStruct venomExecProps venomInst
  fnBlockPlanStaticDfsTrace cfgAnalysisProps fnPlanLineageJoin
  fnBlockPlanStaticJoinCardinality

(* The planner state at instruction index k of bb, when generate_block_plan
   plans bb from ps_in: the parameter and cleanup prefixes, then the
   non-parameter instructions before k. *)
Definition block_plan_state_def:
  block_plan_state liveness dfg cfg fn bb ps_in k ps <=>
    ?param_ops ps1 clean_ops ps2 pre_ops.
      (if bb = HD fn.fn_blocks then prepare_params_plan liveness fn ps_in
       else ([], ps_in)) = (param_ops, ps1) /\
      (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
       then clean_stack_plan liveness cfg fn bb ps1
       else ([], ps1)) = (clean_ops, ps2) /\
      LENGTH (get_params bb.bb_instructions) <= k /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0
        (k - LENGTH (get_params bb.bb_instructions))
        (non_param_insts bb) ps2 = SOME (pre_ops, ps)
End

Theorem regional_actual_phi_cut:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps_l h promised p k ps.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops,ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps_l /\ collect_phis bb.bb_instructions <> [] /\
    p = LENGTH (collect_phis bb.bb_instructions) /\
    p <= k /\ k <= LENGTH bb.bb_instructions /\
    block_plan_state lv dfg cfg fn bb
      (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) k ps ==>
    ?mid tail_ops.
      regional_selected_phi_inv lv dfg sb bb p mid /\
      generate_block_insts_prefix lv dfg cfg fn bb.bb_label (bb_is_halting bb)
        0 (LENGTH bb.bb_instructions) p (k-p) (DROP p bb.bb_instructions) mid =
        SOME (tail_ops,ps)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all regional_phi_no_params >> strip_tac >>
  qpat_x_assum `block_plan_state _ _ _ _ _ _ _ _` mp_tac >>
  simp[block_plan_state_def] >> strip_tac >>
  `p <= LENGTH bb.bb_instructions` by simp[] >>
  qpat_x_assum `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _`
    mp_tac >>
  `k = p + (k-p)` by simp[] >> pop_assum SUBST1_TAC >>
  simp[regional_block_prefix_cut, PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  qexistsl [`mid`, `post`] >> simp[] >>
  gvs[] >> irule regional_lineage_selected_phi_prefix >>
  rpt (first_assum $ irule_at Any) >> simp[]
QED

Theorem regional_actual_phi_lower_inv:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps_l h promised p k ps.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops,ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps_l /\ collect_phis bb.bb_instructions <> [] /\
    p = LENGTH (collect_phis bb.bb_instructions) /\
    p <= k /\ k < LENGTH bb.bb_instructions /\
    block_plan_state lv dfg cfg fn bb
      (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) k ps ==>
    regional_body_lower_inv lv dfg sb bb k ps
Proof
  rpt gen_tac >> strip_tac >>
  `k <= LENGTH bb.bb_instructions` by simp[] >>
  drule_all regional_actual_phi_cut >> strip_tac >>
  `regional_body_lower_inv lv dfg sb bb p mid` by
    metis_tac[regional_selected_phi_exit_lower_inv] >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule lineage_state_dfs_fields >> strip_tac >>
     `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
       metis_tac[dfs_block_state_cfg_reachable] >>
     `wf_function fn` by gvs[codegen_ready_fn_def] >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  qpat_x_assum `lv = _` SUBST_ALL_TAC >>
  qpat_x_assum `dfg = _` SUBST_ALL_TAC >>
  `k = p + (k-p)` by simp[] >> pop_assum SUBST1_TAC >>
  irule regional_body_lower_inv_prefix >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule regional_phi_body_layout >> simp[] >>
      conj_tac >- (qexists_tac `k` >> simp[]) >>
      qexists_tac `fn` >> simp[]) >>
  qexistsl_tac [`cfg`, `tail_ops`, `mid`, `0`] >> gvs[]
QED

Theorem regional_actual_no_phi_lower_inv:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps_l h promised a k ps.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops,ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps_l /\ collect_phis bb.bb_instructions = [] /\
    a = LENGTH (get_params bb.bb_instructions) /\
    a <= k /\ k < LENGTH bb.bb_instructions /\
    block_plan_state lv dfg cfg fn bb
      (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) k ps ==>
    regional_body_lower_inv lv dfg sb bb k ps
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[livenessTransferProofsTheory.lookup_block_mem] >>
  drule_all regional_canonical_body_layout >> strip_tac >>
  qpat_x_assum `block_plan_state _ _ _ _ _ _ _ _` mp_tac >>
  simp[block_plan_state_def] >> strip_tac >>
  `regional_body_lower_inv lv dfg sb bb a ps2` by
    (Cases_on `bb = HD fn.fn_blocks`
     >- (gvs[] >> metis_tac[regional_entry_lower_start]) >>
     `a = 0` by simp[] >> gvs[] >>
     irule regional_nonentry_no_phi_lower_start >>
     rpt (first_assum $ irule_at Any) >> simp[] >>
     qexistsl_tac [`promised`, `h`] >> simp[]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule lineage_state_dfs_fields >> strip_tac >>
     `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
       metis_tac[dfs_block_state_cfg_reachable] >>
     `wf_function fn` by gvs[codegen_ready_fn_def] >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  qpat_x_assum `lv = _` SUBST_ALL_TAC >>
  qpat_x_assum `dfg = _` SUBST_ALL_TAC >>
  `k = a + (k-a)` by simp[] >> pop_assum SUBST1_TAC >>
  irule regional_body_lower_inv_prefix >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule regional_no_phi_body_layout >> simp[] >>
      conj_tac >- (qexists_tac `k` >> simp[]) >>
      qexists_tac `fn` >> simp[]) >>
  qexistsl_tac [`cfg`, `pre_ops`, `ps2`, `a`] >> gvs[]
QED

Theorem regional_actual_lower_inv:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps_l h promised k ps.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops,ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps_l /\
    MAX (LENGTH (get_params bb.bb_instructions))
      (LENGTH (collect_phis bb.bb_instructions)) <= k /\
    k < LENGTH bb.bb_instructions /\
    block_plan_state lv dfg cfg fn bb
      (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) k ps ==>
    regional_body_lower_inv lv dfg sb bb k ps
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `collect_phis bb.bb_instructions = []`
  >- (irule regional_actual_no_phi_lower_inv >>
      rpt (first_assum $ irule_at Any) >> simp[] >>
      qexists_tac `LENGTH (get_params bb.bb_instructions)` >> gvs[arithmeticTheory.MAX_DEF]) >>
  irule (Q.INST [`p` |-> `LENGTH (collect_phis bb.bb_instructions)`]
    (SPEC_ALL regional_actual_phi_lower_inv)) >>
  rpt (first_assum $ irule_at Any) >> gvs[arithmeticTheory.MAX_DEF]
QED

Theorem regional_collect_phis_length:
  !xs. LENGTH (collect_phis xs) = phi_prefix_length xs
Proof
  Induct >> simp[collect_phis_def, phi_prefix_length_def] >>
  gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem regional_actual_lower_inv_at_phi_index:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps_l h promised k ps.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops,ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps_l /\
    phi_prefix_length bb.bb_instructions <= k /\
    k < LENGTH bb.bb_instructions /\
    block_plan_state lv dfg cfg fn bb
      (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) k ps ==>
    regional_body_lower_inv lv dfg sb bb k ps
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH (get_params bb.bb_instructions) <= k` by
    gvs[block_plan_state_def] >>
  irule regional_actual_lower_inv >>
  rpt (first_assum $ irule_at Any) >>
  gvs[arithmeticTheory.MAX_DEF, regional_collect_phis_length]
QED

Theorem ready_ret_body_no_jmp:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM ret bb.bb_instructions /\ ret.inst_opcode = RET ==>
  EVERY (\inst. inst.inst_opcode <> JMP) (non_param_insts bb)
Proof
  strip_tac >> drule_all ready_block_ret_last >> strip_tac >>
  drule lookup_block_MEM >> strip_tac >>
  `bb_well_formed bb` by
    (fs[codegen_ready_fn_def, wf_function_def] >> metis_tac[]) >>
  simp[non_param_insts_def, listTheory.EVERY_FILTER, listTheory.EVERY_MEM] >>
  rpt strip_tac >> fs[listTheory.MEM_FILTER] >>
  `inst = LAST bb.bb_instructions` by
    (irule bb_well_formed_terminator_last >> simp[is_terminator_def]) >>
  gvs[]
QED

Theorem non_phi_index_after_prefix:
  (EL j insts).inst_opcode <> PHI ==> phi_prefix_length insts <= j
Proof
  qid_spec_tac `j` >> Induct_on `insts` >>
  simp[phi_prefix_length_def] >> gen_tac >>
  Cases_on `j` >> simp[phi_prefix_length_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[]
QED

Theorem regional_dfs_preorder_member:
  codegen_ready_fn fn /\
  dfs_block_state lv dfg (cfg_analyze fn) fn ps0 lbl ps ==>
  MEM lbl (cfg_analyze fn).cfg_dfs_pre
Proof
  strip_tac >> drule_all dfs_block_state_cfg_reachable >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem regional_replay_prefix_lower_certificate:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_l /\
  (if bb = HD fn.fn_blocks then prepare_params_plan lv fn
     (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
   else ([], ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
    (param_ops,ps1) /\
  (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
   then clean_stack_plan lv cfg fn bb ps1 else ([],ps1)) = (clean_ops,ps2) /\
  a = LENGTH (get_params bb.bb_instructions) ==>
  !j q pre. a <= j /\ j < LENGTH bb.bb_instructions /\
    generate_block_insts_prefix lv dfg cfg fn bb.bb_label (bb_is_halting bb)
      a (LENGTH bb.bb_instructions) 0 (j-a) (DROP a bb.bb_instructions) ps2 =
        SOME (pre,q) /\ (EL j bb.bb_instructions).inst_opcode <> PHI ==>
    regional_body_lower_inv lv dfg sb bb j q
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  drule_all regional_canonical_body_layout >> strip_tac >>
  irule regional_actual_lower_inv_at_phi_index >>
  rpt (first_assum $ irule_at Any) >>
  qexistsl [`promised`, `h`] >>
  conj_tac >- metis_tac[non_phi_index_after_prefix] >>
  simp[block_plan_state_def] >> rpt (first_assum $ irule_at Any) >>
  gvs[]
QED

Theorem regional_dfs_prefix_lower_certificate:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs /\
  (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps_dfs
   else ([],ps_dfs)) = (param_ops,ps1) /\
  (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
   then clean_stack_plan lv cfg fn bb ps1 else ([],ps1)) = (clean_ops,ps2) /\
  a = LENGTH (get_params bb.bb_instructions) ==>
  !j q pre. a <= j /\ j < LENGTH bb.bb_instructions /\
    generate_block_insts_prefix lv dfg cfg fn bb.bb_label (bb_is_halting bb)
      a (LENGTH bb.bb_instructions) 0 (j-a) (DROP a bb.bb_instructions) ps2 =
        SOME (pre,q) /\ (EL j bb.bb_instructions).inst_opcode <> PHI ==>
    regional_body_lower_inv lv dfg sb bb j q
Proof
  strip_tac >> drule dfs_block_state_lineage_state >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  irule regional_replay_prefix_lower_certificate >>
  rpt (first_assum $ irule_at Any) >>
  qexistsl [`ps_dfs.ps_cleanup_promised`, `param_ops`, `ps_dfs.ps_cleanup_height`] >> gvs[]
QED

Theorem regional_replay_ret_body_signed_balance:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_l /\ MEM ret bb.bb_instructions /\ ret.inst_opcode = RET /\
  (if bb = HD fn.fn_blocks then prepare_params_plan lv fn
     (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
   else ([], ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
    (param_ops,ps1) /\
  (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
   then clean_stack_plan lv cfg fn bb ps1 else ([],ps1)) = (clean_ops,ps2) /\
  generate_block_insts_plan lv dfg cfg fn bb.bb_label (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions) 0
    (non_param_insts bb) ps2 = SOME (inst_ops,qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps2.ps_stack):int) + trace_weight inst_ops +
    FOLDR ($+) (0:int) (MAP instruction_correction (non_param_insts bb))
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  drule_all regional_canonical_body_layout >> strip_tac >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule lineage_state_dfs_fields >> strip_tac >>
     metis_tac[regional_dfs_preorder_member]) >>
  `EVERY (\inst. inst.inst_opcode <> JMP) (non_param_insts bb)` by
    metis_tac[ready_ret_body_no_jmp] >>
  irule (INST_TYPE [``:'a`` |-> ``:cfg_analysis``] reachable_suffix_signed_balance) >>
  rpt (first_assum $ irule_at Any) >>
  qexistsl [`LENGTH (get_params bb.bb_instructions)`, `sb`, `cfg`] >>
  gvs[] >> reverse conj_tac
  >- (qspec_then `bb.bb_instructions` strip_assume_tac
        fnFrameBoundaryEntryParamsTheory.get_params_suffix >>
      pop_assum (mp_tac o AP_TERM ``LENGTH:instruction list->num``) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  irule regional_replay_prefix_lower_certificate >>
  rpt (first_assum $ irule_at Any) >> gvs[]
QED

Theorem regional_dfs_ret_body_signed_balance:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs /\ MEM ret bb.bb_instructions /\ ret.inst_opcode = RET /\
  (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps_dfs
   else ([],ps_dfs)) = (param_ops,ps1) /\
  (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
   then clean_stack_plan lv cfg fn bb ps1 else ([],ps1)) = (clean_ops,ps2) /\
  generate_block_insts_plan lv dfg cfg fn bb.bb_label (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions) 0
    (non_param_insts bb) ps2 = SOME (inst_ops,qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps2.ps_stack):int) + trace_weight inst_ops +
    FOLDR ($+) (0:int) (MAP instruction_correction (non_param_insts bb))
Proof
  strip_tac >> drule dfs_block_state_lineage_state >> strip_tac >>
  irule regional_replay_ret_body_signed_balance >>
  rpt (first_assum $ irule_at Any) >>
  qexistsl [`ps_dfs.ps_cleanup_promised`, `param_ops`, `ps_dfs.ps_cleanup_height`] >> gvs[]
QED

Theorem regional_replay_ret_block_signed_balance:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_l /\ MEM ret bb.bb_instructions /\ ret.inst_opcode = RET /\
  generate_block_plan lv dfg cfg fn bb
    (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (block_ops,qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps_l.ps_stack):int) + trace_weight block_ops +
    &(LENGTH (get_params bb.bb_instructions)) +
    FOLDR ($+) (0:int) (MAP instruction_correction (non_param_insts bb))
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `generate_block_plan _ _ _ _ _ pin` >>
  Cases_on `if bb = HD fn.fn_blocks then prepare_params_plan lv fn pin else ([],pin)` >>
  rename1 `_ = (param_ops,ps1)` >>
  Cases_on `if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
    then clean_stack_plan lv cfg fn bb ps1 else ([],ps1)` >>
  rename1 `_ = (clean_ops,ps2)` >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `_ = (inst_ops,qs)` SUBST_ALL_TAC >>
  `&(LENGTH qs.ps_stack) = (&(LENGTH ps2.ps_stack):int) + trace_weight inst_ops +
    FOLDR ($+) (0:int) (MAP instruction_correction (non_param_insts bb))` by
    (gvs[Abbr `pin`] >> irule regional_replay_ret_body_signed_balance >>
     rpt (first_assum $ irule_at Any) >>
     gvs[]) >>
  `&(LENGTH ps1.ps_stack) = (&(LENGTH pin.ps_stack):int) + trace_weight param_ops +
    &(LENGTH (get_params bb.bb_instructions))` by
    (Cases_on `bb = HD fn.fn_blocks`
     >- (gvs[] >> drule prepare_params_plan_signed_balance >> simp[]) >>
     `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
     drule_all regional_canonical_body_layout >> strip_tac >>
     gvs[trace_weight_def]) >>
  `&(LENGTH ps2.ps_stack) = (&(LENGTH ps1.ps_stack):int) + trace_weight clean_ops` by
    (Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1` >> gvs[trace_weight_def] >>
     drule clean_stack_plan_signed_balance >> simp[]) >>
  gvs[trace_weight_def, trace_weight_append, stack_op_weight_def, Abbr `pin`] >>
  intLib.ARITH_TAC
QED

Theorem regional_dfs_ret_block_signed_balance:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs /\ MEM ret bb.bb_instructions /\ ret.inst_opcode = RET /\
  generate_block_plan lv dfg cfg fn bb ps_dfs = SOME (block_ops,qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps_dfs.ps_stack):int) + trace_weight block_ops +
    &(LENGTH (get_params bb.bb_instructions)) +
    FOLDR ($+) (0:int) (MAP instruction_correction (non_param_insts bb))
Proof
  strip_tac >> drule dfs_block_state_lineage_state >> strip_tac >>
  irule regional_replay_ret_block_signed_balance >>
  rpt (first_assum $ irule_at Any) >>
  qexistsl [`ps_dfs.ps_cleanup_promised`, `ps_dfs.ps_cleanup_height`] >> gvs[]
QED

(* Used at each instruction of the block body's induction, for the
   planner-only premises of the step it takes there.  next_live and
   next_is_term are the lookahead generate_block_insts_plan passes for
   instruction k (live_vars_at at k + 1 in both of its cases, since the
   block length is k + 1 when k is last).  The opcode-guarded clauses are
   the premises of gen_jnz_frame_sim_deep, gen_jmp_frame_sim_deep,
   gen_ret_frame_sim_deep and (at a revert forwarding's RETURNDATACOPY)
   revert_forward_frame_sim_deep that the general ones don't cover.

   PHI-operand slots: lineage_state_static's freshness exempts the PHI
   operands of a join (a loop header x = phi(.., L: v) whose body
   redefines v is entered from L with v in x's slot).  None survives the
   PHI prefix: generate_phi_plan finds the topmost slot holding one of the
   PHI's variable operands (stack_get_phi_depth) and, when that operand is
   not live after the PHI, pokes the output over it (SOPoke dist ret)
   instead of duplicating it.  phi_block_ready (codegen_ready_fn) keeps
   every PHI operand dead after the prefix and out of the other PHIs, so
   the poke is the case taken.  This relies on the entry stack holding
   one operand per PHI, the one from the edge taken (input_vars_from);
   lineage_state_static does not say so of slots below the join's target
   stack.

   Why it should hold: lineage_state_static gives well-formedness and
   freshness at the block's entry.  The cleanup prefix only pops or marks
   slots, the PHI prefix overwrites its operands' slots (above), and each
   instruction before k pushes only its own outputs, distinct from inst's
   by SSA (ssa_form), whose ASSIGN-chain roots are defined before them and
   so are not inst's outputs either (def_dominates_uses).  A variable
   operand of inst is live before it, and the planner holds every live
   variable on its stack or in its spill map: the join entry stack is the
   live-in set, a single-predecessor block gets its predecessor's live-out
   set, and an instruction consumes a variable only at its last use.  The
   same holds for the JMP target's live-in variables, and the operands of
   a revert forwarding's instructions not defined inside it.  A RET block
   is not on a must-halt path, so it has no dead_stack_marker slots, and
   every slot but RET's operands is dead and popped before it (the DFS
   premises tie h and promised: the replay must emit the DFS block's ops,
   so its cleanup pops where the DFS one does).  A revert forwarding's code
   from k on has no spill or restore: its REVERT ends bb and its
   RETURNDATACOPY is in bb, so generate_block_plan would have rejected the
   replay (revert_block_spills) had the instruction ops, of which these
   are a suffix, held one.  OPEN: a dead OFFSET
   output is pushed and never popped (generate_offset_plan), which leaves
   a slot at RET; this conjunct needs that excluded.  The
   marker clauses hold since no instruction has the marker as an operand,
   and normalize_operand only follows ASSIGNs of operands. *)
Theorem block_plan_state_static:
  !liveness dfg cfg ch growth spill_base lbl_ctr fn fn_ops ps_end lbl bb
   ps_l ps_dfs ps_dfs_after h promised block_ops ps_after k ps inst next_live
   next_is_term.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps_l /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after) /\
    generate_block_plan liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops, ps_after) /\
    block_plan_state liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
      k ps /\
    phi_prefix_length bb.bb_instructions <= k /\
    k < LENGTH bb.bb_instructions /\
    EL k bb.bb_instructions = inst /\
    next_live = live_vars_at liveness bb.bb_label (k + 1) /\
    next_is_term =
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
    ==>
    generated_plan_state_wf_marked spill_base ps /\
    MEM inst (fn_insts fn) /\ inst_wf inst /\
    ~is_param_opcode inst.inst_opcode /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_live ps)).ps_stack /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v inst.inst_outputs) /\
    (inst.inst_opcode = JNZ ==>
     !cond_op if_nz if_z.
       inst.inst_operands = [cond_op; Label if_nz; Label if_z] ==>
       1 <= LENGTH (SND (emit_input_plan JNZ [cond_op] next_live ps)).ps_stack /\
       (is_var_operand cond_op ==>
         IS_SOME (stack_get_depth cond_op ps.ps_stack) \/
         IS_SOME (FLOOKUP ps.ps_spilled cond_op)) /\
       cond_op <> dead_stack_marker /\
       (!at. operand_equiv dfg cond_op at ==> at <> dead_stack_marker)) /\
    (inst.inst_opcode = JMP ==>
     !target target_bb target_stack.
       inst.inst_operands = [Label target] /\
       lookup_block target fn.fn_blocks = SOME target_bb /\
       target_stack =
         MAP Var (input_vars_from bb.bb_label target_bb.bb_instructions
                    (live_vars_at liveness target 0)) ==>
       pending_inventory_wf target_stack ps) /\
    (inst.inst_opcode = JMP ==>
     !target target_bb target_stack.
       inst.inst_operands = [Label target] /\
       lookup_block target fn.fn_blocks = SOME target_bb /\
       target_stack =
         MAP Var (input_vars_from bb.bb_label target_bb.bb_instructions
                    (live_vars_at liveness target 0)) ==>
       LENGTH target_stack <=
         LENGTH (SND (restore_spilled_plan target_stack ps)).ps_stack /\
       EVERY (\op. op <> dead_stack_marker /\
         !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
         target_stack) /\
    (inst.inst_opcode = RET ==>
     !ops ps'.
       generate_inst_plan liveness dfg cfg fn inst next_live (bb_is_halting bb)
         next_is_term bb.bb_label ps = SOME (ops, ps') ==>
       ps'.ps_stack = []) /\
    (!j. revert_forward_pair bb k j ==>
     !k' inst' op.
       k <= k' /\ get_instruction bb k' = SOME inst' /\
       MEM op (compute_operands inst') /\ is_var_operand op /\
       (!k'' inst'' x. k <= k'' /\ k'' < k' /\
                       get_instruction bb k'' = SOME inst'' /\
                       op = Var x ==> ~MEM x inst''.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!j. revert_forward_pair bb k j ==>
     !ops ps_end.
       generate_block_insts_plan liveness dfg cfg fn bb.bb_label
         (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
         (LENGTH bb.bb_instructions) (k - LENGTH (get_params bb.bb_instructions))
         (DROP k bb.bb_instructions) ps = SOME (ops, ps_end) ==>
       !off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops)
Proof
  cheat
QED

Theorem regional_actual_dfs_phi_upper_cut:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs /\ MEM ret_inst bb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  collect_phis bb.bb_instructions <> [] /\ p = LENGTH (collect_phis bb.bb_instructions) /\
  p <= k /\ k < LENGTH bb.bb_instructions /\
  block_plan_state lv dfg cfg fn bb ps_dfs k ps ==>
  ?mid tail_ops. regional_body_lower_inv lv dfg sb bb p mid /\
    EVERY (\op. ?v. op = Var v /\ MEM v (live_vars_at lv bb.bb_label p)) mid.ps_stack /\
    generate_block_insts_prefix lv dfg cfg fn bb.bb_label (bb_is_halting bb) 0
      (LENGTH bb.bb_instructions) p (k-p) (DROP p bb.bb_instructions) mid = SOME (tail_ops,ps)
Proof
  strip_tac >>
  `lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs` by metis_tac[dfs_block_state_lineage_state] >>
  `regional_selected_phi_inv lv dfg sb bb 0 ps_dfs` by
    (drule_all regional_lineage_selected_phi_inv >> simp[]) >>
  `fn_reachable fn bb.bb_label` by
    (gvs[] >> drule_all dfs_block_state_cfg_reachable >>
     `wf_function fn` by gvs[codegen_ready_fn_def] >>
     metis_tac[codegenReadyComputeTheory.fn_reachable_cfg_analyze]) >>
  `~bb_is_halting bb` by metis_tac[ready_block_ret_not_halting] >>
  `fn_entry_label fn <> SOME bb.bb_label` by
    (drule regional_entry_structure >> strip_tac >> strip_tac >> gvs[] >>
     metis_tac[]) >>
  drule_all regional_phi_no_params >> strip_tac >>
  drule_all regional_phi_preparation_identity >>
  disch_then (qspecl_then [`lv`,`ps_dfs`] strip_assume_tac) >>
  `EVERY (\op. ?v. op = Var v /\
    (regional_phi_remaining_source bb 0 v \/ MEM v (live_vars_at lv bb.bb_label 0)))
      ps_dfs.ps_stack` by
    (`cfg_path cfg bb.bb_label bb.bb_label` by simp[cfg_path_def] >>
     `?pred pred_bb. lookup_block pred fn.fn_blocks = SOME pred_bb /\
       fn_reachable fn pred /\ MEM bb.bb_label (cfg_succs_of cfg pred) /\
       EVERY (\op. ?v. op = Var v /\ MEM v
         (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0)))
         ps_dfs.ps_stack` by
       (irule regional_dfs_nonentry_cleanup_upper >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     drule_all regional_edge_input_upper >> simp[]) >>
  qpat_x_assum `block_plan_state _ _ _ _ _ _ _ _` mp_tac >>
  simp[block_plan_state_def] >> strip_tac >> fs[] >>
  `k = p + (k-p)` by simp[] >>
  qpat_x_assum `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  pop_assum SUBST1_TAC >> simp[regional_block_prefix_cut, PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> qexistsl [`mid`,`post`] >> simp[] >>
  gvs[] >> conj_tac
  >- (irule regional_selected_phi_exit_lower_inv >>
      irule (INST_TYPE [alpha |-> ``:cfg_analysis``] regional_selected_phi_inv_block_prefix) >> simp[] >>
      rename1 `regional_selected_phi_inv _ _ _ _ 0 initial` >>
      qexistsl [`cfg_analyze fn`,`pre`,`initial`] >> simp[]) >>
  irule (INST_TYPE [alpha |-> ``:cfg_analysis``] regional_selected_phi_upper_complete) >> simp[] >>
  rename1 `regional_selected_phi_inv _ _ _ _ 0 initial` >>
  qexistsl [`cfg_analyze fn`,`pre`,`initial`,`sb`] >> simp[]
QED

Theorem regional_actual_dfs_phi_body_upper:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs /\ MEM ret_inst bb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  collect_phis bb.bb_instructions <> [] /\
  LENGTH (collect_phis bb.bb_instructions) <= k /\ k < LENGTH bb.bb_instructions /\
  block_plan_state lv dfg cfg fn bb ps_dfs k ps ==>
  EVERY (\op. ?v. op = Var v /\ MEM v (live_vars_at lv bb.bb_label k)) ps.ps_stack
Proof
  strip_tac >>
  `?mid tail_ops. regional_body_lower_inv lv dfg sb bb
      (LENGTH (collect_phis bb.bb_instructions)) mid /\
    EVERY (\op. ?v. op = Var v /\ MEM v (live_vars_at lv bb.bb_label
      (LENGTH (collect_phis bb.bb_instructions)))) mid.ps_stack /\
    generate_block_insts_prefix lv dfg cfg fn bb.bb_label (bb_is_halting bb) 0
      (LENGTH bb.bb_instructions) (LENGTH (collect_phis bb.bb_instructions))
      (k - LENGTH (collect_phis bb.bb_instructions))
      (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions) mid =
      SOME (tail_ops,ps)` by
    (irule regional_actual_dfs_phi_upper_cut >> simp[] >> metis_tac[]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (`cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
       metis_tac[dfs_block_state_cfg_reachable] >>
     `wf_function fn` by gvs[codegen_ready_fn_def] >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `~bb_is_halting bb` by metis_tac[ready_block_ret_not_halting] >>
  `k = LENGTH (collect_phis bb.bb_instructions) +
    (k - LENGTH (collect_phis bb.bb_instructions))` by simp[] >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `lv = _` SUBST_ALL_TAC >>
  qpat_x_assum `dfg = _` SUBST_ALL_TAC >>
  irule regional_body_upper_prefix >> simp[] >>
  conj_tac >- metis_tac[regional_phi_body_layout] >>
  qexistsl [`cfg_analyze fn`,`tail_ops`,`mid`,`sb`,`0`] >> gvs[]
QED

Theorem regional_actual_dfs_no_phi_start_upper:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs /\ MEM ret_inst bb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  collect_phis bb.bb_instructions = [] /\
  (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps_dfs
   else ([],ps_dfs)) = (param_ops,ps1) /\
  (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then clean_stack_plan lv cfg fn bb ps1
   else ([],ps1)) = (clean_ops,ps2) ==>
  EVERY (\op. ?v. op = Var v /\ MEM v (live_vars_at lv bb.bb_label
    (LENGTH (get_params bb.bb_instructions)))) ps2.ps_stack
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  drule_all regional_canonical_body_layout >> strip_tac >>
  Cases_on `bb = HD fn.fn_blocks`
  >- (`ps_dfs = init_cleanup_plan_state ch growth sb ctr` by
        (gvs[] >> metis_tac[regional_entry_dfs_initial]) >>
      `cfg_preds_of (cfg_analyze fn) bb.bb_label = []` by
        metis_tac[regional_entry_no_preds] >>
      gvs[] >> irule regional_prepare_params_initial_upper >> simp[] >>
      qexistsl [`ch`,`ctr`,`growth`,`ch`,`param_ops`,`F`,`sb`] >>
      gvs[init_cleanup_plan_state_def]) >>
  `fn_entry_label fn <> SOME bb.bb_label` by
    (drule regional_entry_structure >> strip_tac >> strip_tac >> gvs[] >> metis_tac[]) >>
  `cfg_path cfg bb.bb_label bb.bb_label` by simp[cfg_path_def] >>
  gvs[] >>
  `?pred pred_bb. lookup_block pred fn.fn_blocks = SOME pred_bb /\
    fn_reachable fn pred /\ MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) pred) /\
    EVERY (\op. ?v. op = Var v /\ MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) bb.bb_label 0))) ps2.ps_stack` by
    (irule regional_dfs_nonentry_cleanup_upper >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all regional_edge_input_upper >>
  simp[regional_phi_remaining_source_def]
QED

Theorem regional_actual_dfs_no_phi_body_upper:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr = SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs /\ MEM ret_inst bb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  collect_phis bb.bb_instructions = [] /\
  LENGTH (get_params bb.bb_instructions) <= k /\ k < LENGTH bb.bb_instructions /\
  block_plan_state lv dfg cfg fn bb ps_dfs k ps ==>
  EVERY (\op. ?v. op = Var v /\ MEM v (live_vars_at lv bb.bb_label k)) ps.ps_stack
Proof
  strip_tac >>
  `lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs` by metis_tac[dfs_block_state_lineage_state] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  drule_all regional_canonical_body_layout >> strip_tac >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (`cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
       metis_tac[dfs_block_state_cfg_reachable] >>
     `wf_function fn` by gvs[codegen_ready_fn_def] >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `~bb_is_halting bb` by metis_tac[ready_block_ret_not_halting] >>
  qpat_x_assum `block_plan_state _ _ _ _ _ _ _ _` mp_tac >>
  simp[block_plan_state_def] >> strip_tac >>
  `EVERY (\op. ?v. op = Var v /\ MEM v (live_vars_at lv bb.bb_label
    (LENGTH (get_params bb.bb_instructions)))) ps2.ps_stack` by
    (irule regional_actual_dfs_no_phi_start_upper >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `regional_body_lower_inv lv dfg sb bb (LENGTH (get_params bb.bb_instructions)) ps2` by
    (Cases_on `bb = HD fn.fn_blocks`
     >- (gvs[] >> irule regional_entry_lower_start >>
         rpt (first_assum $ irule_at Any) >> simp[] >>
         qexistsl [`ps_dfs.ps_cleanup_promised`,`param_ops`,`ps_dfs.ps_cleanup_height`] >> simp[]) >>
     gvs[] >> irule regional_nonentry_no_phi_lower_start >>
     rpt (first_assum $ irule_at Any) >> simp[] >>
     rename1 `initial = initial with <|ps_cleanup_height := _; ps_cleanup_promised := _|>` >>
     qexistsl [`initial.ps_cleanup_promised`,`initial.ps_cleanup_height`] >> simp[]) >>
  qpat_x_assum `lv = _` SUBST_ALL_TAC >> qpat_x_assum `dfg = _` SUBST_ALL_TAC >>
  `k = LENGTH (get_params bb.bb_instructions) +
    (k - LENGTH (get_params bb.bb_instructions))` by simp[] >> pop_assum SUBST1_TAC >>
  irule regional_body_upper_prefix >> simp[] >>
  conj_tac >- metis_tac[regional_no_phi_body_layout] >>
  qexistsl [`cfg`,`pre_ops`,`ps2`,`sb`,`LENGTH (get_params bb.bb_instructions)`] >> gvs[]
QED

Theorem regional_actual_dfs_body_upper:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr = SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs /\ MEM ret_inst bb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  MAX (LENGTH (get_params bb.bb_instructions))
    (LENGTH (collect_phis bb.bb_instructions)) <= k /\ k < LENGTH bb.bb_instructions /\
  block_plan_state lv dfg cfg fn bb ps_dfs k ps ==>
  EVERY (\op. ?v. op = Var v /\ MEM v (live_vars_at lv bb.bb_label k)) ps.ps_stack
Proof
  strip_tac >>
  `LENGTH (get_params bb.bb_instructions) <= k /\
   LENGTH (collect_phis bb.bb_instructions) <= k` by
    gvs[arithmeticTheory.MAX_DEF] >>
  Cases_on `collect_phis bb.bb_instructions = []`
  >- (irule regional_actual_dfs_no_phi_body_upper >>
      rpt (first_assum $ irule_at Any) >> simp[]) >>
  irule regional_actual_dfs_phi_body_upper >>
  rpt (first_assum $ irule_at Any) >> simp[]
QED

Theorem regional_actual_dfs_ret_step_empty:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr = SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs /\
  MAX (LENGTH (get_params bb.bb_instructions))
    (LENGTH (collect_phis bb.bb_instructions)) <= k /\ k < LENGTH bb.bb_instructions /\
  block_plan_state lv dfg cfg fn bb ps_dfs k ps /\
  EL k bb.bb_instructions = inst /\ inst.inst_opcode = RET /\
  generate_inst_plan lv dfg cfg fn inst (live_vars_at lv bb.bb_label (k+1))
    (bb_is_halting bb) next_term bb.bb_label ps = SOME (ops,ps') ==>
  ps'.ps_stack = []
Proof
  strip_tac >>
  `MEM inst bb.bb_instructions` by metis_tac[listTheory.EL_MEM] >>
  `lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs` by metis_tac[dfs_block_state_lineage_state] >>
  `regional_body_lower_inv lv dfg sb bb k ps` by
    (irule regional_actual_lower_inv >> rpt (first_assum $ irule_at Any) >> simp[] >>
     qexistsl [`ps_dfs.ps_cleanup_promised`,`ps_dfs.ps_cleanup_height`] >> gvs[]) >>
  `EVERY (\op. ?v. op = Var v /\ MEM v (live_vars_at lv bb.bb_label k)) ps.ps_stack` by
    (irule regional_actual_dfs_body_upper >> rpt (first_assum $ irule_at Any) >> simp[]) >>
  `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by metis_tac[dfs_block_state_cfg_reachable] >>
  `live_vars_at lv bb.bb_label (k+1) = []` by
    (gvs[] >> irule regional_ret_next_live_empty >> metis_tac[]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (`wf_function fn` by gvs[codegen_ready_fn_def] >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `codegen_ready_inst inst /\ inst_wf inst` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, listTheory.EVERY_MEM] >>
     metis_tac[lookup_block_MEM]) >>
  `EVERY (\op. ?v. op = Var v /\ MEM op (compute_operands inst)) ps.ps_stack` by
    (`EVERY (\op. ?v. op = Var v /\
       (MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) \/
        MEM op (compute_operands inst))) ps.ps_stack` by
       (irule regional_body_upper_input_support >>
        rpt (first_assum $ irule_at Any) >> gvs[] >> metis_tac[]) >>
     gvs[arithmeticTheory.ADD1]) >>
  `ALL_DISTINCT ps.ps_stack /\
   DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled)` by
    metis_tac[regional_body_upper_resources] >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (gvs[] >> metis_tac[regional_body_lower_inv_operands]) >>
  `LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan RET (compute_operands inst) [] ps)).ps_stack` by
    (gvs[] >> metis_tac[regional_body_lower_inv_input_capacity]) >>
  `LENGTH (compute_operands inst) <= 16 /\ inst.inst_outputs = []` by
    gvs[codegen_ready_inst_def, venomWfTheory.inst_wf_def] >>
  irule (INST_TYPE [alpha |-> ``:cfg_analysis``] regional_ret_operand_support_empty) >>
  rpt (first_assum $ irule_at Any) >> gvs[] >> metis_tac[]
QED

Theorem regional_ret_step_block_endpoint:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  generate_block_plan lv dfg cfg fn bb pin = SOME (block_ops,qs) /\
  block_plan_state lv dfg cfg fn bb pin k ps /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = RET /\
  generate_inst_plan lv dfg cfg fn inst
    (live_vars_at lv bb.bb_label (k+1)) (bb_is_halting bb) F bb.bb_label ps =
    SOME (ops,ps') ==> ps' = qs
Proof
  strip_tac >>
  `k + 1 = LENGTH bb.bb_instructions` by metis_tac[ready_block_ret_index_last] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  drule_all regional_canonical_body_layout >> strip_tac >>
  gvs[block_plan_state_def] >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  `k - LENGTH (get_params bb.bb_instructions) <=
    LENGTH (DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions)` by
    (simp[listTheory.LENGTH_DROP] >> decide_tac) >>
  mp_tac (Q.SPECL [`k - LENGTH (get_params bb.bb_instructions)`,
    `DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions`]
    (INST_TYPE [alpha |-> ``:cfg_analysis``] generate_block_insts_plan_split)) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th =>
    qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
    pure_rewrite_tac[th]) >> strip_tac >>
  gvs[rich_listTheory.DROP_DROP_T] >>
  `DROP k bb.bb_instructions = [EL k bb.bb_instructions]` by
    (irule listTheory.LIST_EQ >>
     reverse conj_tac >- (simp[listTheory.LENGTH_DROP] >> decide_tac) >>
     simp[NoAsms, listTheory.LENGTH_DROP, listTheory.EL_DROP] >>
     qx_gen_tac `idx` >> strip_tac >> `idx = 0` by decide_tac >> gvs[]) >>
  gvs[generate_block_insts_plan_def, AllCaseEqs()]
QED

Theorem regional_ret_block_last_step:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  MEM ret bb.bb_instructions /\ ret.inst_opcode = RET /\
  generate_block_plan lv dfg cfg fn bb pin = SOME (block_ops,qs) ==>
  ?k ps ops.
    LENGTH (get_params bb.bb_instructions) <= k /\
    phi_prefix_length bb.bb_instructions <= k /\ k < LENGTH bb.bb_instructions /\
    EL k bb.bb_instructions = ret /\
    block_plan_state lv dfg cfg fn bb pin k ps /\
    generate_inst_plan lv dfg cfg fn ret
      (live_vars_at lv bb.bb_label (k+1)) (bb_is_halting bb) F bb.bb_label ps =
      SOME (ops,qs)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM ret (non_param_insts bb)` by
    simp[non_param_insts_def, listTheory.MEM_FILTER, is_param_opcode_def] >>
  drule_all regional_canonical_body_layout >> strip_tac >>
  qpat_x_assum `MEM ret (non_param_insts bb)` mp_tac >>
  simp[listTheory.MEM_EL] >> disch_then (qx_choose_then `j` strip_assume_tac) >>
  qabbrev_tac `k = j + LENGTH (get_params bb.bb_instructions)` >>
  `k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = ret` by
    (gvs[listTheory.LENGTH_DROP, listTheory.EL_DROP, Abbr `k`] >> decide_tac) >>
  `k+1 = LENGTH bb.bb_instructions` by metis_tac[ready_block_ret_index_last] >>
  `phi_prefix_length bb.bb_instructions <= k` by
    (irule non_phi_index_after_prefix >> gvs[]) >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`j`,
    `DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions`]
    (INST_TYPE [alpha |-> ``:cfg_analysis``] generate_block_insts_plan_split)) >>
  (impl_tac >- (simp[listTheory.LENGTH_DROP] >> gvs[Abbr `k`] >> decide_tac)) >>
  disch_then (fn th =>
    qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
    pure_rewrite_tac[th]) >> strip_tac >>
  gvs[rich_listTheory.DROP_DROP_T] >>
  `DROP k bb.bb_instructions = [EL k bb.bb_instructions]` by
    (irule listTheory.LIST_EQ >>
     reverse conj_tac >- (simp[listTheory.LENGTH_DROP] >> decide_tac) >>
     simp[NoAsms, listTheory.LENGTH_DROP, listTheory.EL_DROP] >>
     qx_gen_tac `idx` >> strip_tac >> `idx = 0` by decide_tac >> gvs[]) >>
  gvs[generate_block_insts_plan_def, CaseEq "option", CaseEq "prod"] >>
  qexists_tac `k` >>
  `LENGTH (get_params bb.bb_instructions) <= k` by simp[Abbr `k`] >>
  simp[] >>
  qexistsl_tac [`ps_mid`, `post`] >> simp[] >>
  simp[block_plan_state_def, Abbr `k`] >> metis_tac[]
QED

Theorem regional_actual_dfs_ret_block_empty:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs /\ MEM ret bb.bb_instructions /\ ret.inst_opcode = RET /\
  generate_block_plan lv dfg cfg fn bb ps_dfs = SOME (block_ops,qs) ==>
  qs.ps_stack = []
Proof
  strip_tac >> drule_all regional_ret_block_last_step >> strip_tac >>
  irule regional_actual_dfs_ret_step_empty >>
  rpt (first_assum $ irule_at Any) >>
  gvs[arithmeticTheory.MAX_DEF, regional_collect_phis_length]
QED

Theorem regional_dfs_unique_predecessor_endpoint:
  cfg = cfg_analyze fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,pend) /\
  fn_entry_label fn <> SOME succ /\ cfg_preds_of cfg succ = [pred] /\
  lookup_block pred fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) pred pin /\
  generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) succ ds ==>
  ds.ps_stack = pout.ps_stack /\ ds.ps_spilled = pout.ps_spilled
Proof
  strip_tac >>
  qpat_x_assum `dfs_block_state _ _ _ _ _ succ ds`
    (mp_tac o MATCH_MP dfs_block_state_inverse_origin) >>
  simp[] >> strip_tac >>
  rename1 `MEM succ (cfg_succs_of (cfg_analyze fn) origin)` >>
  `origin = pred` by (gvs[] >> metis_tac[cfg_edge_symmetry_uncond, listTheory.MEM]) >>
  gvs[] >>
  rename1 `generate_block_plan lv dfg _ fn bb other_in = SOME _` >>
  `other_in = pin` by (irule dfs_block_state_unique >> metis_tac[]) >>
  gvs[]
QED

Theorem regional_dfs_unique_predecessor_height:
  cfg = cfg_analyze fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,pend) /\
  fn_entry_label fn <> SOME succ /\ cfg_preds_of cfg succ = [pred] /\
  lookup_block pred fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) pred pin /\
  generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) succ ds /\
  LENGTH replay_out.ps_stack <= LENGTH pout.ps_stack ==>
  LENGTH replay_out.ps_stack <= LENGTH ds.ps_stack
Proof
  strip_tac >>
  drule_all regional_dfs_unique_predecessor_endpoint >> simp[]
QED

Theorem regional_ret_reaching_dfs_join_exact:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  fn_entry_label fn <> SOME lbl /\ LENGTH (cfg_preds_of cfg lbl) <> 1 /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) lbl ds /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret retbb.bb_instructions /\ ret.inst_opcode = RET /\
  cfg_path cfg lbl target ==>
  ?pred pred_bb. lookup_block pred fn.fn_blocks = SOME pred_bb /\
    fn_reachable fn pred /\ MEM lbl (cfg_succs_of cfg pred) /\
    ds.ps_stack = MAP Var (input_vars_from pred bb.bb_instructions
      (live_vars_at lv lbl 0))
Proof
  strip_tac >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  `~MEM dead_stack_marker ds.ps_stack` by
    (irule regional_ret_reaching_dfs_marker_free >> metis_tac[]) >>
  drule_all regional_dfs_incoming_lineage_entry >> strip_tac >>
  `?pre. ds.ps_stack = pre ++ MAP Var (input_vars_from pred bb.bb_instructions
      (live_vars_at lv lbl 0)) /\ EVERY (\op. op = dead_stack_marker) pre` by
    (qpat_x_assum `bb.bb_label = lbl` (SUBST_ALL_TAC o SYM) >>
     drule_all lineage_entry_join_stack >> simp[]) >>
  `pre = []` by
    (Cases_on `pre` >> gvs[listTheory.EVERY_DEF]) >>
  gvs[] >> metis_tac[]
QED

Theorem regional_ret_reaching_dfs_edge_join_exact:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block succ fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) pred pin /\
  generate_block_plan lv dfg cfg fn pb pin = SOME (ops,pout) /\
  MEM succ (cfg_succs_of cfg pred) /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) succ sin /\
  LENGTH (cfg_preds_of cfg succ) <> 1 /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret retbb.bb_instructions /\ ret.inst_opcode = RET /\
  cfg_path cfg succ target ==>
  pout.ps_stack = MAP Var (input_vars_from pred bb.bb_instructions
    (live_vars_at lv succ 0))
Proof
  strip_tac >>
  `bb.bb_label = succ` by metis_tac[lookup_block_label] >>
  `cfg_path cfg pred target` by metis_tac[cfg_path_predecessor_closed] >>
  `~MEM dead_stack_marker pin.ps_stack` by
    (irule regional_ret_reaching_dfs_marker_free >> metis_tac[]) >>
  `~MEM dead_stack_marker pout.ps_stack` by
    (irule regional_dfs_block_marker_free >> metis_tac[]) >>
  `lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) pred pin`
    by metis_tac[dfs_block_state_lineage_state] >>
  `lineage_entry lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    pred succ (sin with <|ps_stack := pout.ps_stack; ps_spilled := pout.ps_spilled|>)`
    by (simp[lineage_entry_def] >>
        qexistsl_tac [`pin`, `pin`, `ops`, `pout`,
          `pin.ps_cleanup_height`, `pin.ps_cleanup_promised`, `pout`, `sin`] >>
        gvs[]) >>
  qpat_x_assum `bb.bb_label = succ` (SUBST_ALL_TAC o SYM) >>
  drule_all lineage_entry_join_stack >> simp[] >> strip_tac >>
  `pre = []` by (Cases_on `pre` >> gvs[listTheory.EVERY_DEF]) >> gvs[]
QED

Theorem regional_ret_reaching_dfs_edge_height:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,pend) /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block succ fn.fn_blocks = SOME bb /\ fn_entry_label fn <> SOME succ /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) pred pin /\
  generate_block_plan lv dfg cfg fn pb pin = SOME (ops,pout) /\
  MEM succ (cfg_succs_of cfg pred) /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) succ sin /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret retbb.bb_instructions /\ ret.inst_opcode = RET /\
  cfg_path cfg succ target ==>
  LENGTH pout.ps_stack = LENGTH sin.ps_stack
Proof
  strip_tac >> Cases_on `LENGTH (cfg_preds_of cfg succ) = 1`
  >- (`cfg_preds_of cfg succ = [pred]` by
        (Cases_on `cfg_preds_of cfg succ` >> gvs[] >>
         metis_tac[cfg_edge_symmetry_uncond, listTheory.MEM]) >>
      drule_all regional_dfs_unique_predecessor_endpoint >> simp[]) >>
  `pout.ps_stack = MAP Var (input_vars_from pred bb.bb_instructions
    (live_vars_at lv succ 0))` by
    (irule regional_ret_reaching_dfs_edge_join_exact >> metis_tac[]) >>
  drule_all regional_ret_reaching_dfs_join_exact >>
  disch_then (qx_choose_then `origin` (qx_choose_then `origin_bb` strip_assume_tac)) >>
  `bb.bb_label = succ /\ MEM bb fn.fn_blocks` by
    metis_tac[lookup_block_label, livenessTransferProofsTheory.lookup_block_mem] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `fn_cfg_edge fn pred bb.bb_label /\ fn_cfg_edge fn origin bb.bb_label` by
    metis_tac[codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze] >>
  gvs[listTheory.LENGTH_MAP] >>
  irule ready_input_vars_from_edge_length >> qexists_tac `fn` >> simp[]
QED

Theorem regional_replay_body_signed_balance:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_l /\
  (if bb = HD fn.fn_blocks then prepare_params_plan lv fn
     (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
   else ([], ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
    (param_ops,ps1) /\
  (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
   then clean_stack_plan lv cfg fn bb ps1 else ([],ps1)) = (clean_ops,ps2) /\
  generate_block_insts_plan lv dfg cfg fn bb.bb_label (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions) 0
    (non_param_insts bb) ps2 = SOME (inst_ops,qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps2.ps_stack):int) + trace_weight inst_ops +
    FOLDR ($+) (0:int) (MAP instruction_correction (non_param_insts bb))
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  drule_all regional_canonical_body_layout >> strip_tac >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule lineage_state_dfs_fields >> strip_tac >>
     metis_tac[regional_dfs_preorder_member]) >>
  irule (INST_TYPE [alpha |-> ``:cfg_analysis``] reachable_suffix_all_signed_balance) >>
  rpt (first_assum $ irule_at Any) >>
  qexistsl [`LENGTH (get_params bb.bb_instructions)`, `sb`, `cfg_analyze fn`] >>
  gvs[] >> reverse conj_tac
  >- (qspec_then `bb.bb_instructions` strip_assume_tac
        fnFrameBoundaryEntryParamsTheory.get_params_suffix >>
      pop_assum (mp_tac o AP_TERM ``LENGTH:instruction list->num``) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  irule regional_replay_prefix_lower_certificate >>
  rpt (first_assum $ irule_at Any) >> gvs[]
QED

Theorem regional_replay_block_signed_balance:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_l /\
  generate_block_plan lv dfg cfg fn bb
    (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (block_ops,qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps_l.ps_stack):int) + trace_weight block_ops +
    &(LENGTH (get_params bb.bb_instructions)) +
    FOLDR ($+) (0:int) (MAP instruction_correction (non_param_insts bb))
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `generate_block_plan _ _ _ _ _ pin` >>
  Cases_on `if bb = HD fn.fn_blocks then prepare_params_plan lv fn pin else ([],pin)` >>
  rename1 `_ = (param_ops,ps1)` >>
  Cases_on `if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
    then clean_stack_plan lv cfg fn bb ps1 else ([],ps1)` >>
  rename1 `_ = (clean_ops,ps2)` >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `_ = (inst_ops,qs)` SUBST_ALL_TAC >>
  `&(LENGTH qs.ps_stack) = (&(LENGTH ps2.ps_stack):int) + trace_weight inst_ops +
    FOLDR ($+) (0:int) (MAP instruction_correction (non_param_insts bb))` by
    (gvs[Abbr `pin`] >> irule regional_replay_body_signed_balance >>
     rpt (first_assum $ irule_at Any) >> gvs[]) >>
  `&(LENGTH ps1.ps_stack) = (&(LENGTH pin.ps_stack):int) + trace_weight param_ops +
    &(LENGTH (get_params bb.bb_instructions))` by
    (Cases_on `bb = HD fn.fn_blocks`
     >- (gvs[] >> drule prepare_params_plan_signed_balance >> simp[]) >>
     `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
     drule_all regional_canonical_body_layout >> strip_tac >>
     gvs[trace_weight_def]) >>
  `&(LENGTH ps2.ps_stack) = (&(LENGTH ps1.ps_stack):int) + trace_weight clean_ops` by
    (Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1` >> gvs[trace_weight_def] >>
     drule clean_stack_plan_signed_balance >> simp[]) >>
  gvs[trace_weight_def, trace_weight_append, stack_op_weight_def, Abbr `pin`] >>
  intLib.ARITH_TAC
QED

Theorem regional_dfs_block_signed_balance:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs /\
  generate_block_plan lv dfg cfg fn bb ps_dfs = SOME (block_ops,qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps_dfs.ps_stack):int) + trace_weight block_ops +
    &(LENGTH (get_params bb.bb_instructions)) +
    FOLDR ($+) (0:int) (MAP instruction_correction (non_param_insts bb))
Proof
  strip_tac >> drule dfs_block_state_lineage_state >> strip_tac >>
  irule regional_replay_block_signed_balance >>
  rpt (first_assum $ irule_at Any) >>
  qexistsl [`ps_dfs.ps_cleanup_promised`, `ps_dfs.ps_cleanup_height`] >> gvs[]
QED

Theorem regional_replay_dfs_block_height_delta:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_l /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs /\
  generate_block_plan lv dfg cfg fn bb ps_dfs = SOME (block_ops,qs_dfs) /\
  generate_block_plan lv dfg cfg fn bb
    (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
    SOME (block_ops,qs) ==>
  (&(LENGTH qs.ps_stack):int) - &(LENGTH qs_dfs.ps_stack) =
    &(LENGTH ps_l.ps_stack) - &(LENGTH ps_dfs.ps_stack)
Proof
  strip_tac >>
  drule_all regional_replay_block_signed_balance >> strip_tac >>
  drule_all regional_dfs_block_signed_balance >> strip_tac >>
  intLib.ARITH_TAC
QED

Theorem regional_ret_reaching_lineage_height:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,pend) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks ==>
  !lbl ps. lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    lbl ps ==>
  !target retbb ret ds.
    lookup_block target fn.fn_blocks = SOME retbb /\
    MEM ret retbb.bb_instructions /\ ret.inst_opcode = RET /\
    cfg_path cfg lbl target /\
    dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      lbl ds ==> LENGTH ps.ps_stack = LENGTH ds.ps_stack
Proof
  strip_tac >> ho_match_mp_tac lineage_state_strongind >> rpt strip_tac
  >- (drule regional_entry_structure >> strip_tac >>
      gvs[] >> drule_all regional_entry_dfs_initial >>
      simp[init_cleanup_plan_state_def, init_plan_state_def]) >>
  rename1 `MEM succ (cfg_succs_of cfg lbl)` >>
  `cfg_path cfg lbl target` by metis_tac[cfg_path_predecessor_closed] >>
  `LENGTH ps.ps_stack = LENGTH ps_dfs.ps_stack` by
    (first_x_assum irule >> metis_tac[]) >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  `(&(LENGTH ps_after.ps_stack):int) - &(LENGTH ps_dfs_after.ps_stack) =
    &(LENGTH ps.ps_stack) - &(LENGTH ps_dfs.ps_stack)` by
    (irule regional_replay_dfs_block_height_delta >> metis_tac[]) >>
  `?succbb. lookup_block succ fn.fn_blocks = SOME succbb` by
    (`cfg_reachable_of (cfg_analyze fn) succ` by
       metis_tac[dfs_block_state_cfg_reachable] >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_in_labels >>
     simp[fn_labels_def, listTheory.MEM_MAP] >> strip_tac >>
     irule_at Any MEM_lookup_block >> simp[] >>
     gvs[codegen_ready_fn_def, wf_function_def, fn_labels_def] >> metis_tac[]) >>
  `fn_entry_label fn <> SOME succ` by
    (drule regional_entry_structure >> strip_tac >> strip_tac >> gvs[] >>
     drule regional_entry_no_preds >>
     metis_tac[cfg_edge_symmetry_uncond, listTheory.MEM]) >>
  `LENGTH ps_dfs_after.ps_stack = LENGTH ds.ps_stack` by
    (irule regional_ret_reaching_dfs_edge_height >> metis_tac[]) >>
  simp[] >> intLib.ARITH_TAC
QED

Theorem regional_replay_ret_block_empty:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,pend) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_l /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_dfs /\
  generate_block_plan lv dfg cfg fn bb ps_dfs = SOME (block_ops,qs_dfs) /\
  generate_block_plan lv dfg cfg fn bb
    (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
    SOME (block_ops,qs) /\
  MEM ret bb.bb_instructions /\ ret.inst_opcode = RET ==> qs.ps_stack = []
Proof
  strip_tac >>
  `LENGTH ps_l.ps_stack = LENGTH ps_dfs.ps_stack` by
    (irule regional_ret_reaching_lineage_height >>
     rpt (first_assum $ irule_at Any) >> simp[cfg_path_def]) >>
  `qs_dfs.ps_stack = []` by
    (irule regional_actual_dfs_ret_block_empty >> metis_tac[]) >>
  drule_all regional_replay_dfs_block_height_delta >>
  simp[] >> strip_tac >>
  `LENGTH qs.ps_stack = 0` by intLib.ARITH_TAC >> gvs[]
QED

Theorem regional_replay_ret_step_empty:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,pend) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) lbl ps_l /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) lbl ps_dfs /\
  generate_block_plan lv dfg cfg fn bb ps_dfs = SOME (block_ops,qs_dfs) /\
  generate_block_plan lv dfg cfg fn bb
    (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
    SOME (block_ops,qs) /\
  block_plan_state lv dfg cfg fn bb
    (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) k ps /\
  phi_prefix_length bb.bb_instructions <= k /\ k < LENGTH bb.bb_instructions /\
  EL k bb.bb_instructions = inst /\
  next_live = live_vars_at lv bb.bb_label (k+1) /\
  next_is_term = (k+1 < LENGTH bb.bb_instructions /\
    is_terminator (EL (k+1) bb.bb_instructions).inst_opcode) /\
  inst.inst_opcode = RET /\
  generate_inst_plan lv dfg cfg fn inst next_live (bb_is_halting bb)
    next_is_term bb.bb_label ps = SOME (ops,ps') ==> ps'.ps_stack = []
Proof
  strip_tac >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  `k+1 = LENGTH bb.bb_instructions` by
    (irule ready_block_ret_index_last >> metis_tac[]) >>
  `MEM inst bb.bb_instructions` by metis_tac[listTheory.EL_MEM] >>
  `ps' = qs` by
    (irule regional_ret_step_block_endpoint >>
     rpt (first_assum $ irule_at Any) >> gvs[]) >>
  gvs[] >> irule regional_replay_ret_block_empty >> metis_tac[]
QED
