Theory fnPlanLineageCallers
Ancestors
  fnPlanLineageSetup fnPlanLineageDemand fnPlanLineagePath fnPlanLineageDemandSupport
  fnPlanLineageLiveness fnPlanLineageStages
  livenessProofs cfgAnalysisProps venomWf stackPlanGen asmIR codegenReadyCompute
  passSharedDefs venomInst callLayoutDefs list rich_list

Theorem compute_operands_inst_uses:
  !inst v. MEM (Var v) (compute_operands inst) ==> MEM v (inst_uses inst)
Proof
  rpt gen_tac >>
  simp[compute_operands_def, inst_uses_def, MEM_operand_vars_eq_Var] >>
  IF_CASES_TAC
  >- simp[asmIRTheory.get_non_label_operands_def, MEM_FILTER] >>
  IF_CASES_TAC
  >- (Cases_on `inst.inst_operands` >> simp[] >> metis_tac[]) >>
  simp[]
QED

Theorem analyzed_computed_operand_demand:
  !fn bb i v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (MEM (Var v) (compute_operands (EL i bb.bb_instructions)) \/
     (MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\
      ~MEM v (EL i bb.bb_instructions).inst_outputs)) ==>
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfg_analyze_reachable_sets >> simp[pred_setTheory.EXTENSION] >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `live_vars_at (liveness_analyze fn) bb.bb_label i =
    liveness_transfer fn.fn_blocks (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))` by
    (drule livenessProofsTheory.live_vars_at_transfer >>
     disch_then (qspecl_then [`bb.bb_label`, `bb`, `i`] mp_tac) >> simp[]) >>
  gvs[livenessDefsTheory.liveness_transfer_def, livenessTransferProofsTheory.live_update_mem,
      venomInstTheory.inst_defs_def] >>
  metis_tac[compute_operands_inst_uses, livenessDefsTheory.MEM_ordered_inst_uses]
QED

(* Backward demand transport over an arbitrary instruction interval. *)
Theorem interval_live_origin:
  !fn bb a j v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    a <= j /\ j <= LENGTH bb.bb_instructions /\
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label j) ==>
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label a) \/
    ?k. a <= k /\ k < j /\ MEM v (EL k bb.bb_instructions).inst_outputs
Proof
  ntac 2 gen_tac >> Induct_on `j`
  >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `a = SUC j`
  >- gvs[] >>
  Cases_on `MEM v (EL j bb.bb_instructions).inst_outputs`
  >- (disj2_tac >> qexists_tac `j` >> simp[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label j)` by
    (irule analyzed_computed_operand_demand >> simp[] >> decide_tac) >>
  first_x_assum (qspecl_then [`a`, `v`] mp_tac) >> simp[] >>
  strip_tac >- simp[] >>
  disj2_tac >> qexists_tac `k` >> simp[]
QED

Theorem interval_computed_query_origin:
  !fn bb a j v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    a <= j /\ j < LENGTH bb.bb_instructions /\
    MEM (Var v) (compute_operands (EL j bb.bb_instructions)) ==>
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label a) \/
    ?k. a <= k /\ k < j /\ MEM v (EL k bb.bb_instructions).inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label j)` by
    (irule analyzed_computed_operand_demand >> simp[]) >>
  irule interval_live_origin >> simp[]
QED

Theorem prefix_live_query_defined_since_boundary:
  !fn bb a j prefix v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    a <= j /\ j <= LENGTH bb.bb_instructions /\
    (!w. MEM (Var w) prefix ==>
      ~MEM w (live_vars_at (liveness_analyze fn) bb.bb_label a)) /\
    MEM (Var v) prefix /\
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label j) ==>
    ?k. a <= k /\ k < j /\ MEM v (EL k bb.bb_instructions).inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all interval_live_origin >> metis_tac[]
QED

Theorem prefix_computed_query_defined_since_boundary:
  !fn bb a j prefix v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    a <= j /\ j < LENGTH bb.bb_instructions /\
    (!w. MEM (Var w) prefix ==>
      ~MEM w (live_vars_at (liveness_analyze fn) bb.bb_label a)) /\
    MEM (Var v) prefix /\
    MEM (Var v) (compute_operands (EL j bb.bb_instructions)) ==>
    ?k. a <= k /\ k < j /\ MEM v (EL k bb.bb_instructions).inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all interval_computed_query_origin >> metis_tac[]
QED

Theorem ordinary_interval_prefix_exclusion:
  !fn bb a j prefix.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    a <= j /\ j < LENGTH bb.bb_instructions /\
    EVERY (\v. ~MEM (Var v) prefix)
      (live_vars_at (liveness_analyze fn) bb.bb_label a) /\
    (!k. a <= k /\ k <= j ==>
      EVERY (\v. ~MEM (Var v) prefix) (EL k bb.bb_instructions).inst_outputs) ==>
    EVERY (\v. ~MEM (Var v) prefix)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC j) ++
       (EL j bb.bb_instructions).inst_outputs)
Proof
  rpt gen_tac >> strip_tac >> simp[EVERY_APPEND] >>
  simp[EVERY_MEM] >> gen_tac >> strip_tac >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label a) \/
   ?k. a <= k /\ k < SUC j /\ MEM v (EL k bb.bb_instructions).inst_outputs` by
    (irule interval_live_origin >> simp[]) >>
  gvs[EVERY_MEM] >>
  `k <= j` by decide_tac >> metis_tac[]
QED

Theorem ordinary_interval_shared_core_replay:
  !fn bb a j prefixP prefixQ inst nl dfg cfg halting term lbl ps.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    a <= j /\ j < LENGTH bb.bb_instructions /\
    EVERY (\v. ~MEM (Var v) prefixP)
      (live_vars_at (liveness_analyze fn) bb.bb_label a) /\
    EVERY (\v. ~MEM (Var v) prefixQ)
      (live_vars_at (liveness_analyze fn) bb.bb_label a) /\
    (!k. a <= k /\ k <= j ==>
      EVERY (\v. ~MEM (Var v) prefixP) (EL k bb.bb_instructions).inst_outputs) /\
    (!k. a <= k /\ k <= j ==>
      EVERY (\v. ~MEM (Var v) prefixQ) (EL k bb.bb_instructions).inst_outputs) /\
    inst = EL j bb.bb_instructions /\
    nl = live_vars_at (liveness_analyze fn) bb.bb_label (SUC j) /\
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
    (!x. MEM x (compute_operands inst) /\ is_var_operand x ==>
      MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled) ==>
    ?ops qs.
      generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn inst nl halting term lbl
        (ps with ps_stack := prefixP ++ ps.ps_stack) =
        (ops,qs with ps_stack := prefixP ++ qs.ps_stack) /\
      generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn inst nl halting term lbl
        (ps with ps_stack := prefixQ ++ ps.ps_stack) =
        (ops,qs with ps_stack := prefixQ ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\v. ~MEM (Var v) prefixP) (nl ++ inst.inst_outputs)` by
    metis_tac[ordinary_interval_prefix_exclusion] >>
  `EVERY (\v. ~MEM (Var v) prefixQ) (nl ++ inst.inst_outputs)` by
    metis_tac[ordinary_interval_prefix_exclusion] >>
  irule native_regular_shared_core_replay >> simp[]
QED

Theorem ordinary_position_invariant:
  !fn bb i dfg cfg halting term lbl ps m core base ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    EVERY (\x. x <> dead_stack_marker) (compute_operands (EL i bb.bb_instructions)) /\
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      demand_available fn bb i v) /\
    generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn
      (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halting term lbl ps = (ops,qs)
    ==>
    (?rest. lineage_core m rest qs /\
      residual_budget_wf base [] (qs with ps_stack := rest)) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
      MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) /\
    (!v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      demand_available fn bb (SUC i) v)
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn /\ wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM (EL i bb.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[EL_MEM]) >>
  `ALL_DISTINCT (EL i bb.bb_instructions).inst_outputs` by
    metis_tac[genBlockSimTheory.codegen_ready_inst_outputs_distinct] >>
  `LENGTH (compute_operands (EL i bb.bb_instructions)) <= 16` by
    (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >>
     metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) \/
      (MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\
       ~MEM v (EL i bb.bb_instructions).inst_outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    metis_tac[analyzed_computed_operand_demand] >>
  `!v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
  drule_all definition_support_output_fresh >> strip_tac >>
  `EVERY (\v. ~MEM (Var v) (compute_operands (EL i bb.bb_instructions)) /\
     ~MEM (Var v) core /\ Var v NOTIN FDOM ps.ps_spilled)
     (EL i bb.bb_instructions).inst_outputs` by
    (gvs[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
  conj_tac
  >- (drule_all native_regular_core_resource >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> drule_all native_regular_live_lower >> simp[]) >>
  ho_match_mp_tac native_regular_variable_support >>
  goal_assum (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> gen_tac >> strip_tac
  >- (irule demand_available_mono >> qexists_tac `i` >> simp[] >>
      first_x_assum irule >> simp[])
  >- (irule demand_available_mono >> qexists_tac `i` >> simp[] >>
      first_x_assum irule >> metis_tac[])
  >- (irule demand_available_mono >> qexists_tac `i` >> simp[] >>
      first_x_assum irule >> metis_tac[])
  >- (irule demand_available_mono >> qexists_tac `i` >> simp[] >>
      first_x_assum irule >> metis_tac[]) >>
  irule current_output_demand_available_suc >> simp[]
QED

(* OFFSET retains its output even when dead: upper support is availability,
   not exact next-live inventory. *)
Theorem offset_position_invariant:
  !fn bb i ps m core base ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = OFFSET /\
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      demand_available fn bb i v) /\
    generate_offset_plan (EL i bb.bb_instructions) ps = (ops,qs)
    ==>
    (?rest. lineage_core m rest qs /\
      residual_budget_wf base [] (qs with ps_stack := rest)) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
      MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) /\
    (!v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      demand_available fn bb (SUC i) v)
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn /\ wf_function fn` by gvs[codegen_ready_fn_def] >>
  `inst_wf (EL i bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >>
     metis_tac[EL_MEM]) >>
  drule_all inst_wf_offset_shape >> strip_tac >>
  drule_all definition_support_output_fresh >> strip_tac >>
  `qs = FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack)
      ps [out]` by
    (drule_all generate_offset_plan_frame >>
     disch_then (qspec_then `ps` mp_tac) >>
     gvs[stackModelTheory.stack_push_def, SNOC_APPEND]) >>
  `EVERY (\v. ~MEM (Var v) core /\ Var v NOTIN FDOM ps.ps_spilled) [out]` by
    (gvs[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
  `ALL_DISTINCT [out]` by simp[] >>
  drule_all output_push_marker_core >> simp[] >> strip_tac >>
  conj_tac
  >- (qexists_tac `core ++ [Var out]` >>
      simp[fnPlanLineageInventoryTheory.lineage_core_def]) >>
  conj_tac
  >- (qx_gen_tac `w` >> strip_tac >> Cases_on `w = out` >- simp[MEM_APPEND] >>
      `MEM w (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
        (irule analyzed_computed_operand_demand >> simp[]) >>
      gvs[MEM_APPEND] >> metis_tac[]) >>
  qx_gen_tac `w` >> disch_tac >>
  Cases_on `w = out`
  >- (gvs[] >> irule current_output_demand_available_suc >> simp[]) >>
  irule demand_available_mono >> qexists_tac `i` >> simp[] >>
  qpat_x_assum `!v. MEM (Var v) ps.ps_stack \/ _ ==> _`
    (qspec_then `w` irule) >>
  gvs[MEM_APPEND] >> metis_tac[]
QED

Theorem param_insts_from_filter[local]:
  !params k. param_insts_from k params ==>
    FILTER (\inst. ~is_param_opcode inst.inst_opcode) params = []
Proof
  Induct >> simp[param_insts_from_def, param_inst_at_def] >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem ready_block_parameter_suffix:
  !fn bb. codegen_ready_fn fn /\ MEM bb fn.fn_blocks ==>
    bb.bb_instructions = get_params bb.bb_instructions ++ non_param_insts bb
Proof
  rpt gen_tac >> strip_tac >>
  `canonical_param_prefix fn` by gvs[codegen_ready_fn_def] >>
  qpat_x_assum `canonical_param_prefix fn` mp_tac >>
  rewrite_tac[canonical_param_prefix_iff] >>
  disch_then (qx_choose_then `entry` (qx_choose_then `rest`
    (qx_choose_then `users` (qx_choose_then `fmp` (qx_choose_then `retpc`
      (qx_choose_then `tail_insts` (map_every assume_tac o CONJUNCTS))))))) >>
  Cases_on `bb = entry`
  >- (gnvs[] >>
      `get_params ((users ++ fmp ++ retpc) ++ tail_insts) = users ++ fmp ++ retpc` by
        (irule get_params_canonical_prefix >> simp[] >> metis_tac[]) >>
      `FILTER (\inst. ~is_param_opcode inst.inst_opcode) (users ++ fmp ++ retpc) = []` by
        metis_tac[param_insts_from_filter] >>
      `FILTER (\inst. ~is_param_opcode inst.inst_opcode) tail_insts = tail_insts` by
        gvs[FILTER_EQ_ID, no_param_insts_def] >>
      simp[non_param_insts_def] >>
      qpat_x_assum `bb.bb_instructions = _` (fn th => rewrite_tac[th]) >>
      once_rewrite_tac[APPEND_ASSOC] >>
      simp[FILTER_APPEND]) >>
  `MEM bb rest` by gvs[] >>
  `no_param_insts bb.bb_instructions` by
    (qpat_x_assum `EVERY _ rest` mp_tac >> simp[EVERY_MEM]) >>
  `get_params bb.bb_instructions = []` by
    (Cases_on `bb.bb_instructions` >> gvs[no_param_insts_def, get_params_def]) >>
  simp[non_param_insts_def, FILTER_EQ_ID] >> gvs[no_param_insts_def]
QED

Theorem ready_block_suffix_index:
  !fn bb k. codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    k < LENGTH (non_param_insts bb) ==>
    EL k (non_param_insts bb) =
      EL (LENGTH (get_params bb.bb_instructions) + k) bb.bb_instructions
Proof
  rpt strip_tac >> drule_all ready_block_parameter_suffix >>
  disch_then (fn th => CONV_TAC (RHS_CONV (RAND_CONV (REWR_CONV th)))) >>
  simp[EL_APPEND2]
QED

Theorem ready_block_suffix_next_live:
  !fn bb lv k inst rest.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    DROP k (non_param_insts bb) = inst::rest /\
    k < LENGTH (non_param_insts bb) ==>
    (if rest = [] then live_vars_at lv bb.bb_label (LENGTH bb.bb_instructions)
     else live_vars_at lv bb.bb_label (k + LENGTH (get_params bb.bb_instructions) + 1)) =
    live_vars_at lv bb.bb_label (SUC (LENGTH (get_params bb.bb_instructions) + k))
Proof
  rpt strip_tac >>
  `LENGTH bb.bb_instructions = LENGTH (get_params bb.bb_instructions) +
      LENGTH (non_param_insts bb)` by
    metis_tac[ready_block_parameter_suffix, LENGTH_APPEND] >>
  reverse (Cases_on `rest = []`)
  >- (simp[] >> AP_TERM_TAC >> decide_tac) >>
  simp[] >>
  `LENGTH (non_param_insts bb) - k = 1` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[]) >>
  `LENGTH bb.bb_instructions = SUC (LENGTH (get_params bb.bb_instructions) + k)` by
    decide_tac >> AP_TERM_TAC >> decide_tac
QED

Theorem analyzed_entry_prefix_support:
  !fn bb n v.
    codegen_ready_fn fn /\ entry_block fn = SOME bb /\
    n <= LENGTH bb.bb_instructions /\
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label n) ==>
    demand_available fn bb n v
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `fn.fn_blocks <> [] /\ bb = HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[entry_block_def]) >>
  `MEM bb fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `fn_reachable fn bb.bb_label` by
    (Cases_on `fn.fn_blocks` >> gvs[fn_reachable_def, fn_entry_label_def] >>
     metis_tac[relationTheory.RTC_REFL]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfg_analyze_reachable_sets >> simp[pred_setTheory.EXTENSION] >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `live_vars_at (liveness_analyze fn) bb.bb_label 0 = []` by
    metis_tac[analyzed_entry_live_empty] >>
  qpat_x_assum `bb = HD _` kall_tac >>
  drule_all live_prefix_demand >>
  simp[MEM_FLAT, MEM_MAP] >> strip_tac >>
  qpat_x_assum `MEM _ (TAKE _ _)` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `j < LENGTH (TAKE n bb.bb_instructions)` >>
  `j < n /\ j < LENGTH bb.bb_instructions` by gvs[LENGTH_TAKE] >>
  `MEM v (EL j bb.bb_instructions).inst_outputs` by
    gvs[EL_TAKE, inst_defs_def] >>
  irule demand_available_mono >> qexists_tac `SUC j` >> simp[] >>
  irule current_output_demand_available_suc >> simp[]
QED

Theorem initial_parameter_definition_support:
  !fn ch growth spill_base lbl_ctr ps v.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    ps = SND (prepare_params_plan (liveness_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) /\
    (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==>
    demand_available fn (HD fn.fn_blocks)
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_parameter_inventory >> strip_tac >>
  `MEM v (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))` by
    (gvs[pred_setTheory.EXTENSION, MEM_MAP] >> metis_tac[]) >>
  `entry_block fn = SOME (HD fn.fn_blocks)` by
    (Cases_on `fn.fn_blocks` >> gvs[entry_block_def]) >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `LENGTH (get_params (HD fn.fn_blocks).bb_instructions) <=
      LENGTH (HD fn.fn_blocks).bb_instructions` by
    (drule_all ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  irule analyzed_entry_prefix_support >> simp[]
QED

Theorem ready_entry_no_clean:
  !fn. codegen_ready_fn fn /\ fn.fn_blocks <> [] ==>
    cfg_preds_of (cfg_analyze fn) (HD fn.fn_blocks).bb_label = []
Proof
  rpt strip_tac >> gvs[codegen_ready_fn_def, block_entries_ready_def] >>
  Cases_on `fn.fn_blocks` >> gvs[entry_block_def, NULL_EQ]
QED

Theorem analyzed_terminal_jmp_target_coverage:
  !fn pred succ bb sb inst ps targets.
    codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME bb /\
    lookup_block succ fn.fn_blocks = SOME sb /\
    bb.bb_instructions <> [] /\ LAST bb.bb_instructions = inst /\
    inst.inst_opcode = JMP /\ inst.inst_operands = [Label succ] /\
    join_target_ops (liveness_analyze fn) fn pred inst = SOME targets /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) pred
                  (LENGTH bb.bb_instructions)) ==>
         MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==>
    !at. MEM at targets ==> MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all analyzed_live_out_jmp >> strip_tac >>
  gvs[join_target_ops_def, MEM_MAP] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* Parameter seeding is an explicitly processed entry prefix, not an
   unexplained external set of variables in the chronological invariant. *)
Theorem initial_parameter_origins:
  !fn ch growth spill_base lbl_ctr ps v.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    ps = SND (prepare_params_plan (liveness_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) /\
    (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==>
    MEM v (MAP (\inst. HD inst.inst_outputs)
      (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_parameter_inventory >> strip_tac >>
  drule_all post_parameter_demand_ready >>
  gvs[EVERY_MEM, pred_setTheory.EXTENSION, MEM_MAP] >> metis_tac[]
QED

(* Chronological producer design audit (not a proved global invariant).

   Proposed exact predicates, with inventory(ps,v) abbreviating
     MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled:

   compiled_origin(fn,visited,v) <=>
     ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
       MEM v di.inst_outputs /\ MEM db.bb_label visited.

   prefix_origin(fn,visited,bb,i,v) <=>
     compiled_origin(fn,visited,v) \/
     ?di. MEM di (TAKE i bb.bb_instructions) /\ MEM v di.inst_outputs.

   Fresh block contract: for lookup_block lbl ... = SOME bb, lbl NOTIN
   visited and inventory(ps) supported by compiled_origin(fn,visited),
   block setup and each processed position i support prefix_origin at i.
   The position counts original instructions, including the parameter
   prefix (ready_block_suffix_index). On return inventory is supported by
   compiled_origin(fn,lbl::visited). This is an ORIGIN contract only.

   Checked stage tests:
   * initial_parameter_origins accounts for every parameter-seeded variable
     by HD outputs of get_params, not by an external assumed parameter set.
     For ready functions each of these singleton parameter outputs is a
     definition in the processed prefix. Initialization itself is empty.
   * generate_phi_plan_inventory_origins (fnPlanLineagePhiInventory) handles
     BOTH physical rename branches, deep duplication, and dead-output pop.
     It adds only Var (HD inst_outputs); fn_inst_wf supplies nonempty PHI
     outputs. It requires no uniqueness, liveness distinctness, or freshness.
   * generate_inst_plan_jmp_inventory_subset (fnPlanLineageInventory) already
     is the symbolic successful-JMP test. With target coverage and empty
     JMP outputs, no new inventory operand appears, even for deep targets.
     restore_spilled_plan_inventory_subset covers restore alone. We do not
     duplicate these tests. analyzed_terminal_jmp_target_coverage supplies
     their target premise from live-out coverage, for an analyzed ready
     reachable terminal JMP. The source coverage remains a separate producer.
   * native_regular_variable_origins requires operand availability and the
     ready <=16 operand bound; available operands reduce its alternatives
     to old inventory or current outputs. OFFSET only pushes its output;
     parameter/NOP steps are identities. Cleanup only pops or replaces by
     dead_stack_marker (a Label), so introduces no Var.

   Mutual trace induction ledger (plan_aux_trace_ind):
   AUX needs support of input ps by compiled_origin(visited).
   SUCCS needs support of BOTH saved stack/spills and ps's own inventory.
   Both conclusions must include visited SUBSET visited' and support of
   result inventory by compiled_origin(visited'); event entry support must
   be indexed by the visited set BEFORE that individual fresh event.
   - empty aux/succs: identity.
   - visited aux head: no block execution, same support and event list.
   - missing aux head: unchanged inventory, enlarge visited monotonically;
     its recorded event has no block or instruction freshness obligation.
   - present fresh head: block contract above adds current block origins;
     call succs with that state as BOTH saved and current inventory; feed
     succs result and its visited' into rest aux. Thread rest result.
   - successor cons: resetting stack/spills uses saved support. After first
     child, visited only grows, so saved support survives sibling reset.
     The sibling's current ps retains its old stack/spills (only allocator
     and label fields change); this explains the second SUCCS premise.
     Thread sibling result. No block is executed at a visited head.

   SSA's global distinct output positions plus lbl NOTIN visited excludes
   current outputs from compiled_origin; prefix indices < i exclude them
   from prefix_origin. This can produce FIRST-COMPILATION output absence,
   without requiring earlier compiled blocks to dominate the current one.

   Limit: lineage_state_step is NOT a fresh compilation event. Its premise
   allows a backedge to a previously compiled label, and its stack/spills
   come from runtime predecessor replay. Thus the proposed chronological
   predicate cannot be asserted there, nor can it alone close replay's
   input-side output-freshness premise. Canonical DFS freshness and runtime
   replay resources must remain separate certificates. The checked trace
   visited-head theorem is precisely the symbolic no-recompilation test;
   no concrete loop fixture is needed for that distinction.

   Still unproved independently: actual live-variable coverage at native
   stages, liveness transport for next-live upper bounds, deep JMP resource
   closure, PHI resource closure, and runtime revisit freshness or an
   alternative observation relation that avoids requiring it. In particular
   an origin bound is neither physical availability nor a count bound.
*)
