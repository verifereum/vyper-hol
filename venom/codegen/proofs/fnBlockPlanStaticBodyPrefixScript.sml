Theory fnBlockPlanStaticBodyPrefix
Ancestors
  fnBlockPlanStaticRegion fnPlanPrefix genBlockSim stackPlanGen asmIR
  venomInst venomWf livenessProofs livenessTransferProofs livenessDefs dfgDefs
  removeUnusedSsaProofs callLayoutDefs stackPlanTypes list rich_list arithmetic finite_map pred_set venomWfProps

Definition regional_body_lower_inv_def:
  regional_body_lower_inv lv dfg sb bb i ps <=>
    generated_plan_state_wf_marked sb ps /\
    (!v. MEM v (live_vars_at lv bb.bb_label i) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!j op v. i <= j /\ j < LENGTH bb.bb_instructions /\
      (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
      (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
      ~MEM v (EL j bb.bb_instructions).inst_outputs)
End

Theorem regional_compute_var_use:
  MEM (Var v) (compute_operands inst) ==> MEM v (inst_uses inst)
Proof
  simp[compute_operands_def, LET_THM] >> rpt IF_CASES_TAC >>
  simp[get_non_label_operands_def, MEM_FILTER, inst_uses_def] >>
  rpt strip_tac >>
  `MEM (Var v) inst.inst_operands` by
    (Cases_on `inst.inst_operands` >> gvs[] >> metis_tac[]) >>
  simp[passSharedDefsTheory.MEM_operand_vars_eq_Var]
QED

Theorem regional_emit_input_capacity:
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) ==>
  LENGTH operands <= LENGTH (SND (emit_input_plan opc operands nl ps)).ps_stack
Proof
  strip_tac >>
  Cases_on `emit_input_plan opc operands nl ps` >> simp[] >>
  irule fnFrameStepsRevertForwardTheory.list_elem_count_dom_length >>
  irule reorderSimTheory.emit_input_plan_materialised >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem regional_body_lower_inv_wf:
  regional_body_lower_inv lv dfg sb bb k ps ==>
  generated_plan_state_wf_marked sb ps
Proof
  simp[regional_body_lower_inv_def]
QED

Theorem regional_body_lower_inv_operands:
  codegen_ready_fn fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  k < LENGTH bb.bb_instructions /\ inst = EL k bb.bb_instructions /\
  regional_body_lower_inv (liveness_analyze fn) dfg sb bb k ps ==>
  !op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  gvs[regional_body_lower_inv_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `op` >> gvs[is_var_operand_def] >>
  rename1 `MEM (Var v) (compute_operands _)` >>
  `MEM v (inst_uses (EL k bb.bb_instructions))` by metis_tac[regional_compute_var_use] >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label k)` by
    (drule live_vars_at_uses >> simp[LET_THM] >> disch_then irule >> metis_tac[]) >>
  metis_tac[]
QED

Theorem regional_body_lower_inv_operand_lookup:
  codegen_ready_fn fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  k < LENGTH bb.bb_instructions /\ inst = EL k bb.bb_instructions /\
  regional_body_lower_inv (liveness_analyze fn) dfg sb bb k ps ==>
  !op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)
Proof
  rpt strip_tac >>
  `MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    metis_tac[regional_body_lower_inv_operands] >>
  Cases_on `stack_get_depth op ps.ps_stack` >> simp[] >>
  gvs[fnBlockPlanStaticInventoryTheory.inventory_depth_none] >>
  `op IN FDOM ps.ps_spilled` by metis_tac[] >> simp[FLOOKUP_DEF]
QED

Theorem regional_body_lower_inv_output_roots:
  regional_body_lower_inv lv dfg sb bb k ps /\
  k < LENGTH bb.bb_instructions /\ inst = EL k bb.bb_instructions ==>
  !op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v inst.inst_outputs
Proof
  simp[regional_body_lower_inv_def] >> metis_tac[LESS_EQ_REFL]
QED

Theorem regional_body_lower_inv_stack_fresh:
  regional_body_lower_inv lv dfg sb bb k ps /\
  k < LENGTH bb.bb_instructions /\ inst = EL k bb.bb_instructions ==>
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    inst.inst_outputs) ps.ps_stack
Proof
  strip_tac >> simp[EVERY_MEM] >> qx_gen_tac `op` >> strip_tac >>
  Cases_on `op` >> simp[] >> metis_tac[regional_body_lower_inv_output_roots]
QED

Theorem regional_body_lower_inv_spills_fresh:
  regional_body_lower_inv lv dfg sb bb k ps /\
  k < LENGTH bb.bb_instructions /\ inst = EL k bb.bb_instructions ==>
  !op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs
Proof
  strip_tac >> simp[EVERY_MEM] >> qx_gen_tac `op` >> strip_tac >>
  Cases_on `op` >> simp[] >> metis_tac[regional_body_lower_inv_output_roots]
QED

Theorem regional_body_lower_inv_input_capacity:
  codegen_ready_fn fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  k < LENGTH bb.bb_instructions /\ inst = EL k bb.bb_instructions /\
  regional_body_lower_inv (liveness_analyze fn) dfg sb bb k ps ==>
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack
Proof
  strip_tac >> irule regional_emit_input_capacity >>
  metis_tac[regional_body_lower_inv_operands]
QED

Theorem regional_body_lower_inv_step:
  codegen_ready_fn fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
  ~is_param_opcode inst.inst_opcode /\
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb i ps /\
  generate_inst_plan (liveness_analyze fn) (dfg_build_function fn) (cfg:cfg_analysis) fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halting next_term
    bb.bb_label ps = SOME (ops,qs) ==>
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb (SUC i) qs
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  `wf_function fn /\ inst_wf inst /\ LENGTH (compute_operands inst) <= 16` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM, codegen_ready_inst_def] >>
     metis_tac[EL_MEM]) >>
  `ALL_DISTINCT inst.inst_outputs` by metis_tac[codegen_ready_inst_outputs_distinct] >>
  gvs[regional_body_lower_inv_def] >>
  `!op. MEM op (compute_operands (EL i bb.bb_instructions)) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt gen_tac >> strip_tac >> Cases_on `op` >> gvs[is_var_operand_def] >>
     rename1 `MEM (Var v) (compute_operands _)` >>
     `MEM v (inst_uses (EL i bb.bb_instructions))` by metis_tac[regional_compute_var_use] >>
     `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
       (drule live_vars_at_uses >> simp[LET_THM] >> disch_then irule >> metis_tac[]) >>
     metis_tac[]) >>
  `EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
    (EL i bb.bb_instructions).inst_outputs` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >>
     qpat_x_assum `!j op v. _` (qspecl_then [`i`, `Var v`, `v`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  conj_tac >- (irule (INST_TYPE [alpha |-> ``:cfg_analysis``] regional_body_marked_wf) >>
    goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >> simp[]) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      irule (INST_TYPE [alpha |-> ``:cfg_analysis``] regional_indexed_body_marked_live_coverage) >>
      goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
      qexists_tac `sb` >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  irule (INST_TYPE [alpha |-> ``:cfg_analysis``] regional_indexed_body_suffix_freshness) >>
  simp[] >> goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> qexists_tac `op` >> simp[] >> metis_tac[]
QED

Theorem regional_body_lower_inv_prefix:
  !n a ps0 ops psn start fn bb sb cfg.
  codegen_ready_fn fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  start <= a /\ a + n <= LENGTH bb.bb_instructions /\
  (!i. a <= i /\ i < a + n ==>
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    ~is_param_opcode (EL i bb.bb_instructions).inst_opcode) /\
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb a ps0 /\
  generate_block_insts_prefix (liveness_analyze fn) (dfg_build_function fn)
    (cfg:cfg_analysis) fn bb.bb_label (bb_is_halting bb) start
    (LENGTH bb.bb_instructions) (a-start) n (DROP a bb.bb_instructions) ps0 =
    SOME (ops,psn) ==>
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb (a+n) psn
Proof
  Induct_on `n`
  >- simp[generate_block_insts_prefix_def] >>
  rpt gen_tac >> strip_tac >>
  `a < LENGTH bb.bb_instructions` by simp[] >>
  `DROP a bb.bb_instructions = EL a bb.bb_instructions :: DROP (SUC a) bb.bb_instructions` by
    metis_tac[DROP_CONS_EL] >>
  qpat_x_assum `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[generate_block_insts_prefix_def, LET_THM] >>
  simp[AllCaseEqs()] >> strip_tac >>
  ` (if LENGTH bb.bb_instructions <= SUC a then
       live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)
     else live_vars_at (liveness_analyze fn) bb.bb_label (a+1)) =
    live_vars_at (liveness_analyze fn) bb.bb_label (SUC a)` by
    (IF_CASES_TAC
     >- (`LENGTH bb.bb_instructions = SUC a` by decide_tac >> simp[]) >> simp[ADD1]) >>
  gvs[] >>
  `regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb (SUC a) ps'` by
    (irule regional_body_lower_inv_step >> simp[] >>
     goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[LESS_EQ_REFL, LESS_EQ_LESS_TRANS]) >>
  `a + SUC n = SUC a + n` by simp[] >> pop_assum SUBST1_TAC >>
  first_x_assum irule >> gvs[ADD1] >>
  goal_assum (drule_at (Pat `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_SUC_REFL]
QED

Theorem regional_selected_phi_exit_lower_inv:
  regional_selected_phi_inv lv dfg sb bb
    (LENGTH (collect_phis bb.bb_instructions)) ps ==>
  regional_body_lower_inv lv dfg sb bb
    (LENGTH (collect_phis bb.bb_instructions)) ps
Proof
  strip_tac >> simp[regional_body_lower_inv_def] >>
  conj_tac >- metis_tac[regional_selected_phi_exit_wf] >>
  conj_tac >- metis_tac[regional_selected_phi_exit_coverage] >>
  rpt gen_tac >> strip_tac >>
  `~MEM v (FLAT (MAP (\inst. inst.inst_outputs)
    (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions)))` by
    metis_tac[regional_selected_phi_exit_freshness] >>
  `MEM (EL j bb.bb_instructions)
    (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions)` by
    (simp[MEM_EL] >>
     qexists_tac `j - LENGTH (collect_phis bb.bb_instructions)` >>
     simp[EL_DROP]) >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem regional_phi_body_layout:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  collect_phis bb.bb_instructions <> [] /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\
  i < k /\ k < LENGTH bb.bb_instructions ==>
  (EL i bb.bb_instructions).inst_opcode <> PHI /\
  (EL i bb.bb_instructions).inst_opcode <> JMP /\
  ~is_param_opcode (EL i bb.bb_instructions).inst_opcode
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `bb_well_formed bb` by
    (gvs[codegen_ready_fn_def, wf_function_def, EVERY_MEM] >>
     metis_tac[]) >>
  conj_tac
  >- (strip_tac >>
      `i < LENGTH (collect_phis bb.bb_instructions)` by
        (irule fnBlockPlanStaticOffsetLiveTheory.phi_index_in_prefix >> simp[] >>
         gvs[bb_well_formed_def] >> metis_tac[LESS_TRANS]) >> decide_tac) >>
  conj_tac
  >- (strip_tac >>
      `is_terminator (EL i bb.bb_instructions).inst_opcode` by
        simp[is_terminator_def] >>
      gvs[bb_well_formed_def] >>
      `i = PRE (LENGTH bb.bb_instructions)` by metis_tac[LESS_TRANS] >> decide_tac) >>
  `no_param_insts bb.bb_instructions` by
    (drule_all regional_phi_no_params >> strip_tac >>
     gvs[non_param_insts_def, no_param_insts_def, FILTER_EQ_ID]) >>
  gvs[no_param_insts_def, EVERY_MEM] >>
  first_x_assum irule >> irule EL_MEM >> decide_tac
QED

Theorem regional_entry_lower_start:
  codegen_ready_fn fn /\ bb = HD fn.fn_blocks /\
  lineage_state (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth sb ctr) bb.bb_label ps_l /\
  prepare_params_plan (liveness_analyze fn) fn
    (ps_l with <|ps_cleanup_height := height; ps_cleanup_promised := promised|>) =
    (param_ops,ps1) /\
  (if LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1 then
     clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb ps1
   else ([],ps1)) = (clean_ops,ps2) ==>
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb
    (LENGTH (get_params bb.bb_instructions)) ps2
Proof
  strip_tac >> gvs[] >>
  `ps_l = init_cleanup_plan_state ch growth sb ctr` by
    metis_tac[regional_entry_lineage_initial] >>
  `cfg_preds_of (cfg_analyze fn) (HD fn.fn_blocks).bb_label = []` by
    metis_tac[regional_entry_no_preds] >>
  gvs[] >> simp[regional_body_lower_inv_def] >>
  conj_tac >- metis_tac[regional_prepare_params_initial_wf] >>
  conj_tac >- metis_tac[regional_prepare_params_initial_live_coverage] >>
  metis_tac[regional_prepare_params_initial_freshness]
QED

Theorem regional_canonical_body_layout:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks ==>
  non_param_insts bb = DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions /\
  no_param_insts (DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions) /\
  (bb <> HD fn.fn_blocks ==> get_params bb.bb_instructions = [])
Proof
  strip_tac >>
  `canonical_param_prefix fn` by gvs[codegen_ready_fn_def] >>
  qpat_x_assum `canonical_param_prefix fn` mp_tac >>
  rewrite_tac[canonical_param_prefix_iff] >>
  simp[PULL_EXISTS] >> map_every qx_gen_tac [`entry`, `rest`, `users`, `fmp`, `retpc`, `suffix`] >> disch_tac >>
  Cases_on `bb = entry`
  >- (`EVERY (\inst. is_param_opcode inst.inst_opcode) (users ++ fmp ++ retpc)` by
        (gvs[EVERY_APPEND, EVERY_MEM, is_param_opcode_def] >> metis_tac[]) >>
      `get_params ((users ++ fmp ++ retpc) ++ suffix) = users ++ fmp ++ retpc` by
        metis_tac[fnFrameBoundaryEntryParamsTheory.get_params_prefix] >>
      gvs[APPEND_ASSOC, non_param_insts_def, FILTER_APPEND, FILTER_EQ_NIL,
          no_param_insts_def, FILTER_EQ_ID] >>
      simp[DROP_LENGTH_APPEND] >>
      `FILTER (\inst. ~is_param_opcode inst.inst_opcode) users = []` by
        (simp[FILTER_EQ_NIL, EVERY_MEM] >> gvs[EVERY_MEM, is_param_opcode_def]) >>
      `FILTER (\inst. ~is_param_opcode inst.inst_opcode) suffix = suffix` by
        (simp[listTheory.FILTER_EQ_ID]) >> simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `no_param_insts bb.bb_instructions` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  `get_params bb.bb_instructions = []` by
    (Cases_on `bb.bb_instructions` >> gvs[no_param_insts_def, get_params_def]) >>
  gvs[non_param_insts_def, no_param_insts_def, FILTER_EQ_ID]
QED

Theorem regional_no_phi_body_layout:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  collect_phis bb.bb_instructions = [] /\
  LENGTH (get_params bb.bb_instructions) <= i /\
  i < k /\ k < LENGTH bb.bb_instructions ==>
  (EL i bb.bb_instructions).inst_opcode <> PHI /\
  (EL i bb.bb_instructions).inst_opcode <> JMP /\
  ~is_param_opcode (EL i bb.bb_instructions).inst_opcode
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `bb_well_formed bb` by
    (gvs[codegen_ready_fn_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (strip_tac >>
      `i < LENGTH (collect_phis bb.bb_instructions)` by
        (irule fnBlockPlanStaticOffsetLiveTheory.phi_index_in_prefix >> simp[] >>
         gvs[bb_well_formed_def] >> metis_tac[LESS_TRANS]) >> gvs[]) >>
  conj_tac
  >- (strip_tac >>
      `is_terminator (EL i bb.bb_instructions).inst_opcode` by simp[is_terminator_def] >>
      gvs[bb_well_formed_def] >>
      `i = PRE (LENGTH bb.bb_instructions)` by metis_tac[LESS_TRANS] >> decide_tac) >>
  drule_all regional_canonical_body_layout >> strip_tac >>
  gvs[no_param_insts_def, EVERY_MEM] >>
  first_x_assum irule >> simp[MEM_EL] >>
  qexists_tac `i - LENGTH (get_params bb.bb_instructions)` >> simp[EL_DROP] >>
  `LENGTH (get_params bb.bb_instructions) + (i - LENGTH (get_params bb.bb_instructions)) = i` by decide_tac >>
  simp[] >> decide_tac
QED

Theorem regional_nonentry_no_phi_lower_start:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    bb.bb_label ps_l /\ bb <> HD fn.fn_blocks /\
  collect_phis bb.bb_instructions = [] /\
  start = ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|> /\
  (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then
    clean_stack_plan lv cfg fn bb start else ([],start)) = (clean_ops,ps2) ==>
  regional_body_lower_inv lv dfg sb bb 0 ps2
Proof
  strip_tac >> simp[regional_body_lower_inv_def] >>
  conj_tac >- metis_tac[regional_nonentry_initial_wf] >>
  conj_tac
  >- (rpt strip_tac >>
      `~MEM (Var v) (FLAT (MAP (\inst. inst.inst_operands) (collect_phis bb.bb_instructions)))` by simp[] >>
      metis_tac[regional_nonentry_initial_coverage]) >>
  `!op v. (MEM op ps2.ps_stack \/ op IN FDOM ps2.ps_spilled) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
    (rpt strip_tac >>
     `~MEM op (FLAT (MAP (\inst. inst.inst_operands) (collect_phis bb.bb_instructions)))` by simp[] >>
     metis_tac[regional_nonentry_initial_freshness]) >>
  rpt gen_tac >> strip_tac >>
  `MEM (EL j bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED


Theorem regional_ready_use_compute:
  codegen_ready_inst inst /\ MEM v (inst_uses inst) ==>
  MEM (Var v) (compute_operands inst)
Proof
  strip_tac >>
  `MEM (Var v) inst.inst_operands` by
    gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
  simp[compute_operands_def, LET_THM] >> rpt IF_CASES_TAC >>
  gvs[get_non_label_operands_def, MEM_FILTER] >>
  gvs[codegen_ready_inst_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `case head of Lit _ => _ | _ => _` >>
  Cases_on `head` >> gvs[]
QED

Theorem regional_body_upper_input_support:
  codegen_ready_fn fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
  regional_body_lower_inv (liveness_analyze fn) dfg sb bb i ps /\
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)) ps.ps_stack ==>
  EVERY (\op. ?v. op = Var v /\
    (MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) \/
     MEM op (compute_operands inst))) ps.ps_stack
Proof
  strip_tac >>
  `wf_function fn /\ codegen_ready_inst inst` by
    (gvs[codegen_ready_fn_def, EVERY_MEM] >> metis_tac[EL_MEM, lookup_block_mem]) >>
  gvs[EVERY_MEM] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  rename1 `MEM (Var v) ps.ps_stack` >>
  `~MEM v (EL i bb.bb_instructions).inst_outputs` by
    metis_tac[regional_body_lower_inv_output_roots] >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) \/
   MEM v (inst_uses (EL i bb.bb_instructions))` by
    (drule live_vars_at_forward_or_used >> simp[LET_THM] >>
     disch_then (qspecl_then [`bb.bb_label`, `bb`, `i`, `SUC i`, `v`] mp_tac) >>
     `!k. i <= k /\ k < SUC i <=> k = i` by decide_tac >>
     simp[inst_defs_def] >> metis_tac[]) >>
  metis_tac[regional_ready_use_compute]
QED

Theorem regional_body_upper_resources:
  regional_body_lower_inv lv dfg sb bb i ps /\
  EVERY (\op. ?v. op = Var v /\ P v) ps.ps_stack ==>
  ALL_DISTINCT ps.ps_stack /\ DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled)
Proof
  simp[regional_body_lower_inv_def, generated_plan_state_wf_marked_def] >>
  strip_tac >>
  `FILTER (\op. op <> dead_stack_marker) ps.ps_stack = ps.ps_stack` by
    (simp[FILTER_EQ_ID, EVERY_MEM, dead_stack_marker_def] >>
     strip_tac >> qpat_x_assum `EVERY _ _` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >>
     disch_then (qspec_then `Label ""` mp_tac) >> simp[]) >>
  gvs[]
QED

Theorem regional_body_upper_step:
  codegen_ready_fn fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
  ~is_param_opcode inst.inst_opcode /\ ~bb_is_halting bb /\
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb i ps /\
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)) ps.ps_stack /\
  generate_inst_plan (liveness_analyze fn) (dfg_build_function fn) (cfg:cfg_analysis) fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) F next_term
    bb.bb_label ps = SOME (ops,qs) ==>
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))) qs.ps_stack
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM]) >>
  `wf_function fn /\ inst_wf inst /\ codegen_ready_inst inst` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  drule_all regional_body_upper_input_support >> strip_tac >>
  `ALL_DISTINCT ps.ps_stack /\ DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled)` by
    metis_tac[regional_body_upper_resources] >>
  Cases_on `inst.inst_opcode = NOP`
  >- (gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
          codegen_ready_inst_def, compute_operands_def, python_stack_operands_def,
          EVERY_MEM] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = OFFSET`
  >- (drule_all inst_wf_offset_shape >> strip_tac >>
      `!v. MEM v inst.inst_outputs ==>
        MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))` by
        metis_tac[fnBlockPlanStaticOffsetLiveTheory.ready_offset_output_live, ADD1] >>
      gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
          generate_offset_plan_def, stackModelTheory.stack_push_def, EVERY_APPEND, EVERY_MEM,
          compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def] >>
      rpt strip_tac >> gvs[] >>
      qpat_x_assum `!op. MEM op _ ==> ?v. _ /\ (_ \/ _)` drule >>
      strip_tac >> gvs[]) >>
  `generate_regular_inst_plan (liveness_analyze fn) (dfg_build_function fn) cfg fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) F next_term
    bb.bb_label ps = (ops,qs)` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def, LET_THM] >> rpt IF_CASES_TAC >> gvs[]) >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    metis_tac[regional_body_lower_inv_operands] >>
  `EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
     ~MEM (Var v) (compute_operands inst)) inst.inst_outputs` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     metis_tac[regional_body_lower_inv_output_roots, is_var_operand_def]) >>
  irule (INST_TYPE [alpha |-> ``:cfg_analysis``]
    fnBlockPlanStaticInventoryTheory.inventory_regular_live_support) >>
  goal_assum (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexists_tac `sb` >> simp[] >>
  metis_tac[regional_emit_input_capacity, codegen_ready_inst_outputs_distinct,
    codegen_ready_inst_def, regional_body_lower_inv_wf, generated_plan_state_wf_marked_def]
QED

Theorem regional_body_upper_prefix:
  !n a ps0 ops psn start fn bb sb cfg.
  codegen_ready_fn fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ ~bb_is_halting bb /\
  start <= a /\ a + n <= LENGTH bb.bb_instructions /\
  (!i. a <= i /\ i < a + n ==>
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    ~is_param_opcode (EL i bb.bb_instructions).inst_opcode) /\
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb a ps0 /\
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label a)) ps0.ps_stack /\
  generate_block_insts_prefix (liveness_analyze fn) (dfg_build_function fn)
    (cfg:cfg_analysis) fn bb.bb_label (bb_is_halting bb) start
    (LENGTH bb.bb_instructions) (a-start) n (DROP a bb.bb_instructions) ps0 =
    SOME (ops,psn) ==>
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (a+n))) psn.ps_stack
Proof
  Induct_on `n` >- simp[generate_block_insts_prefix_def] >>
  rpt gen_tac >> strip_tac >>
  `a < LENGTH bb.bb_instructions` by simp[] >>
  `DROP a bb.bb_instructions = EL a bb.bb_instructions :: DROP (SUC a) bb.bb_instructions` by
    metis_tac[DROP_CONS_EL] >>
  qpat_x_assum `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[generate_block_insts_prefix_def, LET_THM] >>
  simp[AllCaseEqs()] >> strip_tac >>
  ` (if LENGTH bb.bb_instructions <= SUC a then
       live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)
     else live_vars_at (liveness_analyze fn) bb.bb_label (a+1)) =
    live_vars_at (liveness_analyze fn) bb.bb_label (SUC a)` by
    (IF_CASES_TAC
     >- (`LENGTH bb.bb_instructions = SUC a` by decide_tac >> simp[]) >> simp[ADD1]) >>
  gvs[] >>
  rename1 `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = SOME (_,mid)` >>
  `regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb (SUC a) mid` by
    (irule regional_body_lower_inv_step >> simp[] >>
     goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[LESS_EQ_REFL, LESS_EQ_LESS_TRANS]) >>
  `EVERY (\op. ?v. op = Var v /\
     MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC a))) mid.ps_stack` by
    (irule regional_body_upper_step >> simp[] >>
     goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
     qexists_tac `sb` >> simp[] >> metis_tac[LESS_EQ_REFL, LESS_EQ_LESS_TRANS]) >>
  `a + SUC n = SUC a + n` by simp[] >> pop_assum SUBST1_TAC >>
  first_x_assum irule >> gvs[ADD1] >>
  goal_assum (drule_at (Pat `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexists_tac `sb` >> simp[] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_SUC_REFL]
QED
