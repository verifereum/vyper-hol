(*
 * ConcretizeMemLoc's stage contract, the structural part of row 3: the
 * facts of the output context the later runs need that are not about
 * memory.
 *
 * TOP-LEVEL:
 *   concretize_stage_shape
 *)
Theory concretizeStageShape
Ancestors
  concretizeStepStructure o1PassContract stackPlanGen concretizeMemLocDefs venomPassDispatcher venomPassSchedule venomFnScheduleRunner cfgWf
  staticLayoutFoldProofs staticLayoutDefs passSharedDefs venomWf passSimulationDefs list rich_list combin venomInst
  passTransform

Theorem concretize_inst_positions_outputs[local]:
  (inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP positions (Allocation inst.inst_id))) ==>
  (concretize_inst_with_positions positions inst).inst_outputs = inst.inst_outputs
Proof
  Cases_on `inst.inst_opcode = ALLOCA` >>
  simp[concretize_inst_with_positions_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `out::rest` >> Cases_on `rest` >> simp[] >>
  Cases_on `FLOOKUP positions (Allocation inst.inst_id)` >>
  simp[mk_assign_inst_def]
QED

Theorem concretize_inst_positions_nop[local]:
  (concretize_inst_with_positions positions inst).inst_opcode = NOP ==>
  inst.inst_opcode = NOP \/ inst.inst_opcode = ALLOCA
Proof
  Cases_on `inst.inst_opcode = ALLOCA` >>
  simp[concretize_inst_with_positions_def]
QED

Theorem concretize_positions_definition_filter[local]:
  EVERY inst_wf insts /\
  (!inst. MEM inst insts /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP positions (Allocation inst.inst_id))) ==>
  FILTER (\i. MEM v i.inst_outputs)
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions positions) insts)) =
  MAP (concretize_inst_with_positions positions)
    (FILTER (\i. MEM v i.inst_outputs) insts)
Proof
  Induct_on `insts` >- simp[] >>
  simp[] >> rpt strip_tac >>
  ` (concretize_inst_with_positions positions h).inst_outputs = h.inst_outputs`
    by (irule concretize_inst_positions_outputs >> simp[]) >>
  `h.inst_opcode = NOP ==> h.inst_outputs = []`
    by (strip_tac >> gvs[inst_wf_def]) >>
  Cases_on `MEM v h.inst_outputs` >> simp[] >>
  Cases_on `(concretize_inst_with_positions positions h).inst_opcode = NOP` >>
  simp[] >> drule concretize_inst_positions_nop >> strip_tac >> gvs[] >>
  `IS_SOME (FLOOKUP positions (Allocation h.inst_id))` by metis_tac[] >>
  Cases_on `h.inst_outputs` >>
  gvs[concretize_inst_with_positions_def, AllCaseEqs(), mk_assign_inst_def] >>
  rename1 `out::rest` >> Cases_on `rest` >>
  gvs[AllCaseEqs(), mk_assign_inst_def] >>
  Cases_on `FLOOKUP positions (Allocation h.inst_id)` >>
  gvs[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem concretize_positions_path:
  EVERY bb_well_formed fn.fn_blocks ==>
  (is_fn_path (concretize_function_with_positions positions fn) path <=>
   is_fn_path fn path)
Proof
  strip_tac >> Induct_on `path` >- simp[is_fn_path_def] >>
  Cases_on `path` >>
  simp[is_fn_path_def, concretize_positions_cfg_edge]
QED

Theorem concretize_positions_block_instruction:
  MEM inst' (clear_nops_block (block_map_transform
    (concretize_inst_with_positions positions) bb)).bb_instructions <=>
  ?inst. MEM inst bb.bb_instructions /\
    inst' = concretize_inst_with_positions positions inst /\
    inst'.inst_opcode <> NOP
Proof
  simp[clear_nops_block_def, block_map_transform_def, MEM_FILTER, MEM_MAP] >>
  metis_tac[]
QED

Theorem concretize_positions_block_phi:
  inst.inst_opcode = PHI ==>
  (MEM inst (clear_nops_block (block_map_transform
     (concretize_inst_with_positions positions) bb)).bb_instructions <=>
   MEM inst bb.bb_instructions)
Proof
  strip_tac >> simp[concretize_positions_block_instruction] >>
  metis_tac[concretize_positions_phi]
QED

Theorem concretize_positions_block_provenance:
  MEM bb' (concretize_function_with_positions positions fn).fn_blocks <=>
  ?bb. MEM bb fn.fn_blocks /\
    bb' = clear_nops_block
      (block_map_transform (concretize_inst_with_positions positions) bb)
Proof
  simp[concretize_function_with_positions_def, clear_nops_function_def,
       function_map_transform_def, MEM_MAP] >> metis_tac[]
QED

Theorem concretize_positions_insts_blocks[local]:
  fn_insts_blocks (MAP (\bb. clear_nops_block
    (block_map_transform (concretize_inst_with_positions positions) bb)) bbs) =
  FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions positions) (fn_insts_blocks bbs))
Proof
  Induct_on `bbs` >>
  gvs[fn_insts_blocks_def, clear_nops_block_def, block_map_transform_def,
       MAP_APPEND, FILTER_APPEND]
QED

Theorem concretize_positions_insts[local]:
  fn_insts (concretize_function_with_positions positions fn) =
  FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions positions) (fn_insts fn))
Proof
  simp[fn_insts_def, concretize_function_with_positions_def,
       clear_nops_function_def, function_map_transform_def, MAP_MAP_o,
       combinTheory.o_DEF, concretize_positions_insts_blocks]
QED

Theorem concretize_positions_definition_count:
  EVERY inst_wf (fn_insts fn) /\
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP positions (Allocation inst.inst_id))) ==>
  LENGTH (FILTER (\i. MEM v i.inst_outputs)
    (fn_insts (concretize_function_with_positions positions fn))) =
  LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts fn))
Proof
  strip_tac >> simp[concretize_positions_insts] >>
  drule_all concretize_positions_definition_filter >>
  disch_then (qspec_then `v` assume_tac) >> simp[]
QED

Theorem concretize_positions_definition_endpoint:
  EVERY inst_wf xs /\
  (!inst. MEM inst xs /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP positions (Allocation inst.inst_id))) /\
  i < LENGTH xs /\ MEM v (EL i xs).inst_outputs ==>
  ?i'. i' < LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
          (MAP (concretize_inst_with_positions positions) xs)) /\
    MEM v (EL i' (FILTER (\inst. inst.inst_opcode <> NOP)
          (MAP (concretize_inst_with_positions positions) xs))).inst_outputs
Proof
  strip_tac >>
  drule_all concretize_positions_definition_filter >>
  disch_then (qspec_then `v` assume_tac) >>
  `MEM (EL i xs) xs` by simp[EL_MEM] >>
  `MEM (concretize_inst_with_positions positions (EL i xs))
     (MAP (concretize_inst_with_positions positions)
       (FILTER (\inst. MEM v inst.inst_outputs) xs))`
    by (simp[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  qpat_x_assum `FILTER _ _ = _` (fn th => fs[GSYM th, MEM_FILTER]) >>
  qmatch_goalsub_abbrev_tac `LENGTH retained` >>
  `MEM (concretize_inst_with_positions positions (EL i xs)) retained`
    by simp[Abbr `retained`, MEM_FILTER] >>
  qpat_x_assum `MEM _ retained` (strip_assume_tac o REWRITE_RULE[MEM_EL]) >>
  goal_assum drule >> gvs[]
QED

Theorem concretize_positions_definition_before_use:
  EVERY inst_wf xs /\
  (!inst. MEM inst xs /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP positions (Allocation inst.inst_id))) /\
  i < j /\ j < LENGTH xs /\ MEM v (EL i xs).inst_outputs /\
  (concretize_inst_with_positions positions (EL j xs)).inst_opcode <> NOP ==>
  ?i' j'. i' < j' /\
    j' < LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
          (MAP (concretize_inst_with_positions positions) xs)) /\
    MEM v (EL i' (FILTER (\inst. inst.inst_opcode <> NOP)
          (MAP (concretize_inst_with_positions positions) xs))).inst_outputs /\
    EL j' (FILTER (\inst. inst.inst_opcode <> NOP)
          (MAP (concretize_inst_with_positions positions) xs)) =
      concretize_inst_with_positions positions (EL j xs)
Proof
  strip_tac >>
  `xs = TAKE j xs ++ EL j xs :: DROP (SUC j) xs`
    by (qspec_then `j` (qspec_then `xs` mp_tac) TAKE_DROP_SUC >>
        simp[]) >>
  `EVERY inst_wf (TAKE j xs)` by metis_tac[EVERY_APPEND, EVERY_DEF] >>
  `!inst. MEM inst (TAKE j xs) /\ inst.inst_opcode = ALLOCA ==>
     IS_SOME (FLOOKUP positions (Allocation inst.inst_id))`
    by metis_tac[MEM_APPEND] >>
  `i < LENGTH (TAKE j xs) /\ MEM v (EL i (TAKE j xs)).inst_outputs`
    by simp[LENGTH_TAKE, EL_TAKE] >>
  drule_all concretize_positions_definition_endpoint >> strip_tac >>
  qexistsl [`i'`, `LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
       (MAP (concretize_inst_with_positions positions) (TAKE j xs)))`] >>
  `FILTER (\inst. inst.inst_opcode <> NOP)
     (MAP (concretize_inst_with_positions positions) xs) =
   FILTER (\inst. inst.inst_opcode <> NOP)
     (MAP (concretize_inst_with_positions positions) (TAKE j xs)) ++
   concretize_inst_with_positions positions (EL j xs) ::
   FILTER (\inst. inst.inst_opcode <> NOP)
     (MAP (concretize_inst_with_positions positions) (DROP (SUC j) xs))`
    by (qpat_x_assum `xs = _` (fn th =>
          GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) empty_rewrites [th]) >>
        simp[MAP_APPEND, FILTER_APPEND]) >>
  simp[EL_APPEND_EQN]
QED

Theorem concretize_positions_def_on_paths:
  EVERY bb_well_formed fn.fn_blocks /\ fn_inst_wf fn /\
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP positions (Allocation inst.inst_id))) /\
  MEM bb fn.fn_blocks /\
  (case use_opt of NONE => T | SOME inst =>
    (concretize_inst_with_positions positions inst).inst_opcode <> NOP) /\
  def_on_all_paths fn bb use_opt v ==>
  def_on_all_paths (concretize_function_with_positions positions fn)
    (clear_nops_block (block_map_transform
      (concretize_inst_with_positions positions) bb))
    (OPTION_MAP (concretize_inst_with_positions positions) use_opt) v
Proof
  strip_tac >>
  `!b. MEM b fn.fn_blocks ==> EVERY inst_wf b.bb_instructions /\
    (!inst. MEM inst b.bb_instructions /\ inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP positions (Allocation inst.inst_id)))`
    by (gvs[fn_inst_wf_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
        metis_tac[]) >>
  gvs[def_on_all_paths_def, concretize_positions_path,
      concretize_positions_entry_label, clear_nops_block_def,
      block_map_transform_def] >>
  qx_gen_tac `path` >> strip_tac >>
  first_x_assum (qspec_then `path` mp_tac) >> simp[] >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (disj1_tac >>
      `EVERY inst_wf def_bb.bb_instructions /\
       (!inst. MEM inst def_bb.bb_instructions /\ inst.inst_opcode = ALLOCA ==>
          IS_SOME (FLOOKUP positions (Allocation inst.inst_id)))`
        by metis_tac[] >>
      drule_all concretize_positions_definition_filter >>
      disch_then (qspec_then `v` assume_tac) >>
      `MEM (concretize_inst_with_positions positions def_inst)
        (MAP (concretize_inst_with_positions positions)
          (FILTER (\inst. MEM v inst.inst_outputs) def_bb.bb_instructions))`
        by (simp[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
      qpat_x_assum `FILTER _ _ = _` (fn th => fs[GSYM th, MEM_FILTER]) >>
      qexistsl [`k`, `clear_nops_block (block_map_transform
        (concretize_inst_with_positions positions) def_bb)`,
        `concretize_inst_with_positions positions def_inst`] >>
      simp[concretize_positions_block_provenance,
           concretize_positions_block_instruction] >>
      simp[clear_nops_block_def, block_map_transform_def] >> metis_tac[]) >>
  disj2_tac >>
  `EVERY inst_wf bb.bb_instructions /\
   (!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP positions (Allocation inst.inst_id)))`
    by metis_tac[] >>
  Cases_on `use_opt` >> gvs[]
  >- (irule concretize_positions_definition_endpoint >> simp[] >>
      goal_assum drule >> simp[]) >>
  `EVERY inst_wf bb.bb_instructions` by metis_tac[] >>
  drule_all concretize_positions_definition_before_use >>
  strip_tac >> qexists `i'` >> simp[] >>
  qexists `j'` >> simp[]
QED

Theorem concretize_positions_defs_reach_uses:
  EVERY bb_well_formed fn.fn_blocks /\ fn_inst_wf fn /\
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP positions (Allocation inst.inst_id))) /\
  fn_defs_reach_uses fn ==>
  fn_defs_reach_uses (concretize_function_with_positions positions fn)
Proof
  strip_tac >> simp[fn_defs_reach_uses_def] >>
  qx_gen_tac `bb'` >> qx_gen_tac `inst'` >> strip_tac >>
  gvs[concretize_positions_block_provenance,
      concretize_positions_block_instruction] >>
  rename1 `MEM bb fn.fn_blocks` >>
  rename1 `MEM inst bb.bb_instructions` >>
  Cases_on `inst.inst_opcode = PHI`
  >- (`concretize_inst_with_positions positions inst = inst`
        by metis_tac[concretize_positions_phi] >>
      simp[] >> rpt gen_tac >> strip_tac >>
      gvs[concretize_positions_block_provenance] >>
      rename1 `MEM pred_bb fn.fn_blocks` >>
      `fn_cfg_edge fn pred_bb.bb_label bb.bb_label`
        by gvs[clear_nops_block_def, block_map_transform_def,
               concretize_positions_cfg_edge] >>
      `def_on_all_paths fn pred_bb NONE v`
        by (gvs[fn_defs_reach_uses_def, clear_nops_block_def,
                block_map_transform_def] >> metis_tac[]) >>
      drule_at (Pat `def_on_all_paths _ _ _ _`) concretize_positions_def_on_paths >>
      simp[]) >>
  ` (concretize_inst_with_positions positions inst).inst_opcode <> PHI`
    by metis_tac[concretize_positions_phi] >>
  simp[] >> qx_gen_tac `v` >> strip_tac >>
  `MEM (Var v) inst.inst_operands`
    by metis_tac[concretize_positions_var_operand] >>
  `def_on_all_paths fn bb (SOME inst) v`
    by (gvs[fn_defs_reach_uses_def, clear_nops_block_def,
                block_map_transform_def] >> metis_tac[]) >>
  drule_at (Pat `def_on_all_paths _ _ _ _`) concretize_positions_def_on_paths >> simp[]
QED

Theorem concretize_positions_make_ssa_input_ok:
  EVERY bb_well_formed fn.fn_blocks /\ fn_inst_wf fn /\
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP positions (Allocation inst.inst_id))) /\
  make_ssa_input_ok fn ==>
  make_ssa_input_ok (concretize_function_with_positions positions fn)
Proof
  strip_tac >>
  `EVERY inst_wf (fn_insts fn)`
    by (gvs[EVERY_MEM, fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >>
        metis_tac[]) >>
  `!v. LENGTH (FILTER (\i. MEM v i.inst_outputs)
      (fn_insts (concretize_function_with_positions positions fn))) =
       LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts fn))`
    by (gen_tac >> irule concretize_positions_definition_count >> simp[]) >>
  gvs[make_ssa_input_ok_def] >> rpt conj_tac
  >- (gvs[all_reachable_def] >>
      simp[concretize_positions_block_provenance] >> rpt strip_tac >>
      gvs[clear_nops_block_def, block_map_transform_def,
          concretize_positions_reachable] >> metis_tac[]) 
  >- (irule concretize_positions_defs_reach_uses >> simp[])
  >- (gvs[fn_phi_operands_single_def_def] >>
      simp[concretize_positions_block_provenance,
           concretize_positions_block_instruction,
           concretize_positions_phi] >> rpt strip_tac >>
      gvs[concretize_positions_phi, concretize_positions_block_phi] >> metis_tac[])
  >- (gvs[fn_phis_cover_preds_def] >>
      simp[concretize_positions_block_provenance,
           concretize_positions_block_instruction,
           concretize_positions_phi] >> rpt strip_tac >>
      gvs[concretize_positions_block_phi] >>
      gvs[concretize_positions_phi, concretize_positions_cfg_edge,
          clear_nops_block_def, block_map_transform_def] >> metis_tac[])
  >- (gvs[fn_phi_outputs_single_def_def] >>
      simp[concretize_positions_block_provenance,
           concretize_positions_block_instruction,
           concretize_positions_phi] >> rpt strip_tac >>
      gvs[concretize_positions_phi, concretize_positions_block_phi] >> metis_tac[])
  >- (gvs[fn_phis_non_degenerate_def] >>
      simp[concretize_positions_insts, MEM_FILTER, MEM_MAP] >> rpt strip_tac >>
      gvs[concretize_positions_phi, concretize_positions_block_phi] >> metis_tac[]) >>
  simp[concretize_positions_block_provenance,
       concretize_positions_block_instruction,
       concretize_positions_phi] >> rpt strip_tac >>
  gvs[concretize_positions_block_phi] >>
      gvs[concretize_positions_phi, concretize_positions_cfg_edge,
      clear_nops_block_def, block_map_transform_def] >> metis_tac[]
QED

Theorem make_ssa_input_ok_blocks:
  f.fn_blocks = g.fn_blocks ==>
  (make_ssa_input_ok f <=> make_ssa_input_ok g)
Proof
  strip_tac >>
  `fn_cfg_edge f = fn_cfg_edge g`
    by simp[FUN_EQ_THM, fn_cfg_edge_def] >>
  `fn_entry_label f = fn_entry_label g`
    by simp[fn_entry_label_def, entry_block_def] >>
  `!path. is_fn_path f path = is_fn_path g path`
    by (Induct_on `path` >- simp[is_fn_path_def] >>
        Cases_on `path` >> simp[is_fn_path_def]) >>
  simp[make_ssa_input_ok_def, all_reachable_def, fn_reachable_def,
       fn_defs_reach_uses_def, def_on_all_paths_def,
       fn_phi_operands_single_def_def, fn_phis_cover_preds_def,
       fn_phi_outputs_single_def_def, fn_phis_non_degenerate_def, fn_insts_def]
QED

Theorem concretize_positions_no_raw_fmp:
  no_raw_fmp_ops fn ==>
  no_raw_fmp_ops (concretize_function_with_positions positions fn)
Proof
  simp[no_raw_fmp_ops_def, concretize_positions_insts, MEM_FILTER, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  rename1 `MEM inst (fn_insts fn)` >>
  `~is_raw_fmp_opcode inst.inst_opcode` by metis_tac[] >>
  Cases_on `inst.inst_opcode = ALLOCA` >>
  gvs[concretize_inst_with_positions_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  rename1 `out::rest` >> Cases_on `rest` >> gvs[] >>
  Cases_on `FLOOKUP positions (Allocation inst.inst_id)` >>
  gvs[mk_assign_inst_def, mk_nop_inst_def, is_raw_fmp_opcode_def]
QED

Theorem mk_concretize_layout_alloca_positions[local]:
  mk_concretize_layout reserved positions fn = SOME layout ==>
  !inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP layout.cl_positions (Allocation inst.inst_id))
Proof
  simp[mk_concretize_layout_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> drule allocation_eom_fold_success >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  gvs[allocation_end_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP positions (Allocation inst.inst_id)` >> gvs[]
QED

Theorem concretize_function_fresh_positions:
  fn.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' ==>
  ?layout. fn' = apply_context_concretize_layout ctx layout fn /\
    (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP layout.cl_positions (Allocation inst.inst_id)))
Proof
  simp[concretize_function_fuel_in_context_def, fn_has_static_layout_def] >>
  strip_tac >>
  Cases_on `fn_needs_liveness_allocation fn \/ imported_mems_used ctx fn <> []`
  >- (gvs[AllCaseEqs()] >>
      qexists `layout` >> simp[] >>
      qpat_x_assum `compute_function_layout_fuel_in_context _ _ _ _ = _`
        mp_tac >>
      simp[compute_function_layout_fuel_in_context_def, AllCaseEqs()] >>
      rpt strip_tac >> drule mk_concretize_layout_alloca_positions >> simp[]) >>
  gvs[AllCaseEqs()] >> qexists `layout` >> simp[] >>
  qpat_x_assum `compute_function_layout_eval _ _ = _` mp_tac >>
  simp[compute_function_layout_eval_def, AllCaseEqs()] >>
  rpt strip_tac >> drule mk_concretize_layout_alloca_positions >> simp[]
QED

Theorem apply_context_layout_make_ssa_input_ok:
  EVERY bb_well_formed fn.fn_blocks /\ fn_inst_wf fn /\
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP layout.cl_positions (Allocation inst.inst_id))) /\
  make_ssa_input_ok fn ==>
  make_ssa_input_ok (apply_context_concretize_layout ctx layout fn)
Proof
  strip_tac >>
  `make_ssa_input_ok (apply_context_concretize_layout ctx layout fn) =
   make_ssa_input_ok (concretize_function_with_positions layout.cl_positions fn)`
    by (irule make_ssa_input_ok_blocks >>
        simp[apply_context_concretize_layout_def, apply_concretize_layout_def]) >>
  simp[] >> irule concretize_positions_make_ssa_input_ok >> simp[]
QED

Theorem apply_context_layout_no_raw_fmp:
  no_raw_fmp_ops fn ==>
  no_raw_fmp_ops (apply_context_concretize_layout ctx layout fn)
Proof
  strip_tac >>
  drule concretize_positions_no_raw_fmp >>
  disch_then (qspec_then `layout.cl_positions` mp_tac) >>
  simp[no_raw_fmp_ops_def, fn_insts_def,
       apply_context_concretize_layout_def, apply_concretize_layout_def]
QED

Theorem concretize_step_make_ssa_input_ok:
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  wf_function fn /\ fn_inst_wf fn /\ make_ssa_input_ok fn ==>
  make_ssa_input_ok out.fpo_function
Proof
  strip_tac >>
  `execute_configured_fn_pass rpolicy (CFP_Simple VP_ConcretizeMemLoc)
     observed s fn = SOME out` by fs[fn_pass_step_def] >>
  Cases_on `fn.fn_eom`
  >- (gvs[execute_configured_fn_pass_concretize, AllCaseEqs()] >>
      drule_all concretize_function_fresh_positions >> strip_tac >> gvs[] >>
      irule apply_context_layout_make_ssa_input_ok >> simp[] >>
      gvs[wf_function_def, EVERY_MEM]) >>
  `fn_has_static_layout fn` by fs[fn_has_static_layout_def] >>
  qpat_x_assum `execute_configured_fn_pass _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [concretize_function_fuel_in_context_def] >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]
QED

Theorem concretize_step_no_raw_fmp:
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  no_raw_fmp_ops fn ==>
  no_raw_fmp_ops out.fpo_function
Proof
  strip_tac >>
  `execute_configured_fn_pass rpolicy (CFP_Simple VP_ConcretizeMemLoc)
     observed s fn = SOME out` by fs[fn_pass_step_def] >>
  Cases_on `fn.fn_eom`
  >- (gvs[execute_configured_fn_pass_concretize, AllCaseEqs()] >>
      drule_all concretize_function_fresh_positions >> strip_tac >> gvs[] >>
      irule apply_context_layout_no_raw_fmp >> simp[]) >>
  `fn_has_static_layout fn` by fs[fn_has_static_layout_def] >>
  qpat_x_assum `execute_configured_fn_pass _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [concretize_function_fuel_in_context_def] >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]
QED

Theorem concretize_stage_member[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  MEM g C'.ctx_functions ==>
  ?f observed s out. MEM f C.ctx_functions /\
    fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s f out /\
    out.fpo_function = g
Proof
  simp[ctx_pass_stage_def, LIST_REL_EL_EQN, MEM_EL] >> strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >>
  impl_tac >- fs[] >> strip_tac >> metis_tac[]
QED

Theorem concretize_stage_make_ssa_input_ok:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  o1_ctx_shape C /\ EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  EVERY make_ssa_input_ok C.ctx_functions ==>
  EVERY make_ssa_input_ok C'.ctx_functions
Proof
  strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all concretize_stage_member >> strip_tac >> gvs[] >>
  irule concretize_step_make_ssa_input_ok >>
  gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]
QED

Theorem concretize_stage_fmp_free:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\ fmp_free_ctx C ==>
  fmp_free_ctx C'
Proof
  strip_tac >> simp[fmp_free_ctx_def, EVERY_MEM] >> gen_tac >> disch_tac >>
  drule_all concretize_stage_member >> strip_tac >> gvs[] >>
  `f.fn_fmp_signature = NONE /\ no_raw_fmp_ops f /\ f.fn_eom = NONE`
    by (gvs[fmp_free_ctx_def, EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (gvs[fn_pass_step_def, fn_pass_effects_hold_def,
          fn_abi_effect_holds_def, fn_pass_abi_effect_def,
          fn_pass_tag_def, fn_fmp_convention_eq_def]) >>
  irule concretize_step_no_raw_fmp >> metis_tac[]
QED

Theorem concretize_stage_callee_first:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  callee_first names C.ctx_functions ==>
  callee_first names C'.ctx_functions
Proof
  strip_tac >> simp[callee_first_def] >> rpt strip_tac >>
  drule_all concretize_stage_member >> strip_tac >> gvs[] >>
  gvs[fn_pass_step_def, introduces_no_invoke_edges_def,
      fn_invoke_targets_def, callee_first_def, EVERY_MEM] >> metis_tac[]
QED

Theorem collect_fn_eoms_defined:
  EVERY (\fn. IS_SOME fn.fn_eom) fns ==> ?es. collect_fn_eoms fns = SOME es
Proof
  Induct_on `fns` >> simp[collect_fn_eoms_def] >> strip_tac >>
  Cases_on `h.fn_eom` >> gvs[] >>
  Cases_on `collect_fn_eoms fns` >> gvs[]
QED

Theorem global_reserved_end_defined:
  reserved_intervals_wf rs ==> !start. ?e. global_reserved_end rs start = SOME e
Proof
  Induct_on `rs` >- simp[global_reserved_end_def] >>
  Cases_on `h` >> simp[reserved_intervals_wf_def, global_reserved_end_def]
QED

Theorem concretize_stage_max_live_eom:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  reserved_intervals_wf C.ctx_global_reserved ==>
  ?eom. max_live_eom C' = SOME eom
Proof
  strip_tac >>
  `EVERY (\fn. IS_SOME fn.fn_eom) C'.ctx_functions`
    by (simp[EVERY_MEM] >> rpt strip_tac >>
        drule_all concretize_stage_member >> strip_tac >> gvs[] >>
        gvs[fn_pass_step_def, fn_pass_effects_hold_def,
            fn_static_layout_effect_holds_def, fn_pass_static_layout_effect_def,
            fn_pass_tag_def]) >>
  drule collect_fn_eoms_defined >> strip_tac >>
  drule global_reserved_end_defined >>
  disch_then (qspec_then `0` strip_assume_tac) >>
  gvs[ctx_pass_stage_def, max_live_eom_def]
QED

(* Why it holds (intuition, not a prescribed proof).

   Every input function has fn_eom = NONE, so the pass computes a layout
   for each and sets fn_eom to SOME; the global reservations are C's and
   well formed, so max_live_eom C' is SOME.  The rewrite only turns
   ALLOCA into ASSIGN, so the CFG, the PHIs, the definitions and uses,
   the INVOKE targets and the FMP signature are the input's.

   Facts worth knowing (checked against the definitions, not proved):
   - fn_pass_step gives fn_pass_effects_hold for the ConcretizeMemLoc tag:
     IS_SOME out.fn_eom (FSLE_Concretize) and an equal fn_fmp_signature
     (FAE_PreserveFmpConvention); it also gives introduces_no_invoke_edges
     and the unchanged fn_name, which is all callee_first needs.
   - With fn_eom = NONE the pass's layout comes from mk_concretize_layout,
     whose allocation_eom_fold succeeded, so every ALLOCA has a position
     (allocation_eom_fold_success): concretize_inst_with_positions never
     turns an ALLOCA into a NOP.
   - clear_nops_function then drops only NOPs, which have no outputs by
     inst_wf (o1_ctx_shape); terminators are not NOPs, so bb_succs, the
     CFG edges, the entry and the PHIs are unchanged, and the dropped
     instructions only remove uses.
   - global_reserved_end r 0 is SOME when every interval of r is
     reserved_interval_wf, which reserved_intervals_wf implies. *)
Theorem concretize_stage_shape:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\
  reserved_intervals_wf C.ctx_global_reserved /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  fmp_free_ctx C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  callee_first names C.ctx_functions ==>
  fmp_free_ctx C' /\ EVERY make_ssa_input_ok C'.ctx_functions /\
  callee_first names C'.ctx_functions /\
  ?eom. max_live_eom C' = SOME eom
Proof
  strip_tac >> rpt conj_tac
  >- (irule concretize_stage_fmp_free >> metis_tac[])
  >- (irule concretize_stage_make_ssa_input_ok >> metis_tac[])
  >- (irule concretize_stage_callee_first >> metis_tac[]) >>
  irule concretize_stage_max_live_eom >> metis_tac[]
QED
