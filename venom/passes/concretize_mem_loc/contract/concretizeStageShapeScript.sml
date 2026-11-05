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
  o1PassContract stackPlanGen concretizeMemLocDefs venomPassDispatcher
  staticLayoutFoldProofs staticLayoutDefs passSharedDefs venomWf passSimulationDefs list rich_list combin venomInst

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

Theorem concretize_inst_positions_phi[local]:
  ((concretize_inst_with_positions positions inst).inst_opcode = PHI <=>
   inst.inst_opcode = PHI) /\
  (inst.inst_opcode = PHI ==>
   concretize_inst_with_positions positions inst = inst)
Proof
  Cases_on `inst.inst_opcode = ALLOCA` >>
  simp[concretize_inst_with_positions_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `out::rest` >> Cases_on `rest` >> simp[] >>
  Cases_on `FLOOKUP positions (Allocation inst.inst_id)` >>
  simp[mk_assign_inst_def, mk_nop_inst_def]
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

Theorem concretize_positions_terminator[local]:
  is_terminator inst.inst_opcode ==>
  concretize_inst_with_positions positions inst = inst /\
  inst.inst_opcode <> NOP
Proof
  Cases_on `inst.inst_opcode = ALLOCA` >>
  simp[concretize_inst_with_positions_def] >>
  strip_tac >> gvs[is_terminator_def] >>
  strip_tac >> gvs[is_terminator_def]
QED

Theorem concretize_positions_terminator_suffix[local]:
  is_terminator inst.inst_opcode ==>
  FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions positions) (xs ++ [inst])) =
  FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions positions) xs) ++ [inst]
Proof
  strip_tac >>
  drule_then (qspec_then `positions` strip_assume_tac)
    concretize_positions_terminator >>
  simp[MAP_APPEND, FILTER_APPEND]
QED

Theorem concretize_positions_last_terminator[local]:
  insts <> [] /\ is_terminator (LAST insts).inst_opcode ==>
  FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions positions) insts) <> [] /\
  LAST (FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions positions) insts)) = LAST insts
Proof
  strip_tac >>
  `insts = FRONT insts ++ [LAST insts]` by metis_tac[APPEND_FRONT_LAST] >>
  `FILTER (\i. i.inst_opcode <> NOP)
     (MAP (concretize_inst_with_positions positions) insts) =
   FILTER (\i. i.inst_opcode <> NOP)
     (MAP (concretize_inst_with_positions positions) (FRONT insts)) ++ [LAST insts]`
    by metis_tac[concretize_positions_terminator_suffix] >>
  simp[]
QED

Theorem concretize_positions_block_succs[local]:
  bb_well_formed bb ==>
  bb_succs (clear_nops_block
    (block_map_transform (concretize_inst_with_positions positions) bb)) =
  bb_succs bb
Proof
  simp[bb_well_formed_def] >> strip_tac >>
  drule_all concretize_positions_last_terminator >>
  disch_then (qspec_then `positions` strip_assume_tac) >>
  simp[bb_succs_def, clear_nops_block_def, block_map_transform_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  Cases_on `FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions positions) bb.bb_instructions)` >> gvs[]
QED

Theorem concretize_positions_block_labels:
  MAP (\bb. bb.bb_label)
    (concretize_function_with_positions positions fn).fn_blocks =
  MAP (\bb. bb.bb_label) fn.fn_blocks
Proof
  simp[concretize_function_with_positions_def, clear_nops_function_def,
       function_map_transform_def, MAP_MAP_o, o_DEF,
       clear_nops_block_def, block_map_transform_def]
QED

Theorem concretize_positions_entry_label:
  fn_entry_label (concretize_function_with_positions positions fn) =
  fn_entry_label fn
Proof
  Cases_on `fn.fn_blocks` >>
  simp[fn_entry_label_def, entry_block_def,
       concretize_function_with_positions_def, clear_nops_function_def,
       function_map_transform_def, clear_nops_block_def, block_map_transform_def]
QED

Theorem concretize_positions_cfg_edge:
  EVERY bb_well_formed fn.fn_blocks ==>
  (fn_cfg_edge (concretize_function_with_positions positions fn) a b <=>
   fn_cfg_edge fn a b)
Proof
  strip_tac >>
  simp[fn_cfg_edge_def, concretize_function_with_positions_def,
       clear_nops_function_def, function_map_transform_def, MEM_MAP] >>
  eq_tac
  >- (rpt strip_tac >> gvs[] >>
      rename1 `MEM source fn.fn_blocks` >>
      `bb_well_formed source` by metis_tac[EVERY_MEM] >>
      drule concretize_positions_block_succs >>
      disch_then (qspec_then `positions` assume_tac) >>
      qexists `source` >>
      gvs[clear_nops_block_def, block_map_transform_def]) >>
  rpt strip_tac >>
  rename1 `MEM source fn.fn_blocks` >>
  `bb_well_formed source` by metis_tac[EVERY_MEM] >>
  drule concretize_positions_block_succs >>
  disch_then (qspec_then `positions` assume_tac) >>
  qexists `clear_nops_block (block_map_transform
    (concretize_inst_with_positions positions) source)` >>
  conj_tac
  >- (qexists `block_map_transform (concretize_inst_with_positions positions) source` >>
      simp[] >> qexists `source` >> simp[]) >>
  gvs[clear_nops_block_def, block_map_transform_def]
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

Theorem concretize_positions_reachable:
  EVERY bb_well_formed fn.fn_blocks ==>
  (fn_reachable (concretize_function_with_positions positions fn) lbl <=>
   fn_reachable fn lbl)
Proof
  strip_tac >>
  `fn_cfg_edge (concretize_function_with_positions positions fn) = fn_cfg_edge fn`
    by (simp[FUN_EQ_THM, concretize_positions_cfg_edge]) >>
  simp[fn_reachable_def, concretize_positions_entry_label]
QED

Theorem concretize_positions_operand_provenance[local]:
  MEM (Var v) (concretize_inst_with_positions positions inst).inst_operands ==>
  MEM (Var v) inst.inst_operands
Proof
  Cases_on `inst.inst_opcode = ALLOCA` >>
  simp[concretize_inst_with_positions_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `out::rest` >> Cases_on `rest` >> simp[] >>
  Cases_on `FLOOKUP positions (Allocation inst.inst_id)` >>
  simp[mk_assign_inst_def, mk_nop_inst_def]
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
  metis_tac[concretize_inst_positions_phi]
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
  cheat
QED
