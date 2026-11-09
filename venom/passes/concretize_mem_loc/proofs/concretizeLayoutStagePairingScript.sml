Theory concretizeLayoutStagePairing
Ancestors concretizeLayoutPositions concretizeLayoutNumeric
  concretizeLayoutBlockPairing concretizeStepStructure
  concretizeAnalysisMetadataOwnership concretizeMemLocDefs
  staticLayoutAllocatorProofs staticLayoutDefs venomExecSemantics
  list finite_map

(* Retain the successful layout, so rewrite and metadata use one map. *)
Definition layout_stage_row_def:
  layout_stage_row ctx reserved fn out layout <=>
    out = apply_context_concretize_layout ctx layout fn /\
    ((?fuel. compute_function_layout_fuel_in_context fuel ctx reserved fn = SOME layout) \/
     compute_function_layout_eval reserved fn = SOME layout)
End

Theorem layout_stage_row_produce:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  lookup_function name C.ctx_functions = SOME fn /\ fn.fn_eom = NONE ==>
  ?out observed layout.
    lookup_function name C'.ctx_functions = SOME out /\
    walk_view rpolicy (DROP 3 o1_fn_passes) C' fn observed /\
    layout_stage_row observed.cu_context observed.cu_context.ctx_global_reserved
      fn out layout
Proof
  strip_tac >> drule_all concretize_stage_lookup >> strip_tac >>
  qexistsl [`out`, `observed`] >> simp[] >>
  gvs[concretize_function_fuel_in_context_def, fn_has_static_layout_def,
      AllCaseEqs()] >>
  simp[layout_stage_row_def] >> metis_tac[]
QED

Theorem layout_stage_row_items:
  layout_stage_row ctx reserved fn out layout ==>
  ?items. static_alloca_items fn = SOME items
Proof
  simp[layout_stage_row_def] >> strip_tac
  >- (qpat_x_assum `compute_function_layout_fuel_in_context _ _ _ _ = _` mp_tac >>
      simp[compute_function_layout_fuel_in_context_def] >>
      Cases_on `static_alloca_items fn` >> simp[]) >>
  qpat_x_assum `compute_function_layout_eval _ _ = _` mp_tac >>
  simp[compute_function_layout_eval_def, complete_alloc_positions_def] >>
  Cases_on `static_alloca_items fn` >> simp[]
QED

Theorem layout_stage_row_position:
  layout_stage_row ctx reserved fn out layout /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  lookup_function fn.fn_name C'.ctx_functions = SOME out ==>
  FLOOKUP layout.cl_positions (Allocation inst.inst_id) =
    SOME (concretize_positions C' fn inst.inst_id)
Proof
  strip_tac >> drule layout_stage_row_items >> strip_tac >>
  drule_all static_alloca_items_ALLOCA_exact >> strip_tac >>
  rename1 `exact_static_alloca inst = SOME (Allocation inst.inst_id,w2n sz)` >>
  `MEM (Allocation inst.inst_id,w2n sz) items` by
    metis_tac[static_alloca_items_MEM] >>
  `?p. FLOOKUP layout.cl_positions (Allocation inst.inst_id) = SOME p` by
    (gvs[layout_stage_row_def] >>
     metis_tac[context_layout_local_position, eval_layout_local_position]) >>
  `FIND (\(b,q,t). b = Allocation inst.inst_id) out.fn_mems_used =
     SOME (Allocation inst.inst_id,p,w2n sz)` by
    (gvs[layout_stage_row_def] >>
     metis_tac[context_layout_local_lookup_find]) >>
  drule_all concretize_positions_lookup >> simp[]
QED

Theorem layout_stage_row_block_pair:
  layout_stage_row ctx reserved fn out layout /\
  MEM bb fn.fn_blocks /\ bb_well_formed bb ==>
  ?bb'. MEM bb' out.fn_blocks /\ bb'.bb_label = bb.bb_label /\
    layout_block_pair layout.cl_positions bb bb'
      (phi_prefix_length bb.bb_instructions)
      (phi_prefix_length bb'.bb_instructions)
Proof
  strip_tac >> drule_all layout_block_pair_produce >>
  disch_then (qspec_then `layout.cl_positions` strip_assume_tac) >>
  qexists `bb'` >>
  gvs[layout_stage_row_def, apply_context_concretize_layout_def,
      apply_concretize_layout_def]
QED

val _ = export_theory();
