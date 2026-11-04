Theory concretizeAllocationFree
Ancestors
  o1PassContract venomPassDispatcher
  concretizeMemLocDefs concretizeMemLocTransitionProofs
  staticLayoutAllocatorProofs ptrDisciplineEmptyTaint ptrDiscipline
  passSharedDefs passSharedProps passSimulationDefs venomInst list pred_set finite_map

(* The map may be partial: a missing entry rewrites to NOP, not ALLOCA.
   Only malformed outputs could leave ALLOCA, and checked items exclude them. *)
Theorem concretize_inst_opcode_property:
  P ASSIGN /\ P NOP /\
  (inst.inst_opcode <> ALLOCA ==> P inst.inst_opcode) /\
  (inst.inst_opcode = ALLOCA ==> ?out. inst.inst_outputs = [out]) ==>
  P (concretize_inst_with_positions positions inst).inst_opcode
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA` >>
  gvs[concretize_inst_with_positions_def] >>
  CASE_TAC >> simp[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem static_alloca_items_single_output:
  static_alloca_items fn = SOME items /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA ==> ?out. inst.inst_outputs = [out]
Proof
  strip_tac >> drule_all static_alloca_items_ALLOCA_exact >>
  strip_tac >>
  gvs[exact_static_alloca_def, exact_static_alloca_size_def, AllCaseEqs()]
QED

Theorem fn_insts_map_instructions:
  fn_insts (function_map_transform (block_map_transform f) fn) =
  MAP f (fn_insts fn)
Proof
  simp[function_map_transform_def, fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`, `blocks`) >> Induct >>
  simp[fn_insts_blocks_def, block_map_transform_def, MAP_APPEND]
QED

Theorem concretize_function_opcode_property:
  static_alloca_items fn = SOME items /\ P ASSIGN /\ P NOP /\
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode <> ALLOCA ==>
          P inst.inst_opcode) ==>
  EVERY (\inst. P inst.inst_opcode)
    (fn_insts (concretize_function_with_positions positions fn))
Proof
  strip_tac >> simp[EVERY_MEM, concretize_function_with_positions_def] >>
  rpt strip_tac >> drule clear_nops_fn_insts_subset >>
  simp[fn_insts_map_instructions, MEM_MAP] >> strip_tac >> gvs[] >>
  irule concretize_inst_opcode_property >> simp[] >>
  metis_tac[static_alloca_items_single_output]
QED

Theorem concretize_function_in_context_opcode_property:
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' /\
  P ASSIGN /\ P NOP /\
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode <> ALLOCA ==>
          P inst.inst_opcode) ==>
  EVERY (\inst. P inst.inst_opcode) (fn_insts fn')
Proof
  simp[concretize_function_fuel_in_context_def] >>
  Cases_on `fn_has_static_layout fn`
  >- (rpt strip_tac >>
      gvs[fn_has_alloca_def, EXISTS_MEM, is_alloca_op_def, EVERY_MEM] >>
      metis_tac[is_alloca_op_def]) >>
  Cases_on `if imported_mems_used ctx fn = [] ==> fn_needs_liveness_allocation fn then
              compute_function_layout_fuel_in_context fuel ctx reserved fn
            else compute_function_layout_eval reserved fn`
  >- simp[] >>
  rpt strip_tac >> gvs[] >>
  `?items. static_alloca_items fn = SOME items` by
    (Cases_on `fn_needs_liveness_allocation fn \/ imported_mems_used ctx fn <> []` >>
     gvs[compute_function_layout_fuel_in_context_def,
         compute_function_layout_eval_def, complete_alloc_positions_def,
         AllCaseEqs()]) >>
  `EVERY (\inst. P inst.inst_opcode)
    (fn_insts (concretize_function_with_positions x.cl_positions fn))` by
    (irule concretize_function_opcode_property >> metis_tac[]) >>
  gvs[apply_context_concretize_layout_def, apply_concretize_layout_def,
      fn_insts_def]
QED

Theorem concretize_fn_pass_opcode_property:
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  P ASSIGN /\ P NOP /\
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode <> ALLOCA ==>
          P inst.inst_opcode) ==>
  EVERY (\inst. P inst.inst_opcode) (fn_insts out.fpo_function)
Proof
  simp[fn_pass_step_def, execute_configured_fn_pass_concretize] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  irule concretize_function_in_context_opcode_property >> metis_tac[]
QED

Theorem concretize_stage_allocation_free:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  ptr_discipline lo C vs /\ ~ctx_has_dalloca C ==>
  EVERY (\fn. EVERY (\inst. allocation_free_opcode inst.inst_opcode)
                      (fn_insts fn)) C'.ctx_functions
Proof
  simp[ctx_pass_stage_def, ptr_discipline_def, ctx_has_dalloca_def] >>
  rpt strip_tac >>
  fs[LIST_REL_EL_EQN, EVERY_EL, EXISTS_MEM] >>
  qx_gen_tac `n` >> strip_tac >>
  `n < LENGTH C.ctx_functions` by simp[] >>
  qpat_x_assum `!n. _ ==> ?observed s out. _`
    (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  `EVERY (\inst. allocation_free_opcode inst.inst_opcode)
     (fn_insts out.fpo_function)` suffices_by simp[EVERY_EL] >>
  irule concretize_fn_pass_opcode_property >>
  simp[allocation_free_opcode_def] >>
  qexistsl_tac [`EL n C.ctx_functions`, `observed`, `rpolicy`, `s`] >>
  simp[allocation_free_opcode_def] >>
  fs[fn_ptr_ok_def, EVERY_EL] >> metis_tac[MEM_EL]
QED

Theorem concretize_stage_output_taint:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  ptr_discipline lo C vs /\ ~ctx_has_dalloca C /\ o1_run_state_ok vs ==>
  taint_within D C' vs
Proof
  strip_tac >> irule allocation_free_taint_within >> conj_tac
  >- gvs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  irule concretize_stage_allocation_free >> metis_tac[]
QED
