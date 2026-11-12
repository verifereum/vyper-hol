(*
 * ConcretizeMemLoc's stage contract, the memory part of row 3: every
 * access of the output is below its layout end, and the output keeps the
 * syntactic pointer discipline FmpLowering needs; with DALLOCA, every
 * reachable access is in a site of its provenance and the taint stays
 * within the input's.
 *
 * TOP-LEVEL:
 *   concretize_stage_static_mem
 *   concretize_stage_static_ptr_ok
 *   concretize_stage_frame_ptr_ok
 *   concretize_stage_taint_within
 *)
Theory concretizeStageStatic
Ancestors
  o1PassContract ptrDiscipline unitMemInv stackPlanGen concretizeMemLocDefs
  venomPassDispatcher cfgWf
  concretizePtrStagePairedBridge concretizePtrHistoryCoverage
  concretizePtrUniversalExtension concretizePtrCoverageStaticMem
  concretizePtrFrameRetpcShape
  concretizeAllocationFree ptrStaticDiscipline pointerConfinedDefs
  pointerConfinedProps pointerClosure lowerDloadPtrClosure passSharedDefs
  passSharedProps passTransform venomInst list pred_set

(* Why it holds (intuition, not a prescribed proof).

   The pass replaces every ALLOCA with an ASSIGN of a literal position
   from the static layout, whose end is fn_eom <= max_live_eom C'; so C'
   has no ALLOCA, its static accesses are at those positions plus the
   in-site offsets ptr_discipline lo C allows, and its PARAM and
   pointer-compare uses are the input's.  Without DALLOCA, every access
   of C' is below the layout end. *)
Theorem concretize_stage_static_mem:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom ==>
  mem_inv (static_mem_ok eom) C' vs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ptr_stage_paired_bridge) >>
  strip_tac >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ptr_stage_frame_retpc_shape) >>
  strip_tac >>
  `EVERY (\f. fn_inst_wf f /\ unitShapeDefs$retpc_shape_ok f /\ opaque_use_ok f /\
     first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
     ALL_DISTINCT (fn_labels f) /\
     (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
       IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `C.ctx_entry = C'.ctx_entry` by fs[ctx_pass_stage_def] >>
  `vs.vs_vars = FEMPTY` by
    gvs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  `!ht at. ptr_chrono_history vs C' ht at ==>
     (?h a done tokens registry births PT TG saved entries H calls ws.
       ptr_paired_prefix R lp positions lo vs C C' h a ht at done tokens registry births PT TG saved entries H calls ws /\
       a.po_inst.inst_opcode <> NOP /\
       at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst) \/
     (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
       revert_forward_pair bb i j /\
       i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j)` by (
    match_mp_tac ptr_paired_history_coverage >>
    rpt conj_tac
    >~ [`ptr_chrono_step`]
    >- (rpt strip_tac >> drule_all ptr_paired_universal_extension >>
        disch_then ACCEPT_TAC) >>
    fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ptr_paired_coverage_static_mem) >>
  disch_then ACCEPT_TAC
QED

(* ===== Row 3's syntactic pointer discipline ===== *)

(* An output instruction is an input one, or what an ALLOCA became: a NOP
   or an ASSIGN of a literal position.  Neither reads a variable. *)
Theorem concretize_inst_with_positions_cases[local]:
  concretize_inst_with_positions positions i = i \/
  ((concretize_inst_with_positions positions i).inst_opcode = NOP /\
   (concretize_inst_with_positions positions i).inst_operands = []) \/
  ((concretize_inst_with_positions positions i).inst_opcode = ASSIGN /\
   ?w. (concretize_inst_with_positions positions i).inst_operands = [Lit w])
Proof
  rw[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
  simp[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem concretize_fn_pass_inst_cases[local]:
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  MEM inst (fn_insts out.fpo_function) ==>
  MEM inst (fn_insts fn) \/
  (inst.inst_opcode = NOP /\ inst.inst_operands = []) \/
  (inst.inst_opcode = ASSIGN /\ ?w. inst.inst_operands = [Lit w])
Proof
  simp[fn_pass_step_def, execute_configured_fn_pass_concretize] >>
  rpt strip_tac >> gvs[AllCaseEqs(), concretize_function_fuel_in_context_def] >>
  gvs[apply_context_concretize_layout_def, apply_concretize_layout_def] >>
  `MEM inst (fn_insts (concretize_function_with_positions
                         layout.cl_positions fn))` by fs[fn_insts_def] >>
  pop_assum mp_tac >> simp[concretize_function_with_positions_def] >>
  strip_tac >> drule clear_nops_fn_insts_subset >>
  simp[fn_insts_map_instructions, MEM_MAP] >> strip_tac >> gvs[] >>
  metis_tac[concretize_inst_with_positions_cases]
QED

Theorem concretize_fn_pass_fn_name[local]:
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out ==>
  out.fpo_function.fn_name = fn.fn_name
Proof
  simp[fn_pass_step_def, execute_configured_fn_pass_concretize] >>
  rpt strip_tac >> gvs[AllCaseEqs(), concretize_function_fuel_in_context_def] >>
  simp[apply_context_concretize_layout_def, apply_concretize_layout_def,
       concretize_function_with_positions_def, clear_nops_function_def,
       function_map_transform_def]
QED

(* The output's pointer roots are the input's: ALLOCA roots only shrink,
   and DALLOCA and PARAM instructions are kept. *)
Theorem concretize_fn_pass_fn_pv[local]:
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out ==>
  fn_pv P out.fpo_function SUBSET fn_pv P fn
Proof
  strip_tac >>
  `!inst. MEM inst (fn_insts out.fpo_function) ==>
     MEM inst (fn_insts fn) \/
     (inst.inst_opcode = NOP /\ inst.inst_operands = []) \/
     (inst.inst_opcode = ASSIGN /\ ?w. inst.inst_operands = [Lit w])` by
    metis_tac[concretize_fn_pass_inst_cases] >>
  `out.fpo_function.fn_name = fn.fn_name` by
    metis_tac[concretize_fn_pass_fn_name] >>
  `!g. FINITE (ptr_roots P g)` by
    (gen_tac >> irule SUBSET_FINITE >>
     qexists_tac `set (FLAT (MAP (\i. i.inst_outputs) (fn_insts g)))` >>
     simp[SUBSET_DEF, ptr_roots_def, alloca_roots_def, MEM_FLAT, MEM_MAP] >>
     rpt strip_tac >> gvs[inst_output_def, AllCaseEqs()] >> metis_tac[MEM]) >>
  `ptr_roots P out.fpo_function SUBSET ptr_roots P fn` by
    (simp[SUBSET_DEF, ptr_roots_def, alloca_roots_def] >>
     rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
     metis_tac[]) >>
  simp[fn_pv_def, SUBSET_DEF] >>
  ho_match_mp_tac pointer_derived_vars_induction >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule roots_in_pointer_derived_vars >>
      fs[SUBSET_DEF]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[is_pointer_preserving_op_def] >>
  irule pointer_derived_vars_closed >> metis_tac[]
QED

Theorem concretize_fn_pass_static_ptr_ok:
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  fn_static_ptr_ok P fn ==>
  fn_static_ptr_ok P out.fpo_function
Proof
  strip_tac >>
  `!inst. MEM inst (fn_insts out.fpo_function) ==>
     MEM inst (fn_insts fn) \/
     (inst.inst_opcode = NOP /\ inst.inst_operands = []) \/
     (inst.inst_opcode = ASSIGN /\ ?w. inst.inst_operands = [Lit w])` by
    metis_tac[concretize_fn_pass_inst_cases] >>
  `out.fpo_function.fn_name = fn.fn_name` by
    metis_tac[concretize_fn_pass_fn_name] >>
  `fn_pv P out.fpo_function SUBSET fn_pv P fn` by
    metis_tac[concretize_fn_pass_fn_pv] >>
  fs[fn_static_ptr_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[ptr_use_static_ok_def, SUBSET_DEF] >> metis_tac[]) >>
  fs[affine_pointer_ops_def, GSYM fn_pv_def, SUBSET_DEF] >>
  rpt gen_tac >> strip_tac >>
  `MEM inst (fn_insts out.fpo_function)` by
    (simp[fn_insts_def, venomWfPropsTheory.fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  `?bb'. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions` by
    (gvs[fn_insts_def, venomWfPropsTheory.fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  metis_tac[]
QED

(* Row 3's syntactic pointer fact: ConcretizeMemLoc keeps fn_static_ptr_ok
   with the same P, since it only shrinks fn_pv. *)
Theorem concretize_stage_static_ptr_ok:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  EVERY (fn_static_ptr_ok P) C.ctx_functions ==>
  EVERY (fn_static_ptr_ok P) C'.ctx_functions
Proof
  simp[ctx_pass_stage_def] >> rpt strip_tac >>
  fs[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
  `n < LENGTH C.ctx_functions` by simp[] >>
  qpat_x_assum `!n. _ ==> ?observed s out. _`
    (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  metis_tac[concretize_fn_pass_static_ptr_ok]
QED

(* ===== Row 3's run-time facts with DALLOCA ===== *)

(* TEMPORARILY CHEATED - statement fixed for the DALLOCA forms track; the
   proof waits for the concretize pointer tower to cover DALLOCA.
   Why it holds (intuition): DALLOCA outputs keep their site (b, fmp' - b)
   in both runs, since the pass leaves DALLOCA and the free-memory pointer
   alone; ALLOCA-derived variables of C' are ASSIGNs of literals, with no
   provenance, and static_mem puts their accesses at or below eom.  So an
   access ending above eom, or through a variable with provenance, is a
   DALLOCA or PARAM-chain access whose site C's access_ok gives; C''s
   taint is inside the relocation of C's. *)
Theorem concretize_stage_frame_ptr_ok:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  (!eom. max_live_eom C' = SOME eom ==> eom <= w2n vs.vs_initial_fmp) /\
  max_live_eom C' = SOME eom ==>
  !stk PG G tn fn inst s.
    frame_reachable vs C' stk PG G tn fn inst s ==>
    access_ok eom G fn inst s /\ taint_ok fn tn inst s
Proof
  cheat
QED

(* TEMPORARILY CHEATED - statement fixed for the DALLOCA forms track; the
   proof waits for the concretize pointer tower to cover DALLOCA.
   Why it holds (intuition): at each call request and halt of C', the
   paired run of C has at least the taint of C', relocated; a reused
   layout position's stale taint corresponds to the fresh ALLOCA site's
   new_site_bytes taint in C, and the storages agree outside D. *)
Theorem concretize_stage_taint_within:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  (!eom. max_live_eom C' = SOME eom ==> eom <= w2n vs.vs_initial_fmp) ==>
  taint_within D C' vs
Proof
  cheat
QED
