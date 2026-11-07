Theory concretizePtrStagePairedBridge
Ancestors
  concretizePtrStagePlacements concretizePtrExecutedCoverage
  staticLayoutAllocatorProofs concretizeStageShape concretizePtrPairedFields
  concretizeStepStructure venomInst list finite_map
  o1PassContract venomWf venomPassDispatcher stackPlanGen unitShapeDefs
  concretizeMemLocDefs

Theorem ptr_layout_stage_lookup:
  ptr_stage_placements C' positions /\ MEM g C'.ctx_functions /\
  f.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel ctx reserved f = SOME g /\
  g = apply_context_concretize_layout ctx layout f /\
  (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP layout.cl_positions (Allocation i.inst_id))) ==>
  !bb i. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = ALLOCA ==>
    FLOOKUP layout.cl_positions (Allocation i.inst_id) =
      OPTION_MAP FST (FLOOKUP positions (Allocation i.inst_id))
Proof
  strip_tac >>
  drule_all ptr_concretize_static_items >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `MEM i (fn_insts f)` by
    (simp[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[]) >>
  drule_all static_alloca_items_ALLOCA_exact >> strip_tac >>
  rename1 `exact_static_alloca i = SOME (Allocation i.inst_id,w2n n)` >>
  `MEM (Allocation i.inst_id,w2n n) items` by
    (drule static_alloca_items_MEM >> metis_tac[]) >>
  `IS_SOME (FLOOKUP layout.cl_positions (Allocation i.inst_id))` by
    metis_tac[] >>
  Cases_on `FLOOKUP layout.cl_positions (Allocation i.inst_id)` >> gvs[] >>
  `MEM (Allocation i.inst_id,x,w2n n)
     (apply_context_concretize_layout ctx layout f).fn_mems_used` by
    (drule_all ptr_layout_own_mems >>
     disch_then (qspecl_then [`layout`,`ctx`] mp_tac) >> simp[]) >>
  `FLOOKUP positions (Allocation i.inst_id) = SOME (x,w2n n)` by
    (fs[ptr_stage_placements_def] >> metis_tac[]) >>
  simp[]
QED

Theorem ptr_list_coherent_choice[local]:
  !xs ys P Q.
    ALL_DISTINCT xs /\
    LIST_REL (\x y. ?w. P x y w /\ Q x w) xs ys ==>
    ?pick. LIST_REL (\x y. P x y (pick x)) xs ys /\
      EVERY (\x. Q x (pick x)) xs
Proof
  Induct >- simp[] >>
  Cases_on `ys` >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  rename1 `~MEM head xs` >>
  qexists_tac `\x. if x = head then w else pick x` >> simp[] >>
  conj_tac
  >- (fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
      `EL n xs <> head` by metis_tac[EL_MEM] >> simp[]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem ptr_stage_paired_bridge:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom ==>
  ?R lp positions.
    ptr_stage_placements C' positions /\
    LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
    EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
      first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
      ALL_DISTINCT (fn_labels f) /\
      (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
        IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
    EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
    (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name)
Proof
  strip_tac >>
  `?positions. ptr_stage_placements C' positions` by
    (drule_all ptr_stage_placements_exists >> simp[]) >>
  qabbrev_tac `R = \f g. ?n. n < LENGTH C.ctx_functions /\
    f = EL n C.ctx_functions /\ g = EL n C'.ctx_functions` >>
  `ALL_DISTINCT C.ctx_functions` by
    (fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def,
        ctx_fn_names_def] >> metis_tac[ALL_DISTINCT_MAP]) >>
  `LIST_REL (\f g. ?p.
     ptr_paired_code R (\f. p) positions f g /\
     (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
       IS_SOME (FLOOKUP p (Allocation i.inst_id))))
     C.ctx_functions C'.ctx_functions` by
    (fs[ctx_pass_stage_def, LIST_REL_EL_EQN] >> rpt strip_tac >>
     qpat_x_assum `!n. n < _ ==> ?observed s out. _`
       (qspec_then `n` mp_tac) >> impl_tac >- decide_tac >> strip_tac >>
     `MEM (EL n C.ctx_functions) C.ctx_functions` by metis_tac[EL_MEM] >>
     `MEM (EL n C'.ctx_functions) C'.ctx_functions` by metis_tac[EL_MEM] >>
     ` (EL n C.ctx_functions).fn_eom = NONE` by fs[EVERY_MEM] >>
     gvs[fn_pass_step_def, execute_configured_fn_pass_concretize, AllCaseEqs()] >>
     drule_all concretize_function_fresh_positions >> strip_tac >>
     `!bb i. MEM bb (EL n C.ctx_functions).fn_blocks /\
       MEM i bb.bb_instructions /\ i.inst_opcode = ALLOCA ==>
       FLOOKUP layout.cl_positions (Allocation i.inst_id) =
       OPTION_MAP FST (FLOOKUP positions (Allocation i.inst_id))` by
       (rpt gen_tac >> strip_tac >>
        irule ptr_layout_stage_lookup >>
        rpt (goal_assum (drule_at Any)) >> simp[]) >>
     qexists_tac `layout.cl_positions` >> simp[] >>
     simp[ptr_paired_code_def] >> conj_tac
     >- (simp[Abbr `R`] >> qexists_tac `n` >> simp[]) >>
     simp[apply_context_concretize_layout_def, apply_concretize_layout_def] >>
     conj_tac
     >- (mp_tac (Q.SPECL [`layout.cl_positions`,`EL n C.ctx_functions`]
           (GEN_ALL concretize_positions_entry_label)) >>
         simp[fn_entry_label_def, entry_block_def]) >> metis_tac[]) >>
  drule ptr_list_coherent_choice >>
  disch_then (mp_tac o Q.ISPECL [`C'.ctx_functions`,
    `\f g p. ptr_paired_code R (\f. p) (positions:allocation |-> num # num) f g`,
    `\f p. !i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP p (Allocation i.inst_id) : num option)`]) >>
  simp[] >> strip_tac >>
  qexistsl [`R`,`pick`,`positions`] >> simp[] >>
  conj_tac
  >- (fs[LIST_REL_EL_EQN, ptr_paired_code_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
       wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (fs[LIST_REL_EL_EQN, EVERY_EL, ptr_paired_code_def,
        o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >>
      rpt strip_tac >>
      `ALL_DISTINCT (fn_labels (EL n C.ctx_functions))` by metis_tac[EL_MEM] >>
      `fn_labels (EL n C'.ctx_functions) =
         fn_labels (concretize_function_with_positions
           (pick (EL n C.ctx_functions)) (EL n C.ctx_functions))` by
        (simp[fn_labels_def] >> metis_tac[]) >>
      metis_tac[concretize_positions_labels]) >>
  rpt gen_tac >> simp[ptr_paired_code_def, Abbr `R`] >> strip_tac >>
  fs[ctx_pass_stage_def, LIST_REL_EL_EQN, fn_pass_step_def] >>
  metis_tac[]
QED
