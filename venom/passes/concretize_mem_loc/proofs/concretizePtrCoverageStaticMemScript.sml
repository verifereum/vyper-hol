(* Static memory bounds from the actual paired-prefix coverage. *)
Theory concretizePtrCoverageStaticMem
Ancestors
  concretizePtrStagePairedBridge concretizePtrHistoryCoverage
  concretizePtrStorageReadProducer unitMemInv o1PassLift
  concretizePtrCoverageStaticMemReachability concretizePtrCurrentObservation
  o1PassContract concretizePtrPairedFields concretizePtrChronologicalHistory list pair
  contextCodegenRel concretizePtrOperationalOpcodes stepWriteFootprintBase
  venomExecProofs venomWf venomExecSemantics venomInst codegenRel o1SafeUpto

Theorem ptr_paired_coverage_static_mem_upto:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  fixed_region_reserved lo C /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  C.ctx_entry = SOME nm /\ lookup_function nm C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  (?R lp positions.
    ptr_stage_placements C' positions /\
    LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
    EVERY (\f. fn_inst_wf f /\ unitShapeDefs$retpc_shape_ok f /\ opaque_use_ok f /\
      first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
      ALL_DISTINCT (fn_labels f) /\
      (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
        IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
    EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
    (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
    (!ht at. ptr_chrono_history vs C' ht at /\ gas_cut ncut vs at.po_state ==>
      (?h a done tokens registry births PT TG saved entries H calls ws.
        ptr_paired_prefix R lp positions lo vs C C'
          h a ht at done tokens registry births PT TG saved entries H calls ws /\
        a.po_inst.inst_opcode <> NOP /\
        at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst) \/
      (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
        revert_forward_pair bb i j /\
        i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j)) /\
    (!h a ht at done tokens registry births PT TG saved entries H calls ws.
      ptr_paired_prefix R lp positions lo vs C C'
        h a ht at done tokens registry births PT TG saved entries H calls ws /\
      a.po_inst.inst_opcode <> NOP /\
      at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
      gas_cut ncut vs at.po_state ==>
      in_revert_forward at.po_fn at.po_state \/
      (!off len.
        MEM (off,len) (source_memory_read_ranges at.po_inst at.po_state ++
                      source_memory_write_ranges at.po_inst at.po_state) ==>
        len = 0 \/ off + len <= eom))) ==>
  mem_inv (\ctx fn inst s. gas_cut ncut vs s ==> static_mem_ok eom ctx fn inst s) C' vs
Proof
  strip_tac >>
  `C'.ctx_entry = C.ctx_entry` by fs[ctx_pass_stage_def] >>
  rewrite_tac[mem_inv_raw_reachable] >> conj_tac
  >- (drule_all list_rel_lookup_function >>
      disch_then (qspec_then `nm` mp_tac) >> simp[] >>
      Cases_on `lookup_function nm C'.ctx_functions` >> simp[] >>
      strip_tac >> fs[ptr_paired_code_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >> strip_tac >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  drule ptr_reachable_has_chrono_history >> strip_tac >>
  qpat_x_assum `!ht at. _` drule >> simp[ptr_observe_def] >> strip_tac
  >- (qpat_x_assum `!h a ht at done tokens registry births PT TG saved entries H calls ws. _`
        drule >> simp[] >>
      strip_tac >>
      gvs[static_mem_ok_def, inst_mem_ranges_def, EVERY_MEM, FORALL_PROD,
          ptr_observe_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  gvs[ptr_observe_def] >>
  Cases_on `s.vs_inst_idx = j`
  >- (simp[static_mem_ok_def, in_revert_forward_def, revert_forward_at_def] >>
      metis_tac[]) >>
  `MEM fn' C'.ctx_functions` by metis_tac[ptr_frame_context_membership] >>
  `ALL_DISTINCT (fn_labels fn')` by gvs[EVERY_MEM] >>
  drule raw_reachable_active >>
  rewrite_tac[active_inst_def] >> strip_tac >>
  `lookup_block s.vs_current_bb fn'.fn_blocks = SOME bb'` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `bb' = bb` by metis_tac[optionTheory.SOME_11] >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by fs[get_instruction_def] >>
  `inst.inst_opcode = ASSIGN` by
    (qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
     simp[revert_forward_pair_def] >> strip_tac >>
     first_x_assum irule >> qexists `s.vs_inst_idx` >> simp[]) >>
  simp[static_mem_ok_def, inst_mem_ranges_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

Theorem ptr_paired_coverage_static_mem:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  (?R lp positions.
    ptr_stage_placements C' positions /\
    LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
    EVERY (\f. fn_inst_wf f /\ unitShapeDefs$retpc_shape_ok f /\ opaque_use_ok f /\
      first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
      ALL_DISTINCT (fn_labels f) /\
      (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
        IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
    EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
    (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
    !ht at. ptr_chrono_history vs C' ht at ==>
      (?h a done tokens registry births PT TG saved entries H calls ws.
        ptr_paired_prefix R lp positions lo vs C C'
          h a ht at done tokens registry births PT TG saved entries H calls ws /\
        a.po_inst.inst_opcode <> NOP /\
        at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst) \/
      (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
        revert_forward_pair bb i j /\
        i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j)) ==>
  mem_inv (static_mem_ok eom) C' vs
Proof
  strip_tac >>
  `?nm fn lbl. C.ctx_entry = SOME nm /\
    lookup_function nm C.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl` by
    metis_tac[mem_inv_raw_reachable] >>
  `mem_inv (\ctx fn inst s. gas_cut (SUC (LENGTH vs.vs_gas_readings)) vs s ==>
      static_mem_ok eom ctx fn inst s) C' vs` suffices_by simp[SF ETA_ss] >>
  irule ptr_paired_coverage_static_mem_upto >> simp[] >>
  qexistsl [`C`, `fn`, `lbl`, `lo`, `nm`, `rpolicy`] >> simp[] >>
  (reverse conj_tac >- metis_tac[]) >>
  qexistsl [`R`, `lp`, `positions`] >> simp[] >>
  rpt strip_tac >>
  drule_at (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ptr_paired_current_static_bound >> simp[] >>
  disch_then (qspec_then `rpolicy` mp_tac) >>
  (impl_tac >- metis_tac[]) >> simp[]
QED
