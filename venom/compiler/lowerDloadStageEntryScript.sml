Theory lowerDloadStageEntry
Ancestors
  lowerDloadTopEntryControl o1ContractLowerDload o1PassContract
  lowerDloadDefs venomPassSchedule venomFnScheduleRunner
  venomCompilerTypes irSupply venomPassDispatcher venomInst
  unitMemInv venomState list

Theorem lower_dload_stage_lookup_source:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  lookup_function name C'.ctx_functions = SOME g ==>
  ?f a b. lookup_function name C.ctx_functions = SOME f /\
    ir_supply_covers_fn a f /\ lower_dload_function_supply a f = (g,b)
Proof
  strip_tac >>
  `LIST_REL (\f g. ?s t. ir_supply_covers_fn s f /\
       lower_dload_function_supply s f = (g,t))
       C.ctx_functions C'.ctx_functions` by
    (qpat_x_assum `ctx_pass_stage _ _ _ _ _` mp_tac >>
     rw[ctx_pass_stage_def] >>
     irule LIST_REL_mono >> goal_assum (drule_at Any) >>
     rpt strip_tac >> gvs[fn_pass_step_def, AllCaseEqs()] >>
     rename1 `lower_dload_function_supply seed src = (dst,last)` >>
     `MEM src observed.cu_context.ctx_functions` by
       (gvs[lookup_unique_function_def, AllCaseEqs()] >>
        `MEM src (FILTER (\g. g.fn_name = src.fn_name)
           observed.cu_context.ctx_functions)` by simp[] >>
        gvs[MEM_FILTER]) >>
     qexistsl_tac [`seed`, `last`] >> simp[] >>
     gvs[ir_supply_covers_unit_def, ir_supply_covers_fn_def, list_subset_def,
         unit_ir_inst_ids_def, unit_ir_vars_def, unit_ir_labels_def,
         EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  qpat_x_assum `ctx_pass_stage _ _ _ _ _` kall_tac >>
  qpat_x_assum `lookup_function _ _ = _` mp_tac >>
  qid_spec_tac `g` >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  Q.SPEC_TAC (`C'.ctx_functions`, `gs`) >>
  Q.SPEC_TAC (`C.ctx_functions`, `fs`) >>
  Induct >> Cases_on `gs` >>
  simp[lookup_function_def, FIND_thm] >> rpt strip_tac >>
  rename1 `lower_dload_function_supply supply src = (dst,supply')` >>
  drule lower_dload_function_supply_labels >> strip_tac >>
  Cases_on `src.fn_name = name` >> gvs[] >>
  fs[GSYM lookup_function_def] >> metis_tac[]
QED

Theorem lower_dload_stage_top_entry_annotated:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs0 /\
  C'.ctx_entry = SOME name /\
  lookup_function name C'.ctx_functions = SOME gn /\
  fn_entry_label gn = SOME lbl /\
  z = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                 vs_inst_idx := 0|> /\
  enters_block gn z t /\ lookup_block lbl gn.fn_blocks = SOME gb /\
  t.vs_inst_idx < LENGTH gb.bb_instructions ==>
  ?fn a b bb i post code tail amid aend.
    C.ctx_entry = SOME name /\
    lookup_function name C.ctx_functions = SOME fn /\
    ir_supply_covers_fn a fn /\ lower_dload_function_supply a fn = (gn,b) /\
    fn_entry_label fn = SOME lbl /\ t = z /\ enters_block fn z t /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb.bb_instructions = i::post /\
    lower_dload_block_supply a bb = (gb,aend) /\
    lower_dload_inst_supply a i = (code,amid) /\
    lower_dload_insts_supply amid post = (tail,aend) /\
    gb.bb_instructions = code ++ tail /\ code <> [] /\
    active_inst fn i t /\ EL t.vs_inst_idx gb.bb_instructions = HD code /\
    ld_annotated_reachable vs0 C [] 0 FEMPTY [] FEMPTY entry_taint fn i t
Proof
  strip_tac >> drule_all lower_dload_stage_lookup_source >> strip_tac >>
  `C.ctx_entry = SOME name` by gvs[ctx_pass_stage_def] >>
  `fn_entry_label f = SOME lbl` by
    metis_tac[lower_dload_function_supply_labels] >>
  `first_block_no_phi f` by
    (gvs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  drule_all lower_dload_top_entry_control >> strip_tac >>
  `t.vs_allocas = FEMPTY` by
    gvs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  `ld_annotated_reachable vs0 C [] 0 FEMPTY [] FEMPTY entry_taint f i t` by
    (qpat_x_assum `z = _` SUBST_ALL_TAC >>
     drule_all lowerDloadCoverageInvariantTheory.ld_frame_data_source_entry >> simp[]) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
