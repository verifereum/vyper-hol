Theory loweringRuntimeBudgetShape
Ancestors
  loweringCallBudgetHistory entryRuntimeContextCode allocaFrontierBound
  list rich_list

Theorem budget_context_active_no_dalloca[local]:
  (!f. MEM f ctx.ctx_functions ==>
    ~EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts f)) /\
  MEM fn ctx.ctx_functions /\ active_inst fn i s ==>
  i.inst_opcode <> DALLOCA
Proof
  strip_tac >> drule active_inst_mem_fn_insts >> strip_tac >>
  first_x_assum drule >> simp[EVERY_MEM]
QED

Theorem budget_path_context_shape[local]:
  !checked cfg root h marks q.
    lower_budget_path checked cfg root h marks q ==>
    !D lo explicit ctx.
      cfg = (D,lo,explicit,ctx) /\
      (!f. MEM f ctx.ctx_functions ==>
        ~EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts f)) /\
      MEM root.bp_fn ctx.ctx_functions /\
      EVERY (\f. MEM f.cf_fn ctx.ctx_functions) root.bp_stack ==>
      MEM q.bp_fn ctx.ctx_functions /\
      EVERY (\f. MEM f.cf_fn ctx.ctx_functions) q.bp_stack /\
      FILTER lower_event_allocates h = []
Proof
  ho_match_mp_tac lower_budget_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[FILTER_APPEND, lower_event_allocates_def, EVERY_MEM] >>
  qpat_x_assum `_ ==> _ /\ _ /\ _` drule_all >> strip_tac >>
  imp_res_tac active_inst_mem_fn_insts >>
  gvs[] >> rpt conj_tac >> rpt strip_tac >> gvs[] >>
  metis_tac[venomInstTheory.lookup_function_MEM, COND_CLAUSES]
QED

Theorem supported_runtime_budget_allocation_shape:
  !tops rpolicy unit vs D lo explicit name fn lbl entered p h marks q.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    unit.cu_context.ctx_entry = SOME name /\
    lookup_function name unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    enters_block fn
      (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                  vs_inst_idx := 0 |>) entered /\
    p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
           bp_taint := entry_taint; bp_fn := fn; bp_state := entered |> /\
    lower_budget_path F (D,lo,explicit,unit.cu_context) p h marks q ==>
    LENGTH (FILTER lower_event_allocates h) = 0 /\
    (!i. active_inst q.bp_fn i q.bp_state ==> i.inst_opcode <> DALLOCA) /\
    (?pair. lower_history_pairs h pair /\ lower_history_current h pair q /\
      (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
        ?f i s op sz t. lower_alloc_record h n f i s op sz t))
Proof
  rpt gen_tac >> strip_tac >>
  `!f. MEM f unit.cu_context.ctx_functions ==>
    ~EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts f)` by
    metis_tac[entry_runtime_context_no_dalloca] >>
  drule budget_path_context_shape >>
  disch_then (qspecl_then [`D`, `lo`, `explicit`, `unit.cu_context`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[venomInstTheory.lookup_function_MEM])) >>
  strip_tac >>
  `!i. active_inst q.bp_fn i q.bp_state ==> i.inst_opcode <> DALLOCA` by
    metis_tac[budget_context_active_no_dalloca] >>
  `!n. n < LENGTH h ==> ~lower_event_allocates (EL n h)` by
    (gvs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  simp[] >> qexists_tac `K 0` >>
  simp[lower_history_pairs_def, lower_history_current_def] >> metis_tac[]
QED
