Theory loweringRuntimeBudgetShape
Ancestors
  loweringCallBudgetHistory entryRuntimeContextCode allocaFrontierBound
  list rich_list vyperCompiler

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

Theorem supported_runtime_context_fmp_guards:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops ==>
  !fn i. MEM fn unit.cu_context.ctx_functions /\ MEM i (fn_insts fn) ==>
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DRET
Proof
  strip_tac >>
  drule vyperLoweringCorrectTheory.lower_vyper_runtime_unit_context_entry >> strip_tac >>
  `!f. MEM f unit.cu_context.ctx_functions ==>
    ~EXISTS (\j. j.inst_opcode = DALLOCA) (fn_insts f)` by
    metis_tac[entry_runtime_context_no_dalloca] >>
  `EVERY (\fn. fn_ptr_ok_check (ctx_ptr_param_list unit.cu_context) fn /\
      wf_function fn /\
      EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn) /\
      fn_ptr_ok_check (ctx_ptr_param_list unit.cu_context)
        (fn_reachable_blocks fn)) unit.cu_context.ctx_functions` by
    (gvs[lowering_context_ok_def, ptr_ok_check_def, EXISTS_MEM, EVERY_MEM] >>
     metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[EVERY_MEM] >>
  first_x_assum drule >> strip_tac >>
  rename1 `MEM i (fn_insts f)` >>
  qpat_x_assum `fn_ptr_ok_check _ f` mp_tac >>
  simp[fn_ptr_ok_check_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!inst. MEM inst (fn_insts f) ==> _` drule >>
  simp[inst_ptr_ok_check_def]
QED

Theorem budget_path_context_fmp_guards[local]:
  !checked cfg root h marks q.
    lower_budget_path checked cfg root h marks q ==>
    !D lo explicit ctx.
      cfg = (D,lo,explicit,ctx) /\
      MEM root.bp_fn ctx.ctx_functions /\
      EVERY (\f. MEM f.cf_fn ctx.ctx_functions) root.bp_stack /\
      (!fn i. MEM fn ctx.ctx_functions /\ MEM i (fn_insts fn) ==>
        i.inst_opcode <> SETFMP /\ i.inst_opcode <> DRET) ==>
      MEM q.bp_fn ctx.ctx_functions /\
      EVERY (\f. MEM f.cf_fn ctx.ctx_functions) q.bp_stack /\
      (!n p i fuel t r. MEM (BudgetStep n p i fuel (OK t) r) h ==>
        i.inst_opcode <> SETFMP) /\
      (!n p i fuel ret se t r. MEM (BudgetReturn n p i fuel ret se t r) h ==>
        i.inst_opcode <> DRET)
Proof
  ho_match_mp_tac lower_budget_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- simp[EVERY_MEM] >>
  qpat_x_assum `(_,_,_,_) = (_,_,_,_)`
    (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  BasicProvers.var_eq_tac >>
  qpat_x_assum `!D lo explicit ctx. _`
    (drule_all o SIMP_RULE (srw_ss()) [pairTheory.PAIR_EQ]) >> strip_tac >>
  imp_res_tac active_inst_mem_fn_insts >>
  fs[EVERY_MEM, MEM_APPEND]
  >- (rpt strip_tac >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >> gvs[] >> metis_tac[])
  >- (drule venomInstTheory.lookup_function_MEM >> strip_tac >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem lower_budget_path_fmp_guards:
  !checked D lo explicit ctx root h marks q.
    lower_budget_path checked (D,lo,explicit,ctx) root h marks q /\
    MEM root.bp_fn ctx.ctx_functions /\
    EVERY (\f. MEM f.cf_fn ctx.ctx_functions) root.bp_stack /\
    (!fn i. MEM fn ctx.ctx_functions /\ MEM i (fn_insts fn) ==>
       i.inst_opcode <> SETFMP /\ i.inst_opcode <> DRET) ==>
    (!n p i fuel t r.
       n < LENGTH h /\ EL n h = BudgetStep n p i fuel (OK t) r ==>
       i.inst_opcode <> SETFMP) /\
    (!n p i fuel ret se t r.
       n < LENGTH h /\ EL n h = BudgetReturn n p i fuel ret se t r ==>
       i.inst_opcode <> DRET)
Proof
  rpt gen_tac >> strip_tac >> drule budget_path_context_fmp_guards >>
  disch_then (qspecl_then [`D`, `lo`, `explicit`, `ctx`] mp_tac) >>
  simp[] >> strip_tac >> metis_tac[EL_MEM]
QED
