Theory loweringBudgetCursorCuts
Ancestors fragExec loweringCallBudgetHistory list rich_list venomInst contextCodegenRel

Theorem embedded_current_active_inst:
  !a b fn s i.
    fn_has_code a b fn /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
    s.vs_current_bb = b.cs_current_bb /\
    s.vs_inst_idx < LENGTH b.cs_current_insts ==>
    (active_inst fn i s <=> i = EL s.vs_inst_idx b.cs_current_insts)
Proof
  rpt strip_tac >>
  gvs[fn_has_code_def] >>
  `!bbs bb. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\ MEM bb bbs ==>
      lookup_block bb.bb_label bbs = SOME bb` by
    (Induct >> rw[lookup_block_def, FIND_thm] >>
     fs[lookup_block_def, MEM_MAP] >> metis_tac[]) >>
  gvs[active_inst_def, rich_listTheory.IS_PREFIX_APPEND] >>
  eq_tac >> rpt strip_tac
  >- (rename1 `MEM cb fn.fn_blocks` >>
      `lookup_block cb.bb_label fn.fn_blocks = SOME cb` by metis_tac[] >>
      `cb = bb` by metis_tac[optionTheory.SOME_11] >>
      gvs[] >> simp[rich_listTheory.EL_APPEND]) >>
  qexists_tac `bb` >>
  gvs[lookup_block_def] >>
  imp_res_tac venomInstTheory.FIND_MEM >>
  imp_res_tac venomInstTheory.FIND_P >>
  fs[rich_listTheory.EL_APPEND]
QED

Theorem embedded_current_next:
  !D lo explicit ctx root h marks p a b i fuel t q j.
    lower_budget_path F (D,lo,explicit,ctx) root h marks p /\
    fn_has_code a b p.bp_fn /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) p.bp_fn.fn_blocks) /\
    p.bp_state.vs_current_bb = b.cs_current_bb /\
    p.bp_state.vs_inst_idx < LENGTH b.cs_current_insts /\
    i = EL p.bp_state.vs_inst_idx b.cs_current_insts /\
    ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    step_inst fuel ctx i p.bp_state = OK t /\
    q = p with <|
      bp_state := (t with vs_inst_idx := SUC p.bp_state.vs_inst_idx);
      bp_prov := step_prov p.bp_params p.bp_prov i t;
      bp_taint := step_taint i p.bp_state t p.bp_taint |> /\
    active_inst q.bp_fn j q.bp_state ==>
    lower_budget_path F (D,lo,explicit,ctx) root
      (h ++ [BudgetStep (LENGTH h) p i fuel (OK t) q])
      (marks ++ MAP (\key. key IN explicit)
        (gas_events_step fuel ctx p.bp_fn.fn_name i p.bp_state)) q
Proof
  rpt strip_tac >>
  `active_inst p.bp_fn i p.bp_state` by
    metis_tac[embedded_current_active_inst] >>
  irule lower_budget_path_next >> gvs[] >> metis_tac[]
QED
