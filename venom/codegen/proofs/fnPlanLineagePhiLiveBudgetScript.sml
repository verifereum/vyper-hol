Theory fnPlanLineagePhiLiveBudget
Ancestors
  fnPlanLineagePhiResources fnPlanLineagePhiTemporal deepResidualBudget doSwapSim
  fnPlanLineageInventory
  stackPlanGen stackPlanOps stackModel stackPlanTypes list rich_list

Theorem phi_write_live_count[local]:
  !inst live d ps ops qs v.
    d < LENGTH ps.ps_stack /\ MEM v live /\
    phi_write_phase inst live d ps = (ops,qs) ==>
    qs.ps_spilled = ps.ps_spilled /\
    LIST_ELEM_COUNT (Var v) qs.ps_stack =
      LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if v = HD inst.inst_outputs then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM (operand_to_string (stack_peek d ps.ps_stack)) live`
  >- (Cases_on `do_dup d ps` >> rename1 `do_dup d ps = (dups,dup)` >>
      drule do_dup_spilled_eq >> strip_tac >>
      drule do_dup_stack_exact >> simp[] >> strip_tac >>
      gvs[phi_write_phase_def] >>
      simp[stack_poke_def, LUPDATE_APPEND2, LUPDATE_def,
           reorderSimTheory.elem_count_append, LIST_ELEM_COUNT_DEF] >>
      Cases_on `v = HD inst.inst_outputs` >> simp[FILTER_APPEND]) >>
  `Var v <> stack_peek d ps.ps_stack` by
    (strip_tac >>
     qpat_x_assum `Var v = _` (assume_tac o SYM) >>
     fs[operand_to_string_def]) >>
  gvs[phi_write_phase_def] >>
  drule stack_poke_count_balance >>
  disch_then (qspecl_then [`Var v`,`Var (HD inst.inst_outputs)`] mp_tac) >> simp[]
QED

Theorem generate_phi_plan_live_count:
  !inst live halt ps ops qs out dist v.
    inst.inst_outputs = [out] /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME dist /\
    MEM v live /\ generate_phi_plan inst live halt ps = (ops,qs) ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack + (if Var v IN FDOM qs.ps_spilled then 1 else 0) =
    LIST_ELEM_COUNT (Var v) ps.ps_stack + (if Var v IN FDOM ps.ps_spilled then 1 else 0) +
      (if v = out then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  `dist < LENGTH ps.ps_stack` by
    (fs[stack_get_phi_depth_def] >> drule planAlignTheory.stack_find_bound >> simp[]) >>
  drule generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`live`,`halt`] mp_tac) >>
  Cases_on `phi_write_phase inst live dist ps` >>
  rename1 `phi_write_phase inst live dist ps = (writes,written)` >>
  simp[] >> strip_tac >>
  drule_at (Pat `phi_write_phase _ _ _ _ = _`) phi_write_live_count >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `~halt /\ ~MEM out live` >> gvs[]
  >- (pairarg_tac >> gvs[] >>
      drule_at (Pat `popmany_plan _ _ = _`) popmany_plan_other_elem_count >>
      disch_then (qspec_then `Var v` mp_tac) >>
      `v <> out` by metis_tac[] >> simp[] >> strip_tac >>
      qpat_x_assum `popmany_plan _ _ = _`
        (mp_tac o Q.AP_TERM `\r. (SND r).ps_spilled`) >>
      simp[popmany_plan_spilled_unchanged]) >>
  simp[] >> decide_tac
QED

Theorem generate_phi_plan_live_budget:
  !inst live halt ps ops qs out dist.
    inst.inst_outputs = [out] /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME dist /\
    ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled /\
    (!v. MEM v live /\ v <> out ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!v. MEM v live /\ v <> out ==>
      LIST_ELEM_COUNT (Var v) ps.ps_stack +
        (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1) /\
    generate_phi_plan inst live halt ps = (ops,qs) ==>
    (!v. MEM v live ==> MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) /\
    (!v. MEM v live ==> LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1)
Proof
  rpt gen_tac >> strip_tac >>
  `!v. MEM v live ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack + (if Var v IN FDOM qs.ps_spilled then 1 else 0) =
    LIST_ELEM_COUNT (Var v) ps.ps_stack + (if Var v IN FDOM ps.ps_spilled then 1 else 0) +
      (if v = out then 1 else 0)` by
    (gen_tac >> strip_tac >> drule_all generate_phi_plan_live_count >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!v. MEM v live ==> _` (qspec_then `v` mp_tac) >> simp[] >>
      Cases_on `v = out`
      >- (gvs[GSYM LIST_ELEM_COUNT_MEM] >>
          Cases_on `Var out IN FDOM qs.ps_spilled` >> simp[] >>
          strip_tac >> spose_not_then assume_tac >> gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
      `MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
      strip_tac >> spose_not_then assume_tac >>
      gvs[GSYM LIST_ELEM_COUNT_MEM] >>
      Cases_on `Var v IN FDOM ps.ps_spilled` >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `!v. MEM v live ==> _` (qspec_then `v` mp_tac) >> simp[] >>
  Cases_on `v = out` >- gvs[GSYM LIST_ELEM_COUNT_MEM] >>
  `LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1` by metis_tac[] >>
  simp[]
QED
