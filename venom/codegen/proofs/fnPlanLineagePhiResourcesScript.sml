Theory fnPlanLineagePhiResources
Ancestors fnPlanLineagePhiInventory

Theorem dead_phi_selected_erased:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  stack_peek d ps.ps_stack = Var v /\
  LENGTH (FILTER (\op. op = Var v) ps.ps_stack) = 1 /\
  Var v NOTIN FDOM ps.ps_spilled /\ ~MEM v next /\
  HD inst.inst_outputs <> v /\
  generate_phi_plan inst next halting ps = (ops,qs) ==>
  ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  strip_tac >>
  `~MEM (operand_to_string (Var v)) next` by
    simp[stackPlanTypesTheory.operand_to_string_def] >>
  drule_all dead_phi_spilled_unchanged >> strip_tac >>
  conj_tac >- (strip_tac >> drule_all dead_phi_stack_inventory >> simp[]) >>
  simp[]
QED

Theorem lupdate_elem_count_balance:
  !(xs:'a list) n y z.
    n < LENGTH xs ==>
    LIST_ELEM_COUNT z (LUPDATE y n xs) + (if z = EL n xs then 1 else 0) =
    LIST_ELEM_COUNT z xs + (if z = y then 1 else 0)
Proof
  Induct >> simp[] >> gen_tac >> Cases_on `n`
  >- (rpt gen_tac >> simp[listTheory.LUPDATE_def,
        rich_listTheory.LIST_ELEM_COUNT_DEF] >>
      rpt (IF_CASES_TAC >> simp[])) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `n'` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`y`,`z`] mp_tac) >>
  simp[listTheory.LUPDATE_def, rich_listTheory.LIST_ELEM_COUNT_DEF] >>
  rpt (IF_CASES_TAC >> simp[]) >> decide_tac
QED

Theorem stack_poke_count_balance:
  d < LENGTH stk ==>
  LIST_ELEM_COUNT z (stack_poke d y stk) +
    (if z = stack_peek d stk then 1 else 0) =
  LIST_ELEM_COUNT z stk + (if z = y then 1 else 0)
Proof
  strip_tac >> simp[stackModelTheory.stack_poke_def, stackModelTheory.stack_peek_def] >>
  irule lupdate_elem_count_balance >> simp[]
QED

(* Exact balance deliberately permits old copies of the output. *)
Theorem dead_phi_retained_count_balance:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  stack_peek d ps.ps_stack = Var v /\ ~MEM v next /\
  (halting \/ MEM (HD inst.inst_outputs) next) /\
  generate_phi_plan inst next halting ps = (ops,qs) ==>
  !w. LIST_ELEM_COUNT (Var w) qs.ps_stack + (if w = v then 1 else 0) =
    LIST_ELEM_COUNT (Var w) ps.ps_stack +
    (if w = HD inst.inst_outputs then 1 else 0)
Proof
  strip_tac >>
  `d < LENGTH ps.ps_stack` by
    (fs[stackModelTheory.stack_get_phi_depth_def] >>
     drule planAlignTheory.stack_find_bound >> simp[]) >>
  drule fnPlanLineagePhiTemporalTheory.generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`,`halting`] mp_tac) >>
  simp[fnPlanLineagePhiTemporalTheory.phi_write_phase_def,
       stackPlanTypesTheory.operand_to_string_def] >> strip_tac >> gvs[] >>
  gen_tac >> drule stack_poke_count_balance >>
  disch_then (qspecl_then [`Var w`,`Var (HD inst.inst_outputs)`] mp_tac) >> simp[]
QED

Theorem dead_phi_fresh_result_resource:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  stack_peek d ps.ps_stack = Var v /\ ~MEM v next /\
  (halting \/ MEM (HD inst.inst_outputs) next) /\
  ~MEM (Var (HD inst.inst_outputs)) ps.ps_stack /\
  Var (HD inst.inst_outputs) NOTIN FDOM ps.ps_spilled /\
  generate_phi_plan inst next halting ps = (ops,qs) ==>
  LIST_ELEM_COUNT (Var (HD inst.inst_outputs)) qs.ps_stack +
    (if Var (HD inst.inst_outputs) IN FDOM qs.ps_spilled then 1 else 0) = 1
Proof
  strip_tac >>
  `~MEM (operand_to_string (Var v)) next` by
    simp[stackPlanTypesTheory.operand_to_string_def] >>
  drule_all dead_phi_spilled_unchanged >> strip_tac >>
  `!w. LIST_ELEM_COUNT (Var w) qs.ps_stack + (if w = v then 1 else 0) =
    LIST_ELEM_COUNT (Var w) ps.ps_stack +
    (if w = HD inst.inst_outputs then 1 else 0)` by
    (irule dead_phi_retained_count_balance >> conj_tac
     >- (qexists_tac `d` >> simp[]) >>
     qexistsl_tac [`halting`,`next`,`ops`] >> simp[]) >>
  pop_assum (qspec_then `HD inst.inst_outputs` mp_tac) >>
  `MEM (Var v) ps.ps_stack` by
    (fs[stackModelTheory.stack_get_phi_depth_def] >>
     drule planAlignTheory.stack_find_bound >> strip_tac >>
     fs[stackModelTheory.stack_peek_def] >>
     `LENGTH ps.ps_stack - (d+1) < LENGTH ps.ps_stack` by decide_tac >>
     metis_tac[listTheory.EL_MEM]) >>
  `HD inst.inst_outputs <> v` by metis_tac[] >>
  `LIST_ELEM_COUNT (Var (HD inst.inst_outputs)) ps.ps_stack = 0` by
    (fs[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM]) >> simp[]
QED

Theorem dead_phi_other_resource_unchanged:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  stack_peek d ps.ps_stack = Var v /\ ~MEM v next /\
  (halting \/ MEM (HD inst.inst_outputs) next) /\
  generate_phi_plan inst next halting ps = (ops,qs) /\
  w <> v /\ w <> HD inst.inst_outputs ==>
  LIST_ELEM_COUNT (Var w) qs.ps_stack +
    (if Var w IN FDOM qs.ps_spilled then 1 else 0) =
  LIST_ELEM_COUNT (Var w) ps.ps_stack +
    (if Var w IN FDOM ps.ps_spilled then 1 else 0)
Proof
  strip_tac >>
  `~MEM (operand_to_string (Var v)) next` by
    simp[stackPlanTypesTheory.operand_to_string_def] >>
  drule_all dead_phi_spilled_unchanged >> strip_tac >>
  `LIST_ELEM_COUNT (Var w) qs.ps_stack + (if w = v then 1 else 0) =
    LIST_ELEM_COUNT (Var w) ps.ps_stack +
    (if w = HD inst.inst_outputs then 1 else 0)` by
    (irule dead_phi_retained_count_balance >> conj_tac
     >- (qexists_tac `d` >> simp[]) >>
     qexistsl_tac [`halting`,`next`,`ops`] >> simp[]) >> gvs[]
QED
