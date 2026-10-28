(* Static allocation accounting within a single frame.  Calls leave the
   caller's frontier and allocation map as they were. *)
Theory allocaBudgetProps
Ancestors
  vyperCompiler venomMemProps venomExecSemantics venomState venomInst
  finite_map list arithmetic

(* Charge each unvisited ALLOCA site once, using the compiler's literal size. *)
Definition remaining_alloca_budget_def:
  remaining_alloca_budget insts s =
    SUM (MAP alloca_size
      (FILTER (\i. i.inst_opcode = ALLOCA /\
                    i.inst_id NOTIN FDOM s.vs_allocas) insts))
End

Theorem remaining_alloca_budget_le:
  remaining_alloca_budget insts s <=
    SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) insts))
Proof
  Induct_on `insts` >> simp[remaining_alloca_budget_def] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[remaining_alloca_budget_def]
QED

Theorem remaining_alloca_budget_domain_cong:
  FDOM s'.vs_allocas = FDOM s.vs_allocas ==>
  remaining_alloca_budget insts s' = remaining_alloca_budget insts s
Proof
  simp[remaining_alloca_budget_def]
QED

Theorem remaining_alloca_budget_empty:
  s.vs_allocas = FEMPTY ==>
  remaining_alloca_budget insts s =
    SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) insts))
Proof
  simp[remaining_alloca_budget_def]
QED

Theorem remaining_alloca_budget_no_hit[local]:
  (!i. MEM i xs ==> i.inst_id <> k) /\
  FDOM t.vs_allocas = k INSERT FDOM s.vs_allocas ==>
  remaining_alloca_budget xs t = remaining_alloca_budget xs s
Proof
  Induct_on `xs` >> simp[remaining_alloca_budget_def] >>
  rpt strip_tac >> rpt IF_CASES_TAC >>
  gvs[remaining_alloca_budget_def] >> metis_tac[]
QED

Theorem remaining_alloca_budget_fresh_debit:
  ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\ MEM inst insts /\
  inst.inst_opcode = ALLOCA /\ inst.inst_id NOTIN FDOM s.vs_allocas /\
  FDOM s'.vs_allocas = inst.inst_id INSERT FDOM s.vs_allocas ==>
  remaining_alloca_budget insts s =
    alloca_size inst + remaining_alloca_budget insts s'
Proof
  Induct_on `insts` >- simp[] >>
  rpt gen_tac >> simp[MEM_MAP] >> strip_tac >>
  Cases_on `inst = h`
  >- (gvs[] >>
      `remaining_alloca_budget insts s' = remaining_alloca_budget insts s`
        by (irule remaining_alloca_budget_no_hit >> metis_tac[]) >>
      gvs[remaining_alloca_budget_def]) >>
  `h.inst_id <> inst.inst_id` by metis_tac[] >>
  `remaining_alloca_budget insts s =
    alloca_size inst + remaining_alloca_budget insts s'`
    by metis_tac[] >>
  simp[remaining_alloca_budget_def] >>
  rpt IF_CASES_TAC >> gvs[remaining_alloca_budget_def] >> decide_tac
QED

Theorem step_inst_base_alloca_effect:
  inst.inst_opcode = ALLOCA /\ step_inst_base inst s = OK s' ==>
  if inst.inst_id IN FDOM s.vs_allocas then
    FDOM s'.vs_allocas = FDOM s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
  else
    FDOM s'.vs_allocas = inst.inst_id INSERT FDOM s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next + alloca_size inst
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[exec_alloca_def, AllCaseEqs()] >> strip_tac >>
  gvs[alloca_size_def, update_var_def, FLOOKUP_DEF, AllCaseEqs()]
QED

(* Successful ALLOCA requires a literal size; a repeated id consumes no
   further budget. Other successful base steps preserve both fields. *)
Theorem step_inst_base_alloca_budget:
  ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\ MEM inst insts /\
  inst.inst_opcode <> INVOKE /\ step_inst_base inst s = OK s' ==>
  s'.vs_alloca_next + remaining_alloca_budget insts s' =
  s.vs_alloca_next + remaining_alloca_budget insts s
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (drule_all step_inst_base_alloca_effect >>
      Cases_on `inst.inst_id IN FDOM s.vs_allocas` >> simp[] >> strip_tac
      >- (drule remaining_alloca_budget_domain_cong >> simp[]) >>
      drule_all remaining_alloca_budget_fresh_debit >> strip_tac >> decide_tac) >>
  `s'.vs_allocas = s.vs_allocas`
    by metis_tac[step_inst_base_preserves_allocas] >>
  `s'.vs_alloca_next = s.vs_alloca_next`
    by metis_tac[step_inst_base_preserves_alloca_next] >>
  `remaining_alloca_budget insts s' = remaining_alloca_budget insts s`
    by (irule remaining_alloca_budget_domain_cong >> simp[]) >> simp[]
QED

Theorem static_alloca_append[local]:
  SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) (xs ++ ys))) =
  SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) xs)) +
  SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) ys))
Proof
  Induct_on `xs` >> simp[] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[]
QED

Theorem static_alloca_function_le[local]:
  MEM func funcs ==>
  SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func))) <=
  SUM (MAP alloca_size
    (FILTER (\i. i.inst_opcode = ALLOCA) (FLAT (MAP fn_insts funcs))))
Proof
  Induct_on `funcs` >> simp[static_alloca_append] >>
  rpt strip_tac >> gvs[] >> res_tac >> decide_tac
QED

Theorem remaining_alloca_budget_unit:
  MEM func ctx.ctx_functions ==>
  remaining_alloca_budget (fn_insts func) s <= unit_alloca_budget ctx
Proof
  strip_tac >> drule static_alloca_function_le >> strip_tac >>
  `remaining_alloca_budget (fn_insts func) s <=
    SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func)))`
    by irule remaining_alloca_budget_le >>
  simp[unit_alloca_budget_def, RIGHT_ADD_DISTRIB] >> decide_tac
QED
