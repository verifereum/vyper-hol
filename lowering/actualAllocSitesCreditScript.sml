(* Missing physical sites, not every ID in a numerical interval.
   No distinctness premise is needed: duplicate instructions add credit. *)
Theory actualAllocSitesCredit
Ancestors actualAllocCredit allocaBudgetProps vyperCompiler venomInst venomState
  finite_map list arithmetic words pred_set

Theorem remaining_alloca_budget_sites:
  !insts selected s n. FINITE selected /\
  (!id. id IN selected ==> id NOTIN FDOM s.vs_allocas /\
    ?inst. MEM inst insts /\ inst.inst_id = id /\
      inst.inst_opcode = ALLOCA /\ alloca_size inst = n) ==>
  n * CARD selected <= remaining_alloca_budget insts s
Proof
  Induct
  >- (rpt strip_tac >> `selected = {}` by (simp[EXTENSION] >> metis_tac[MEM]) >>
      simp[remaining_alloca_budget_def]) >>
  rpt strip_tac >>
  Cases_on `h.inst_id IN selected /\ h.inst_opcode = ALLOCA /\ alloca_size h = n`
  >- (fs[] >>
      `h.inst_id NOTIN FDOM s.vs_allocas` by metis_tac[] >>
      `n * CARD (selected DELETE h.inst_id) <= remaining_alloca_budget insts s` by
        (first_x_assum irule >> simp[] >> metis_tac[MEM]) >>
      `CARD selected = SUC (CARD (selected DELETE h.inst_id))` by
        (`selected = h.inst_id INSERT (selected DELETE h.inst_id)` by
           (simp[EXTENSION] >> metis_tac[]) >>
         pop_assum (fn th => once_rewrite_tac[th]) >> simp[CARD_INSERT]) >>
      `remaining_alloca_budget (h::insts) s =
         n + remaining_alloca_budget insts s` by
        simp[remaining_alloca_budget_def] >>
      qpat_x_assum `n * CARD _ <= _` mp_tac >>
      qpat_x_assum `CARD selected = SUC _` (fn th => rewrite_tac[th]) >>
      asm_rewrite_tac[] >> POP_ASSUM_LIST (K all_tac) >>
      pure_rewrite_tac[MULT_SUC] >> decide_tac) >>
  `n * CARD selected <= remaining_alloca_budget insts s` by
    (first_x_assum irule >> simp[] >> metis_tac[MEM]) >>
  Cases_on `h.inst_opcode = ALLOCA` >>
  Cases_on `h.inst_id IN FDOM s.vs_allocas` >>
  gvs[remaining_alloca_budget_def]
QED
