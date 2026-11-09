(* Missing actual counter sites are covered by the global weighted budget. *)
Theory entryReachBodyScratchCapacity
Ancestors
  entryReachBodyScratchSet entryReachBodyScratchSites allocaFrontierBound allocaBudgetProps
  venomMemDefs venomState finite_map list pred_set arithmetic

Theorem entry_missing_site_credit[local]:
  FINITE selected /\
  (!id. id IN selected ==> id NOTIN FDOM s.vs_allocas /\
    ?inst. MEM inst insts /\ inst.inst_id = id /\
      inst.inst_opcode = ALLOCA /\ alloca_size inst = 32) ==>
  32 * CARD selected <= remaining_alloca_budget insts s
Proof
  qid_spec_tac `selected` >> Induct_on `insts`
  >- (rpt strip_tac >> `selected = {}` by (simp[EXTENSION] >> metis_tac[MEM]) >>
      simp[remaining_alloca_budget_def]) >>
  rpt strip_tac >>
  Cases_on `h.inst_id IN selected /\ h.inst_opcode = ALLOCA /\ alloca_size h = 32`
  >- (gvs[] >>
      `h.inst_id NOTIN FDOM s.vs_allocas` by metis_tac[] >>
      `32 * CARD (selected DELETE h.inst_id) <= remaining_alloca_budget insts s` by
        (first_x_assum irule >> simp[] >> metis_tac[MEM]) >>
      `CARD selected = SUC (CARD (selected DELETE h.inst_id))` by
        (`selected = h.inst_id INSERT (selected DELETE h.inst_id)` by
           (simp[EXTENSION] >> metis_tac[]) >>
         pop_assum (fn th => once_rewrite_tac[th]) >> simp[CARD_INSERT]) >>
      `remaining_alloca_budget (h::insts) s =
         32 + remaining_alloca_budget insts s` by
        simp[remaining_alloca_budget_def] >>
      qpat_x_assum `32 * CARD _ <= _` mp_tac >>
      qpat_x_assum `CARD selected = SUC _` (fn th => rewrite_tac[th]) >>
      asm_rewrite_tac[] >> POP_ASSUM_LIST (K all_tac) >>
      pure_rewrite_tac[MULT_SUC] >> decide_tac) >>
  `32 * CARD selected <= remaining_alloca_budget insts s` by
    (first_x_assum irule >> simp[] >> metis_tac[MEM]) >>
  Cases_on `h.inst_opcode = ALLOCA` >>
  Cases_on `h.inst_id IN FDOM s.vs_allocas` >>
  gvs[remaining_alloca_budget_def]
QED

Theorem entry_scratch_missing_global_credit:
  FINITE sites /\
  (!id. id IN sites ==> ?inst. MEM inst insts /\ inst.inst_id = id /\
     inst.inst_opcode = ALLOCA /\ alloca_size inst = 32) ==>
  32 * CARD (entry_scratch_missing sites s) <= remaining_alloca_budget insts s
Proof
  strip_tac >> irule entry_missing_site_credit >>
  simp[entry_scratch_missing_def] >> metis_tac[]
QED

Theorem entry_scratch_ready_global:
  FINITE sites /\ alloca_frontier_inv ctx fn site s /\ alloca_inv s /\
  (!id. id IN sites ==> ?inst. MEM inst (fn_insts fn) /\ inst.inst_id = id /\
     inst.inst_opcode = ALLOCA /\ alloca_size inst = 32) /\
  (!id r. id IN sites /\ FLOOKUP s.vs_allocas id = SOME r ==> SND r = 32) ==>
  entry_scratch_ready sites 0 (unit_alloca_budget ctx) s
Proof
  strip_tac >> drule_all entry_scratch_missing_global_credit >>
  disch_then (qspec_then `s` assume_tac) >>
  simp[entry_scratch_ready_def] >> conj_tac
  >- (fs[alloca_frontier_inv_def] >> decide_tac) >>
  rpt gen_tac >> PairCases_on `r` >> strip_tac >>
  `r1 = 32` by metis_tac[pairTheory.SND] >> gvs[] >>
  fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]
QED
