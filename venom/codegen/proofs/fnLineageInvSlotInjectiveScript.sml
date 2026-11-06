Theory fnLineageInvSlotInjective
Ancestors
  fnPlanLineagePhiSlots fnPlanLineagePhiMaps stackPlanGen finite_map list

Theorem phi_slot_realize_supported_injective:
  !phis p om mm live a b.
    phi_uses_disjoint phis /\ build_phi_maps p phis = (om,mm) /\
    (!v i. MEM v live /\ FLOOKUP om v = SOME i ==> IS_SOME (FLOOKUP mm i)) /\
    MEM a (phi_slot_trace om live) /\ MEM b (phi_slot_trace om live) /\
    phi_slot_realize mm a = phi_slot_realize mm b ==> a = b
Proof
  rpt gen_tac >> strip_tac >>
  `!i. MEM (INR i) (phi_slot_trace om live) ==>
       FLOOKUP om (THE (FLOOKUP mm i)) = SOME i` by
    (simp[phi_slot_trace_inr_mem] >> rpt strip_tac >>
     `IS_SOME (FLOOKUP mm i)` by metis_tac[] >>
     Cases_on `FLOOKUP mm i` >> gvs[] >>
     metis_tac[build_phi_maps_matching_operand, pairTheory.FST,
               pairTheory.SND]) >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[phi_slot_trace_inl_mem, phi_slot_trace_inr_mem, phi_slot_realize_def] >>
  metis_tac[phi_slot_trace_inr_mem, optionTheory.SOME_11, optionTheory.NOT_NONE_SOME]
QED

Theorem input_vars_from_slot_distinct_iff:
  !insts p om mm live.
    ~NULL (collect_phis insts) /\ phi_uses_disjoint (collect_phis insts) /\
    build_phi_maps p (collect_phis insts) = (om,mm) /\
    (!v i. MEM v live /\ FLOOKUP om v = SOME i ==> IS_SOME (FLOOKUP mm i)) ==>
    (ALL_DISTINCT (input_vars_from p insts live) <=>
     ALL_DISTINCT (phi_slot_trace om live))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all input_vars_from_slot_factor >> disch_then SUBST1_TAC >>
  eq_tac >- metis_tac[ALL_DISTINCT_MAP] >>
  strip_tac >> irule ALL_DISTINCT_MAP_INJ >> simp[] >>
  rpt strip_tac >> irule phi_slot_realize_supported_injective >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
