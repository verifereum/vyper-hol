Theory lowerDloadPtrPhaseNext
Ancestors
  lowerDloadPtrJointNext lowerDloadPtrAggregate lowerDloadPtrPhase
  lowerDloadPtrRel o1ContractLowerDload lowerDloadDefs
  ptrDiscipline venomExecSemantics venomState venomInst venomExecProofs
  contextCodegenRel list rich_list arithmetic

Theorem dload_insts_supply_segment:
  !src n q ys last before u xs after k.
    lower_dload_insts_supply q src = (ys,last) /\
    n < LENGTH src /\
    lower_dload_insts_supply q (TAKE n src) = (before,u) /\
    lower_dload_inst_supply u (EL n src) = (xs,after) /\ k < LENGTH xs ==>
    LENGTH before + k < LENGTH ys /\
    EL (LENGTH before + k) ys = EL k xs
Proof
  Induct >- simp[] >> Cases_on `n` >> rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac
  >- (gvs[lower_dload_insts_supply_def] >> simp[EL_APPEND_EQN]) >>
  gvs[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >>
  `k + (LENGTH out + LENGTH outs') = LENGTH out + (k + LENGTH outs')` by decide_tac >>
  pop_assum SUBST1_TAC >> simp[EL_APPEND_EQN]
QED

Theorem dload_control_interior_next_fields:
  dload_control_match q f g s t i xs k /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  SUC k < LENGTH xs /\
  v.vs_current_bb = t.vs_current_bb /\ v.vs_prev_bb = t.vs_prev_bb /\
  active_inst g j (v with vs_inst_idx := SUC t.vs_inst_idx) /\
  ((i.inst_opcode = DLOAD /\ LENGTH xs = 4) \/
   (i.inst_opcode = DLOADBYTES /\ LENGTH xs = 2)) ==>
  j = EL (SUC k) xs /\
  dload_control_match q f g s (v with vs_inst_idx := SUC t.vs_inst_idx) i xs (SUC k)
Proof
  strip_tac >>
  qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
  simp[dload_control_match_def] >> strip_tac >>
  `?aq. lower_dload_blocks_supply q f.fn_blocks = (g.fn_blocks,aq)` by
    (gvs[lower_dload_function_supply_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all dload_blocks_supply_el >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lower_dload_block_supply bs _ = (gb,_)` >>
  `gb.bb_label = (EL bi f.fn_blocks).bb_label /\
   ?aq. lower_dload_insts_supply bs (EL bi f.fn_blocks).bb_instructions =
      (gb.bb_instructions,aq)` by
    (qpat_x_assum `lower_dload_block_supply _ _ = _` mp_tac >>
     simp[lower_dload_block_supply_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `LENGTH before + SUC k < LENGTH gb.bb_instructions /\
   EL (LENGTH before + SUC k) gb.bb_instructions = EL (SUC k) xs` by
    (qpat_x_assum `i = _` SUBST_ALL_TAC >>
     drule_all dload_insts_supply_segment >> simp[]) >>
  `active_inst g (EL (SUC k) xs) (v with vs_inst_idx := SUC t.vs_inst_idx)` by
    (`SUC t.vs_inst_idx = LENGTH before + SUC k` by decide_tac >>
     simp[active_inst_def] >> qexists_tac `gb` >>
     simp[Abbr `gb`, EL_MEM]) >>
  `j = EL (SUC k) xs` by
    (qpat_x_assum `active_inst f _ _` kall_tac >>
     qpat_x_assum `active_inst g _ t` kall_tac >>
     gvs[active_inst_def] >>
     `bb = bb'` by metis_tac[MEM_lookup_block, optionTheory.SOME_11] >> gvs[]) >>
  simp[] >> qexistsl [`bi`,`before`,`is`,`after`] >>
  gvs[ADD_CLAUSES, Abbr `bs`]
QED

Theorem dload_supply_interior_shape:
  lower_dload_inst_supply supply i = (xs,next) /\ SUC k < LENGTH xs ==>
  ((i.inst_opcode = DLOAD /\ LENGTH xs = 4) \/
   (i.inst_opcode = DLOADBYTES /\ LENGTH xs = 2)) /\
  MEM (EL k xs).inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      `k = 0 \/ k = 1 \/ k = 2` by decide_tac >> gvs[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >> `k = 0` by decide_tac >> gvs[]) >>
  simp[lower_dload_inst_supply_def] >> rpt strip_tac >> gvs[]
QED

Theorem dload_expanded_step_blocks:
  MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD] /\
  step_inst fuel C i t = OK v ==>
  v.vs_current_bb = t.vs_current_bb /\ v.vs_prev_bb = t.vs_prev_bb
Proof
  simp[] >> strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()]
  >- (gvs[exec_alloca_def, AllCaseEqs(), update_var_def])
  >- (gvs[exec_pure2_def, AllCaseEqs(), update_var_def])
  >- (gvs[write_memory_with_expansion_def]) >>
  gvs[exec_read1_def, AllCaseEqs(), update_var_def]
QED

Theorem dload_actual_phase_next:
  dload_phase_core fuel Ct q f g i xs k
    lo fs V Ws PG PH G tn s t H un cs ds /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  SUC k < LENGTH xs /\
  step_inst fuel Ct (EL k xs) t = OK v /\
  active_inst g j (v with vs_inst_idx := SUC t.vs_inst_idx) ==>
  j = EL (SUC k) xs /\
  dload_phase_core fuel Ct q f g i xs (SUC k)
    lo fs V Ws PG PH G tn s (v with vs_inst_idx := SUC t.vs_inst_idx)
    (step_prov PH H (EL k xs) v)
    (step_taint (EL k xs) t v un) cs ds
Proof
  strip_tac >> drule dload_phase_anchor >> strip_tac >>
  qpat_assum `dload_control_match _ _ _ _ t _ _ _`
    (mp_then Any mp_tac dload_control_match_expansion) >> strip_tac >>
  drule_all dload_supply_interior_shape >> strip_tac >>
  drule_all dload_expanded_step_blocks >> strip_tac >>
  qpat_assum `dload_control_match _ _ _ _ t _ _ _`
    (mp_then Any mp_tac dload_control_interior_next_fields) >>
  simp[] >> disch_then (qspecl_then [`v`,`j`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  irule dload_phase_extend >> simp[]
QED
