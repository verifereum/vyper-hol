Theory fnPlanLineagePhiSuffixResources
Ancestors
  fnPlanLineagePhiSchedule fnPlanLineageNativeTargets fnPlanLineagePhiTemporal

(* Physical value counts, unlike origin-class counts, include PHI writes. *)
Theorem phi_origin_write_value_count_le:
  !left op keep d ret cells.
    LIST_ELEM_COUNT op (MAP (phi_cell_value left)
      (phi_origin_write keep d ret cells)) <=
    LIST_ELEM_COUNT op (MAP (phi_cell_value left) cells) +
      (if op = ret then 1 else 0)
Proof
  rpt gen_tac >> Cases_on `keep`
  >- (Cases_on `op = ret` >>
      simp[phi_origin_write_keep, rich_listTheory.LIST_ELEM_COUNT_DEF,
           listTheory.FILTER_APPEND_DISTRIB, phi_cell_value_def]) >>
  simp[phi_origin_write_def, stackModelTheory.stack_poke_def,
       rich_listTheory.LIST_ELEM_COUNT_DEF, rich_listTheory.FILTER_MAP,
       combinTheory.o_DEF] >>
  Cases_on `LENGTH cells - 1 - d < LENGTH cells`
  >- (drule filter_lupdate_count >>
      disch_then (qspecl_then [`\c. phi_cell_value left c = op`, `PhiCommon ret`] mp_tac) >>
      simp[phi_cell_value_def] >>
      Cases_on `op = ret` >> gvs[] >>
      strip_tac >>
      Cases_on `phi_cell_value left (EL (LENGTH cells - (d + 1)) cells) = op` >>
      gvs[] >> decide_tac) >>
  Cases_on `cells` >> gvs[listTheory.LUPDATE_def]
QED

Theorem phi_origin_pop_value_count_le:
  !left op d cells.
    LIST_ELEM_COUNT op (MAP (phi_cell_value left) (phi_origin_pop d cells)) <=
    LIST_ELEM_COUNT op (MAP (phi_cell_value left) cells)
Proof
  rpt gen_tac >>
  simp[phi_origin_pop_def, stackModelTheory.stack_pop_def,
       rich_listTheory.LIST_ELEM_COUNT_DEF, rich_listTheory.FILTER_MAP,
       combinTheory.o_DEF] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  irule_at Any filter_take_count_le >> simp[filter_stack_swap_count]
QED

Theorem phi_origin_stage_value_count_le:
  !inst next halting p q cells cells1 left op.
    phi_origin_stage inst next halting p q cells cells1 ==>
    LIST_ELEM_COUNT op (MAP (phi_cell_value left) cells1) <=
    LIST_ELEM_COUNT op (MAP (phi_cell_value left) cells) +
      (if op = Var (HD inst.inst_outputs) then 1 else 0)
Proof
  rpt gen_tac >> rewrite_tac[phi_origin_stage_def] >> strip_tac >>
  `LIST_ELEM_COUNT op (MAP (phi_cell_value left) written) <=
   LIST_ELEM_COUNT op (MAP (phi_cell_value left) cells) +
     (if op = Var (HD inst.inst_outputs) then 1 else 0)` by
    (gvs[] >> irule phi_origin_write_value_count_le) >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next`
  >- (gvs[] >> irule arithmeticTheory.LESS_EQ_TRANS >>
      goal_assum (drule_at Any) >> irule phi_origin_pop_value_count_le) >>
  gvs[]
QED

Theorem phi_origin_schedule_value_count_le:
  !steps p q cells cells_end left op.
    phi_origin_schedule_ready steps p q cells cells_end ==>
    LIST_ELEM_COUNT op (MAP (phi_cell_value left) cells_end) <=
    LIST_ELEM_COUNT op (MAP (phi_cell_value left) cells) +
    LIST_ELEM_COUNT op (MAP (\(inst,next,halting). Var (HD inst.inst_outputs)) steps)
Proof
  Induct >- simp[phi_origin_schedule_ready_def, rich_listTheory.LIST_ELEM_COUNT_DEF] >>
  Cases_on `h` >> Cases_on `r` >>
  rename1 `(inst,next,halting)::steps` >> rpt gen_tac >>
  simp[phi_origin_schedule_ready_def] >> strip_tac >>
  drule phi_origin_stage_value_count_le >>
  disch_then (qspecl_then [`left`, `op`] assume_tac) >>
  first_x_assum drule >>
  disch_then (qspecl_then [`left`, `op`] mp_tac) >>
  simp[rich_listTheory.LIST_ELEM_COUNT_DEF] >>
  Cases_on `op = Var (HD inst.inst_outputs)` >>
  gvs[rich_listTheory.LIST_ELEM_COUNT_DEF] >> decide_tac
QED
