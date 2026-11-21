(* Temporary reorder spill slots are fresh for the incoming planner map. *)
Theory reorderSpillFresh
Ancestors reorderPreparationProps reorderPreparationInventoryProps fnPlanLineageReorder
          foldlSim indexedLists reorderSim reduceDepthSim doSwapSim planWf prefixSpillReplay stackPlanGen stackPlanOps
          stackPlanTypes stackModel finite_map list rich_list pred_set arithmetic
Libs BasicProvers

Theorem alloc_spill_slot_keep_layout:
  !al fm off al'.
    spill_alloc_layout_wf al fm /\ alloc_spill_slot al = (off,al') ==>
    spill_alloc_layout_wf al' fm /\
    (!key old. FLOOKUP fm key = SOME old ==>
       old + 32 <= off \/ off + 32 <= old)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `al.sa_free_slots`
  >- (gvs[alloc_spill_slot_def, spill_alloc_layout_wf_def] >>
      conj_tac >- (rpt strip_tac >> res_tac >> decide_tac) >>
      rpt strip_tac >> res_tac >> decide_tac) >>
  gvs[alloc_spill_slot_def, spill_alloc_layout_wf_def] >>
  conj_tac
  >- (conj_tac >- metis_tac[] >>
      conj_tac >- (rpt strip_tac >> drule MEM_FRONT >> simp[] >> metis_tac[]) >>
      conj_tac >- metis_tac[] >>
      conj_tac >- simp[ALL_DISTINCT_FRONT] >>
      conj_tac
      >- (rpt strip_tac >> simp[EL_FRONT] >>
          qpat_x_assum `!i j. i < SUC _ /\ _ ==> _`
            (qspecl_then [`i`, `j`] mp_tac) >> simp[]) >>
      rpt strip_tac >> drule MEM_FRONT >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM (LAST (h::t)) (h::t)` by simp[MEM_LAST] >> fs[] >> metis_tac[]
QED

Theorem spill_alloc_n_fresh_for_map[local]:
  !items al fm offs.
    spill_alloc_layout_wf al fm /\
    EVERY (\off. !key old. FLOOKUP fm key = SOME old ==>
       old + 32 <= off \/ off + 32 <= old) offs ==>
    spill_alloc_layout_wf (SND (spill_alloc_n offs al items)) fm /\
    EVERY (\off. !key old. FLOOKUP fm key = SOME old ==>
       old + 32 <= off \/ off + 32 <= old)
       (FST (spill_alloc_n offs al items))
Proof
  Induct >> simp[spill_alloc_n_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `alloc_spill_slot al` >> simp[] >>
  drule_all alloc_spill_slot_keep_layout >> strip_tac >>
  first_x_assum irule >> simp[EVERY_SNOC] >> metis_tac[]
QED

Theorem do_swap_spills_fresh_for_map:
  !dist ps.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    dist < LENGTH ps.ps_stack ==>
    EVERY (spill_fresh_for ps.ps_spilled) (FST (do_swap dist ps))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `dist <= 16`
  >- (simp[do_swap_def, LET_THM] >>
      Cases_on `dist = 0` >> simp[spill_fresh_for_def]) >>
  mp_tac (Q.SPECL [`dist`, `ps`] do_swap_big_decompose) >>
  (impl_tac >- decide_tac) >> simp[LET_THM] >> strip_tac >>
  `EVERY (\off. !key old. FLOOKUP ps.ps_spilled key = SOME old ==>
       old + 32 <= off \/ off + 32 <= old)
       (FST (spill_alloc_n [] ps.ps_alloc (top_n (dist + 1) ps.ps_stack)))` by
    (qspecl_then [`top_n (dist + 1) ps.ps_stack`, `ps.ps_alloc`, `ps.ps_spilled`, `[]`]
       mp_tac spill_alloc_n_fresh_for_map >> simp[]) >>
  simp[EVERY_MAP, spill_fresh_for_def, combinTheory.o_DEF] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem do_swap_spills_fresh_frame:
  !dist ps fm ops ps'.
    spill_alloc_layout_wf ps.ps_alloc fm /\
    dist < LENGTH ps.ps_stack /\ do_swap dist ps = (ops,ps') ==>
    EVERY (spill_fresh_for fm) ops /\
    spill_alloc_layout_wf ps'.ps_alloc fm
Proof
  rpt gen_tac >> strip_tac >> Cases_on `dist <= 16`
  >- (gvs[do_swap_def, LET_THM] >>
      Cases_on `dist = 0` >> gvs[spill_fresh_for_def]) >>
  mp_tac (Q.SPECL [`dist`, `ps`] do_swap_big_decompose) >>
  (impl_tac >- decide_tac) >> simp[LET_THM] >> strip_tac >>
  `EVERY (\off. !key old. FLOOKUP fm key = SOME old ==>
       old + 32 <= off \/ off + 32 <= old)
       (FST (spill_alloc_n [] ps.ps_alloc (top_n (dist + 1) ps.ps_stack)))` by
    (qspecl_then [`top_n (dist + 1) ps.ps_stack`, `ps.ps_alloc`, `fm`, `[]`]
       mp_tac spill_alloc_n_fresh_for_map >> simp[]) >>
  qspecl_then [`ps.ps_alloc`, `fm`, `top_n (dist + 1) ps.ps_stack`]
    mp_tac spill_alloc_n_free_layout_wf_arbitrary >>
  gvs[LET_THM, EVERY_MAP, spill_fresh_for_def, combinTheory.o_DEF] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem do_spill_at_spills_fresh_frame:
  !dist ps fm ops ps'.
    spill_alloc_layout_wf ps.ps_alloc fm /\
    do_spill_at dist ps = (ops,ps') ==>
    EVERY (spill_fresh_for fm) ops /\
    spill_alloc_layout_wf ps'.ps_alloc fm
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >>
  drule_all alloc_spill_slot_keep_layout >> strip_tac >>
  Cases_on `dist = 0` >>
  gvs[do_spill_at_def, do_spill_tos_def, LET_THM, spill_fresh_for_def] >>
  metis_tac[]
QED

Theorem reduce_depth_plan_spills_fresh_frame:
  !fuel targets op f n ps fm ops ps'.
    spill_alloc_layout_wf ps.ps_alloc fm /\
    reduce_depth_plan fuel targets op f n ps = (ops,ps') ==>
    EVERY (spill_fresh_for fm) ops /\
    spill_alloc_layout_wf ps'.ps_alloc fm
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `f + 1 < n` >> gvs[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> gvs[] >>
  rename1 `SOME dist` >> Cases_on `dist <= 16` >> gvs[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets dist n` >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  drule_all do_spill_at_spills_fresh_frame >> strip_tac >>
  first_x_assum drule >> disch_then drule >>
  simp[]
QED

Theorem reorder_one_existing_spills_fresh_frame:
  !dfg targets idx op ps d fm ops ps'.
    spill_alloc_layout_wf ps.ps_alloc fm /\
    idx < LENGTH targets /\ LENGTH targets <= 16 /\
    LENGTH targets <= LENGTH ps.ps_stack /\
    stack_get_unfixed_depth op (LENGTH targets - 1 - idx)
      (LENGTH targets) ps.ps_stack = SOME d /\
    reorder_one dfg targets idx op ps = (ops,ps') ==>
    EVERY (spill_fresh_for fm) ops /\
    spill_alloc_layout_wf ps'.ps_alloc fm
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH targets - 1 - idx = LENGTH targets - (idx + 1)` by decide_tac >>
  fs[] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `EVERY (spill_fresh_for fm) reduce_ops /\
   spill_alloc_layout_wf ps2.ps_alloc fm /\
   LENGTH targets <= LENGTH ps2.ps_stack` by
    (Cases_on `d > 16` >> gvs[] >>
     drule_all reduce_depth_plan_spills_fresh_frame >> strip_tac >>
     drule reduce_depth_plan_length_floor >> simp[] >> decide_tac) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
      (LENGTH targets) ps2.ps_stack` >> gvs[] >>
  rename1 `_ = SOME dist` >>
  `dist < LENGTH ps2.ps_stack` by metis_tac[stack_get_unfixed_depth_props] >>
  `LENGTH targets - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `dist = LENGTH targets - (idx + 1)` >> gvs[] >>
  Cases_on `operand_equiv dfg op
      (stack_peek (LENGTH targets - (idx + 1)) ps2.ps_stack)` >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  drule_all do_swap_spills_fresh_frame >> strip_tac >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspecl_then [`dist`, `ps2`] mp_tac do_swap_length >> simp[]) >>
  `LENGTH targets - (idx + 1) < LENGTH ps3.ps_stack` by decide_tac >>
  drule_all do_swap_spills_fresh_frame >> strip_tac >>
  simp[]
QED

Theorem reorder_prepare_spills_fresh_frame[local]:
  !targets ps ops post fm.
    reorder_prepare_plan targets ps = (ops,post) /\
    spill_alloc_layout_wf ps.ps_alloc fm /\
    (!x. MEM x targets /\ is_var_operand x ==> x NOTIN FDOM ps.ps_spilled) ==>
    EVERY (spill_fresh_for fm) ops /\
    spill_alloc_layout_wf post.ps_alloc fm /\
    (!x. MEM x targets /\ is_var_operand x ==> x NOTIN FDOM post.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`targets`, `ps`, `ops`, `post`,
    `\st trace out.
       spill_alloc_layout_wf st.ps_alloc fm /\
       (!x. MEM x targets /\ is_var_operand x ==> x NOTIN FDOM st.ps_spilled) ==>
       EVERY (spill_fresh_for fm) trace /\
       spill_alloc_layout_wf out.ps_alloc fm /\
       (!x. MEM x targets /\ is_var_operand x ==> x NOTIN FDOM out.ps_spilled)`]
    (mp_tac o BETA_RULE) reorder_prepare_trace_relation >>
  impl_tac
  >- (rpt conj_tac
      >- (simp[] >> gen_tac >> disch_then (ACCEPT_TAC o CONJUNCT2))
      >- metis_tac[EVERY_APPEND]
      >- (rpt gen_tac >> strip_tac >> strip_tac >>
          `FLOOKUP st.ps_spilled op = NONE` by
            (fs[flookup_thm] >> metis_tac[]) >>
          gvs[do_restore_def] >> first_assum ACCEPT_TAC)
      >- (rpt gen_tac >> strip_tac >> strip_tac >>
          drule_all reduce_depth_plan_spills_fresh_frame >> strip_tac >> simp[] >>
          rpt gen_tac >> strip_tac >>
          qspecl_then [`LENGTH st.ps_stack - LENGTH targets`, `targets`,
            `op`, `0`, `0`, `st`, `x`] mp_tac reduce_depth_plan_not_spilled >>
          simp[] >> metis_tac[])
      >- first_assum ACCEPT_TAC) >>
  simp[]
QED

Theorem reorder_plan_exact_two_spills_fresh:
  !base dfg h h' ps ops ps'.
    exact_two_planner_ready base h h' ps /\
    reorder_plan dfg [h;h'] ps = (ops,ps') ==>
    EVERY (spill_fresh_for ps.ps_spilled) ops
Proof
  rpt gen_tac >> strip_tac >>
  drule reorder_plan_split >> strip_tac >>
  rename1 `reorder_prepare_plan [h;h'] ps = (prep,start)` >>
  fs[exact_two_planner_ready_def] >>
  qspecl_then [`base'`, `[h;h']`, `ps`, `prep`, `start`] mp_tac
    reorder_prepare_keeps_budget >> simp[] >> strip_tac >>
  qspecl_then [`[h;h']`, `ps`, `prep`, `start`] mp_tac
    reorder_prepare_materialised_counts >> simp[] >> strip_tac >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by fs[residual_budget_wf_def] >>
  qspecl_then [`[h;h']`, `ps`, `prep`, `start`, `ps.ps_spilled`]
    mp_tac reorder_prepare_spills_fresh_frame >> simp[] >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  `!x. MEM x [h;h'] ==> LIST_ELEM_COUNT x [h;h'] <= LIST_ELEM_COUNT x start.ps_stack` by
    (qspecl_then [`[h;h']`, `ps`, `prep`, `start`] mp_tac
       reorder_prepare_count_dom >> simp[] >> metis_tac[]) >>
  `exact_two_planner_ready base' h h' start` by
    (simp[exact_two_planner_ready_def] >> conj_tac >-
     (gen_tac >> Cases_on `MEM x [h;h']` >- metis_tac[] >>
      fs[LIST_ELEM_COUNT_DEF]) >>
     first_assum ACCEPT_TAC) >>
  `plan_state_residual_wf base' [h;h'] 0 start` by
    fs[residual_budget_wf_def, plan_state_residual_wf_def] >>
  `?d. stack_get_unfixed_depth h 1 2 start.ps_stack = SOME d` by
    (qspecl_then [`base'`, `[h;h']`, `0`, `start`]
       mp_tac materialised_pending_next_on_stack >>
     simp[] >> fs[exact_two_planner_ready_def]) >>
  qpat_x_assum `plan_steps _ _ _ = _` mp_tac >>
  simp[MAPi_def, MAPi_ACC_def, plan_steps_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  `exact_two_planner_ready base' h h' ps1` by
    (qspecl_then [`dfg`, `base'`, `h`, `h'`, `0`, `h`, `start`, `step_ops`, `ps1`]
       mp_tac reorder_one_exact_two_planner_ready >> simp[]) >>
  `EVERY (spill_fresh_for ps.ps_spilled) step_ops /\
   spill_alloc_layout_wf ps1.ps_alloc ps.ps_spilled` by
    (qspecl_then [`dfg`, `[h;h']`, `0`, `h`, `start`, `d`,
       `ps.ps_spilled`, `step_ops`, `ps1`]
       mp_tac reorder_one_existing_spills_fresh_frame >>
     simp[]) >>
  `stack_peek 1 ps1.ps_stack = h` by
    (qspecl_then [`dfg`, `[h;h']`, `0`, `h`, `start`, `step_ops`, `ps1`]
       mp_tac reorder_one_places >> simp[] >>
     fs[exact_two_planner_ready_def] >> metis_tac[]) >>
  `plan_state_residual_wf base' [h;h'] 1 ps1` by
    (fs[exact_two_planner_ready_def, residual_budget_wf_def,
       plan_state_residual_wf_def] >>
     rpt strip_tac >> `i = 0` by decide_tac >> simp[]) >>
  `?d'. stack_get_unfixed_depth h' 0 2 ps1.ps_stack = SOME d'` by
    (qspecl_then [`base'`, `[h;h']`, `1`, `ps1`]
       mp_tac materialised_pending_next_on_stack >>
     simp[] >> fs[exact_two_planner_ready_def]) >>
  `EVERY (spill_fresh_for ps.ps_spilled) rest_ops` by
    (qspecl_then [`dfg`, `[h;h']`, `1`, `h'`, `ps1`, `d'`,
       `ps.ps_spilled`, `rest_ops`, `ps'`]
       mp_tac reorder_one_existing_spills_fresh_frame >>
     simp[] >> fs[exact_two_planner_ready_def]) >>
  simp[]
QED
