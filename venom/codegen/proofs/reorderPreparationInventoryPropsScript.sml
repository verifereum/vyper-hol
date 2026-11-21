(* Stack height and operand counts through reorder preparation. *)
Theory reorderPreparationInventoryProps
Ancestors
  reorderPreparationProps foldlSim operandInventory doSwapSim depthReductionLengthProps
  stackPlanTypes stackPlanOps stackPlanGen stackModel planWf indexedLists list rich_list
  finite_map arithmetic
Libs BasicProvers

Theorem stack_pop_one_elem_count:
  !x (xs : 'a list).
    xs <> [] ==>
    LIST_ELEM_COUNT x (stack_pop 1 xs) +
    LIST_ELEM_COUNT x [stack_peek 0 xs] = LIST_ELEM_COUNT x xs
Proof
  rpt strip_tac >>
  `?ys y. xs = SNOC y ys` by metis_tac[rich_listTheory.SNOC_CASES] >>
  gvs[stack_pop_def, stack_peek_def, elem_count_snoc,
      rich_listTheory.TAKE_SNOC, EL_LENGTH_SNOC]
QED

Theorem do_spill_at_stack_count:
  !d ps ops ps' x.
    d < LENGTH ps.ps_stack /\ d <= 16 /\
    do_spill_at d ps = (ops,ps') ==>
    LIST_ELEM_COUNT x ps'.ps_stack +
      LIST_ELEM_COUNT x [stack_peek d ps.ps_stack] =
    LIST_ELEM_COUNT x ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `ps.ps_stack <> []` by (strip_tac >> gvs[]) >>
  Cases_on `d = 0`
  >- (gvs[do_spill_at_def, do_spill_tos_def, LET_THM] >>
      Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[] >>
      qspecl_then [`x`, `ps.ps_stack`] mp_tac
        stack_pop_one_elem_count >> simp[] >> decide_tac) >>
  `stack_peek 0 (stack_swap d ps.ps_stack) =
    stack_peek d ps.ps_stack` by
    (simp[stack_peek_def, stack_swap_def, LET_THM, EL_LUPDATE] >>
     IF_CASES_TAC >> gvs[] >> decide_tac) >>
  `LIST_ELEM_COUNT x (stack_swap d ps.ps_stack) =
    LIST_ELEM_COUNT x ps.ps_stack` by
    (qspecl_then [`d`, `ps`, `x`] mp_tac do_swap_multiplicity >>
     simp[do_swap_def]) >>
  gvs[do_spill_at_def, do_spill_tos_def, LET_THM] >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[] >>
  `stack_swap d ps.ps_stack <> []` by
    (strip_tac >> gvs[stack_swap_def]) >>
  qspecl_then [`x`, `stack_swap d ps.ps_stack`] mp_tac
    stack_pop_one_elem_count >> simp[] >> decide_tac
QED

Theorem do_spill_at_other_stack_count:
  !d ps ops ps' x.
    d < LENGTH ps.ps_stack /\ d <= 16 /\
    do_spill_at d ps = (ops,ps') /\
    x <> stack_peek d ps.ps_stack ==>
    LIST_ELEM_COUNT x ps'.ps_stack = LIST_ELEM_COUNT x ps.ps_stack
Proof
  rpt strip_tac >> drule_all do_spill_at_stack_count >>
  disch_then (qspec_then `x` mp_tac) >> simp[LIST_ELEM_COUNT_THM]
QED

Theorem select_spill_candidate_var_not_pending:
  !stk pending target_dist target_len cand.
    select_spill_candidate stk pending target_dist target_len = SOME cand ==>
    ~MEM (stack_peek cand stk) pending /\
    is_var_operand (stack_peek cand stk)
Proof
  rpt gen_tac >> strip_tac >>
  fs[select_spill_candidate_def, LET_THM] >>
  imp_res_tac FIND_SOME_MEM >> gvs[]
QED

Theorem select_spill_candidate_not_pending:
  !stk pending target_dist target_len cand.
    select_spill_candidate stk pending target_dist target_len = SOME cand ==>
    ~MEM (stack_peek cand stk) pending
Proof
  metis_tac[select_spill_candidate_var_not_pending]
QED

Theorem reduce_depth_plan_keeps_pending_count:
  !fuel pending target_op f width ps ops ps' x.
    MEM x pending /\
    reduce_depth_plan fuel pending target_op f width ps =
      (ops,ps') ==>
    LIST_ELEM_COUNT x ps'.ps_stack = LIST_ELEM_COUNT x ps.ps_stack
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth target_op f width
              ps.ps_stack` >> gvs[] >>
  Cases_on `f + 1 < width` >> gvs[] >>
  Cases_on `x' <= 16` >> gvs[] >>
  Cases_on `select_spill_candidate ps.ps_stack pending x'
              width` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `do_spill_at cand ps = (spill_ops,ps1)` >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> simp[]) >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    metis_tac[select_spill_candidate_bound] >>
  `~MEM (stack_peek cand ps.ps_stack) pending` by
    metis_tac[select_spill_candidate_not_pending] >>
  `LIST_ELEM_COUNT x ps1.ps_stack = LIST_ELEM_COUNT x ps.ps_stack` by
    metis_tac[do_spill_at_other_stack_count] >>
  Cases_on `reduce_depth_plan fuel pending target_op f
              width ps1` >> gvs[] >>
  metis_tac[]
QED

Theorem restore_spilled_plan_length_mono:
  !targets ps ops post.
    restore_spilled_plan targets ps = (ops,post) ==>
    LENGTH ps.ps_stack <= LENGTH post.ps_stack
Proof
  Induct >> simp[restore_spilled_plan_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 `do_restore h ps = (head_ops,mid)` >>
  qspecl_then [`h`, `ps`] mp_tac do_restore_length >> simp[] >>
  first_x_assum drule >> decide_tac
QED

Theorem restore_spilled_plan_counts:
  !targets ps ops post.
    restore_spilled_plan targets ps = (ops,post) ==>
    (!x. x IN FDOM post.ps_spilled <=>
         x IN FDOM ps.ps_spilled /\ ~MEM x targets) /\
    (!x. LIST_ELEM_COUNT x post.ps_stack = LIST_ELEM_COUNT x ps.ps_stack +
         (if MEM x targets /\ x IN FDOM ps.ps_spilled then 1 else 0))
Proof
  Induct >> simp[restore_spilled_plan_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 `do_restore h ps = (head_ops,mid)` >>
  first_x_assum drule >> strip_tac >>
  Cases_on `FLOOKUP ps.ps_spilled h` >>
  gvs[do_restore_def, FLOOKUP_DEF, stack_push_def, elem_count_snoc] >>
  rpt conj_tac >> rpt gen_tac >>
  rpt (first_x_assum (qspec_then `x` mp_tac)) >>
  Cases_on `x = h` >> Cases_on `MEM x targets` >>
  Cases_on `x IN FDOM ps.ps_spilled` >> gvs[LIST_ELEM_COUNT_THM]
QED

Theorem reorder_reduce_counts[local]:
  !ordered targets ps ops post.
    LENGTH targets <= LENGTH ps.ps_stack /\
    plan_steps (\op st. reduce_depth_plan
      (LENGTH st.ps_stack - LENGTH targets) targets op 0 0 st)
      ordered ps = (ops,post) ==>
    LENGTH targets <= LENGTH post.ps_stack /\
    (!x. MEM x targets ==>
         LIST_ELEM_COUNT x post.ps_stack = LIST_ELEM_COUNT x ps.ps_stack)
Proof
  Induct >- simp[plan_steps_def] >>
  rpt gen_tac >> strip_tac >>
  drule plan_steps_cons_result >> strip_tac >> gvs[] >>
  rename1 `reduce_depth_plan _ _ _ 0 0 ps = (step_ops,mid)` >>
  `LENGTH targets <= LENGTH mid.ps_stack` by
    (drule reduce_depth_plan_excess_length_floor >> simp[] >> decide_tac) >>
  `!x. MEM x targets ==>
       LIST_ELEM_COUNT x mid.ps_stack = LIST_ELEM_COUNT x ps.ps_stack` by
    metis_tac[reduce_depth_plan_keeps_pending_count] >>
  first_x_assum drule_all >> simp[]
QED

Theorem reorder_prepare_materialised_counts:
  !targets ps ops post.
    LENGTH targets <= LENGTH ps.ps_stack /\
    reorder_prepare_plan targets ps = (ops,post) ==>
    LENGTH targets <= LENGTH post.ps_stack /\
    (!x. MEM x targets ==>
         LIST_ELEM_COUNT x post.ps_stack = LIST_ELEM_COUNT x ps.ps_stack +
           (if is_var_operand x /\ x IN FDOM ps.ps_spilled then 1 else 0))
Proof
  rpt gen_tac >> strip_tac >>
  drule reorder_prepare_plan_split >> strip_tac >>
  rename1 `restore_spilled_plan _ ps = (restore_ops,restored)` >>
  `LENGTH targets <= LENGTH restored.ps_stack` by
    (qspecl_then [`FILTER is_var_operand targets`, `ps`, `restore_ops`, `restored`]
       mp_tac restore_spilled_plan_length_mono >> simp[] >> decide_tac) >>
  drule_all reorder_reduce_counts >> strip_tac >>
  drule restore_spilled_plan_counts >> simp[MEM_FILTER] >>
  metis_tac[]
QED

Theorem reorder_prepare_count_dom:
  !targets ps ops post.
    LENGTH targets <= LENGTH ps.ps_stack /\
    (!x. MEM x targets ==>
      LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack) /\
    reorder_prepare_plan targets ps = (ops,post) ==>
    !x. MEM x targets ==>
      LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x post.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  drule_all reorder_prepare_materialised_counts >> strip_tac >>
  rpt strip_tac >> irule LESS_EQ_TRANS >>
  qexists_tac `LIST_ELEM_COUNT x ps.ps_stack` >>
  simp[LESS_EQ_ADD]
QED

Theorem stack_peek_mem:
  !d stk. d < LENGTH stk ==> MEM (stack_peek d stk) stk
Proof
  rpt strip_tac >> simp[stack_peek_def] >> irule EL_MEM >> decide_tac
QED

Theorem do_restore_inventory_subset:
  !op ps ops ps'.
    do_restore op ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[stack_push_def, FLOOKUP_DEF] >>
  rpt strip_tac >> gvs[] >> fs[FLOOKUP_DEF]
QED

Theorem stack_swap_mem_subset:
  !d stk at. MEM at (stack_swap d stk) ==> MEM at stk
Proof
  rpt gen_tac >> Cases_on `stk = []` >- simp[stack_swap_def, LUPDATE_def] >>
  `LENGTH stk - 1 < LENGTH stk /\
   LENGTH stk - (d + 1) < LENGTH stk` by (Cases_on `stk` >> gvs[]) >>
  `MEM (EL (LENGTH stk - 1) stk) stk /\
   MEM (EL (LENGTH stk - (d + 1)) stk) stk` by
    (conj_tac >> irule EL_MEM >> decide_tac) >>
  simp[stack_swap_def, LET_THM] >> strip_tac >>
  fs[MEM_LUPDATE, EL_LUPDATE] >> gvs[] >> metis_tac[EL_MEM]
QED

Theorem do_spill_at_inventory_subset:
  !d ps ops ps'.
    d < LENGTH ps.ps_stack /\ do_spill_at d ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `d = 0` >>
  gvs[do_spill_at_def, do_spill_tos_def, LET_THM] >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >>
  gvs[stack_pop_def, FDOM_FUPDATE] >>
  rpt strip_tac >> gvs[]
  >- metis_tac[MEM_TAKE]
  >- metis_tac[stack_peek_mem]
  >- metis_tac[MEM_TAKE, stack_swap_mem_subset]
  >> disj1_tac >> irule stack_swap_mem_subset >>
     qexists_tac `d` >> irule stack_peek_mem >> simp[] >> decide_tac
QED

Theorem reduce_depth_plan_inventory_subset:
  !fuel tops op f n ps ops ps'.
    reduce_depth_plan fuel tops op f n ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `f + 1 < n` >> gvs[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> gvs[] >>
  rename1 `stack_get_unfixed_depth op f n ps.ps_stack = SOME dist` >>
  Cases_on `dist <= 16` >> gvs[] >>
  Cases_on `select_spill_candidate ps.ps_stack tops dist n` >> gvs[] >>
  rename1 `select_spill_candidate ps.ps_stack tops dist n = SOME cand` >>
  Cases_on `do_spill_at cand ps` >> gvs[] >>
  rename1 `do_spill_at cand ps = (spill_ops, ps1)` >>
  Cases_on `reduce_depth_plan fuel tops op f n ps1` >> gvs[] >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> simp[]) >>
  `cand < LENGTH ps.ps_stack` by
    metis_tac[select_spill_candidate_bound] >>
  rpt strip_tac >>
  `MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[do_spill_at_inventory_subset]
QED

Theorem reorder_prepare_inventory_subset:
  !targets ps ops post.
    reorder_prepare_plan targets ps = (ops,post) ==>
    !x. MEM x post.ps_stack \/ x IN FDOM post.ps_spilled ==>
        MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`targets`, `ps`, `ops`, `post`,
    `\(st : plan_state) (trace : stack_op list) (finish : plan_state).
       !x. MEM x finish.ps_stack \/ x IN FDOM finish.ps_spilled ==>
           MEM x st.ps_stack \/ x IN FDOM st.ps_spilled`]
    (mp_tac o BETA_RULE) reorder_prepare_trace_relation >>
  impl_tac >- (rpt conj_tac
  >- simp[]
  >- metis_tac[]
  >- (rpt strip_tac >> drule do_restore_inventory_subset >> simp[])
  >- (rpt strip_tac >> drule reduce_depth_plan_inventory_subset >> simp[])
  >- first_assum ACCEPT_TAC) >> simp[]
QED

Theorem list_elem_count_dom_length:
  !xs ys. (!x. LIST_ELEM_COUNT x xs <= LIST_ELEM_COUNT x ys) ==>
    LENGTH xs <= LENGTH ys
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `MEM h ys` by
    (first_x_assum (qspec_then `h` mp_tac) >>
     Cases_on `MEM h ys` >> simp[LIST_ELEM_COUNT_THM] >>
     gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
  qpat_x_assum `MEM h ys` mp_tac >>
  rewrite_tac[listTheory.MEM_SPLIT] >> strip_tac >> gvs[] >>
  `!x. LIST_ELEM_COUNT x xs <= LIST_ELEM_COUNT x (l1 ++ l2)` by
    (gen_tac >> first_x_assum (qspec_then `x` mp_tac) >>
     simp[LIST_ELEM_COUNT_DEF, FILTER_APPEND] >>
     Cases_on `h = x` >> simp[] >> decide_tac) >>
  first_x_assum drule >> simp[]
QED

Theorem reorder_prepare_noop:
  !targets ps.
    (!op. MEM op targets /\ is_var_operand op ==> op NOTIN FDOM ps.ps_spilled) /\
    (LENGTH ps.ps_stack <= LENGTH targets \/
     !op. MEM op ps.ps_stack /\ is_var_operand op ==> MEM op targets) ==>
    reorder_prepare_plan targets ps = ([],ps)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `restore_spilled_plan (FILTER is_var_operand targets) ps = ([],ps)` by
    (irule restore_spilled_plan_absent >> simp[MEM_FILTER]) >>
  `!op. reduce_depth_plan (LENGTH ps.ps_stack - LENGTH targets) targets op 0 0 ps =
    ([],ps)` by
    (gen_tac >> Cases_on `LENGTH ps.ps_stack <= LENGTH targets`
     >- (`LENGTH ps.ps_stack - LENGTH targets = 0` by decide_tac >>
         simp[reduce_depth_plan_def]) >>
     Cases_on `LENGTH ps.ps_stack - LENGTH targets`
     >- simp[reduce_depth_plan_def] >>
     simp[reduce_depth_plan_def] >>
     Cases_on `stack_get_unfixed_depth op 0 0 ps.ps_stack`
     >- simp[] >>
     rename1 `stack_get_unfixed_depth op 0 0 ps.ps_stack = SOME dist` >>
     Cases_on `dist <= 16` >- simp[] >>
     `select_spill_candidate ps.ps_stack targets dist 0 = NONE` by
       (Cases_on `select_spill_candidate ps.ps_stack targets dist 0` >> simp[] >>
        rename1 `select_spill_candidate _ _ _ _ = SOME cand` >>
        `1 <= LENGTH ps.ps_stack` by
          (drule stack_get_unfixed_depth_bound >> simp[]) >>
        `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
          metis_tac[select_spill_candidate_bound] >>
        qpat_x_assum `select_spill_candidate _ _ _ _ = _` mp_tac >>
        simp[select_spill_candidate_def] >> strip_tac >>
        imp_res_tac FIND_SOME_MEM >> gvs[] >> metis_tac[stack_peek_mem]) >>
     simp[]) >>
  simp[reorder_prepare_plan_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL _ _ ordered` >>
  pop_assum kall_tac >>
  Induct_on `ordered` >> simp[]
QED
