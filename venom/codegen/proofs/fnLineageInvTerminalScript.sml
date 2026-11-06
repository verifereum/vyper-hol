Theory fnLineageInvTerminal
Ancestors
  fnPlanLineageReorder fnPlanLineageInventory stackPlanOps stackModel
  reorderSim doSwapSim planWf generatedPrefixSim planSpillBounds
  list sorting pred_set stackPlanGen venomInst finite_map rich_list indexedLists

Theorem full_support_select_spill_candidate_none:
  !stk targets dist n.
    stk <> [] /\
    (!op. MEM op stk /\ is_var_operand op ==> MEM op targets) ==>
    select_spill_candidate stk targets dist n = NONE
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `select_spill_candidate stk targets dist n` >> simp[] >>
  rename1 `select_spill_candidate stk targets dist n = SOME cand` >>
  drule select_spill_candidate_var_not_pending >> strip_tac >>
  `1 <= LENGTH stk` by (Cases_on `stk` >> gvs[]) >>
  drule_all planWfTheory.select_spill_candidate_bound >> strip_tac >>
  drule reorderSimTheory.stack_peek_mem >> strip_tac >>
  metis_tac[]
QED

Theorem full_support_reduce_depth_plan_identity:
  !fuel targets target f n ps.
    (!op. MEM op ps.ps_stack /\ is_var_operand op ==> MEM op targets) ==>
    reduce_depth_plan fuel targets target f n ps = ([],ps)
Proof
  Cases >> rpt gen_tac >> strip_tac >>
  simp[Once reduce_depth_plan_def] >>
  Cases_on `ps.ps_stack = []`
  >- simp[stack_get_unfixed_depth_def, stack_get_depth_def, stack_find_def] >>
  drule_all full_support_select_spill_candidate_none >> strip_tac >>
  Cases_on `stack_get_unfixed_depth target f n' ps.ps_stack` >> simp[]
QED

Theorem full_inventory_swap_preservation:
  !base targets ps d ops qs.
    lineage_inventory (set targets) ps /\ ps.ps_spilled = FEMPTY /\
    plan_slots_bounded base ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    d < LENGTH targets /\ ALL_DISTINCT targets /\
    do_swap d ps = (ops,qs) ==>
    lineage_inventory (set targets) qs /\ qs.ps_spilled = FEMPTY /\
    plan_slots_bounded base qs /\
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  fs[lineage_inventory_def, lineage_core_def] >>
  `LENGTH core = LENGTH targets` by metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  `d < LENGTH ps.ps_stack` by simp[] >>
  drule_all planSpillBoundsTheory.do_swap_slots_bounded >> strip_tac >>
  drule_all doSwapSimTheory.do_swap_multiplicity_layout >> strip_tac >>
  `qs = SND (do_swap d ps)` by simp[] >>
  `d < LENGTH core` by simp[] >>
  drule_all do_swap_core >> strip_tac >>
  `qs.ps_stack = REPLICATE m dead_stack_marker ++ stack_swap d core` by metis_tac[] >>
  qpat_x_assum `qs = SND _` kall_tac >>
  qpat_x_assum `(SND _).ps_stack = _` kall_tac >>
  simp[] >>
  qexistsl_tac [`m`, `stack_swap d core`] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem full_inventory_reorder_one_preservation:
  !base targets dfg ps idx op ops qs.
    ALL_DISTINCT targets /\ lineage_inventory (set targets) ps /\
    ps.ps_spilled = FEMPTY /\ plan_slots_bounded base ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    idx < LENGTH targets /\ MEM op targets /\
    reorder_one dfg targets idx op ps = (ops,qs) ==>
    lineage_inventory (set targets) qs /\ qs.ps_spilled = FEMPTY /\
    plan_slots_bounded base qs /\
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `!x. MEM x ps.ps_stack /\ is_var_operand x ==> MEM x targets` by
    (drule lineage_inventory_stack_subset >>
     simp[SUBSET_DEF] >> rpt strip_tac >>
     first_x_assum drule >>
     Cases_on `x = dead_stack_marker` >>
     gvs[dead_stack_marker_def, stackPlanTypesTheory.is_var_operand_def]) >>
  `!fuel f n. reduce_depth_plan fuel targets op f n ps = ([],ps)` by
    metis_tac[full_support_reduce_depth_plan_identity] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - 1 - idx)
                (LENGTH targets) ps.ps_stack`
  >- gvs[reorder_one_def, FLOOKUP_EMPTY] >>
  rename1 `stack_get_unfixed_depth op _ _ _ = SOME d` >>
  fs[] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def] >> disch_tac >>
  Cases_on `d = LENGTH targets - 1 - idx`
  >- gvs[] >>
  `lineage_inventory (set targets) ps` by simp[] >>
  drule stack_get_unfixed_depth_bound >> strip_tac >>
  drule stack_get_unfixed_depth_peek >> strip_tac >>
  fs[lineage_inventory_def, lineage_core_def] >>
  `LENGTH core = LENGTH targets` by metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  `LENGTH targets - 1 - idx < LENGTH core` by decide_tac >>
  `is_var_operand op` by (fs[EVERY_MEM] >> metis_tac[MEMBER_NOT_EMPTY]) >>
  `op <> dead_stack_marker` by
    (strip_tac >> gvs[dead_stack_marker_def, stackPlanTypesTheory.is_var_operand_def]) >>
  `stack_get_unfixed_depth op (LENGTH targets - 1 - idx) (LENGTH targets) core = SOME d` by
    (qpat_x_assum `stack_get_unfixed_depth _ _ _ _ = SOME _` mp_tac >>
     asm_rewrite_tac[] >>
     simp[stack_get_unfixed_depth_bottom_excluded, MEM_REPLICATE]) >>
  `d < LENGTH core` by metis_tac[stack_get_unfixed_depth_bound] >>
  `stack_peek d core = op` by metis_tac[stack_get_unfixed_depth_peek] >>
  `LENGTH targets < idx + (LENGTH ps.ps_stack + 1)` by simp[] >>
  fs[] >>
  Cases_on `operand_equiv dfg op (stack_peek (LENGTH targets - (idx + 1)) ps.ps_stack)`
  >- suspend "exchange" >>
  suspend "swaps"
QED

Resume full_inventory_reorder_one_preservation[exchange]:
  gvs[] >>
  `LENGTH targets - (idx + 1) < LENGTH core` by decide_tac >>
  `stack_peek (LENGTH targets - (idx + 1)) ps.ps_stack =
   stack_peek (LENGTH targets - (idx + 1)) core` by
    simp[stack_peek_def, EL_APPEND2] >>
  qspecl_then [`core`, `d`, `LENGTH targets - (idx + 1)`] mp_tac
    stack_poke_exchange_structural_wf >> simp[] >> strip_tac >>
  qexistsl_tac [`m`, `stack_poke (LENGTH targets - (idx + 1))
    (stack_peek d core) (stack_poke d (stack_peek (LENGTH targets - (idx + 1)) core) core)`] >>
  `LENGTH (stack_poke d (stack_peek (LENGTH targets - (idx + 1)) core) core) = LENGTH core` by
    simp[stack_poke_def] >>
  simp[stack_poke_bottom_extension] >>
  gvs[EVERY_MEM, stack_peek_def, EL_APPEND2] >>
  irule stack_poke_bottom_extension >> simp[]
QED

Resume full_inventory_reorder_one_preservation[swaps]:
  `lineage_inventory (set targets) ps` by
    (simp[lineage_inventory_def, lineage_core_def] >>
     qexistsl_tac [`m`, `core`] >> simp[]) >>
  pure_rewrite_tac[GSYM lineage_core_def, GSYM lineage_inventory_def] >>
  fs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `d < LENGTH targets` by simp[] >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by simp[] >>
  drule_all full_inventory_swap_preservation >> strip_tac >>
  qpat_x_assum `do_swap d ps = _` kall_tac >>
  irule full_inventory_swap_preservation >> simp[] >>
  qexistsl_tac [`LENGTH targets - (idx + 1)`, `swap2_ops`, `ps3`] >> simp[]
QED

Finalise full_inventory_reorder_one_preservation

Theorem full_inventory_reorder_fold_preservation[local]:
  !pairs base targets dfg acc ps.
    ALL_DISTINCT targets /\ lineage_inventory (set targets) ps /\
    ps.ps_spilled = FEMPTY /\ plan_slots_bounded base ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    EVERY (\(idx,op). idx < LENGTH targets /\ MEM op targets) pairs ==>
    lineage_inventory (set targets)
      (SND (FOLDL (\(ops,st) (idx,op).
        (\(step_ops,st'). (ops ++ step_ops,st'))
          (reorder_one dfg targets idx op st)) (acc,ps) pairs)) /\
    (SND (FOLDL (\(ops,st) (idx,op).
        (\(step_ops,st'). (ops ++ step_ops,st'))
          (reorder_one dfg targets idx op st)) (acc,ps) pairs)).ps_spilled = FEMPTY /\
    plan_slots_bounded base
      (SND (FOLDL (\(ops,st) (idx,op).
        (\(step_ops,st'). (ops ++ step_ops,st'))
          (reorder_one dfg targets idx op st)) (acc,ps) pairs)) /\
    spill_alloc_layout_wf
      (SND (FOLDL (\(ops,st) (idx,op).
        (\(step_ops,st'). (ops ++ step_ops,st'))
          (reorder_one dfg targets idx op st)) (acc,ps) pairs)).ps_alloc
      (SND (FOLDL (\(ops,st) (idx,op).
        (\(step_ops,st'). (ops ++ step_ops,st'))
          (reorder_one dfg targets idx op st)) (acc,ps) pairs)).ps_spilled
Proof
  Induct
  >- (simp[] >> rpt strip_tac >> gvs[]) >>
  gen_tac >> PairCases_on `h` >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `reorder_one dfg targets h0 h1 ps` >>
  drule_all full_inventory_reorder_one_preservation >> strip_tac >>
  qpat_assum `reorder_one _ _ _ _ _ = _`
    (fn th => pure_rewrite_tac[th, pairTheory.pair_case_thm]) >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  rule_assum_tac (CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)) >>
  first_x_assum irule >> simp[]
QED

Theorem full_inventory_reorder_plan_preservation:
  !base targets dfg ps ops qs.
    ALL_DISTINCT targets /\ lineage_inventory (set targets) ps /\
    ps.ps_spilled = FEMPTY /\ plan_slots_bounded base ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    reorder_plan dfg targets ps = (ops,qs) ==>
    lineage_inventory (set targets) qs /\ qs.ps_spilled = FEMPTY /\
    plan_slots_bounded base qs /\
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\(idx,op). idx < LENGTH targets /\ MEM op targets)
    (MAPi (\i op. (i,op)) targets)` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
     rpt strip_tac >> gvs[] >> metis_tac[MEM_EL]) >>
  drule_all full_inventory_reorder_fold_preservation >>
  disch_then (qspecl_then [`dfg`, `[]`] mp_tac) >>
  gvs[reorder_plan_def]
QED

Theorem restore_spilled_plan_resources:
  !targets base ps ops qs.
    plan_slots_bounded base ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    restore_spilled_plan targets ps = (ops,qs) ==>
    plan_slots_bounded base qs /\
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  Induct >- (simp[restore_spilled_plan_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `do_restore h ps` >>
  Cases_on `restore_spilled_plan targets r` >>
  gvs[restore_spilled_plan_def] >>
  drule_all do_restore_slots_bounded >> strip_tac >>
  drule_all do_restore_layout_wf >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem full_inventory_restore_reorder_preservation:
  !base targets dfg ps rops rs qops qs.
    ALL_DISTINCT targets /\ lineage_inventory (set targets) ps /\
    plan_slots_bounded base ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    restore_spilled_plan targets ps = (rops,rs) /\
    reorder_plan dfg targets rs = (qops,qs) ==>
    lineage_inventory (set targets) qs /\ qs.ps_spilled = FEMPTY /\
    plan_slots_bounded base qs /\
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule restore_spilled_plan_inventory_exhausted >>
  disch_then (qspec_then `targets` mp_tac) >> simp[] >> strip_tac >>
  drule restore_spilled_plan_lineage_inventory >>
  disch_then (qspec_then `targets` mp_tac) >> simp[] >> strip_tac >>
  drule_all restore_spilled_plan_resources >> strip_tac >>
  drule_all full_inventory_reorder_plan_preservation >> simp[]
QED

Theorem full_inventory_restore_reorder_budget:
  !base targets dfg ps rops rs qops qs.
    ALL_DISTINCT targets /\ lineage_inventory (set targets) ps /\
    plan_slots_bounded base ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    restore_spilled_plan targets ps = (rops,rs) /\
    reorder_plan dfg targets rs = (qops,qs) ==>
    lineage_inventory (set targets) qs /\ qs.ps_spilled = FEMPTY /\
    ?m core. lineage_core m core qs /\ EVERY is_var_operand core /\
      residual_budget_wf base [] (qs with ps_stack := core)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all full_inventory_restore_reorder_preservation >> strip_tac >>
  simp[] >>
  qpat_x_assum `lineage_inventory _ qs` mp_tac >>
  simp[lineage_inventory_def] >> strip_tac >>
  qexistsl_tac [`m`, `core`] >> simp[] >>
  irule residual_budget_wf_canonical >>
  gvs[lineage_core_def]
QED

Theorem do_swap_deep_out_of_range:
  !d ps ops qs.
    16 < d /\ LENGTH ps.ps_stack <= d /\ do_swap d ps = (ops,qs) ==>
    qs.ps_stack = MAP (\i. EL i ps.ps_stack)
      ([d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0]) /\
    qs.ps_spilled = ps.ps_spilled /\ LENGTH qs.ps_stack = d + 1
Proof
  rpt gen_tac >> strip_tac >>
  gvs[do_swap_def, top_n_def, TAKE_LENGTH_TOO_LONG] >>
  pairarg_tac >> gvs[] >> simp[]
QED

Theorem do_swap_deep_out_of_range_perm:
  !d ps ops qs.
    16 < d /\ LENGTH ps.ps_stack <= d /\ do_swap d ps = (ops,qs) ==>
    PERM qs.ps_stack
      (ps.ps_stack ++ GENLIST (\i. EL (LENGTH ps.ps_stack + i) ps.ps_stack)
        (d + 1 - LENGTH ps.ps_stack))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all do_swap_deep_out_of_range >> strip_tac >>
  `PERM qs.ps_stack
     (MAP (\i. EL i ps.ps_stack) (GENLIST I (d + 1)))` by
    (asm_rewrite_tac[] >> irule PERM_MAP >>
     qspec_then `d + 1` mp_tac desired_perm_indices >> simp[]) >>
  `d + 1 = LENGTH ps.ps_stack + (d + 1 - LENGTH ps.ps_stack)` by decide_tac >>
  qpat_x_assum `PERM _ _` mp_tac >>
  simp[MAP_GENLIST, combinTheory.o_DEF] >>
  qpat_x_assum `d + 1 = _` (fn th => once_rewrite_tac[th]) >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  simp[GENLIST_APPEND, GENLIST_ID, combinTheory.I_THM,
       arithmeticTheory.ADD_COMM]
QED

Theorem do_swap_deep_out_of_range_count:
  !d ps ops qs x.
    16 < d /\ LENGTH ps.ps_stack <= d /\ do_swap d ps = (ops,qs) ==>
    LIST_ELEM_COUNT x qs.ps_stack =
      LIST_ELEM_COUNT x ps.ps_stack +
      LIST_ELEM_COUNT x
        (GENLIST (\i. EL (LENGTH ps.ps_stack + i) ps.ps_stack)
          (d + 1 - LENGTH ps.ps_stack))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all do_swap_deep_out_of_range_perm >>
  simp[PERM_DEF] >> disch_then (qspec_then `x` mp_tac) >>
  `((\y. x = y) : operand -> bool) = ($= x)` by
    simp[FUN_EQ_THM] >>
  simp[LIST_ELEM_COUNT_DEF, FILTER_APPEND, FILTER_EQ, EQ_SYM_EQ] >>
  disch_then (mp_tac o AP_TERM ``LENGTH : operand list -> num``) >> simp[]
QED

(* Exact selector obstruction: HD [] alone does not simplify other ELs. *)
Theorem constant_target_first_overflow_iff:
  !dfg ps v.
    ps.ps_stack = [Var v] ==>
    ((SND (reorder_one dfg (REPLICATE 18 (Var v)) 0 (Var v) ps)).ps_stack =
       REPLICATE 18 (Var v) <=>
     EVERY (\i. EL i ([]:operand list) = Var v) (GENLIST I 17)) /\
    (SND (reorder_one dfg (REPLICATE 18 (Var v)) 0 (Var v) ps)).ps_spilled =
      ps.ps_spilled
Proof
  rpt strip_tac >>
  drule reorder_one_short_bulk_branch >>
  disch_then (qspec_then `dfg` assume_tac) >>
  simp[] >>
  qspecl_then [`17`, `ps`] mp_tac do_swap_deep_out_of_range >>
  simp[] >>
  disch_then (qspecl_then [`FST (do_swap 17 ps)`, `SND (do_swap 17 ps)`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[GENLIST_CONS, EL, REPLICATE] >>
  CONV_TAC (LAND_CONV (RAND_CONV EVAL)) >>
  pure_rewrite_tac[CONS_11] >> metis_tac[]
QED
