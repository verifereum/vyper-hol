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

Theorem bounded_do_swap_stack_perm:
  !d ps. d <= 16 \/ d < LENGTH ps.ps_stack ==>
    PERM (SND (do_swap d ps)).ps_stack ps.ps_stack
Proof
  rpt gen_tac >> strip_tac
  >- (Cases_on `d = 0` >- simp[do_swap_def] >>
      Cases_on `ps.ps_stack = []`
      >- simp[do_swap_def, stack_swap_def] >>
      `MIN d (LENGTH ps.ps_stack - 1) < LENGTH ps.ps_stack` by
        (Cases_on `ps.ps_stack` >> gvs[] >> decide_tac) >>
      Cases_on `LENGTH ps.ps_stack = 1`
      >- (Cases_on `ps.ps_stack` >>
          gvs[do_swap_def, stack_swap_def, LUPDATE_def]) >>
      `MIN d (LENGTH ps.ps_stack - 1) <> 0 /\
       MIN d (LENGTH ps.ps_stack - 1) <= 16 /\
       LENGTH ps.ps_stack - 1 - MIN d (LENGTH ps.ps_stack - 1) =
       LENGTH ps.ps_stack - 1 - d` by
        (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
      qspec_then `MIN d (LENGTH ps.ps_stack - 1)` mp_tac
        do_swap_stack_perm >>
      disch_then (qspec_then `ps` mp_tac) >>
      simp[do_swap_def, stack_swap_def])
  >> irule do_swap_stack_perm >> simp[]
QED

Theorem safe_full_support_reorder_one_perm:
  !targets dfg ps idx op ops qs.
    (!d:num. d < LENGTH targets /\ 16 < d ==> d < LENGTH ps.ps_stack) /\
    ps.ps_spilled = FEMPTY /\
    (!x. MEM x ps.ps_stack /\ is_var_operand x ==> MEM x targets) /\
    idx < LENGTH targets /\ MEM op targets /\
    reorder_one dfg targets idx op ps = (ops,qs) ==>
    PERM qs.ps_stack ps.ps_stack /\ qs.ps_spilled = FEMPTY
Proof
  rpt gen_tac >> strip_tac >>
  `!fuel f n. reduce_depth_plan fuel targets op f n ps = ([],ps)` by
    metis_tac[full_support_reduce_depth_plan_identity] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - 1 - idx)
    (LENGTH targets) ps.ps_stack` >> simp[] >> strip_tac >> gvs[] >>
  `x < LENGTH ps.ps_stack /\ stack_peek x ps.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_bound, stack_get_unfixed_depth_peek] >>

  Cases_on `x = LENGTH targets - (idx + 1)` >> gvs[] >>
  Cases_on `LENGTH targets < idx + (LENGTH ps.ps_stack + 1) /\
            0 < LENGTH ps.ps_stack` >> gvs[]
  >- (Cases_on `operand_equiv dfg (stack_peek x ps.ps_stack)
        (stack_peek (LENGTH targets - (idx + 1)) ps.ps_stack)` >> gvs[]
      >- (simp[stack_poke_def, stack_peek_def] >>
          irule lupdate_exchange_perm >> simp[]) >>
      suspend "swaps") >>
  suspend "swaps"
QED

Resume safe_full_support_reorder_one_perm[swaps]:
  markerLib.RESUME_TAC >> rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  `PERM ps3.ps_stack ps.ps_stack` by
    (qspec_then `x` (qspec_then `ps` mp_tac) do_swap_stack_perm >> gvs[]) >>
  `LENGTH ps3.ps_stack = LENGTH ps.ps_stack` by metis_tac[PERM_LENGTH] >>
  `PERM ps4.ps_stack ps3.ps_stack` by
    (qspec_then `LENGTH (targets:operand list) - (idx + 1)`
       (qspec_then `ps3` mp_tac) bounded_do_swap_stack_perm >>
     (impl_tac >- (
       `0 < LENGTH targets` by (Cases_on `targets` >> gvs[]) >>
       qpat_x_assum `!d. d < _ /\ _ ==> _`
         (qspec_then `LENGTH (targets:operand list) - (idx + 1)` mp_tac) >>
       decide_tac)) >> gvs[]) >>
  metis_tac[PERM_TRANS, do_swap_spilled_unchanged, pairTheory.SND]
QED

Finalise safe_full_support_reorder_one_perm

Theorem safe_full_support_reorder_fold_perm[local]:
  !pairs targets dfg acc ps.
    (!d:num. d < LENGTH targets /\ 16 < d ==> d < LENGTH ps.ps_stack) /\
    ps.ps_spilled = FEMPTY /\
    (!x. MEM x ps.ps_stack /\ is_var_operand x ==> MEM x targets) /\
    EVERY (\(idx,op). idx < LENGTH targets /\ MEM op targets) pairs ==>
    PERM (SND (FOLDL (\(ops,st) (idx,op).
      (\(step_ops,st'). (ops ++ step_ops,st'))
        (reorder_one dfg targets idx op st)) (acc,ps) pairs)).ps_stack ps.ps_stack /\
    (SND (FOLDL (\(ops,st) (idx,op).
      (\(step_ops,st'). (ops ++ step_ops,st'))
        (reorder_one dfg targets idx op st)) (acc,ps) pairs)).ps_spilled = FEMPTY
Proof
  Induct >- simp[] >>
  gen_tac >> PairCases_on `h` >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `reorder_one dfg targets h0 h1 ps` >>
  drule_all safe_full_support_reorder_one_perm >> strip_tac >>
  qpat_assum `reorder_one _ _ _ _ _ = _`
    (fn th => pure_rewrite_tac[th, pairTheory.pair_case_thm]) >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  rule_assum_tac (CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)) >>
  `!x. MEM x r.ps_stack /\ is_var_operand x ==> MEM x targets` by
    metis_tac[PERM_MEM_EQ] >>
  `LENGTH r.ps_stack = LENGTH ps.ps_stack` by metis_tac[PERM_LENGTH] >>
  first_x_assum (qspecl_then [`targets`, `dfg`, `acc ++ q`, `r`] mp_tac) >>
  simp[] >> metis_tac[PERM_TRANS]
QED

Theorem safe_full_support_reorder_perm:
  !targets dfg ps ops qs.
    (!d:num. d < LENGTH targets /\ 16 < d ==> d < LENGTH ps.ps_stack) /\
    ps.ps_spilled = FEMPTY /\
    (!x. MEM x ps.ps_stack /\ is_var_operand x ==> MEM x targets) /\
    reorder_plan dfg targets ps = (ops,qs) ==>
    PERM qs.ps_stack ps.ps_stack /\ qs.ps_spilled = FEMPTY
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\(idx,op). idx < LENGTH targets /\ MEM op targets)
    (MAPi (\i op. (i,op)) targets)` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
     rpt strip_tac >> gvs[] >> metis_tac[MEM_EL]) >>
  drule_all safe_full_support_reorder_fold_perm >>
  disch_then (qspecl_then [`dfg`, `[]`] mp_tac) >>
  gvs[reorder_plan_def]
QED

Theorem safe_restore_reorder_suffix_distinct:
  !targets dfg ps rops rs qops qs.
    (!d:num. d < LENGTH targets /\ 16 < d ==> d < LENGTH rs.ps_stack) /\
    lineage_inventory (set targets) ps /\
    restore_spilled_plan targets ps = (rops,rs) /\
    reorder_plan dfg targets rs = (qops,qs) /\
    stack_pop (LENGTH targets) qs.ps_stack ++ targets = qs.ps_stack ==>
    ALL_DISTINCT targets
Proof
  rpt gen_tac >> strip_tac >>
  `lineage_inventory (set targets) rs` by
    metis_tac[restore_spilled_plan_lineage_inventory, pairTheory.SND] >>
  `rs.ps_spilled = FEMPTY` by
    metis_tac[restore_spilled_plan_inventory_exhausted, SUBSET_REFL, pairTheory.SND] >>
  `!x. MEM x rs.ps_stack /\ is_var_operand x ==> MEM x targets` by
    (drule lineage_inventory_stack_subset >>
     simp[SUBSET_DEF, stackPlanTypesTheory.is_var_operand_def, dead_stack_marker_def] >>
     rpt strip_tac >> Cases_on `x` >> gvs[stackPlanTypesTheory.is_var_operand_def] >>
     first_x_assum drule >> simp[]) >>
  drule_all safe_full_support_reorder_perm >> strip_tac >>
  qpat_x_assum `lineage_inventory _ rs` mp_tac >>
  simp[lineage_inventory_def, lineage_core_def] >> strip_tac >>
  `FILTER (\op. op <> dead_stack_marker) core = core` by
    (simp[FILTER_EQ_ID, EVERY_MEM] >> rpt strip_tac >>
     gvs[EVERY_MEM] >> first_x_assum drule >>
     simp[stackPlanTypesTheory.is_var_operand_def, dead_stack_marker_def]) >>
  `FILTER (\op. op <> dead_stack_marker) targets = targets` by
    (simp[FILTER_EQ_ID, EVERY_MEM] >>
     `~MEM dead_stack_marker core` by
       (qpat_x_assum `FILTER _ core = core` mp_tac >>
        disch_then (mp_tac o AP_TERM ``MEM dead_stack_marker``) >>
        simp[MEM_FILTER]) >> ASM_SET_TAC[]) >>
  `FILTER (\op. op <> dead_stack_marker) (REPLICATE m dead_stack_marker) = []` by
    simp[FILTER_EQ_NIL, EVERY_MEM, MEM_REPLICATE] >>
  `ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) rs.ps_stack)` by
    simp[FILTER_APPEND] >>
  `ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) qs.ps_stack)` by
    metis_tac[PERM_FILTER, ALL_DISTINCT_PERM] >>
  qpat_x_assum `_ ++ targets = qs.ps_stack` mp_tac >>
  disch_then (mp_tac o AP_TERM ``FILTER (\op. op <> dead_stack_marker)``) >>
  simp[FILTER_APPEND] >> metis_tac[ALL_DISTINCT_APPEND]
QED

Theorem safe_restore_reorder_suffix_preservation:
  !base targets dfg ps rops rs qops qs.
    (!d:num. d < LENGTH targets /\ 16 < d ==> d < LENGTH rs.ps_stack) /\
    lineage_inventory (set targets) ps /\
    plan_slots_bounded base ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    restore_spilled_plan targets ps = (rops,rs) /\
    reorder_plan dfg targets rs = (qops,qs) /\
    stack_pop (LENGTH targets) qs.ps_stack ++ targets = qs.ps_stack ==>
    lineage_inventory (set targets) qs /\ qs.ps_spilled = FEMPTY /\
    plan_slots_bounded base qs /\
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all safe_restore_reorder_suffix_distinct >> strip_tac >>
  irule full_inventory_restore_reorder_preservation >>
  metis_tac[]
QED

Theorem target_window_select_spill_candidate_none:
  !stk forbidden dist n.
    1 <= LENGTH stk /\ LENGTH stk <= n ==>
    select_spill_candidate stk forbidden dist n = NONE
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `select_spill_candidate stk forbidden dist n` >> simp[] >>
  drule_all planWfTheory.select_spill_candidate_bound >> strip_tac >>
  drule planWfTheory.select_spill_candidate_below_target >> decide_tac
QED

Theorem target_window_reduce_depth_plan_identity:
  !fuel targets target f n ps.
    LENGTH ps.ps_stack <= n ==>
    reduce_depth_plan fuel targets target f n ps = ([],ps)
Proof
  Cases >> rpt gen_tac >> strip_tac >> simp[Once reduce_depth_plan_def] >>
  Cases_on `ps.ps_stack = []`
  >- simp[stack_get_unfixed_depth_def, stack_get_depth_def, stack_find_def] >>
  `1 <= LENGTH ps.ps_stack` by (Cases_on `ps.ps_stack` >> gvs[]) >>
  drule_all target_window_select_spill_candidate_none >> strip_tac >>
  Cases_on `stack_get_unfixed_depth target f n' ps.ps_stack` >> simp[]
QED

Theorem target_window_reorder_one_perm:
  !targets dfg ps idx op ops qs.
    ps.ps_spilled = FEMPTY /\ LENGTH ps.ps_stack = LENGTH targets /\
    idx < LENGTH targets /\ reorder_one dfg targets idx op ps = (ops,qs) ==>
    PERM qs.ps_stack ps.ps_stack /\ qs.ps_spilled = FEMPTY
Proof
  rpt gen_tac >> strip_tac >>
  `!fuel f. reduce_depth_plan fuel targets op f (LENGTH targets) ps = ([],ps)` by
    (rpt gen_tac >> irule target_window_reduce_depth_plan_identity >> simp[]) >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - 1 - idx)
    (LENGTH targets) ps.ps_stack` >> simp[] >> strip_tac >> gvs[] >>
  `x < LENGTH ps.ps_stack /\ stack_peek x ps.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_bound, stack_get_unfixed_depth_peek] >>
  Cases_on `x = LENGTH targets - (idx + 1)` >> gvs[] >>
  `LENGTH targets - (idx + 1) < LENGTH ps.ps_stack` by decide_tac >>
  simp[] >>
  Cases_on `operand_equiv dfg (stack_peek x ps.ps_stack)
    (stack_peek (LENGTH targets - (idx + 1)) ps.ps_stack)` >> gvs[]
  >- (simp[stack_poke_def, stack_peek_def] >>
      irule lupdate_exchange_perm >> simp[]) >>
  rpt (pairarg_tac >> gvs[]) >>
  `PERM ps3.ps_stack ps.ps_stack` by
    (qspec_then `x` (qspec_then `ps` mp_tac) do_swap_stack_perm >> gvs[]) >>
  `LENGTH ps3.ps_stack = LENGTH ps.ps_stack` by metis_tac[PERM_LENGTH] >>
  `PERM ps4.ps_stack ps3.ps_stack` by
    (qspec_then `LENGTH (targets:operand list) - (idx + 1)`
       (qspec_then `ps3` mp_tac) do_swap_stack_perm >> simp[]) >>
  metis_tac[PERM_TRANS, do_swap_spilled_unchanged, pairTheory.SND]
QED

Theorem target_window_reorder_fold_perm:
  !pairs targets dfg acc ps.
    ps.ps_spilled = FEMPTY /\ LENGTH ps.ps_stack = LENGTH targets /\
    EVERY (\(idx,op). idx < LENGTH targets) pairs ==>
    PERM (SND (FOLDL (\(ops,st) (idx,op).
      (\(step_ops,st'). (ops ++ step_ops,st'))
        (reorder_one dfg targets idx op st)) (acc,ps) pairs)).ps_stack ps.ps_stack /\
    (SND (FOLDL (\(ops,st) (idx,op).
      (\(step_ops,st'). (ops ++ step_ops,st'))
        (reorder_one dfg targets idx op st)) (acc,ps) pairs)).ps_spilled = FEMPTY
Proof
  Induct >- simp[] >>
  gen_tac >> PairCases_on `h` >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `reorder_one dfg targets h0 h1 ps` >>
  drule_all target_window_reorder_one_perm >> strip_tac >>
  qpat_assum `reorder_one _ _ _ _ _ = _`
    (fn th => pure_rewrite_tac[th, pairTheory.pair_case_thm]) >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  rule_assum_tac (CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)) >>
  `LENGTH r.ps_stack = LENGTH targets` by metis_tac[PERM_LENGTH] >>
  first_x_assum (qspecl_then [`targets`, `dfg`, `acc ++ q`, `r`] mp_tac) >>
  simp[] >> metis_tac[PERM_TRANS]
QED

Theorem full_support_first_reorder_overflow:
  !targets dfg ps d ops qs.
    ps.ps_spilled = FEMPTY /\
    (!x. MEM x ps.ps_stack /\ is_var_operand x ==> MEM x targets) /\
    LENGTH ps.ps_stack < LENGTH targets /\ 17 < LENGTH targets /\
    stack_get_depth (HD targets) ps.ps_stack = SOME d /\
    reorder_one dfg targets 0 (HD targets) ps = (ops,qs) ==>
    ?swap_ops mid.
      do_swap d ps = (swap_ops,mid) /\
      PERM mid.ps_stack ps.ps_stack /\
      LENGTH qs.ps_stack = LENGTH targets /\ qs.ps_spilled = FEMPTY /\
      PERM qs.ps_stack
        (mid.ps_stack ++ GENLIST (\i. EL (LENGTH mid.ps_stack + i) mid.ps_stack)
          (LENGTH targets - LENGTH mid.ps_stack))
Proof
  rpt gen_tac >> strip_tac >>
  `d < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  `!fuel f n. reduce_depth_plan fuel targets (HD targets) f n ps = ([],ps)` by
    metis_tac[full_support_reduce_depth_plan_identity] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, stack_get_unfixed_depth_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `do_swap (LENGTH targets - 1) ps3 = (swap2_ops,qs)` >>
  `PERM ps3.ps_stack ps.ps_stack` by
    (qspec_then `d` (qspec_then `ps` mp_tac) do_swap_stack_perm >> gvs[]) >>
  `LENGTH ps3.ps_stack = LENGTH ps.ps_stack` by metis_tac[PERM_LENGTH] >>
  `16 < LENGTH targets - 1 /\ LENGTH ps3.ps_stack <= LENGTH targets - 1` by
    decide_tac >>
  drule_all do_swap_deep_out_of_range_perm >> strip_tac >>
  `LENGTH qs.ps_stack = LENGTH targets` by
    (drule PERM_LENGTH >> simp[] >> decide_tac) >>
  `qs.ps_spilled = FEMPTY` by
    metis_tac[do_swap_spilled_unchanged, pairTheory.SND] >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem full_support_successful_reorder_overflow:
  !targets dfg rs ops qs.
    lineage_inventory (set targets) rs /\ rs.ps_spilled = FEMPTY /\
    LENGTH rs.ps_stack < LENGTH targets /\ 17 < LENGTH targets /\
    reorder_plan dfg targets rs = (ops,qs) /\
    stack_pop (LENGTH targets) qs.ps_stack ++ targets = qs.ps_stack ==>
    ?first_ops first_state d swap_ops mid.
      reorder_one dfg targets 0 (HD targets) rs = (first_ops,first_state) /\
      stack_get_depth (HD targets) rs.ps_stack = SOME d /\
      do_swap d rs = (swap_ops,mid) /\ PERM mid.ps_stack rs.ps_stack /\
      LENGTH first_state.ps_stack = LENGTH targets /\
      PERM targets first_state.ps_stack /\
      PERM first_state.ps_stack
        (mid.ps_stack ++ GENLIST (\i. EL (LENGTH mid.ps_stack + i) mid.ps_stack)
          (LENGTH targets - LENGTH mid.ps_stack))
Proof
  Cases >- simp[] >> rpt gen_tac >> strip_tac >>
  `MEM h rs.ps_stack` by
    (gvs[lineage_inventory_def, lineage_core_def, EXTENSION] >>
     metis_tac[MEM_APPEND, MEM]) >>
  `?d. stack_get_depth h rs.ps_stack = SOME d` by
    (Cases_on `stack_get_depth h rs.ps_stack`
     >- (gvs[stack_get_depth_NONE, stack_peek_def] >>
         qpat_x_assum `MEM h rs.ps_stack`
           (strip_assume_tac o REWRITE_RULE[MEM_EL]) >>
         qpat_x_assum `!d. d < _ ==> _`
           (qspec_then `LENGTH rs.ps_stack - (n + 1)` mp_tac) >>
         simp[]) >> metis_tac[]) >>
  `!x. MEM x rs.ps_stack /\ is_var_operand x ==> MEM x (h::t)` by
    (drule lineage_inventory_stack_subset >>
     simp[pred_setTheory.SUBSET_DEF] >>
     metis_tac[stackPlanTypesTheory.is_var_operand_def, dead_stack_marker_def]) >>
  Cases_on `reorder_one dfg (h::t) 0 h rs` >>
  fs[] >>
  drule_all (Q.SPEC `h::t` full_support_first_reorder_overflow |> SRULE[HD]) >>
  strip_tac >>
  qexistsl_tac [`swap_ops`, `mid`] >> simp[arithmeticTheory.ADD_COMM] >>
  `EVERY (\(idx,op). idx < LENGTH (h::t))
    (MAPi (\i op. (SUC i,op)) t)` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
     rpt strip_tac >> gvs[]) >>
  qpat_assum `r.ps_spilled = FEMPTY`
    (mp_then Any mp_tac target_window_reorder_fold_perm) >>
  disch_then (qspecl_then [`MAPi (\i op. (SUC i,op)) t`, `h::t`, `dfg`, `q`] mp_tac) >>
  simp[] >>
  qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
  simp[reorder_plan_def, indexedListsTheory.MAPi_def] >>
  simp[combinTheory.o_DEF] >> strip_tac >> gvs[] >> strip_tac >>
  `LENGTH qs.ps_stack = SUC (LENGTH t)` by metis_tac[PERM_LENGTH] >>
  gvs[stack_pop_def, arithmeticTheory.ADD_COMM]
QED
