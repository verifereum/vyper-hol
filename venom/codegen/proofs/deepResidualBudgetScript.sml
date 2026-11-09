(*
 * The marker-tolerant residual budgets behind deepResidualSim, and the
 * planner steps of input emission and reorder that preserve them.
 *
 * residual_budget_wf_marked and plan_state_residual_wf_marked are
 * reorderSim's residual_budget_wf and plan_state_residual_wf with the
 * per-operand stack count exempting dead_stack_marker, which a cleanup
 * elision leaves in several slots, and the marker kept out of the spill map.
 *
 * TOP-LEVEL:
 *   residual_budget_wf_marked, plan_state_residual_wf_marked
 *                                           - the marker-tolerant budgets
 *   emit_input_plan_residual_budget_wf_marked
 *                                           - input emission keeps the budget
 *   reorder_plan_residual_budget_wf_marked  - reordering keeps the budget,
 *                                             the inventory and the length
 *                                             floor, with no bound on the
 *                                             number of targets
 *)

Theory deepResidualBudget
Ancestors
  fnPlanPrefix preparedPrefixSim generatedPrefixSim generatedReorderSim
  genericInputReady reorderSim doSwapSim codegenRel asmSem planExec
  stackPlanGen stackPlanOps stackPlanTypes stackModel blockSimHelpers planWf planSpillBounds foldlSim
  reorderSpillFresh prefixSpillReplay scratchPrefixSim spillSim stackOpSim
  list rich_list finite_map arithmetic
Libs BasicProvers

Definition residual_budget_wf_marked_def:
  residual_budget_wf_marked base pending (ps : plan_state) <=>
    plan_slots_bounded base ps /\
    doSwapSim$spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    dead_stack_marker NOTIN FDOM ps.ps_spilled /\
    (!op. op <> dead_stack_marker ==>
          LIST_ELEM_COUNT op ps.ps_stack <=
          SUC (LIST_ELEM_COUNT op pending)) /\
    (!op. op IN FDOM ps.ps_spilled ==>
          LIST_ELEM_COUNT op ps.ps_stack <= LIST_ELEM_COUNT op pending)
End

Definition plan_state_residual_wf_marked_def:
  plan_state_residual_wf_marked base pending fixed (ps : plan_state) <=>
    plan_slots_bounded base ps /\
    doSwapSim$spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    dead_stack_marker NOTIN FDOM ps.ps_spilled /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    fixed <= LENGTH pending /\
    (!i. i < fixed ==>
       stack_peek (LENGTH pending - 1 - i) ps.ps_stack = EL i pending) /\
    (!op. op <> dead_stack_marker ==>
          LIST_ELEM_COUNT op ps.ps_stack <=
          SUC (LIST_ELEM_COUNT op pending)) /\
    (!op. op IN FDOM ps.ps_spilled ==>
          LIST_ELEM_COUNT op ps.ps_stack <= LIST_ELEM_COUNT op pending)
End


Theorem var_operand_not_marker:
  !op. is_var_operand op ==> op <> dead_stack_marker
Proof
  Cases >> simp[is_var_operand_def, dead_stack_marker_def]
QED

Theorem elem_count_replicate:
  !k (x : 'a) y.
    LIST_ELEM_COUNT x (REPLICATE k y) = if x = y then k else 0
Proof
  Induct >> rpt gen_tac
  >- simp[LIST_ELEM_COUNT_THM] >>
  Cases_on `x = y`
  >- gvs[LIST_ELEM_COUNT_THM] >>
  `y <> x` by simp[] >> simp[LIST_ELEM_COUNT_THM]
QED

(* The marked budget is the unmarked one with the stack's markers added to
   the pending list. *)
Theorem residual_budget_wf_marked_pad:
  !base pending ps.
    residual_budget_wf_marked base pending ps ==>
    residual_budget_wf base
      (pending ++ REPLICATE (LIST_ELEM_COUNT dead_stack_marker ps.ps_stack)
                    dead_stack_marker) ps
Proof
  rw[residual_budget_wf_marked_def, residual_budget_wf_def,
     LIST_ELEM_COUNT_THM, elem_count_replicate]
  >- (Cases_on `op = dead_stack_marker` >> simp[]) >>
  `op <> dead_stack_marker` by (strip_tac >> gvs[]) >>
  simp[]
QED

Theorem residual_budget_wf_unpad:
  !base pending pending' ps.
    residual_budget_wf base pending' ps /\
    (!op. op <> dead_stack_marker ==>
          LIST_ELEM_COUNT op pending' = LIST_ELEM_COUNT op pending) /\
    dead_stack_marker NOTIN FDOM ps.ps_spilled ==>
    residual_budget_wf_marked base pending ps
Proof
  rw[residual_budget_wf_marked_def, residual_budget_wf_def] >>
  `op <> dead_stack_marker` by (strip_tac >> gvs[]) >>
  metis_tac[]
QED

Theorem residual_budget_wf_marked_perm:
  !xs ys base ps. PERM xs ys ==>
    (residual_budget_wf_marked base xs ps <=>
     residual_budget_wf_marked base ys ps)
Proof
  rpt strip_tac >> drule perm_operand_counts >>
  simp[residual_budget_wf_marked_def]
QED

Theorem do_dup_spilled_eq:
  !dist ps ops ps'.
    do_dup dist ps = (ops, ps') ==> ps'.ps_spilled = ps.ps_spilled
Proof
  rw[do_dup_def, LET_THM] >> rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem emit_one_input_not_spilled:
  !opc nl op ps ops ps' x.
    emit_one_input opc nl op ps = (ops, ps') /\
    x NOTIN FDOM ps.ps_spilled ==>
    x NOTIN FDOM ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> Cases_on `op` >>
  gvs[emit_one_input_def, is_var_operand_def, do_restore_def, LET_THM] >>
  rpt (FULL_CASE_TAC >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac do_dup_spilled_eq >> gvs[finite_mapTheory.FDOM_DOMSUB]
QED

Theorem emit_input_plan_not_spilled:
  !operands opc nl ps ops ps' x.
    emit_input_plan opc operands nl ps = (ops, ps') /\
    x NOTIN FDOM ps.ps_spilled ==>
    x NOTIN FDOM ps'.ps_spilled
Proof
  Induct >> simp[emit_input_plan_cons] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_all emit_one_input_not_spilled >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem emit_one_input_residual_budget_wf_marked:
  !base pending opc nl op ps ops ps'.
    residual_budget_wf_marked base pending ps /\
    emit_one_input opc nl op ps = (ops, ps') ==>
    residual_budget_wf_marked base (pending ++ [op]) ps'
Proof
  rpt strip_tac >>
  drule residual_budget_wf_marked_pad >> strip_tac >>
  drule_all emit_one_input_residual_budget_wf >> strip_tac >>
  qpat_x_assum `residual_budget_wf_marked _ _ _`
    (strip_assume_tac o REWRITE_RULE [residual_budget_wf_marked_def]) >>
  drule_all emit_one_input_not_spilled >> strip_tac >>
  qspecl_then [`base'`, `pending ++ [op]`,
    `(pending ++ REPLICATE (LIST_ELEM_COUNT dead_stack_marker
        ps.ps_stack) dead_stack_marker) ++ [op]`, `ps'`]
    irule residual_budget_wf_unpad >>
  simp[LIST_ELEM_COUNT_THM, elem_count_replicate] >>
  qexists_tac `ps` >> fs[]
QED

Theorem emit_input_plan_residual_budget_wf_marked:
  !operands base pending opc nl ps iops ps1.
    residual_budget_wf_marked base pending ps /\
    emit_input_plan opc operands nl ps = (iops,ps1) ==>
    residual_budget_wf_marked base (pending ++ operands) ps1
Proof
  rpt strip_tac >>
  drule residual_budget_wf_marked_pad >> strip_tac >>
  drule_all emit_input_plan_residual_budget_wf >> strip_tac >>
  qpat_x_assum `residual_budget_wf_marked _ _ _`
    (strip_assume_tac o REWRITE_RULE [residual_budget_wf_marked_def]) >>
  drule_all emit_input_plan_not_spilled >> strip_tac >>
  qspecl_then [`base'`, `pending ++ operands`,
    `(pending ++ REPLICATE (LIST_ELEM_COUNT dead_stack_marker
        ps.ps_stack) dead_stack_marker) ++ operands`, `ps1`]
    irule residual_budget_wf_unpad >>
  simp[LIST_ELEM_COUNT_THM, elem_count_replicate] >>
  qexists_tac `ps` >> fs[]
QED

(* ===== Reorder steps over the marked budget =====
   reorder_one reads LENGTH target_ops, so padding the pending list with
   markers would change the plan; these follow reorderSim's unmarked proofs
   directly, without its LENGTH pending <= 16 bound. *)

Theorem elem_count_sing[local]:
  !x (y : 'a). LIST_ELEM_COUNT x [y] = if x = y then 1 else 0
Proof
  rw[LIST_ELEM_COUNT_DEF] >> gvs[]
QED

Theorem select_spill_candidate_props:
  !stk forbidden dist target_len cand.
    select_spill_candidate stk forbidden dist target_len = SOME cand ==>
    target_len <= cand /\ ~MEM (stack_peek cand stk) forbidden /\
    is_var_operand (stack_peek cand stk)
Proof
  rpt gen_tac >> simp[select_spill_candidate_def, LET_THM] >>
  strip_tac >> imp_res_tac FIND_SOME_MEM >> gvs[]
QED

Theorem do_spill_at_length[local]:
  !d ps.
    d < LENGTH ps.ps_stack ==>
    LENGTH (SND (do_spill_at d ps)).ps_stack = LENGTH ps.ps_stack - 1
Proof
  rpt gen_tac >> strip_tac >>
  simp[do_spill_at_def, do_spill_tos_def, LET_THM] >>
  Cases_on `d = 0` >> simp[stack_pop_def] >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[stack_pop_def]
QED

Theorem do_spill_at_spilled_update:
  !d ps ops ps'.
    d < LENGTH ps.ps_stack /\ do_spill_at d ps = (ops, ps') ==>
    ?off. ps'.ps_spilled = ps.ps_spilled |+ (stack_peek d ps.ps_stack, off)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `d = 0`
  >- (gvs[do_spill_at_def, do_spill_tos_def, LET_THM] >>
      Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[] >> metis_tac[]) >>
  `stack_peek 0 (stack_swap d ps.ps_stack) = stack_peek d ps.ps_stack` by
    (simp[stack_peek_def, stack_swap_def, LET_THM, EL_LUPDATE] >>
     IF_CASES_TAC >> gvs[] >> decide_tac) >>
  gvs[do_spill_at_def, do_spill_tos_def, LET_THM] >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[] >> metis_tac[]
QED

(* select_spill_candidate only picks offsets at or above target_len, so a
   depth reduction never cuts the stack below target_len. *)
Theorem reduce_depth_plan_target_len_floor:
  !fuel target_ops target_op f target_len ps ops ps'.
    reduce_depth_plan fuel target_ops target_op f target_len ps = (ops, ps') /\
    target_len <= LENGTH ps.ps_stack ==>
    target_len <= LENGTH ps'.ps_stack
Proof
  Induct >- simp[reduce_depth_plan_def] >>
  rpt gen_tac >> simp[Once reduce_depth_plan_def, LET_THM] >>
  Cases_on `f + 1 < target_len` >> simp[] >>
  TRY (strip_tac >> gvs[] >> NO_TAC) >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack` >>
  simp[] >> TRY (strip_tac >> gvs[] >> NO_TAC) >>
  Cases_on `x <= 16` >> simp[] >> TRY (strip_tac >> gvs[] >> NO_TAC) >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x target_len` >>
  simp[] >> TRY (strip_tac >> gvs[] >> NO_TAC) >>
  pairarg_tac >> simp[] >>
  rename1 `do_spill_at cand ps = (spill_ops, ps1)` >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule stack_get_unfixed_depth_bound >> strip_tac >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  `cand < LENGTH ps.ps_stack` by metis_tac[select_spill_candidate_bound] >>
  drule select_spill_candidate_props >> strip_tac >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack - 1` by
    (qspecl_then [`cand`, `ps`] mp_tac do_spill_at_length >> simp[]) >>
  `target_len <= LENGTH ps1.ps_stack` by decide_tac >>
  metis_tac[]
QED

Theorem residual_budget_wf_marked_do_swap:
  !base pending dist ps ops ps'.
    residual_budget_wf_marked base pending ps /\
    dist < LENGTH ps.ps_stack /\
    do_swap dist ps = (ops, ps') ==>
    residual_budget_wf_marked base pending ps'
Proof
  rpt gen_tac >> strip_tac >>
  fs[residual_budget_wf_marked_def] >>
  imp_res_tac do_swap_slots_bounded >>
  imp_res_tac do_swap_multiplicity_layout >> gvs[]
QED

Theorem residual_budget_wf_marked_stack_poke_exchange:
  !base pending ps d1 d2.
    residual_budget_wf_marked base pending ps /\
    d1 < LENGTH ps.ps_stack /\ d2 < LENGTH ps.ps_stack ==>
    residual_budget_wf_marked base pending
      (ps with ps_stack :=
        stack_poke d2 (stack_peek d1 ps.ps_stack)
          (stack_poke d1 (stack_peek d2 ps.ps_stack) ps.ps_stack))
Proof
  rpt strip_tac >>
  fs[residual_budget_wf_marked_def, stack_poke_exchange_multiplicity]
QED

Theorem residual_budget_wf_marked_restore:
  !base pending op ps ops ps'.
    residual_budget_wf_marked base pending ps /\
    do_restore op ps = (ops, ps') ==>
    residual_budget_wf_marked base pending ps'
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `residual_budget_wf_marked sb pending ps` >>
  `plan_slots_bounded sb ps'` by
    metis_tac[do_restore_slots_bounded, residual_budget_wf_marked_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op`
  >- gvs[do_restore_def] >>
  rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  `op IN FDOM ps.ps_spilled` by fs[finite_mapTheory.flookup_thm] >>
  fs[residual_budget_wf_marked_def] >>
  `op <> dead_stack_marker` by (strip_tac >> gvs[]) >>
  gvs[do_restore_def, stack_push_def, SNOC_APPEND, LIST_ELEM_COUNT_THM,
      elem_count_sing, finite_mapTheory.FDOM_DOMSUB] >>
  rpt conj_tac
  >- metis_tac[spill_alloc_layout_wf_after_free]
  >- (rpt strip_tac >> rw[] >> res_tac >> decide_tac)
  >> rpt strip_tac >> rw[] >> res_tac >> decide_tac
QED

Theorem residual_budget_wf_marked_do_spill_at:
  !base pending d ps ops ps'.
    residual_budget_wf_marked base pending ps /\
    d < LENGTH ps.ps_stack /\ d <= 16 /\
    ~MEM (stack_peek d ps.ps_stack) pending /\
    stack_peek d ps.ps_stack <> dead_stack_marker /\
    do_spill_at d ps = (ops, ps') ==>
    residual_budget_wf_marked base pending ps'
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `v = stack_peek d ps.ps_stack` >>
  `!x. LIST_ELEM_COUNT x ps'.ps_stack + LIST_ELEM_COUNT x [v] =
       LIST_ELEM_COUNT x ps.ps_stack` by
    metis_tac[do_spill_at_stack_count] >>
  `?off. ps'.ps_spilled = ps.ps_spilled |+ (v, off)` by
    metis_tac[do_spill_at_spilled_update] >>
  `LIST_ELEM_COUNT v pending = 0` by fs[GSYM LIST_ELEM_COUNT_MEM] >>
  rename1 `residual_budget_wf_marked sb pending ps` >>
  fs[residual_budget_wf_marked_def] >>
  `plan_slots_bounded sb ps'` by metis_tac[do_spill_at_slots_bounded] >>
  `spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled` by
    metis_tac[do_spill_at_layout_wf] >>
  `dead_stack_marker <> v` by metis_tac[] >>
  `!x. LIST_ELEM_COUNT x ps'.ps_stack <= LIST_ELEM_COUNT x ps.ps_stack` by
    (gen_tac >> qpat_assum `!x. _ + _ = _` (qspec_then `x` mp_tac) >>
     decide_tac) >>
  `LIST_ELEM_COUNT v ps'.ps_stack + 1 = LIST_ELEM_COUNT v ps.ps_stack` by
    (`LIST_ELEM_COUNT v [v] = 1` by simp[elem_count_sing] >>
     qpat_assum `!x. _ + _ = _` (qspec_then `v` mp_tac) >>
     decide_tac) >>
  `LIST_ELEM_COUNT v ps.ps_stack <= 1` by
    (`LIST_ELEM_COUNT v ps.ps_stack <= SUC (LIST_ELEM_COUNT v pending)` by
       metis_tac[] >> decide_tac) >>
  gvs[finite_mapTheory.FDOM_FUPDATE] >> rpt strip_tac
  >- (res_tac >>
      qpat_assum `!x. LIST_ELEM_COUNT x ps'.ps_stack <= _`
        (qspec_then `op` assume_tac) >> decide_tac)
  >- simp[]
  >> res_tac >>
     qpat_assum `!x. LIST_ELEM_COUNT x ps'.ps_stack <= _`
       (qspec_then `op` assume_tac) >> decide_tac
QED

Theorem select_spill_candidate_not_spilled_marked:
  !base pending ps dist target_len d.
    residual_budget_wf_marked base pending ps /\
    1 <= LENGTH ps.ps_stack /\
    select_spill_candidate ps.ps_stack pending dist target_len = SOME d ==>
    stack_peek d ps.ps_stack NOTIN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all select_spill_candidate_bound >> strip_tac >>
  drule select_spill_candidate_props >> strip_tac >>
  strip_tac >> fs[residual_budget_wf_marked_def] >>
  qpat_assum `!op. op IN FDOM ps.ps_spilled ==> _`
    (qspec_then `stack_peek d ps.ps_stack` (drule_then assume_tac)) >>
  `MEM (stack_peek d ps.ps_stack) ps.ps_stack` by
    (rewrite_tac[stack_peek_def] >> irule EL_MEM >> decide_tac) >>
  fs[GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem do_spill_at_inventory_count_marked[local]:
  !d ps ops ps'.
    d < LENGTH ps.ps_stack /\ d <= 16 /\
    stack_peek d ps.ps_stack NOTIN FDOM ps.ps_spilled /\
    do_spill_at d ps = (ops, ps') ==>
    !x.
      LIST_ELEM_COUNT x ps'.ps_stack +
        (if x IN FDOM ps'.ps_spilled then 1 else 0) =
      LIST_ELEM_COUNT x ps.ps_stack +
        (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt strip_tac >>
  `LIST_ELEM_COUNT x ps'.ps_stack +
     LIST_ELEM_COUNT x [stack_peek d ps.ps_stack] =
   LIST_ELEM_COUNT x ps.ps_stack` by metis_tac[do_spill_at_stack_count] >>
  drule_all do_spill_at_spilled_update >> strip_tac >>
  Cases_on `x = stack_peek d ps.ps_stack` >>
  gvs[finite_mapTheory.FDOM_FUPDATE, elem_count_sing]
QED

Theorem reduce_depth_plan_residual_budget_wf_marked:
  !fuel base pending target_op f ps ops ps'.
    residual_budget_wf_marked base pending ps /\
    reduce_depth_plan fuel pending target_op f (LENGTH pending) ps =
      (ops, ps') ==>
    residual_budget_wf_marked base pending ps'
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth target_op f (LENGTH pending)
              ps.ps_stack` >> gvs[] >>
  Cases_on `f + 1 < LENGTH pending` >> gvs[] >>
  Cases_on `x <= 16` >> gvs[] >>
  Cases_on `select_spill_candidate ps.ps_stack pending x
              (LENGTH pending)` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `do_spill_at cand ps = (spill_ops, ps1)` >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> simp[]) >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    metis_tac[select_spill_candidate_bound] >>
  drule select_spill_candidate_props >> strip_tac >>
  `stack_peek cand ps.ps_stack <> dead_stack_marker` by
    metis_tac[var_operand_not_marker] >>
  `residual_budget_wf_marked base' pending ps1` by
    metis_tac[residual_budget_wf_marked_do_spill_at] >>
  Cases_on `reduce_depth_plan fuel pending target_op f (LENGTH pending) ps1` >>
  gvs[] >> metis_tac[]
QED

Theorem reduce_depth_plan_pending_inventory_mono_marked:
  !fuel pending target_op f ps ops ps' base x.
    residual_budget_wf_marked base pending ps /\
    reduce_depth_plan fuel pending target_op f (LENGTH pending) ps =
      (ops,ps') ==>
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x ps'.ps_stack +
      (if x IN FDOM ps'.ps_spilled then 1 else 0)
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth target_op f (LENGTH pending)
              ps.ps_stack` >> gvs[] >>
  Cases_on `f + 1 < LENGTH pending` >> gvs[] >>
  Cases_on `x' <= 16` >> gvs[] >>
  Cases_on `select_spill_candidate ps.ps_stack pending x'
              (LENGTH pending)` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `do_spill_at cand ps = (spill_ops,ps1)` >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> simp[]) >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    metis_tac[select_spill_candidate_bound] >>
  drule select_spill_candidate_props >> strip_tac >>
  `stack_peek cand ps.ps_stack <> dead_stack_marker` by
    metis_tac[var_operand_not_marker] >>
  `stack_peek cand ps.ps_stack NOTIN FDOM ps.ps_spilled` by
    metis_tac[select_spill_candidate_not_spilled_marked] >>
  `!y. LIST_ELEM_COUNT y ps1.ps_stack +
       (if y IN FDOM ps1.ps_spilled then 1 else 0) =
       LIST_ELEM_COUNT y ps.ps_stack +
       (if y IN FDOM ps.ps_spilled then 1 else 0)` by
    (qspecl_then [`cand`, `ps`, `spill_ops`, `ps1`] mp_tac
       do_spill_at_inventory_count_marked >> simp[]) >>
  `residual_budget_wf_marked base' pending ps1` by
    metis_tac[residual_budget_wf_marked_do_spill_at] >>
  Cases_on `reduce_depth_plan fuel pending target_op f
              (LENGTH pending) ps1` >> gvs[] >>
  first_x_assum
    (qspecl_then [`pending`, `target_op`, `f`, `ps1`, `q`, `ps'`,
                  `base'`, `x`] mp_tac) >>
  simp[] >>
  qpat_assum `!y. _` (qspec_then `x` assume_tac) >>
  decide_tac
QED

Theorem reorder_restore_residual_budget_wf_marked:
  !base pending op f ps.
    residual_budget_wf_marked base pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack ==>
    let (_,ps') =
      case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
        SOME _ => ([] : stack_op list, ps)
      | NONE =>
          (case FLOOKUP ps.ps_spilled op of
             SOME _ => do_restore op ps
           | NONE => ([], ps))
    in residual_budget_wf_marked base pending ps' /\
       LENGTH pending <= LENGTH ps'.ps_stack
Proof
  rpt strip_tac >> simp[LET_THM] >>
  Cases_on `stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack` >>
  simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  Cases_on `do_restore op ps` >> gvs[] >>
  conj_tac
  >- (qspecl_then [`base'`, `pending`, `op`, `ps`, `q`, `r`] mp_tac
        residual_budget_wf_marked_restore >> simp[])
  >> qspecl_then [`op`, `ps`] mp_tac do_restore_length >> simp[]
QED

Theorem do_restore_inventory_count_marked[local]:
  !(ps : plan_state) op off x.
    FLOOKUP ps.ps_spilled op = SOME off ==>
    LIST_ELEM_COUNT x (SND (do_restore op ps)).ps_stack +
      (if x IN FDOM (SND (do_restore op ps)).ps_spilled then 1 else 0) =
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt strip_tac >>
  simp[do_restore_def, stack_push_def, SNOC_APPEND, LIST_ELEM_COUNT_THM,
       elem_count_sing, finite_mapTheory.FDOM_DOMSUB] >>
  Cases_on `x = op` >> gvs[finite_mapTheory.flookup_thm]
QED

Theorem reorder_restore_inventory_mono_marked[local]:
  !op f target_len (ps : plan_state) x.
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x
      (SND (case stack_get_unfixed_depth op f target_len ps.ps_stack of
              SOME _ => ([] : stack_op list, ps)
            | NONE =>
                (case FLOOKUP ps.ps_spilled op of
                   SOME _ => do_restore op ps
                 | NONE => ([], ps)))).ps_stack +
      (if x IN FDOM
        (SND (case stack_get_unfixed_depth op f target_len ps.ps_stack of
                SOME _ => ([] : stack_op list, ps)
              | NONE =>
                  (case FLOOKUP ps.ps_spilled op of
                     SOME _ => do_restore op ps
                   | NONE => ([], ps)))).ps_spilled then 1 else 0)
Proof
  rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth op f target_len ps.ps_stack` >> simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  qspecl_then [`ps`, `op`, `off`, `x`] mp_tac do_restore_inventory_count_marked >>
  simp[]
QED

Theorem reorder_one_residual_budget_wf_marked:
  !dfg pending idx op ps ops ps' base.
    residual_budget_wf_marked base pending ps /\
    idx < LENGTH pending /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    reorder_one dfg pending idx op ps = (ops, ps') ==>
    residual_budget_wf_marked base pending ps' /\
    LENGTH pending <= LENGTH ps'.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  `residual_budget_wf_marked base' pending ps1 /\
   LENGTH pending <= LENGTH ps1.ps_stack` by
    (qspecl_then [`base'`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `ps`]
       mp_tac reorder_restore_residual_budget_wf_marked >> simp[] >> gvs[]) >>
  gvs[] >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  pairarg_tac >> simp[] >>
  `residual_budget_wf_marked base' pending ps2` by
    (Cases_on `x > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `base'`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `ps1`, `reduce_ops`, `ps2`]
       mp_tac reduce_depth_plan_residual_budget_wf_marked >> simp[]) >>
  `LENGTH pending <= LENGTH ps2.ps_stack` by
    (Cases_on `x > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `LENGTH pending`, `ps1`,
       `reduce_ops`, `ps2`] mp_tac reduce_depth_plan_target_len_floor >>
     fs[]) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  `dist' < LENGTH ps2.ps_stack /\ stack_peek dist' ps2.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  qpat_x_assum `stack_peek dist' ps2.ps_stack = op`
    (fn th => SUBST_ALL_TAC (SYM th)) >>
  `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `dist' = LENGTH pending - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` >> gvs[] >>
  Cases_on `operand_equiv dfg (stack_peek dist' ps2.ps_stack)
    (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[] >> conj_tac
      >- (irule residual_budget_wf_marked_stack_poke_exchange >> simp[])
      >> simp[stack_poke_def]) >>
  pairarg_tac >> simp[] >>
  rename1 `do_swap dist' ps2 = (swap1_ops, ps3)` >>
  pairarg_tac >> simp[] >>
  rename1 `do_swap (LENGTH pending - (idx + 1)) ps3 =
           (swap2_ops, ps4)` >>
  `residual_budget_wf_marked base' pending ps3` by
    metis_tac[residual_budget_wf_marked_do_swap] >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspecl_then [`dist'`, `ps2`] mp_tac do_swap_length >> simp[]) >>
  `residual_budget_wf_marked base' pending ps4` by
    (qspecl_then [`base'`, `pending`,
       `LENGTH pending - (idx + 1)`, `ps3`, `swap2_ops`, `ps4`]
       mp_tac residual_budget_wf_marked_do_swap >> simp[]) >>
  `LENGTH ps4.ps_stack = LENGTH ps3.ps_stack` by
    (qspecl_then [`LENGTH pending - (idx + 1)`, `ps3`]
       mp_tac do_swap_length >> simp[]) >>
  strip_tac >> gvs[]
QED

Theorem reorder_one_pending_inventory_wf_marked:
  !dfg pending idx op ps ops ps' base.
    pending_inventory_wf pending ps /\
    residual_budget_wf_marked base pending ps /\ idx < LENGTH pending /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    reorder_one dfg pending idx op ps = (ops,ps') ==>
    pending_inventory_wf pending ps'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  `residual_budget_wf_marked base' pending ps1 /\
   LENGTH pending <= LENGTH ps1.ps_stack` by
    (qspecl_then [`base'`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `ps`]
       mp_tac reorder_restore_residual_budget_wf_marked >> simp[] >> gvs[]) >>
  `!x. MEM x pending ==>
      LIST_ELEM_COUNT x ps.ps_stack +
        (if x IN FDOM ps.ps_spilled then 1 else 0) <=
      LIST_ELEM_COUNT x ps1.ps_stack +
        (if x IN FDOM ps1.ps_spilled then 1 else 0)` by
    (gen_tac >> strip_tac >>
     qspecl_then [`op`, `LENGTH pending - (idx + 1)`,
       `LENGTH pending`, `ps`, `x`]
       mp_tac reorder_restore_inventory_mono_marked >> gvs[]) >>
  gvs[] >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[] >> rewrite_tac[pending_inventory_wf_def] >>
      gen_tac >> Cases_on `MEM op' pending`
      >- (qpat_assum `!x. MEM x pending ==> _`
            (qspec_then `op'` (drule_then assume_tac)) >>
          qpat_assum `pending_inventory_wf pending ps`
            (assume_tac o Q.SPEC `op'` o
             REWRITE_RULE [pending_inventory_wf_def]) >>
          irule LESS_EQ_TRANS >>
          qexists_tac `LIST_ELEM_COUNT op' ps.ps_stack +
            (if op' IN FDOM ps.ps_spilled then 1 else 0)` >> simp[])
      >> fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  pairarg_tac >> simp[] >>
  `residual_budget_wf_marked base' pending ps2` by
    (Cases_on `x > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `base'`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `ps1`, `reduce_ops`, `ps2`]
       mp_tac reduce_depth_plan_residual_budget_wf_marked >> simp[]) >>
  `!y. MEM y pending ==>
      LIST_ELEM_COUNT y ps1.ps_stack +
        (if y IN FDOM ps1.ps_spilled then 1 else 0) <=
      LIST_ELEM_COUNT y ps2.ps_stack +
        (if y IN FDOM ps2.ps_spilled then 1 else 0)` by
    (gen_tac >> strip_tac >> Cases_on `x > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `ps1`, `reduce_ops`, `ps2`,
       `base'`, `y`] mp_tac reduce_depth_plan_pending_inventory_mono_marked >>
     simp[]) >>
  `LENGTH pending <= LENGTH ps2.ps_stack` by
    (Cases_on `x > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `LENGTH pending`, `ps1`,
       `reduce_ops`, `ps2`] mp_tac reduce_depth_plan_target_len_floor >>
     fs[]) >>
  `pending_inventory_wf pending ps2` by
    (rewrite_tac[pending_inventory_wf_def] >> gen_tac >>
     Cases_on `MEM op' pending`
     >- (qpat_assum `!y. MEM y pending ==> _`
           (qspec_then `op'` (drule_then assume_tac)) >>
         qpat_assum `!x. MEM x pending ==> _`
           (qspec_then `op'` (drule_then assume_tac)) >>
         qpat_assum `pending_inventory_wf pending ps`
           (assume_tac o Q.SPEC `op'` o
            REWRITE_RULE [pending_inventory_wf_def]) >>
         irule LESS_EQ_TRANS >>
         qexists_tac `LIST_ELEM_COUNT op' ps1.ps_stack +
           (if op' IN FDOM ps1.ps_spilled then 1 else 0)` >>
         conj_tac
         >- (irule LESS_EQ_TRANS >>
             qexists_tac `LIST_ELEM_COUNT op' ps.ps_stack +
               (if op' IN FDOM ps.ps_spilled then 1 else 0)` >> simp[])
         >> simp[])
     >> fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  `dist' < LENGTH ps2.ps_stack /\ stack_peek dist' ps2.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  qpat_x_assum `stack_peek dist' ps2.ps_stack = op`
    (fn th => SUBST_ALL_TAC (SYM th)) >>
  `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> decide_tac) >>
  Cases_on `dist' = LENGTH pending - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` >> gvs[] >>
  Cases_on `operand_equiv dfg (stack_peek dist' ps2.ps_stack)
    (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[pending_inventory_wf_def] >> gen_tac >>
      qpat_assum `!op. LIST_ELEM_COUNT op pending <= _`
        (qspec_then `op'` assume_tac) >>
      simp[stack_poke_exchange_multiplicity]) >>
  pairarg_tac >> simp[] >>
  rename1 `do_swap dist' ps2 = (swap1_ops,ps3)` >>
  pairarg_tac >> simp[] >>
  rename1 `do_swap (LENGTH pending - (idx + 1)) ps3 = (swap2_ops,ps4)` >>
  `ps3.ps_spilled = ps2.ps_spilled /\
   (!y. LIST_ELEM_COUNT y ps3.ps_stack = LIST_ELEM_COUNT y ps2.ps_stack)` by
    (qspecl_then [`dist'`, `ps2`, `swap1_ops`, `ps3`] mp_tac
       do_swap_multiplicity_layout >> fs[residual_budget_wf_marked_def]) >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspecl_then [`dist'`, `ps2`] mp_tac do_swap_length >> simp[]) >>
  `ps4.ps_spilled = ps3.ps_spilled /\
   (!y. LIST_ELEM_COUNT y ps4.ps_stack = LIST_ELEM_COUNT y ps3.ps_stack)` by
    (qspecl_then [`LENGTH pending - (idx + 1)`, `ps3`,
       `swap2_ops`, `ps4`] mp_tac do_swap_multiplicity_layout >>
     `spill_alloc_layout_wf ps3.ps_alloc ps3.ps_spilled` by
       (qspecl_then [`base'`, `pending`, `dist'`, `ps2`,
          `swap1_ops`, `ps3`] mp_tac residual_budget_wf_marked_do_swap >>
        impl_tac >- simp[] >>
        disch_then (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o
          REWRITE_RULE [residual_budget_wf_marked_def])) >>
     simp[]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `pending_inventory_wf pending ps2` mp_tac >>
  simp[pending_inventory_wf_def]
QED

Theorem plan_steps_reorder_residual_budget_wf_marked:
  !items ps ops ps'.
    EVERY (\(idx,op). idx < LENGTH pending) items /\
    residual_budget_wf_marked sb pending ps /\
    pending_inventory_wf pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps =
      (ops,ps') ==>
    residual_budget_wf_marked sb pending ps' /\
    pending_inventory_wf pending ps' /\
    LENGTH pending <= LENGTH ps'.ps_stack
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[plan_steps_def]) >>
  rpt gen_tac >> Cases_on `h` >> rename1 `(idx,op)::items` >> strip_tac >>
  qpat_x_assum `plan_steps _ (_::_) _ = _` mp_tac >>
  simp[Once plan_steps_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `reorder_one dfg pending idx op ps = (step_ops,ps1)` >>
  `residual_budget_wf_marked sb pending ps1 /\
   LENGTH pending <= LENGTH ps1.ps_stack` by
    metis_tac[reorder_one_residual_budget_wf_marked] >>
  `pending_inventory_wf pending ps1` by
    metis_tac[reorder_one_pending_inventory_wf_marked] >>
  first_x_assum drule_all >> simp[]
QED

(* The budget half of deepResidualSim's reorder_plan_venom_asm_rel_numeric_marked,
   with the stack-length floor it needs. *)
Theorem reorder_plan_residual_budget_wf_marked:
  !dfg target_ops ps ops ps' base.
    residual_budget_wf_marked base target_ops ps /\
    pending_inventory_wf target_ops ps /\
    LENGTH target_ops <= LENGTH ps.ps_stack /\
    reorder_plan dfg target_ops ps = (ops,ps') ==>
    residual_budget_wf_marked base target_ops ps' /\
    pending_inventory_wf target_ops ps' /\
    LENGTH target_ops <= LENGTH ps'.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\(idx,op). idx < LENGTH target_ops)
     (MAPi (\i op. (i,op)) target_ops)` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
     rpt strip_tac >> gvs[]) >>
  qpat_x_assum `reorder_plan _ _ _ = _`
    (assume_tac o REWRITE_RULE [reorder_plan_eq_plan_steps]) >>
  drule_all plan_steps_reorder_residual_budget_wf_marked >> simp[]
QED

Theorem reorder_restore_inventory_subset_nb[local]:
  !op f n ps ops ps'.
    (case stack_get_unfixed_depth op f n ps.ps_stack of
       SOME _ => ([],ps)
     | NONE => case FLOOKUP ps.ps_spilled op of
                 SOME _ => do_restore op ps | NONE => ([],ps)) = (ops,ps') ==>
    LENGTH ps.ps_stack <= LENGTH ps'.ps_stack /\
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  strip_tac >> gvs[] >>
  conj_tac
  >- (qpat_x_assum `do_restore _ _ = _` mp_tac >>
      simp[do_restore_def] >> strip_tac >> gvs[stack_push_def]) >>
  metis_tac[do_restore_inventory_subset]
QED

Theorem stack_poke_mem_subset_nb[local]:
  !d op stk at. MEM at (stack_poke d op stk) ==> at = op \/ MEM at stk
Proof
  simp[stack_poke_def, MEM_LUPDATE] >> metis_tac[EL_MEM]
QED

Theorem reorder_reduce_inventory_subset_nb:
  !(dist:num) tops op f ps ops ps'.
    (if dist > 16 then
       reduce_depth_plan (LENGTH ps.ps_stack) tops op f (LENGTH tops) ps
     else ([],ps)) = (ops,ps') ==>
    LENGTH tops <= LENGTH ps.ps_stack ==>
    LENGTH tops <= LENGTH ps'.ps_stack /\
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> Cases_on `dist > 16` >> simp[] >> ntac 2 strip_tac >> gvs[] >>
  conj_tac
  >- (drule reduce_depth_plan_target_len_floor >> fs[]) >>
  metis_tac[reduce_depth_plan_inventory_subset]
QED

Theorem reorder_one_inventory_subset_nb:
  !dfg tops idx op ps ops ps'.
    idx < LENGTH tops /\
    LENGTH tops <= LENGTH ps.ps_stack /\
    reorder_one dfg tops idx op ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> gvs[] >>
  `LENGTH tops <= LENGTH ps1.ps_stack /\
   !at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (drule reorder_restore_inventory_subset_nb >> simp[] >> metis_tac[LESS_EQ_TRANS]) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH tops - (idx + 1)) (LENGTH tops) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps1.ps_stack = SOME dist` >>
  pairarg_tac >> simp[] >>
  `LENGTH tops <= LENGTH ps2.ps_stack /\
   !at. MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled ==>
        MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled` by
    (drule reorder_reduce_inventory_subset_nb >> simp[] >> metis_tac[]) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH tops - (idx + 1)) (LENGTH tops) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[] >> metis_tac[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  `dist' < LENGTH ps2.ps_stack /\ stack_peek dist' ps2.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `MEM op ps2.ps_stack` by metis_tac[stack_peek_mem] >>
  `LENGTH tops - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `dist' = LENGTH tops - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[] >> metis_tac[]) >>
  `MEM (stack_peek (LENGTH tops - (idx + 1)) ps2.ps_stack) ps2.ps_stack` by
    (irule stack_peek_mem >> decide_tac) >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH tops - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[] >> rpt strip_tac >>
      metis_tac[stack_poke_mem_subset_nb]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rename1 `do_swap dist' ps2 = (swap1_ops,ps3)` >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspec_then `ps2` mp_tac (Q.SPEC `dist'` do_swap_length) >> simp[]) >>
  `!at. MEM at ps3.ps_stack \/ at IN FDOM ps3.ps_spilled ==>
        MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled` by
    (qspec_then `dist'` mp_tac do_swap_inventory_subset >>
     disch_then drule >> simp[] >> metis_tac[]) >>
  strip_tac >> gvs[] >>
  `LENGTH tops - (idx + 1) < LENGTH ps3.ps_stack` by decide_tac >>
  drule_at (Pat `do_swap _ _ = _`) do_swap_inventory_subset >>
  simp[] >> metis_tac[]
QED

(* generatedReorderSim's reorder simulation chain over the marked budget,
   without its LENGTH pending <= 16 bound. *)

Theorem reorder_prepare_venom_asm_rel_numeric_marked:
  residual_budget_wf_marked spill_base pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
     SOME d => ([],ps)
   | NONE => (case FLOOKUP ps.ps_spilled op of
       SOME off => do_restore op ps | NONE => ([],ps))) = (restore_ops,ps1) /\
  stack_get_unfixed_depth op f (LENGTH pending) ps1.ps_stack = SOME dist /\
  (if dist > 16 then
     reduce_depth_plan (LENGTH ps1.ps_stack) pending op f (LENGTH pending) ps1
   else ([],ps1)) = (reduce_ops,ps2) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (restore_ops ++ reduce_ops) /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (restore_ops ++ reduce_ops)) ==>
  spill_alloc_layout_wf ps2.ps_alloc ps2.ps_spilled /\
  LENGTH pending <= LENGTH ps2.ps_stack /\
  ?st2. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) st = AsmOK st2 /\
        venom_asm_rel lo ps2 vs st2 /\
        st2.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))
Proof
  strip_tac >>
  `residual_budget_wf_marked spill_base pending ps1 /\
   LENGTH pending <= LENGTH ps1.ps_stack` by
    (drule_all reorder_restore_residual_budget_wf_marked >>
     disch_then (qspecl_then [`op`, `f`] mp_tac) >> simp[LET_THM] >> gvs[]) >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by fs[residual_budget_wf_marked_def] >>
  gvs[EVERY_APPEND] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[execute_plan_append, asm_block_at_append] >> strip_tac >>
  drule_all reorder_restore_venom_asm_rel_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo ps1 vs mid` >>
  Cases_on `dist > 16` >> gvs[]
  >- ( `LENGTH pending <= LENGTH ps2.ps_stack` by
         (drule reduce_depth_plan_target_len_floor >> fs[]) >>
       `asm_block_at prog mid.as_pc (execute_plan initial_fmp reduce_ops)` by
         metis_tac[ADD_COMM] >>
       drule_all reduce_depth_plan_venom_asm_rel_numeric >>
       disch_then (qspec_then `o2pc` strip_assume_tac) >>
       rename1 `venom_asm_rel lo ps2 vs final` >> simp[] >> qexists `final` >>
       simp[] >> once_rewrite_tac[ADD_COMM] >>
       irule asm_steps_compose_ok >> qexists `mid` >> simp[]) >>
  simp[] >> qexists `mid` >> fs[execute_plan_def]
QED

Theorem reorder_one_venom_asm_rel_numeric_marked:
  residual_budget_wf_marked spill_base pending ps /\
  pending_inventory_wf pending ps /\
  (!at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
  op <> dead_stack_marker /\
  idx < LENGTH pending /\ MEM op pending /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  reorder_one dfg pending idx op ps = (ops,ps') /\
  (!op1 at. MEM op1 pending /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
    operand_equiv dfg op1 at ==>
    operand_val vs lo op1 = operand_val vs lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        venom_asm_rel lo ps' vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
        residual_budget_wf_marked spill_base pending ps' /\
        pending_inventory_wf pending ps'
Proof
  strip_tac >>
  `residual_budget_wf_marked spill_base pending ps' /\
   LENGTH pending <= LENGTH ps'.ps_stack` by
    (drule_all reorder_one_residual_budget_wf_marked >> simp[]) >>
  `pending_inventory_wf pending ps'` by
    (drule_all reorder_one_pending_inventory_wf_marked >> simp[]) >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[residual_budget_wf_marked_def] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rename1 `LENGTH pending = num_ops` >>
  Cases_on `stack_get_unfixed_depth op (num_ops - (idx + 1)) num_ops ps1.ps_stack` >> simp[]
  >- suspend "restore_only" >>
  pairarg_tac >> simp[] >>
  rename1 `(if dist > 16 then _ else _) = (reduce_ops,ps2)` >>
  suspend "after_reduce"
QED

Resume reorder_one_venom_asm_rel_numeric_marked[restore_only]:
  strip_tac >> gvs[] >>
  drule_all reorder_restore_venom_asm_rel_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists `st'` >> asm_rewrite_tac[] >> MATCH_ACCEPT_TAC ADD_COMM
QED

Resume reorder_one_venom_asm_rel_numeric_marked[after_reduce]:
  strip_tac >>
  qpat_x_assum `LENGTH pending = num_ops` (SUBST_ALL_TAC o SYM) >>
  `?suffix. ops = (restore_ops ++ reduce_ops) ++ suffix` by
    (qpat_x_assum `(case stack_get_unfixed_depth _ _ _ ps2.ps_stack of _ => _ | _ => _) = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
     pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
     metis_tac[APPEND_ASSOC, APPEND_NIL]) >>
  gvs[] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[execute_plan_append, asm_block_at_append] >> strip_tac >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
     | SORestore off => off < dimword(:256) | _ => T) (restore_ops ++ reduce_ops)` by
    fs[EVERY_APPEND] >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp (restore_ops ++ reduce_ops))` by
    simp[execute_plan_append, asm_block_at_append] >>
  drule_all reorder_prepare_venom_asm_rel_numeric_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo ps2 vs mid` >>
  `asm_block_at prog mid.as_pc (execute_plan initial_fmp suffix)` by
    (fs[execute_plan_append] >> metis_tac[ADD_ASSOC, ADD_COMM]) >>
  `!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (qpat_x_assum `(case stack_get_unfixed_depth _ _ _ ps.ps_stack of _ => _ | _ => _) = _` mp_tac >>
     Cases_on `stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
       (LENGTH pending) ps.ps_stack` >> simp[] >>
     Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
     rpt strip_tac >> gvs[] >> metis_tac[do_restore_inventory_subset]) >>
  `!at. MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled ==>
        MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled` by
    (Cases_on `dist > 16` >> gvs[] >>
     metis_tac[reduce_depth_plan_inventory_subset]) >>
  `!at. (MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled) /\
        operand_equiv dfg op at ==>
        operand_val vs lo op = operand_val vs lo at` by metis_tac[] >>
  `?final. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp suffix)) mid = AsmOK final /\
           venom_asm_rel lo ps' vs final /\
           final.as_pc = mid.as_pc + LENGTH (execute_plan initial_fmp suffix)` by
    (qpat_x_assum `residual_budget_wf_marked spill_base pending ps` kall_tac >>
     qpat_x_assum `pending_inventory_wf pending ps` kall_tac >>
     qpat_x_assum `venom_asm_rel lo ps vs st` kall_tac >>
     qpat_x_assum `(case stack_get_unfixed_depth _ _ _ ps.ps_stack of _ => _ | _ => _) = _` kall_tac >>
     qpat_x_assum `(if dist > 16 then _ else _) = _` kall_tac >>
     qpat_x_assum `stack_get_unfixed_depth _ _ _ ps1.ps_stack = _` kall_tac >>
     qpat_x_assum `EVERY _ restore_ops` kall_tac >>
     qpat_x_assum `EVERY _ reduce_ops` kall_tac >>
     suspend "suffix") >>
  `asm_steps lo o2pc prog
     (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops)) +
      LENGTH (execute_plan initial_fmp suffix)) st = AsmOK final` by
    (irule asm_steps_compose_ok >> qexists `mid` >> asm_rewrite_tac[]) >>
  qexists `final` >> fs[execute_plan_append]
QED

Resume reorder_one_venom_asm_rel_numeric_marked[suffix]:
  Cases_on `stack_get_unfixed_depth op (LENGTH pending - (idx + 1)) (LENGTH pending) ps2.ps_stack`
  >- (gvs[] >> simp[execute_plan_def, asm_steps_def]) >>
  rename1 `stack_get_unfixed_depth _ _ _ ps2.ps_stack = SOME sd` >>
  `sd < LENGTH ps2.ps_stack /\ stack_peek sd ps2.ps_stack = op` by
    (drule stack_get_unfixed_depth_props >> simp[]) >>
  `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `sd = LENGTH pending - (idx + 1)`
  >- (gvs[] >> simp[execute_plan_def, asm_steps_def]) >>
  `((LENGTH pending < idx + (LENGTH ps2.ps_stack + 1) /\
     0 < idx + LENGTH ps2.ps_stack) /\ 0 < LENGTH ps2.ps_stack)` by decide_tac >>
  Cases_on `operand_equiv dfg op (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)`
  >- suspend "alias_suffix" >>
  gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  qpat_assum `do_swap sd ps2 = _`
    (mp_then Any mp_tac do_swap_pair_venom_asm_rel_numeric) >>
  simp[EVERY_APPEND] >> disch_then drule_all >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo ps' vs final` >>
  qexists `final` >> asm_rewrite_tac[]
QED

Resume reorder_one_venom_asm_rel_numeric_marked[alias_suffix]:
  gvs[] >> simp[execute_plan_def, asm_steps_def] >>
  irule venom_asm_rel_sem_stack_transport >>
  goal_assum (drule_at Any) >> simp[] >>
  irule plan_stack_sem_eq_exchange >>
  `MEM (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)
     ps2.ps_stack` by (irule stack_peek_mem >> decide_tac) >>
  simp[] >> metis_tac[]
QED

Finalise reorder_one_venom_asm_rel_numeric_marked

Theorem plan_steps_reorder_venom_asm_rel_numeric_marked:
  !items ps ops ps' st.
    EVERY (\(idx,op). idx < LENGTH pending /\ MEM op pending) items /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
    residual_budget_wf_marked spill_base pending ps /\ pending_inventory_wf pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps = (ops,ps') /\
    (!op1 at. MEM op1 pending /\
      (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
      operand_equiv dfg op1 at ==> operand_val vs lo op1 = operand_val vs lo at) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
          venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
          residual_budget_wf_marked spill_base pending ps' /\ pending_inventory_wf pending ps'
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[plan_steps_def] >>
      simp[execute_plan_def, asm_steps_def]) >>
  rpt gen_tac >> Cases_on `h` >> rename1 `(idx,op)::items` >> strip_tac >>
  qpat_x_assum `plan_steps _ (_::_) _ = _` mp_tac >>
  simp[Once plan_steps_def] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 `reorder_one dfg pending idx op ps = (step_ops,ps1)` >>
  rename1 `plan_steps _ items ps1 = (rest_ops,ps')` >>
  `op <> dead_stack_marker /\
   (!at. operand_equiv dfg op at ==> at <> dead_stack_marker)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[execute_plan_append, asm_block_at_append] >> strip_tac >>
  drule_all reorder_one_venom_asm_rel_numeric_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo ps1 vs mid` >>
  `LENGTH pending <= LENGTH ps1.ps_stack` by
    (drule_all reorder_one_residual_budget_wf_marked >> simp[]) >>
  `asm_block_at prog mid.as_pc (execute_plan initial_fmp rest_ops)` by metis_tac[ADD_COMM] >>
  `!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (drule_at (Pat `reorder_one _ _ _ _ _ = _`)
       reorder_one_inventory_subset_nb >> simp[]) >>
  `!op1 at. MEM op1 pending /\
        (MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled) /\
        operand_equiv dfg op1 at ==>
        operand_val vs lo op1 = operand_val vs lo at` by metis_tac[] >>
  first_x_assum (qspec_then `ps1` mp_tac) >> disch_then drule_all >> strip_tac >>
  rename1 `venom_asm_rel lo ps' vs final` >>
  `asm_steps lo o2pc prog
    (LENGTH (execute_plan initial_fmp step_ops) + LENGTH (execute_plan initial_fmp rest_ops)) st = AsmOK final` by
    (irule asm_steps_compose_ok >> qexists `mid` >> asm_rewrite_tac[]) >>
  qexists `final` >> fs[execute_plan_append]
QED

(* ===== Popping a fully placed target window under the marked budget ===== *)

Theorem count_le_one_all_distinct[local]:
  !(xs : 'a list). (!x. LIST_ELEM_COUNT x xs <= 1) ==> ALL_DISTINCT xs
Proof
  Induct >> rw[]
  >- (qpat_x_assum `!x. LIST_ELEM_COUNT x (h::xs) <= 1`
        (qspec_then `h` mp_tac) >>
      simp[LIST_ELEM_COUNT_THM] >> strip_tac >>
      fs[GSYM LIST_ELEM_COUNT_MEM]) >>
  first_x_assum irule >> gen_tac >>
  qpat_x_assum `!x. LIST_ELEM_COUNT x (h::xs) <= 1`
    (qspec_then `x` mp_tac) >>
  Cases_on `h = x` >> simp[LIST_ELEM_COUNT_THM]
QED

Theorem elem_count_filter:
  !P x (l : 'a list).
    LIST_ELEM_COUNT x (FILTER P l) = if P x then LIST_ELEM_COUNT x l else 0
Proof
  gen_tac >> gen_tac >> Induct >> rw[LIST_ELEM_COUNT_DEF, FILTER] >>
  gvs[LIST_ELEM_COUNT_DEF] >> Cases_on `h = x` >> gvs[]
QED

Theorem elem_count_split[local]:
  !(full : 'a list) prefix suffix.
    full = prefix ++ suffix ==>
    !x. LIST_ELEM_COUNT x full =
        LIST_ELEM_COUNT x prefix + LIST_ELEM_COUNT x suffix
Proof
  rpt strip_tac >> gvs[LIST_ELEM_COUNT_THM]
QED

Theorem plan_state_residual_wf_marked_pop:
  !sb pending ps.
    plan_state_residual_wf_marked sb pending (LENGTH pending) ps ==>
    plan_slots_bounded sb
      (ps with ps_stack := stack_pop (LENGTH pending) ps.ps_stack) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    dead_stack_marker NOTIN FDOM ps.ps_spilled /\
    ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker)
                   (stack_pop (LENGTH pending) ps.ps_stack)) /\
    DISJOINT (set (stack_pop (LENGTH pending) ps.ps_stack))
             (FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >> fs[plan_state_residual_wf_marked_def] >>
  `ps.ps_stack = stack_pop (LENGTH pending) ps.ps_stack ++ pending` by
    (irule fixed_suffix_decompose >> simp[]) >>
  drule elem_count_split >> strip_tac >>
  `!x. x <> dead_stack_marker ==>
       LIST_ELEM_COUNT x (stack_pop (LENGTH pending) ps.ps_stack) <= 1` by
    (rpt strip_tac >> res_tac >>
     qpat_x_assum `!x. LIST_ELEM_COUNT x ps.ps_stack = _`
       (qspec_then `x` assume_tac) >> decide_tac) >>
  `!x. x IN FDOM ps.ps_spilled ==>
       ~MEM x (stack_pop (LENGTH pending) ps.ps_stack)` by
    (rpt strip_tac >> res_tac >>
     qpat_x_assum `!x. LIST_ELEM_COUNT x ps.ps_stack = _`
       (qspec_then `x` assume_tac) >>
     fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  `plan_slots_bounded sb
     (ps with ps_stack := stack_pop (LENGTH pending) ps.ps_stack)` by
    (fs[plan_slots_bounded_def] >> metis_tac[]) >>
  `ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker)
     (stack_pop (LENGTH pending) ps.ps_stack))` by
    (irule count_le_one_all_distinct >> rw[elem_count_filter]) >>
  `DISJOINT (set (stack_pop (LENGTH pending) ps.ps_stack))
     (FDOM ps.ps_spilled)` by
    (simp[pred_setTheory.IN_DISJOINT] >> metis_tac[]) >>
  simp[]
QED


(* ===== reorderSim's materialisation chain over the marked residual ===== *)

Theorem elem_count_take_el_lt_m[local]:
  !(xs : operand list) n.
    n < LENGTH xs ==>
    LIST_ELEM_COUNT (EL n xs) (TAKE n xs) <
      LIST_ELEM_COUNT (EL n xs) xs
Proof
  rpt strip_tac >> drule TAKE_DROP_SUC >>
  disch_then (fn th => mp_tac
    (AP_TERM ``LIST_ELEM_COUNT (EL n xs) : operand list -> num`` th)) >>
  simp[elem_count_append, LIST_ELEM_COUNT_THM] >> decide_tac
QED

Theorem fixed_window_segment_m[local]:
  !(pending : operand list) fixed stack.
    LENGTH pending <= LENGTH stack /\ fixed <= LENGTH pending /\
    (!i. i < fixed ==>
      stack_peek (LENGTH pending - 1 - i) stack = EL i pending) ==>
    TAKE fixed (DROP (LENGTH stack - LENGTH pending) stack) =
      TAKE fixed pending
Proof
  rpt gen_tac >> strip_tac >> irule LIST_EQ >>
  simp[LENGTH_TAKE, LENGTH_DROP] >> rpt strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >>
  simp[stack_peek_def, EL_TAKE, EL_DROP] >>
  AP_TERM_TAC >> decide_tac
QED

Theorem fixed_window_count_bound_m[local]:
  !(pending : operand list) fixed stack op.
    LENGTH pending <= LENGTH stack /\ fixed <= LENGTH pending /\
    (!i. i < fixed ==>
      stack_peek (LENGTH pending - 1 - i) stack = EL i pending) /\
    stack_get_unfixed_depth op (LENGTH pending - 1 - fixed)
      (LENGTH pending) stack = NONE ==>
    LIST_ELEM_COUNT op stack <= LIST_ELEM_COUNT op (TAKE fixed pending)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stack_get_unfixed_depth _ _ _ _ = NONE` mp_tac >>
  simp[stack_get_unfixed_depth_NONE] >> strip_tac >>
  qabbrev_tac `off = LENGTH stack - LENGTH pending` >>
  `TAKE fixed (DROP off stack) = TAKE fixed pending` by
    (unabbrev_all_tac >> irule fixed_window_segment_m >> simp[]) >>
  `stack = TAKE off stack ++ TAKE fixed (DROP off stack) ++
           DROP (off + fixed) stack` by
    (`TAKE fixed (DROP off stack) ++ DROP (off + fixed) stack =
       DROP off stack` by
       MATCH_ACCEPT_TAC
         (ONCE_REWRITE_RULE [Q.SPECL [`fixed`, `off`] ADD_COMM]
            (REWRITE_RULE [DROP_DROP_T]
              (Q.SPECL [`fixed`, `DROP off stack`] TAKE_DROP))) >>
     once_rewrite_tac[GSYM APPEND_ASSOC] >>
     qpat_assum
       `TAKE fixed (DROP off stack) ++ DROP (off + fixed) stack =
          DROP off stack`
       (fn th => once_rewrite_tac[th]) >>
     MATCH_ACCEPT_TAC (SYM (Q.SPECL [`off`, `stack`] TAKE_DROP))) >>
  `~MEM op (TAKE off stack)` by
    (simp[MEM_EL] >> rpt strip_tac >>
     first_x_assum (qspec_then `LENGTH stack - 1 - n` mp_tac) >>
     simp[stack_peek_def] >>
     `n < LENGTH stack` by
       (qpat_assum `stack = _`
          (fn th => mp_tac (AP_TERM ``LENGTH : operand list -> num`` th)) >>
        simp[] >> decide_tac) >>
     `LENGTH stack - 1 - (LENGTH stack - 1 - n) = n` by decide_tac >>
     `off <= LENGTH stack` by (unabbrev_all_tac >> decide_tac) >>
     `n < off` by fs[LENGTH_TAKE] >>
     `LENGTH pending <= LENGTH stack - 1 - n` by
       (unabbrev_all_tac >> decide_tac) >>
     simp[EL_TAKE] >> decide_tac) >>
  `~MEM op (DROP (off + fixed) stack)` by
    (simp[MEM_EL] >> rpt strip_tac >>
     first_x_assum
       (qspec_then `LENGTH stack - 1 - (off + fixed + n)` mp_tac) >>
     simp[stack_peek_def, EL_DROP] >>
     `LENGTH stack - 1 - (LENGTH stack - 1 - (off + fixed + n)) =
        off + fixed + n` by decide_tac >>
     `LENGTH stack - 1 - (off + fixed + n) <=
        LENGTH pending - 1 - fixed` by
       (unabbrev_all_tac >> decide_tac) >>
     simp[] >> unabbrev_all_tac >> decide_tac) >>
  `LIST_ELEM_COUNT op (TAKE off stack) = 0 /\
   LIST_ELEM_COUNT op (DROP (off + fixed) stack) = 0` by
    fs[GSYM LIST_ELEM_COUNT_MEM] >>
  qpat_x_assum `stack = _`
    (fn th => mp_tac
      (AP_TERM ``LIST_ELEM_COUNT op : operand list -> num`` th)) >>
  simp[elem_count_append] >> decide_tac
QED

Theorem residual_budget_wf_marked_to_residual:
  !base pending ps.
    residual_budget_wf_marked base pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack ==>
    plan_state_residual_wf_marked base pending 0 ps
Proof
  simp[residual_budget_wf_marked_def, plan_state_residual_wf_marked_def]
QED

Theorem materialised_pending_next_on_stack_marked:
  !base pending fixed ps.
    (!op. LIST_ELEM_COUNT op pending <=
          LIST_ELEM_COUNT op ps.ps_stack) /\
    plan_state_residual_wf_marked base pending fixed ps /\
    fixed < LENGTH pending ==>
    ?d. stack_get_unfixed_depth (EL fixed pending)
          (LENGTH pending - 1 - fixed) (LENGTH pending)
          ps.ps_stack = SOME d
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth (EL fixed pending)
    (LENGTH pending - 1 - fixed) (LENGTH pending) ps.ps_stack`
  >- (`LIST_ELEM_COUNT (EL fixed pending) ps.ps_stack <=
         LIST_ELEM_COUNT (EL fixed pending) (TAKE fixed pending)` by
        (irule fixed_window_count_bound_m >>
         fs[plan_state_residual_wf_marked_def]) >>
      qpat_assum `!op. LIST_ELEM_COUNT op pending <= _`
        (qspec_then `EL fixed pending` assume_tac) >>
      drule_then assume_tac elem_count_take_el_lt_m >>
      qsuff_tac `F` >- simp[] >> decide_tac)
  >> simp[]
QED

Theorem plan_state_residual_wf_fix_next_marked:
  !base pending fixed ps.
    plan_state_residual_wf_marked base pending fixed ps /\
    fixed < LENGTH pending /\
    stack_peek (LENGTH pending - 1 - fixed) ps.ps_stack =
      EL fixed pending ==>
    plan_state_residual_wf_marked base pending (SUC fixed) ps
Proof
  simp[plan_state_residual_wf_marked_def] >> rpt strip_tac >>
  Cases_on `i = fixed` >> gvs[] >>
  first_x_assum irule >> decide_tac
QED

Theorem reorder_one_materialised_fix_next_marked:
  !spillbase pending idx ps dfg ops ps'.
    plan_state_residual_wf_marked spillbase pending idx ps /\
    (!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack) /\
    idx < LENGTH pending /\ LENGTH pending <= 16 /\
    reorder_one dfg pending idx (EL idx pending) ps = (ops,ps') ==>
    plan_state_residual_wf_marked spillbase pending (SUC idx) ps' /\
    (!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps'.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `residual_budget_wf_marked spillbase pending ps /\
   LENGTH pending <= LENGTH ps.ps_stack` by
    fs[plan_state_residual_wf_marked_def, residual_budget_wf_marked_def] >>
  `MEM (EL idx pending) pending` by simp[EL_MEM] >>
  drule_all materialised_pending_next_on_stack_marked >> strip_tac >>
  drule_all reorder_one_residual_budget_wf_marked >> strip_tac >>
  `!i. i < idx ==>
       stack_peek (LENGTH pending - 1 - i) ps'.ps_stack = EL i pending` by
    (rpt strip_tac >>
     drule_all reorder_one_preserves_fixed >>
     fs[plan_state_residual_wf_marked_def]) >>
  `stack_peek (LENGTH pending - 1 - idx) ps'.ps_stack = EL idx pending` by
    (irule reorder_one_places >> metis_tac[]) >>
  conj_tac
  >- (irule plan_state_residual_wf_fix_next_marked >> simp[] >>
      fs[plan_state_residual_wf_marked_def, residual_budget_wf_marked_def]) >>
  gen_tac >> Cases_on `MEM x pending`
  >- (drule_all reorder_one_materialised_counts_unconditional >> simp[]) >>
  gvs[GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem plan_steps_reorder_materialised_marked[local]:
  !rest done pending spillbase dfg ps ops ps'.
    pending = done ++ rest /\
    plan_state_residual_wf_marked spillbase pending (LENGTH done) ps /\
    (!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack) /\
    LENGTH pending <= 16 /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps)
      (MAPi (\i op. (LENGTH done + i,op)) rest) ps = (ops,ps') ==>
    plan_state_residual_wf_marked spillbase pending (LENGTH pending) ps'
Proof
  Induct_on `rest`
  >- (rpt gen_tac >> simp[plan_steps_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `plan_steps _ _ _ = _` mp_tac >>
  simp[indexedListsTheory.MAPi_def, combinTheory.o_DEF, ADD_CLAUSES] >>
  strip_tac >> drule plan_steps_cons_result >> strip_tac >> gvs[] >>
  `EL (LENGTH done) (done ++ h::rest) = h` by simp[EL_APPEND_EQN] >>
  `LENGTH done < LENGTH (done ++ h::rest)` by simp[] >>
  `plan_state_residual_wf_marked spillbase (done ++ h::rest) (SUC (LENGTH done)) ps1 /\
   (!x. LIST_ELEM_COUNT x (done ++ h::rest) <= LIST_ELEM_COUNT x ps1.ps_stack)` by
    (irule reorder_one_materialised_fix_next_marked >> simp[] >>
     qexistsl_tac [`dfg`, `step_ops`, `ps`] >>
     rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
     asm_rewrite_tac[]) >>
  first_x_assum (qspec_then `done ++ [h]` mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND, LENGTH_APPEND, LENGTH,
                   ADD_CLAUSES] >>
  disch_then irule >> conj_tac >- decide_tac >>
  qexistsl_tac [`dfg`, `rest_ops`, `ps1`] >> simp[ADD_CLAUSES]
QED

Theorem reorder_plan_materialised_arranged_marked:
  !spillbase pending dfg ps ops ps'.
    residual_budget_wf_marked spillbase pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack /\ LENGTH pending <= 16 /\
    (!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack) /\
    reorder_plan dfg pending ps = (ops,ps') ==>
    plan_state_residual_wf_marked spillbase pending (LENGTH pending) ps' /\
    ps'.ps_stack = stack_pop (LENGTH pending) ps'.ps_stack ++ pending
Proof
  rpt gen_tac >> strip_tac >>
  `plan_state_residual_wf_marked spillbase pending (LENGTH pending) ps'` by
    (irule plan_steps_reorder_materialised_marked >> simp[] >>
     qexistsl_tac [`dfg`, `[]`, `ops`, `ps`, `pending`] >>
     simp[GSYM reorder_plan_eq_plan_steps] >>
     irule residual_budget_wf_marked_to_residual >> simp[]) >>
  simp[] >> irule fixed_suffix_decompose >>
  fs[plan_state_residual_wf_marked_def]
QED
