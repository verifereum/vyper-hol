Theory regularPostfixSim
Ancestors
  spillPlanSim stackPlanGen stackPlanOps stackPlanTypes codegenRel spillSim allocMono mixedPrefixSim asmSem planExec
  doSwapSim planWf stackModel list rich_list planAlign planSpillBounds

Theorem initial_fmp_generated_postfix_sim:
  !lo o2pc prog initial_fmp next_liveness tail ps_emit ps9 ps' vs as.
    prefix_wf lo (LENGTH ps_emit.ps_stack) tail /\
    prefix_spill_wf initial_fmp lo tail ps_emit /\
    EVERY is_prefix_op tail /\
    apply_prefix_ops initial_fmp lo tail ps_emit = ps9 /\
    ps' = release_dead_spills next_liveness ps9 /\
    venom_asm_rel lo ps_emit vs as /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp tail) ==>
    ?as'.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp tail)) as =
        AsmOK as' /\
      venom_asm_rel lo ps' vs as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp tail)
Proof
  rpt strip_tac >>
  qspecl_then [`tail`, `initial_fmp`, `lo`, `o2pc`, `prog`,
    `ps_emit`, `vs`, `as`] mp_tac mixed_prefix_venom_asm_rel >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  strip_tac >>
  `venom_asm_rel lo ps9 vs st'` by gvs[] >>
  qexists_tac `st'` >> ASM_REWRITE_TAC[] >>
  irule venom_asm_rel_release_dead_spills >> ASM_REWRITE_TAC[]
QED

Theorem optimistic_swap_plan_postfix_sim_structural:
  !base dfg inst next_liveness next_is_term ps ops ps'
   initial_fmp lo o2pc prog vs st spill_view.
    plan_slots_bounded base ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    optimistic_swap_plan dfg inst next_liveness next_is_term ps = (ops,ps') /\
    prefix_spill_wf initial_fmp lo (FRONT ops) spill_view /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      plan_slots_bounded base ps' /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
      ALL_DISTINCT ps'.ps_stack /\
      DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled)
Proof
  qx_gen_tac `spill_base` >> rpt strip_tac >>
  qpat_x_assum `optimistic_swap_plan _ _ _ _ _ = _` mp_tac >>
  simp[optimistic_swap_plan_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  TRY (strip_tac >> gvs[] >> qexists `st` >>
       simp[execute_plan_def, asm_steps_def] >> NO_TAC) >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[]
  >- (qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  rename1 `stack_get_depth _ ps.ps_stack = SOME dist` >>
  `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  `ALL_DISTINCT (top_n (dist + 1) ps.ps_stack)` by
    (simp[top_n_def] >> irule ALL_DISTINCT_TAKE >> simp[ALL_DISTINCT_REVERSE]) >>
  `prefix_spill_wf initial_fmp lo ops ps` by
    (irule do_swap_prefix_spill_wf_from_front_cross_view >>
     conj_tac >- (qexistsl_tac [`dist`, `ps'`] >> simp[]) >>
     simp[] >> qexists_tac `spill_view` >> simp[]) >>
  `plan_slots_bounded spill_base ps'` by metis_tac[do_swap_plan_slots_bounded] >>
  `spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
   ALL_DISTINCT ps'.ps_stack /\
   DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled)` by
    (drule_all do_swap_structural_layout_wf >> simp[]) >>
  drule_all do_swap_venom_asm_rel_layout >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `st'` >> simp[] >> decide_tac
QED

Theorem popmany_plan_top_singleton:
  stack_get_depth v ps.ps_stack = SOME 0 ==>
  popmany_plan [v] ps =
    ([SOPop 1], ps with ps_stack := stack_pop 1 ps.ps_stack)
Proof
  strip_tac >>
  simp[popmany_plan_def, is_contiguous_top_def, popmany_individual_def,
       sortingTheory.QSORT_DEF, sortingTheory.PARTITION_DEF,
       sortingTheory.PART_DEF]
QED

Theorem popmany_plan_singleton_stack[local]:
  popmany_plan [v] (ps with ps_stack := [v]) =
    ([SOPop 1], ps with ps_stack := [])
Proof
  `stack_get_depth v [v] = SOME 0` by
    simp[stack_get_depth_def, stack_find_def] >>
  simp[popmany_plan_top_singleton, stack_pop_def]
QED

Theorem popmany_plan_top_singleton_sim:
  stack_get_depth v ps.ps_stack = SOME 0 /\
  popmany_plan [v] ps = (ops, ps') /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
    venom_asm_rel lo ps' vs st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  `0 < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  gvs[popmany_plan_top_singleton] >>
  `prefix_wf lo (LENGTH ps.ps_stack) [SOPop 1] /\
   prefix_spill_wf initial_fmp lo [SOPop 1] ps /\
   EVERY is_prefix_op [SOPop 1]` by
    simp[prefixExecTheory.prefix_wf_def, prefixExecTheory.stack_op_wf_def,
         prefix_spill_wf_def, spill_op_wf_def, prefixSimTheory.is_prefix_op_def] >>
  drule_all mixed_prefix_venom_asm_rel >>
  disch_then (qspec_then `o2pc` mp_tac) >>
  simp[sopop_align, stack_pop_def]
QED

Theorem pop_stack_structural_wf:
  !base ps n.
  plan_slots_bounded base ps /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  ALL_DISTINCT ps.ps_stack /\
  DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) ==>
  plan_slots_bounded base (ps with ps_stack := stack_pop n ps.ps_stack) /\
  spill_alloc_layout_wf
    (ps with ps_stack := stack_pop n ps.ps_stack).ps_alloc
    (ps with ps_stack := stack_pop n ps.ps_stack).ps_spilled /\
  ALL_DISTINCT (ps with ps_stack := stack_pop n ps.ps_stack).ps_stack /\
  DISJOINT (set (ps with ps_stack := stack_pop n ps.ps_stack).ps_stack)
    (FDOM (ps with ps_stack := stack_pop n ps.ps_stack).ps_spilled)
Proof
  rpt gen_tac >> strip_tac >> simp[stack_pop_def] >>
  conj_tac >- (irule ALL_DISTINCT_TAKE >> simp[]) >>
  gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[MEM_TAKE]
QED

Theorem regular_generated_postfix_sim_structural:
  !dfg inst next_liveness is_halting next_is_term ps7 pop_ops ps8 opt_ops ps9 ps'
   base initial_fmp lo o2pc prog vs st spill_view.
  LENGTH inst.inst_outputs <= 1 /\
  (!out. inst.inst_outputs = [out] ==>
    stack_get_depth (Var out) ps7.ps_stack = SOME 0) /\
  plan_slots_bounded base ps7 /\
  spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled /\
  ALL_DISTINCT ps7.ps_stack /\
  DISJOINT (set ps7.ps_stack) (FDOM ps7.ps_spilled) /\
  (if inst.inst_outputs = [] \/ is_halting then ([],ps7)
   else popmany_plan (MAP Var (FILTER (\out. ~MEM out next_liveness)
     inst.inst_outputs)) ps7) = (pop_ops,ps8) /\
  (if FILTER (\out. MEM out next_liveness) inst.inst_outputs = [] then ([],ps8)
   else optimistic_swap_plan dfg inst next_liveness next_is_term ps8) = (opt_ops,ps9) /\
  ps' = release_dead_spills next_liveness ps9 /\
  prefix_spill_wf initial_fmp lo (FRONT opt_ops) spill_view /\
  venom_asm_rel lo ps7 vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (pop_ops ++ opt_ops)) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (pop_ops ++ opt_ops))) st =
    AsmOK st' /\ venom_asm_rel lo ps' vs st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (pop_ops ++ opt_ops))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[]
  >- (qexists_tac `st` >> simp[execute_plan_def, asm_steps_def] >>
      irule venom_asm_rel_release_dead_spills >> simp[]) >>
  rename1 `inst.inst_outputs = out::outs` >>
  `outs = []` by (Cases_on `outs` >> gvs[]) >> gvs[] >>
  Cases_on `MEM out next_liveness` >> gvs[]
  >- (Cases_on `is_halting` >> gvs[popmany_plan_def] >>
      drule_all optimistic_swap_plan_postfix_sim_structural >>
      disch_then (qspec_then `o2pc` strip_assume_tac) >>
      qexists_tac `st'` >> simp[] >>
      irule venom_asm_rel_release_dead_spills >> simp[]) >>
  Cases_on `is_halting` >> gvs[]
  >- (qexists_tac `st` >> simp[execute_plan_def, asm_steps_def] >>
      irule venom_asm_rel_release_dead_spills >> simp[]) >>
  drule_all popmany_plan_top_singleton_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `st'` >> simp[] >>
  irule venom_asm_rel_release_dead_spills >> simp[]
QED
