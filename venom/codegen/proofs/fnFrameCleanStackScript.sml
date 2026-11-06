(*
 * clean_stack_plan's cleanup code against frameRel$fn_frame_inv.
 *
 * cleanOpsSim$clean_ops_sim simulates the cleanup against the whole-stack
 * relation venom_asm_rel, for stacks of at most 17 entries.  This is the
 * frame version, for any depth: the frame's own stack above the caller's
 * rest, spills inside the frame's region, and a stack that may already
 * repeat dead_stack_marker (generated_plan_state_wf_marked).
 *
 * TOP-LEVEL:
 *   clean_stack_plan_frame_sim - arbitrary-depth cleanup frame simulation
 *)

Theory fnFrameCleanStack
Ancestors
  fnPlanPrefix cleanOpsSim genFrameSim frameRel contextCodegenRel codegenRel
  planSpillBounds stackPlanGen stackPlanTypes planExec asmSem
  sorting list rich_list pair finite_map pred_set stackModel stackPlanOps reorderSim fnAliasStep
  fnFrameStepsPhi doSwapSim fnFrameDeepInvoke

Theorem mark_dead_stack_filter:
  !retained stk.
    FILTER (\op. op <> dead_stack_marker) (mark_dead_stack retained stk) =
    FILTER (\op. ~MEM op retained)
      (FILTER (\op. op <> dead_stack_marker) stk)
Proof
  gen_tac >> Induct >> gvs[mark_dead_stack_def] >>
  gen_tac >> Cases_on `MEM h retained` >>
  Cases_on `h = dead_stack_marker` >> gvs[]
QED

Theorem mark_dead_stack_mem:
  !retained stk op.
    MEM op (mark_dead_stack retained stk) ==>
    op = dead_stack_marker \/ MEM op stk
Proof
  simp[mark_dead_stack_def, MEM_MAP] >> metis_tac[]
QED

Theorem mark_dead_stack_wf_marked:
  !base ps retained.
    generated_plan_state_wf_marked base ps ==>
    generated_plan_state_wf_marked base
      (ps with ps_stack := mark_dead_stack retained ps.ps_stack)
Proof
  simp[generated_plan_state_wf_marked_def, mark_dead_stack_filter] >>
  rpt strip_tac
  >- metis_tac[FILTER_ALL_DISTINCT] >>
  fs[IN_DISJOINT] >> metis_tac[mark_dead_stack_mem]
QED

Theorem forget_stack_wf_marked:
  !base ps.
    generated_plan_state_wf_marked base ps ==>
    generated_plan_state_wf_marked base
      (ps with ps_stack := MAP (K dead_stack_marker) ps.ps_stack)
Proof
  rpt gen_tac >>
  `FILTER (K F) ps.ps_stack = []` by simp[FILTER_EQ_NIL] >>
  simp[generated_plan_state_wf_marked_def, FILTER_MAP,
       IN_DISJOINT, MEM_MAP, combinTheory.K_THM] >>
  metis_tac[]
QED

Theorem clean_stack_plan_wf_marked:
  !base ps liveness cfg fn bb ops ps'.
    generated_plan_state_wf_marked base ps /\
    clean_stack_plan liveness cfg fn bb ps = (ops, ps') ==>
    generated_plan_state_wf_marked base ps'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  simp[clean_stack_plan_def] >>
  Cases_on `cfg_preds_of cfg bb.bb_label`
  >- (simp[] >> rpt strip_tac >> gvs[]) >> simp[] >>
  Cases_on `t` >> simp[]
  >- (IF_CASES_TAC
      >- (simp[] >> rpt strip_tac >> gvs[]) >>
      Cases_on `lookup_block h fn.fn_blocks`
      >- (simp[] >> rpt strip_tac >> gvs[]) >> simp[] >>
      qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
      IF_CASES_TAC
      >- (strip_tac >> gvs[] >>
          drule forget_stack_wf_marked >>
          simp[generated_plan_state_wf_marked_def, plan_slots_bounded_def] >>
          metis_tac[]) >>
      IF_CASES_TAC
      >- (pairarg_tac >> strip_tac >> gvs[] >>
          `generated_plan_state_wf_marked base' ps''` by
            metis_tac[popmany_plan_wf_marked] >>
          drule mark_dead_stack_wf_marked >>
          simp[generated_plan_state_wf_marked_def, plan_slots_bounded_def] >>
          metis_tac[]) >>
      metis_tac[popmany_plan_wf_marked]) >>
  strip_tac >> gvs[]
QED

Theorem clean_stack_plan_inventory:
  !ps liveness cfg fn bb ops ps'.
    clean_stack_plan liveness cfg fn bb ps = (ops, ps') ==>
    !op. MEM op ps'.ps_stack \/ op IN FDOM ps'.ps_spilled ==>
      op = dead_stack_marker \/ MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> simp[clean_stack_plan_def] >>
  Cases_on `cfg_preds_of cfg bb.bb_label`
  >- (simp[] >> rpt strip_tac >> gvs[]) >> simp[] >>
  Cases_on `t` >> simp[]
  >- (IF_CASES_TAC
      >- (simp[] >> rpt strip_tac >> gvs[]) >>
      Cases_on `lookup_block h fn.fn_blocks`
      >- (simp[] >> rpt strip_tac >> gvs[]) >> simp[] >>
      qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
      IF_CASES_TAC
      >- (strip_tac >> gvs[MEM_MAP] >> metis_tac[]) >>
      IF_CASES_TAC
      >- (pairarg_tac >> strip_tac >> gvs[] >>
          metis_tac[mark_dead_stack_mem, popmany_plan_inventory_subset]) >>
      metis_tac[popmany_plan_inventory_subset]) >>
  strip_tac >> gvs[]
QED

Theorem clean_stack_plan_spilled:
  !ps liveness cfg fn bb ops ps'.
    clean_stack_plan liveness cfg fn bb ps = (ops, ps') ==>
    ps'.ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> simp[clean_stack_plan_def] >>
  Cases_on `cfg_preds_of cfg bb.bb_label`
  >- (simp[] >> rpt strip_tac >> gvs[]) >> simp[] >>
  Cases_on `t` >> simp[]
  >- (IF_CASES_TAC
      >- (simp[] >> rpt strip_tac >> gvs[]) >>
      Cases_on `lookup_block h fn.fn_blocks`
      >- (simp[] >> rpt strip_tac >> gvs[]) >> simp[] >>
      qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
      IF_CASES_TAC
      >- (strip_tac >> gvs[]) >>
      IF_CASES_TAC
      >- (pairarg_tac >> strip_tac >> gvs[] >>
          metis_tac[phi_popmany_spilled]) >>
      metis_tac[phi_popmany_spilled]) >>
  strip_tac >> gvs[]
QED

Theorem plan_stack_rel_forget_map:
  !lo vs stk astk f.
    plan_stack_rel lo vs stk astk /\
    (!op. MEM op stk ==> f op = dead_stack_marker \/ f op = op) ==>
    plan_stack_rel lo vs (MAP f stk) astk
Proof
  simp[plan_stack_rel_def, GSYM MAP_REVERSE] >> rpt strip_tac >>
  simp[EL_MAP] >>
  `MEM (EL i (REVERSE stk)) stk` by
    metis_tac[MEM_EL, MEM_REVERSE, LENGTH_REVERSE] >>
  metis_tac[]
QED

Theorem fn_frame_inv_forget_map:
  !ctx cp lo fn ra rest mem0 ps vs as f.
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    (!op. MEM op ps.ps_stack ==> f op = dead_stack_marker \/ f op = op) ==>
    fn_frame_inv ctx cp lo fn ra rest mem0
      (ps with ps_stack := MAP f ps.ps_stack) vs as
Proof
  simp[fn_frame_inv_def, context_venom_asm_rel_def] >>
  rpt strip_tac >>
  metis_tac[plan_stack_rel_forget_map]
QED

Theorem do_swap_local_marked_sim:
  !base dist ps ops ps' lo o2pc prog vs st initial_fmp.
    generated_plan_state_wf_marked base ps /\
    do_swap dist ps = (ops, ps') /\ dist < LENGTH ps.ps_stack /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==>
           off < dimword (:256)) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      venom_asm_rel lo ps' vs st' /\
      generated_plan_state_wf_marked base ps'
Proof
  rpt gen_tac >> strip_tac >>
  `generated_plan_state_wf_marked base' ps'` by
    metis_tac[do_swap_wf_marked] >>
  `EVERY (\s. case s of SOSpill off => off < dimword (:256)
        | SORestore off => off < dimword (:256) | _ => T) ops` by
    (simp[EVERY_MEM] >> gen_tac >> strip_tac >>
     Cases_on `s` >> simp[] >> metis_tac[]) >>
  drule do_swap_venom_asm_rel_numeric >>
  disch_then drule >>
  fs[generated_plan_state_wf_marked_def] >>
  metis_tac[]
QED

Theorem venom_asm_rel_forget_map:
  !lo ps vs st f.
    venom_asm_rel lo ps vs st /\
    (!op. MEM op ps.ps_stack ==> f op = dead_stack_marker \/ f op = op) ==>
    venom_asm_rel lo (ps with ps_stack := MAP f ps.ps_stack) vs st
Proof
  simp[venom_asm_rel_def] >> rpt strip_tac >>
  metis_tac[plan_stack_rel_forget_map]
QED

Theorem clean_stack_plan_local_sim:
  !base ps ops ps' lo o2pc prog vs st initial_fmp liveness cfg fn bb.
    clean_stack_plan liveness cfg fn bb ps = (ops, ps') /\
    generated_plan_state_wf_marked base ps /\
    EVERY (\s. case s of SOSpill off => off < dimword (:256)
      | SORestore off => off < dimword (:256) | _ => T) ops /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      generated_plan_state_wf_marked base ps'
Proof
  rpt gen_tac >> strip_tac >>
  `generated_plan_state_wf_marked base' ps'` by
    metis_tac[clean_stack_plan_wf_marked] >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[generated_plan_state_wf_marked_def] >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  simp[clean_stack_plan_def] >>
  Cases_on `cfg_preds_of cfg bb.bb_label`
  >- (strip_tac >> gvs[] >> qexists `st` >>
      simp[execute_plan_def, asm_steps_def]) >> simp[] >>
  Cases_on `t`
  >- (simp[] >> IF_CASES_TAC
      >- (strip_tac >> gvs[] >> qexists `st` >>
          simp[execute_plan_def, asm_steps_def]) >>
      Cases_on `lookup_block h fn.fn_blocks`
      >- (simp[] >> strip_tac >> gvs[] >> qexists `st` >>
          simp[execute_plan_def, asm_steps_def]) >> simp[] >>
      qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
      IF_CASES_TAC
      >- (strip_tac >> gvs[] >> qexists `st` >>
          simp[execute_plan_def, asm_steps_def] >>
          irule venom_asm_rel_forget_map >> simp[]) >>
      IF_CASES_TAC
      >- (pairarg_tac >> strip_tac >> gvs[] >>
          drule_all popmany_plan_sim_numeric >>
          disch_then (qspec_then `o2pc` strip_assume_tac) >>
          qexists `st'` >> simp[] >>
          simp[mark_dead_stack_def] >>
          irule venom_asm_rel_forget_map >> simp[] >>
          rpt strip_tac >> IF_CASES_TAC >> simp[]) >>
      strip_tac >> drule_all popmany_plan_sim_numeric >>
      disch_then (qspec_then `o2pc` strip_assume_tac) >>
      qexists `st'` >> simp[] >> decide_tac) >>
  simp[] >> strip_tac >> gvs[] >> qexists `st` >>
  simp[execute_plan_def, asm_steps_def]
QED

(* Used by fnFrameSinglePred$single_pred_prefix_frame_sim, for the cleanup
   a single-predecessor block runs before its instructions.

   Why it should hold: the cleanup either emits nothing and only replaces
   stack entries by dead_stack_marker (mark_dead_stack, or the whole stack
   when no variable is needed), which plan_stack_rel accepts at any slot, or
   pops variables by popmany_plan (swaps to the top, spilling when deeper
   than 16, then POP).  Those moves keep every remaining slot's value;
   spills use fresh offsets inside the frame's region (the region premise
   on ps2 and the allocator's monotonicity), so the caller's rest, the
   context memory relation and spill bytes outside the frame's closure are
   unchanged.  The surviving slots are a subset of the old ones plus
   markers. *)
Theorem clean_stack_plan_frame_sim:
  !ctx cp lo o2pc prog liveness cfg fn bb base ps vs as clean_ops ps2
   r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generated_plan_state_wf_marked base ps /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    clean_stack_plan liveness cfg fn bb ps = (clean_ops, ps2) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps2.ps_alloc.sa_spill_base /\
    ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) clean_ops \/ MEM (SORestore off) clean_ops ==>
           off < dimword (:256)) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp clean_ops)
    ==>
    ?n as2.
      asm_steps lo o2pc prog n as = AsmOK as2 /\
      as2.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp clean_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps2 vs as2 /\
      generated_plan_state_wf_marked base ps2 /\
      (!op. MEM op ps2.ps_stack \/ op IN FDOM ps2.ps_spilled ==>
            op = dead_stack_marker \/ MEM op ps.ps_stack \/
            op IN FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `generated_plan_state_wf_marked spillbase ps` >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  `EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) clean_ops` by
    (simp[EVERY_MEM] >> gen_tac >> strip_tac >>
     Cases_on `s` >> simp[] >> metis_tac[]) >>
  drule fnFrameTerminalPrepTheory.fn_frame_inv_local_state >> strip_tac >>
  `asm_block_at prog (st with as_stack := top).as_pc
    (execute_plan cplan.cp_initial_fmp clean_ops)` by simp[] >>
  drule_all clean_stack_plan_local_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo ps2 _ endpoint` >>
  drule asmFrameTheory.asm_steps_frame >> disch_then (qspec_then `rest` assume_tac) >>
  `st with as_stack := top ++ rest = st` by
    simp[asm_state_component_equality] >>
  qexistsl [`LENGTH (execute_plan cplan.cp_initial_fmp clean_ops)`,
    `endpoint with as_stack := endpoint.as_stack ++ rest`] >>
  conj_tac >- gvs[] >>
  conj_tac >- gvs[] >>
  conj_tac
  >- (irule fnFrameBoundaryInvokeTheory.invoke_prefix_frame_transport >> metis_tac[]) >>
  simp[] >> metis_tac[clean_stack_plan_inventory]
QED
