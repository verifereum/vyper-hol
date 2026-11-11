(*
 * gen_invoke_frame_sim_deep: fnFrameBoundary's gen_invoke_frame_sim for INVOKE, with
 * operands at any stack depth, repeated dead_stack_marker slots
 * (generated_plan_state_wf_marked) and only an address bound on the
 * plan's spill and restore offsets.  fnFrameDeep collects it with the
 * other instruction frame lemmas the block induction composes.
 *
 * TOP-LEVEL:
 *   gen_invoke_frame_sim_deep
 *)

Theory fnFrameDeepInvoke
Ancestors
  deepResidualSim deepResidualBudget fnPlanPrefix fnFrameBoundary fnFrameBoundaryInvoke
  fnFrameBoundaryGenRet
  fnFrameBoundaryEntryParams fnFrameTerminalPrep genFrameSim frameRel contextCodegenRel
  codegenRel regularPostfixSim preparedPrefixSim asmFrame prefixSim stackOpSim
  doSwapSim cleanOpsSim planAlign foldlSim strongPrefixSim prefixExec blockSimHelpers unitShapeDefs genBlockSim
  mixedPrefixSim stackPlanGen stackPlanTypes stackPlanOps planExec asmSem
  venomExecSemantics venomState venomInst fcgDefs livenessDefs dfgDefs cfgDefs
  venomWf venomEffects asmIR frameViewFacts finite_map callLayoutDefs fmpWfDefs
  list rich_list pred_set reorderSim planWf stackModel regularMemorySim fcgPostorder
  contextPlanLayoutProps fmpLowerProps generatedPrefixSim allocMono codegen

(* ===== Cleanup without stack distinctness =====

   With repeated dead_stack_marker slots the residual stack need not be
   ALL_DISTINCT, so the dead-output pops and the optimistic swap are
   simulated with do_swap_venom_asm_rel_numeric, which needs only the
   spill layout and an address bound on the plan's offsets. *)

Theorem pop_one_step_sim_numeric:
  !item ps ops ps' lo o2pc prog vs st initial_fmp.
    pop_one_step item ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_depth item ps.ps_stack`
  >- (gvs[pop_one_step_def] >> qexists `st` >>
      simp[execute_plan_def, asm_steps_def]) >>
  rename1 `stack_get_depth item ps.ps_stack = SOME dist` >>
  `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  drule_all entry_pop_one_step_some >> strip_tac >>
  qspecl_then [`dist`, `ps`] mp_tac do_swap_layout_wf >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on `do_swap dist ps` >>
  rename1 `do_swap dist ps = (swap_ops, ps2)` >>
  gvs[] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  pure_rewrite_tac[execute_plan_append, asm_block_at_append] >> strip_tac >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) swap_ops` by
    fs[EVERY_APPEND] >>
  drule_all do_swap_venom_asm_rel_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `0 < LENGTH ps2.ps_stack` by
    (drule do_swap_length >> simp[] >> decide_tac) >>
  `is_simple_stack_op (SOPop 1)` by simp[is_simple_stack_op_def] >>
  `FST (stack_op_wf lo (SOPop 1) (LENGTH ps2.ps_stack))` by
    simp[stack_op_wf_def] >>
  `asm_block_at prog st'.as_pc (exec_stack_op initial_fmp (SOPop 1))` by
    gvs[execute_plan_def] >>
  qpat_x_assum `venom_asm_rel lo ps vs st` kall_tac >>
  drule_all simple_op_venom_asm_rel >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists `st''` >> conj_tac
  >- (simp[execute_plan_def] >> irule asm_steps_compose_ok >>
      qexists `st'` >> gvs[execute_plan_def]) >>
  gvs[apply_simple_op_def, execute_plan_def, stack_pop_def]
QED

Theorem pop_steps_sim_numeric:
  !items ps ops ps' lo o2pc prog vs st initial_fmp.
    plan_steps pop_one_step items ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  Induct
  >- (rpt gen_tac >> simp[plan_steps_def] >> strip_tac >>
      gvs[] >> qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `pop_one_step h ps` >>
  rename1 `pop_one_step h ps = (ops1, ps1)` >>
  Cases_on `plan_steps pop_one_step items ps1` >>
  rename1 `plan_steps pop_one_step items ps1 = (ops2, ps2)` >>
  gvs[plan_steps_def] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  pure_rewrite_tac[execute_plan_append, asm_block_at_append] >> strip_tac >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops1 /\
   EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops2` by
    fs[EVERY_APPEND] >>
  drule_all pop_one_step_sim_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `asm_block_at prog st'.as_pc (execute_plan initial_fmp ops2)` by gvs[] >>
  first_x_assum drule_all >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists `st''` >> simp[] >> irule asm_steps_compose_ok >>
  qexists `st'` >> simp[]
QED

Theorem popmany_plan_sim_numeric:
  !items ps ops ps' lo o2pc prog vs st initial_fmp.
    popmany_plan items ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `items = []`
  >- (gvs[popmany_plan_def] >> qexists `st` >>
      simp[execute_plan_def, asm_steps_def]) >>
  Cases_on `EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) items) /\
    is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) items))`
  >- ( qpat_x_assum `_ /\ _` strip_assume_tac >>
       `LENGTH items < LENGTH ps.ps_stack` by
        (irule contiguous_top_stack_bound >> simp[]) >>
       `LENGTH items <= 16` by gvs[is_contiguous_top_def] >>
       drule_all popmany_plan_contiguous_sim >>
       disch_then (qspec_then `o2pc` strip_assume_tac) >>
       qexists `st'` >> simp[] >>
       qspecl_then [`LENGTH items`, `ps`] mp_tac do_swap_layout_wf >>
       impl_tac >- simp[] >> strip_tac >>
       qpat_x_assum `popmany_plan _ _ = _` mp_tac >>
       Cases_on `items` >- gvs[] >>
       simp[popmany_plan_def] >>
       Cases_on `do_swap (LENGTH (h::t)) ps` >>
       rename1 `do_swap _ ps = (swap_ops, ps2)` >>
       strip_tac >> gvs[]) >>
  `popmany_individual items ps = (ops,ps')` by
    (drule_all popmany_plan_noncontig_new >> simp[]) >>
  qpat_x_assum `popmany_individual _ _ = _` mp_tac >>
  pure_rewrite_tac[popmany_individual_eq_foldl, pop_foldl_body_eq_foldl_body,
    GSYM plan_steps_eq_foldl] >>
  strip_tac >> drule_all pop_steps_sim_numeric >> simp[]
QED

Theorem optimistic_swap_sim_numeric:
  !dfg inst next_live next_is_term ps ops ps' lo o2pc prog vs st initial_fmp.
    optimistic_swap_plan dfg inst next_live next_is_term ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `optimistic_swap_plan _ _ _ _ _ = _` mp_tac >>
  simp[optimistic_swap_plan_def] >>
  Cases_on `next_is_term` >- (simp[] >> strip_tac >> gvs[] >>
    qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  Cases_on `inst.inst_outputs = []` >- (simp[] >> strip_tac >> gvs[] >>
    qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  Cases_on `next_live = []` >- (simp[] >> strip_tac >> gvs[] >>
    qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  Cases_on `operand_equiv dfg (Var (LAST inst.inst_outputs)) (Var (LAST next_live))`
  >- (simp[] >> strip_tac >> gvs[] >> qexists `st` >>
      simp[execute_plan_def, asm_steps_def]) >>
  simp[] >> Cases_on `stack_get_depth (Var (LAST next_live)) ps.ps_stack`
  >- (simp[] >> strip_tac >> gvs[] >> qexists `st` >>
      simp[execute_plan_def, asm_steps_def]) >>
  rename1 `stack_get_depth _ ps.ps_stack = SOME dist` >> simp[] >> strip_tac >>
  `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  qspecl_then [`dist`, `ps`] mp_tac do_swap_layout_wf >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all do_swap_venom_asm_rel_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists `st'` >> gvs[]
QED

(* The context-level versions, with the footprint outside fn's closure. *)
Theorem context_popmany_outside_closure_numeric:
  !items ps ops ps' cp lo o2pc prog vs st initial_fmp r ctx name.
    popmany_plan items ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    context_venom_asm_rel cp lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      context_venom_asm_rel cp lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~closure_spill_byte ctx cp name b ==>
        read_byte b st'.as_memory = read_byte b st.as_memory) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule entry_context_to_local_memory >> strip_tac >>
  drule_all popmany_plan_sim_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `context_venom_asm_rel cplan lo ps vs st` >>
  `context_memory_rel cplan vs.vs_memory st.as_memory` by
    gvs[context_venom_asm_rel_def] >>
  drule_all entry_local_to_context_memory >> strip_tac >>
  drule entry_local_memory_footprint >> strip_tac >>
  qexists `st'` >> simp[] >> rpt strip_tac >>
  irule entry_local_footprint_outside_closure >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem context_optimistic_swap_outside_closure_numeric:
  !dfg inst next_live next_is_term ps ops ps' cp lo o2pc prog vs st initial_fmp r ctx name.
    optimistic_swap_plan dfg inst next_live next_is_term ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    context_venom_asm_rel cp lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      context_venom_asm_rel cp lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~closure_spill_byte ctx cp name b ==>
        read_byte b st'.as_memory = read_byte b st.as_memory) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule entry_context_to_local_memory >> strip_tac >>
  drule_all optimistic_swap_sim_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `context_venom_asm_rel cplan lo ps vs st` >>
  `context_memory_rel cplan vs.vs_memory st.as_memory` by
    gvs[context_venom_asm_rel_def] >>
  drule_all entry_local_to_context_memory >> strip_tac >>
  drule entry_local_memory_footprint >> strip_tac >>
  qexists `st'` >> simp[] >> rpt strip_tac >>
  irule entry_local_footprint_outside_closure >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem invoke_cleanup_context_numeric:
  !outs nl halting called pops popped dfg inst term opts swapped final
    cplan lo o2pc prog vs st r ctx name.
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped /\
  spill_alloc_layout_wf called.ps_alloc called.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (pops ++ opts) /\
  context_venom_asm_rel cplan lo called vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp (pops ++ opts)) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))) st = AsmOK st' /\
    context_venom_asm_rel cplan lo final vs st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts)) /\
    (!b. ~closure_spill_byte ctx cplan name b ==>
      read_byte b st'.as_memory = read_byte b st.as_memory)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all invoke_cleanup_alloc >> strip_tac >>
  `r.sr_spill_base <= popped.ps_alloc.sa_spill_base /\
   popped.ps_alloc.sa_next_offset <= r.sr_spill_end /\
   r.sr_spill_base <= swapped.ps_alloc.sa_spill_base /\
   swapped.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
     | SORestore off => off < dimword(:256) | _ => T) pops /\
   EVERY (\s. case s of SOSpill off => off < dimword(:256)
     | SORestore off => off < dimword(:256) | _ => T) opts` by
    fs[EVERY_APPEND] >>
  `asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp pops) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp pops))
     (execute_plan cplan.cp_initial_fmp opts)` by
    gvs[execute_plan_append, asm_block_at_append] >>
  `?mid. asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp pops)) st =
       AsmOK mid /\
     context_venom_asm_rel cplan lo popped vs mid /\
     mid.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp pops) /\
     (!b. ~closure_spill_byte ctx cplan name b ==>
       read_byte b mid.as_memory = read_byte b st.as_memory) /\
     spill_alloc_layout_wf popped.ps_alloc popped.ps_spilled` by
    (Cases_on `outs = []`
     >- (gvs[] >> qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
     Cases_on `~halting \/ LENGTH outs > 1`
     >- (fs[] >> drule_all context_popmany_outside_closure_numeric >>
         disch_then (qspecl_then [`o2pc`, `ctx`] strip_assume_tac) >>
         qexists `st'` >> simp[]) >>
     gvs[] >> qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  `asm_block_at prog mid.as_pc (execute_plan cplan.cp_initial_fmp opts)` by
    (qpat_x_assum `mid.as_pc = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `?fin. asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp opts)) mid =
       AsmOK fin /\
     context_venom_asm_rel cplan lo swapped vs fin /\
     fin.as_pc = mid.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp opts) /\
     (!b. ~closure_spill_byte ctx cplan name b ==>
       read_byte b fin.as_memory = read_byte b mid.as_memory)` by
    (Cases_on `outs = [] \/ FILTER (\out. MEM out nl) outs = []`
     >- (gvs[] >> qexists `mid` >> simp[execute_plan_def, asm_steps_def]) >>
     fs[] >> drule_all context_optimistic_swap_outside_closure_numeric >>
     disch_then (qspecl_then [`o2pc`, `ctx`] strip_assume_tac) >>
     qexists `st'` >> simp[]) >>
  qexists `fin` >>
  conj_tac >- (pure_rewrite_tac[execute_plan_append, LENGTH_APPEND] >>
              irule asm_steps_compose_ok >> qexists `mid` >> simp[]) >>
  conj_tac >- metis_tac[invoke_context_release_dead_spills] >>
  simp[execute_plan_append] >> metis_tac[]
QED

(* fnFrameBoundaryInvoke's invoke_return_frame without stack distinctness
   of the residual, and with the address bound on the cleanup's offsets. *)
Theorem invoke_return_frame_numeric_exact:
  !ctx cplan lo o2pc prog fn ra rest mem0 arranged operands args vs mid saved vals
   callee rvs ret vs' asr r outs nl halting dfg inst term ret_lbl called
   pops popped opts swapped final.
  ordered_spill_regions cplan.cp_regions /\ MEM r cplan.cp_regions /\
  r.sr_fn_name = fn.fn_name /\
  fn_directly_calls ctx fn.fn_name callee.fn_name /\
  ~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 arranged vs mid /\
  arranged.ps_stack = stack_pop (LENGTH operands) arranged.ps_stack ++ operands /\
  mid.as_stack = REVERSE args ++ saved ++ rest /\
  LENGTH args = LENGTH operands /\
  spill_alloc_layout_wf arranged.ps_alloc arranged.ps_spilled /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T) outs)
    arranged.ps_stack /\
  (!op. op IN FDOM arranged.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) outs) /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  fn_return_state_rel ctx cplan callee rvs mid asr /\
  asr.as_stack = REVERSE vals ++ saved ++ rest /\
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state vs rvs)) = SOME vs' /\
  ALL_DISTINCT outs /\ EVERY (\x. ~retpc_var fn x) outs /\
  fresh_label "return_label"
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      (arranged with ps_stack := stack_pop (LENGTH operands) arranged.ps_stack)
      outs) = (ret_lbl, called) /\
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (pops ++ opts) /\
  asm_block_at prog asr.as_pc
    (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts))) /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  ?fin.
    asm_steps lo o2pc prog
      (1 + LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))) asr = AsmOK fin /\
    fn_frame_inv ctx cplan lo fn ra rest mem0 final vs' fin /\
    fin.as_pc = asr.as_pc +
      LENGTH (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts)))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `consumed = arranged with
    ps_stack := stack_pop (LENGTH operands) arranged.ps_stack` >>
  `context_venom_asm_rel cplan lo consumed (frame_view fn ra vs)
     (mid with as_stack := saved)` by
    (simp[Abbr `consumed`] >> irule invoke_consumed_context >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`ctx`, `mem0`, `rest`, `REVERSE args`] >> simp[]) >>
  suspend "local"
QED

Resume invoke_return_frame_numeric_exact[local]:
  `spill_alloc_layout_wf consumed.ps_alloc consumed.ps_spilled /\
   (!op. op IN FDOM consumed.ps_spilled ==>
     EVERY (\out. case op of Var x => x <> out | _ => T) outs) /\
   r.sr_spill_base <= consumed.ps_alloc.sa_spill_base /\
   consumed.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    simp[Abbr `consumed`] >>
  `EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T) outs)
     consumed.ps_stack` by
    (simp[Abbr `consumed`] >>
     qpat_x_assum `arranged.ps_stack = _` (fn th =>
       qpat_x_assum `EVERY _ arranged.ps_stack`
         (mp_tac o ONCE_REWRITE_RULE [th])) >>
     simp[EVERY_APPEND]) >>
  `!op off. FLOOKUP consumed.ps_spilled op = SOME off ==>
     r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end /\
     EVERY (\out. case op of Var x => x <> out | _ => T) outs` by
    (rpt gen_tac >> strip_tac >>
     `op IN FDOM consumed.ps_spilled` by fs[FLOOKUP_DEF] >>
     fs[doSwapSimTheory.spill_alloc_layout_wf_def] >> res_tac >> simp[]) >>
  `fn_return_state_rel ctx cplan callee rvs (mid with as_stack := saved)
     (asr with as_stack := REVERSE vals ++ saved)` by
    fs[fn_return_state_rel_def, venom_asm_terminal_rel_def] >>
  qspecl_then [`ctx`, `cplan`, `fn`, `callee`, `r`, `lo`, `ra`, `consumed`, `outs`,
    `vals`, `vs`, `rvs`, `ret`, `vs'`, `mid with as_stack := saved`,
    `asr with as_stack := REVERSE vals ++ saved`] mp_tac invoke_return_context >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, fs[]]) >>
  strip_tac >>
  drule_all invoke_called_plan_fields >> strip_tac >>
  suspend "cleanup"
QED

Resume invoke_return_frame_numeric_exact[cleanup]:
  `spill_alloc_layout_wf called.ps_alloc called.ps_spilled` by
    (qpat_x_assum `called.ps_alloc = _` SUBST1_TAC >>
     qpat_x_assum `called.ps_spilled = _` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `context_venom_asm_rel cplan lo called (frame_view fn ra vs')
     ((asr with as_pc := asr.as_pc + 1) with as_stack := REVERSE vals ++ saved)` by
    (qpat_x_assum `context_venom_asm_rel _ _ (consumed with ps_stack := _) _ _` mp_tac >>
     simp[context_venom_asm_rel_def]) >>
  `asm_block_at prog asr.as_pc [AsmLabel ret_lbl] /\
   asm_block_at prog (asr.as_pc + 1)
     (execute_plan cplan.cp_initial_fmp (pops ++ opts))` by
    (qpat_x_assum `asm_block_at prog asr.as_pc _` mp_tac >>
     pure_rewrite_tac[execute_plan_def, MAP, FLAT, exec_stack_op_def,
       asm_block_at_append] >> simp[]) >>
  `asm_steps lo o2pc prog 1 asr = AsmOK (asr with as_pc := asr.as_pc + 1)` by
    (irule label_op_asm_steps >> qexists `ret_lbl` >> simp[]) >>
  qspecl_then [`outs`, `nl`, `halting`, `called`, `pops`, `popped`, `dfg`, `inst`,
    `term`, `opts`, `swapped`, `final`, `cplan`, `lo`, `o2pc`, `prog`,
    `frame_view fn ra vs'`,
    `(asr with as_pc := asr.as_pc + 1) with as_stack := REVERSE vals ++ saved`,
    `r`, `ctx`, `fn.fn_name`] mp_tac invoke_cleanup_context_numeric >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, fs[]]) >>
  disch_then (qx_choose_then `fin0` strip_assume_tac) >>
  suspend "lift"
QED

Resume invoke_return_frame_numeric_exact[lift]:
  qspecl_then [`LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))`, `lo`, `o2pc`,
    `prog`, `asr with as_pc := asr.as_pc + 1`, `REVERSE vals ++ saved`, `rest`,
    `fin0`] mp_tac asm_steps_frame >>
  impl_tac >- fs[] >> strip_tac >>
  `(asr with as_pc := asr.as_pc + 1) with as_stack := REVERSE vals ++ saved ++ rest =
     asr with as_pc := asr.as_pc + 1` by
    simp[asm_state_component_equality] >>
  qexists `fin0 with as_stack := fin0.as_stack ++ rest` >>
  conj_tac >- (irule asm_steps_compose_ok >>
               qexists `asr with as_pc := asr.as_pc + 1` >> fs[]) >>
  reverse conj_tac
  >- simp[execute_plan_def, exec_stack_op_def] >>
  drule invoke_return_frame_fields >> strip_tac >>
  `!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
     read_byte b asr.as_memory = read_byte b mem0` by
    (qspecl_then [`ctx`, `cplan`, `lo`, `fn`, `ra`, `rest`, `mem0`, `arranged`,
       `vs`, `mid`, `callee`, `rvs`, `mid`, `asr`] mp_tac
       invoke_return_outside_closure >> simp[]) >>
  qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fn_frame_inv_def] >> strip_tac >>
  rpt conj_tac >>
  qpat_x_assum `final = _` SUBST_ALL_TAC >>
  FIRST [first_assum ACCEPT_TAC,
         rpt strip_tac >> fs[] >> NO_TAC,
         qexists `r` >> fs[] >> NO_TAC]
QED

Finalise invoke_return_frame_numeric_exact

Theorem invoke_return_frame_numeric:
  !ctx cplan lo o2pc prog fn ra rest mem0 arranged operands args vs mid saved vals
   callee rvs ret vs' asr r outs nl halting dfg inst term ret_lbl called
   pops popped opts swapped final.
  ordered_spill_regions cplan.cp_regions /\ MEM r cplan.cp_regions /\
  r.sr_fn_name = fn.fn_name /\
  fn_directly_calls ctx fn.fn_name callee.fn_name /\
  ~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 arranged vs mid /\
  arranged.ps_stack = stack_pop (LENGTH operands) arranged.ps_stack ++ operands /\
  mid.as_stack = REVERSE args ++ saved ++ rest /\
  LENGTH args = LENGTH operands /\
  spill_alloc_layout_wf arranged.ps_alloc arranged.ps_spilled /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T) outs)
    arranged.ps_stack /\
  (!op. op IN FDOM arranged.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) outs) /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  fn_return_state_rel ctx cplan callee rvs mid asr /\
  asr.as_stack = REVERSE vals ++ saved ++ rest /\
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state vs rvs)) = SOME vs' /\
  ALL_DISTINCT outs /\ EVERY (\x. ~retpc_var fn x) outs /\
  fresh_label "return_label"
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      (arranged with ps_stack := stack_pop (LENGTH operands) arranged.ps_stack)
      outs) = (ret_lbl, called) /\
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (pops ++ opts) /\
  asm_block_at prog asr.as_pc
    (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts))) /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  ?n fin.
    asm_steps lo o2pc prog n asr = AsmOK fin /\
    fn_frame_inv ctx cplan lo fn ra rest mem0 final vs' fin /\
    fin.as_pc = asr.as_pc +
      LENGTH (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all invoke_return_frame_numeric_exact >> metis_tac[]
QED

(* ===== Entry: input prefix and call packet over the marked state ===== *)

Theorem invoke_selected_prefix_sim_marked:
  EVERY (\op. ~is_label_operand op) operands /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan INVOKE operands nl ps = (iops,prepared) /\
  reorder_plan dfg operands prepared = (rops,arranged) /\
  LENGTH operands <= 16 /\ LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val vs lo op = operand_val vs lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  plan_state_residual_wf_marked spillbase operands (LENGTH operands) arranged /\
  arranged.ps_stack = stack_pop (LENGTH operands) arranged.ps_stack ++ operands /\
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (iops ++ rops)))
          st = AsmOK st' /\
    venom_asm_rel lo arranged vs st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops))
Proof
  strip_tac >>
  `emit_input_plan ADD operands nl ps = (iops,prepared)` by
    metis_tac[invoke_label_free_input] >>
  `!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)` by
    (rpt strip_tac >>
     qpat_x_assum `EVERY (\op. ~is_label_operand op) _` mp_tac >>
     simp[EVERY_MEM] >> disch_then (qspec_then `Label l` mp_tac) >>
     simp[stackPlanTypesTheory.is_label_operand_def]) >>
  `ADD <> INVOKE /\ PERM operands operands` by simp[] >>
  drule_all selected_prefix_prepared_sim_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >> simp[] >>
  qexists `st'` >> simp[]
QED

Theorem invoke_frame_prefix_marked:
  !ctx cp lo o2pc prog fn ra rest mem0 base ps vs st operands nl
    iops prepared dfg rops arranged r.
  EVERY (\op. ~is_label_operand op) operands /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan INVOKE operands nl ps = (iops,prepared) /\
  reorder_plan dfg operands prepared = (rops,arranged) /\
  LENGTH operands <= 16 /\ LENGTH operands <= LENGTH prepared.ps_stack /\
  generated_plan_state_wf_marked base ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp (iops ++ rops)) ==>
  plan_state_residual_wf_marked base operands (LENGTH operands) arranged /\
  arranged.ps_stack = stack_pop (LENGTH operands) arranged.ps_stack ++ operands /\
  ?mid. asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)))
          st = AsmOK mid /\
    fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `generated_plan_state_wf_marked spillbase ps` >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  drule fnFrameTerminalPrepTheory.fn_frame_inv_local_state >> strip_tac >>
  `residual_budget_wf_marked spillbase [] ps /\ plan_slots_bounded spillbase ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    (drule generated_plan_state_wf_marked_residual_nil >>
     fs[generated_plan_state_wf_marked_def]) >>
  `!op. operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
    operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[operand_val_def]) >>
  `!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo at` by
    (simp[] >> metis_tac[]) >>
  `asm_block_at prog (st with as_stack := top).as_pc
    (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by simp[] >>
  drule_all invoke_selected_prefix_sim_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  suspend "lift"
QED

Resume invoke_frame_prefix_marked[lift]:
  rename1 `venom_asm_rel lo arranged _ endpoint` >>
  simp[] >>
  drule asm_steps_frame >> disch_then (qspec_then `rest` assume_tac) >>
  `st with as_stack := top ++ rest = st` by
    simp[asm_state_component_equality] >>
  qexists `endpoint with as_stack := endpoint.as_stack ++ rest` >>
  conj_tac >- gvs[] >>
  conj_tac >- (irule invoke_prefix_frame_transport >> metis_tac[]) >>
  simp[]
QED
Finalise invoke_frame_prefix_marked

(* Any-depth ownership, as the marked state allows, gives membership. *)
Theorem owned_operands_mem[local]:
  !operands ps.
  (!op. MEM op operands /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) ==>
  !op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled
Proof
  rpt strip_tac >>
  qpat_x_assum `!op. MEM op _ /\ is_var_operand op ==> _` drule >>
  simp[] >> strip_tac
  >- (Cases_on `stack_get_depth op ps.ps_stack` >> gvs[] >>
      drule stack_get_depth_props >> simp[stack_peek_def] >>
      strip_tac >> disj1_tac >>
      qpat_x_assum `EL _ _ = op` (SUBST1_TAC o SYM) >>
      irule EL_MEM >> decide_tac) >>
  Cases_on `op IN FDOM ps.ps_spilled` >> fs[FLOOKUP_DEF]
QED

Theorem invoke_generated_frame_prefix_marked:
  !ctx cp lo o2pc prog liveness dfg cfg fn inst nl halting term label
    base ps vs st ops final ra rest mem0 nm arg_ops values r.
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  EVERY (\op. ~is_label_operand op) (compute_operands inst) /\
  generated_plan_state_wf_marked base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan INVOKE (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  eval_operands (REVERSE (compute_operands inst)) (frame_view fn ra vs) = SOME values ==>
  ?iops prepared rops arranged ret_lbl post mid saved.
    emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)))
      st = AsmOK mid /\
    asm_block_at prog mid.as_pc (execute_plan cp.cp_initial_fmp
      ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
    plan_state_residual_wf_marked base (compute_operands inst) (LENGTH (compute_operands inst)) arranged /\
    arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++ compute_operands inst /\
    mid.as_stack = values ++ saved ++ rest /\
    LENGTH saved = LENGTH (stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack) /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `generated_plan_state_wf_marked spillbase ps` >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  drule_all invoke_plan_decompose >> strip_tac >>
  suspend "bounds"
QED

Resume invoke_generated_frame_prefix_marked[bounds]:
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (mp_tac (Q.SPECL [`compute_operands inst`, `ps`] owned_operands_mem) >>
     impl_tac >- metis_tac[] >> simp[]) >>
  `r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    (drule_all invoke_arranged_alloc >> strip_tac >> gvs[] >> decide_tac) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops)` by
    (qpat_x_assum `EVERY _ ops` mp_tac >>
     qpat_x_assum `ops = _` (fn th => pure_rewrite_tac[th]) >>
     simp[EVERY_APPEND]) >>
  `asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    gvs[execute_plan_append, asm_block_at_append] >>
  qpat_x_assum `consumed = _` kall_tac >>
  qpat_x_assum `pushed = _` kall_tac >>
  qpat_x_assum `fresh_label _ _ = _` kall_tac >>
  ntac 2 (qpat_x_assum `(if _ then _ else _) = _` kall_tac) >>
  qpat_x_assum `final = _` kall_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `EVERY _ ops` kall_tac >>
  `LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack` by gvs[] >>
  drule_all invoke_frame_prefix_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  suspend "finish"
QED

Resume invoke_generated_frame_prefix_marked[finish]:
  `EVERY (\op. op <> dead_stack_marker) (compute_operands inst)` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all invoke_frame_arranged_stack >> strip_tac >>
  `asm_block_at prog mid.as_pc (execute_plan cplan.cp_initial_fmp
    ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ (pops ++ opts)))` by
    (qpat_x_assum `asm_block_at prog st.as_pc (execute_plan _ ops)` mp_tac >>
     qpat_x_assum `ops = _` mp_tac >>
     qpat_x_assum `mid.as_pc = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[execute_plan_append, asm_block_at_append] >> rpt strip_tac >>
     gvs[] >> metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  qexistsl [`iops`, `prepared`, `rops`, `arranged`, `ret_lbl`, `pops ++ opts`, `mid`, `saved`] >>
  simp[APPEND_ASSOC]
QED
Finalise invoke_generated_frame_prefix_marked

(* fnFrameBoundaryInvoke's invoke_enter_callee over the marked state, with
   any-depth ownership and the address bound on all of ops. *)
Theorem invoke_enter_callee_marked:
  !Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops callee args cvs.
  ctx = unit.cu_context /\
  unit_shape_ok unit /\
  codegen_context_obligations Inv ctx cp /\
  reachability_closed Inv ctx /\
  MEM fn ctx.ctx_functions /\
  MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
  Inv ctx fn inst vs /\ active_inst fn inst vs /\
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\
  (!f inst callee_name args callee.
     MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
     MEM inst (fn_insts f) /\
     inst.inst_opcode = INVOKE /\
     inst.inst_operands = Label callee_name :: args /\
     lookup_function callee_name ctx.ctx_functions = SOME callee ==>
     fn_has_retpc callee) /\
  (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
     ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
              FLOOKUP o2pc off = SOME pc /\
              asm_block_at prog pc
                (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
  opaque_use_ok fn /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\
  MEM inst (fn_insts fn) /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode
      (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
           EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
           ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                 FLOOKUP o2pc off = SOME (st.as_pc + i)) /\
  (!op. MEM op (compute_operands inst) ==>
        eval_operand op (frame_view fn ra vs) =
        operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
           (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
            MEM at (compute_operands inst)) /\
           operand_equiv dfg op at ==>
           operand_val (frame_view fn ra vs) lo op =
           operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
    (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps =
    SOME (ops, final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops vs = SOME args /\
  setup_callee callee args vs = SOME cvs ==>
  ?j iops prepared rops arranged ret_lbl ret_off post mid saved cas pc.
    callee.fn_name = nm /\
    LENGTH args = LENGTH (compute_operands inst) /\
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    fn_entry_inv Inv ctx callee cvs /\
    asm_block_at prog cas.as_pc
      (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_has_retpc callee /\
    fn_entry_state_rel cp callee cvs cas (n2w ret_off) (saved ++ rest) /\
    FLOOKUP o2pc (w2n ((n2w ret_off):bytes32)) =
      SOME (st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) /\
    emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)))
      st = AsmOK mid /\
    asm_block_at prog mid.as_pc (execute_plan cp.cp_initial_fmp
      ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
    plan_state_residual_wf_marked base (compute_operands inst)
      (LENGTH (compute_operands inst)) arranged /\
    arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++
      compute_operands inst /\
    mid.as_stack = REVERSE args ++ saved ++ rest /\
    LENGTH saved = LENGTH (stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack) /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    asm_steps lo o2pc prog 3 mid = AsmOK cas /\
    cas = mid with <| as_stack := n2w ret_off :: mid.as_stack; as_pc := pc |>
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `codegen_context_obligations Inv ctx cplan` >>
  `compute_operands inst = arg_ops /\ EVERY (\op. ~is_label_operand op) arg_ops` by
    (irule invoke_compute_operands >> gvs[] >> metis_tac[]) >>
  drule_all invoke_callee_entry_facts >> strip_tac >>
  `fn_has_retpc callee` by (first_x_assum irule >> metis_tac[]) >>
  `invoke_layout_wf ctx inst` by
    (fs[codegen_context_obligations_def, fmp_lowered_context_wf_def] >>
     metis_tac[]) >>
  drule_all invoke_callee_param_arity >> strip_tac >>
  `eval_operands (REVERSE (compute_operands inst)) (frame_view fn ra vs) =
     SOME (REVERSE args)` by
    (simp[eval_operands_reverse] >>
     drule_all invoke_operands_frame_values >> simp[]) >>
  `EVERY (\op. ~is_label_operand op) (compute_operands inst) /\
   LENGTH (compute_operands inst) <=
     LENGTH (SND (emit_input_plan INVOKE (compute_operands inst) nl ps)).ps_stack` by
    (qpat_x_assum `inst.inst_opcode = INVOKE` (fn th => fs[th]) >> gvs[]) >>
  drule_all invoke_generated_frame_prefix_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  suspend "call"
QED

Resume invoke_enter_callee_marked[call]:
  `MEM callee ctx.ctx_functions /\ callee.fn_name = nm` by simp[] >>
  drule_all invoke_indexed_callee_target >>
  disch_then (qx_choosel_then [`j`, `off`, `pc`] strip_assume_tac) >>
  `?ret_off. FLOOKUP lo ret_lbl = SOME ret_off /\ ret_off < dimword (:256) /\
     FLOOKUP o2pc ret_off =
       SOME (st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3)` by
    (irule invoke_return_label_target >> qexistsl [`nm`, `ops`, `post`] >>
     simp[]) >>
  `asm_block_at prog mid.as_pc
     [AsmPushLabel ret_lbl; AsmPushLabel callee.fn_name; AsmOp "JUMP"]` by
    (irule invoke_packet_block >> metis_tac[]) >>
  `mid.as_stack = REVERSE args ++ saved ++ rest` by gvs[] >>
  qpat_x_assum `callee.fn_name = nm` (SUBST_ALL_TAC o SYM) >>
  drule_all invoke_call_entry >> strip_tac >>
  drule_all invoke_call_packet >> strip_tac >>
  `LENGTH args = LENGTH (compute_operands inst)` by
    metis_tac[eval_operands_some_length] >>
  `LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256)` by
    (`LENGTH args + 1 < 18` by decide_tac >>
     `18 < dimword (:256)` by simp[wordsTheory.dimword_def] >> decide_tac) >>
  qexistsl [`j`, `iops`, `prepared`, `rops`, `arranged`, `ret_lbl`, `ret_off`,
    `post`, `mid`, `saved`, `cas`, `pc`] >>
  gvs[] >> simp[asm_state_component_equality]
QED

Finalise invoke_enter_callee_marked

(* The structural facts invoke_return_frame_numeric_exact needs about the
   arranged state. *)
Theorem invoke_entry_structural_marked:
  !spillbase ps inst nl iops prepared dfg rops arranged.
  generated_plan_state_wf_marked spillbase ps /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
  reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    inst.inst_outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) ==>
  spill_alloc_layout_wf arranged.ps_alloc arranged.ps_spilled /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    inst.inst_outputs) arranged.ps_stack /\
  (!op. op IN FDOM arranged.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs)
Proof
  rpt gen_tac >> strip_tac >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (mp_tac (Q.SPECL [`compute_operands inst`, `ps`] owned_operands_mem) >>
     impl_tac >- metis_tac[] >> simp[]) >>
  `residual_budget_wf_marked spillbase [] ps` by
    metis_tac[generated_plan_state_wf_marked_residual_nil] >>
  `plan_state_residual_wf_marked spillbase (compute_operands inst)
     (LENGTH (compute_operands inst)) arranged` by
    metis_tac[selected_input_arranged_marked, sortingTheory.PERM_REFL] >>
  conj_tac >- fs[plan_state_residual_wf_marked_def] >>
  drule_all emit_input_plan_output_exclusion >> strip_tac >>
  `LENGTH (compute_operands inst) <= 17` by decide_tac >>
  drule_all reorder_plan_output_exclusion >> simp[]
QED

(* Enter the callee and instantiate its simulation; leaves the callee's
   three outcome clauses and the call-entry steps as assumptions. *)
val invoke_enter_marked_tac =
  drule_all invoke_enter_callee_marked >> strip_tac >>
  first_x_assum (qspecl_then [`j`, `callee`, `EL j cplan.cp_regions`, `cvs`,
    `cas`, `n2w ret_off`, `saved ++ rest`,
    `st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3`]
    mp_tac) >>
  impl_tac
  >- (rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC,
             qpat_x_assum `setup_callee _ _ _ = SOME _` mp_tac >>
               rw[setup_callee_def] >> fs[] >> NO_TAC,
             fs[] >> NO_TAC]) >>
  strip_tac >>
  `asm_steps lo o2pc prog
     (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3) st =
   AsmOK cas` by
    (irule asm_steps_compose_ok >> qexists `mid` >>
     conj_tac >> first_assum ACCEPT_TAC);

(* gen_invoke_frame_sim with any-depth ownership, generated_plan_state_wf_marked and an
   address bound on spill and restore offsets. *)
Theorem gen_invoke_frame_sim_deep:
  !fuel rpolicy unit cp prog ctx lo o2pc Inv liveness dfg cfg fn inst
   next_liveness is_halting next_is_term bb_label base ps vs as ops ps' r ra
   rest mem0 nm arg_ops.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv ctx cp /\
    reachability_closed Inv ctx /\
    MEM fn ctx.ctx_functions /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    Inv ctx fn inst vs /\ active_inst fn inst vs /\
    inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label nm :: arg_ops /\
    ~vs.vs_call_ctx.cc_static /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\
       inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
       ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
                FLOOKUP o2pc off = SOME pc /\
                asm_block_at prog pc
                  (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
    (* The callee's function-level simulation at this fuel. *)
    (!j callee rj cvs cas cra crest cpc.
       j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
       EL j cp.cp_regions = rj /\
       MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
       (!l. FLOOKUP cvs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
       fn_entry_inv Inv ctx callee cvs /\
       ~cvs.vs_call_ctx.cc_static /\
       asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp rj.sr_plan) /\
       LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
       fn_entry_state_rel cp callee cvs cas cra crest /\
       (fn_has_retpc callee ==> FLOOKUP o2pc (w2n cra) = SOME cpc) ==>
       (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
          ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
                  venom_asm_terminal_rel vs' as') /\
       (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
          ?n as'. ((a = Revert_abort /\
                    asm_steps lo o2pc prog n cas = AsmRevert as') \/
                   (a = ExHalt_abort /\
                    asm_steps lo o2pc prog n cas = AsmFault as')) /\
                  venom_asm_terminal_rel vs' as') /\
       (!ret vs'. run_blocks fuel ctx callee cvs = IntRet ret vs' ==>
          ?n as'. asm_steps lo o2pc prog n cas = AsmOK as' /\
                  as'.as_pc = cpc /\
                  as'.as_stack = REVERSE ret.iret_values ++ crest /\
                  fn_return_state_rel ctx cp callee vs' cas as')) /\
    opaque_use_ok fn /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword (:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    (!vs'. step_inst fuel ctx inst vs = OK vs' ==>
       ?n as'.
         asm_steps lo o2pc prog n as = AsmOK as' /\
         fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
         as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops)) /\
    (!vs'. step_inst fuel ctx inst vs = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as') /\
    (!a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as')
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `codegen_context_obligations Inv ctx cplan` >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  rename1 `generated_plan_state_wf_marked spillbase ps` >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- suspend "ok"
  >- (drule_all invoke_source_halt >> strip_tac >> invoke_enter_marked_tac >>
      first_x_assum drule >> strip_tac >>
      qexistsl [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3 + n`,
        `as'`] >>
      metis_tac[asm_steps_compose_halt]) >>
  drule_all invoke_source_abort >> strip_tac >> invoke_enter_marked_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3 + n`,
    `as'`] >>
  metis_tac[asm_steps_compose_revert, asm_steps_compose_fault]
QED

Resume gen_invoke_frame_sim_deep[ok]:
  drule_all invoke_source_ok >> strip_tac >> invoke_enter_marked_tac >>
  first_x_assum drule >> strip_tac >>
  rename1 `asm_steps lo o2pc prog n cas = AsmOK asr` >>
  drule_all invoke_plan_decompose >> strip_tac >>
  map_every (fn q => qpat_x_assum q kall_tac) [`ctx = _`, `lo = _`, `o2pc = _`] >>
  gvs[] >>
  rename1 `emit_input_plan INVOKE _ _ ps = (iops, prepared)` >>
  rename1 `reorder_plan _ _ prepared = (rops, arranged)` >>
  rename1 `fresh_label "return_label" _ = (ret_lbl, called)` >>
  suspend "frame"
QED

Resume gen_invoke_frame_sim_deep[frame]:
  `ordered_spill_regions cplan.cp_regions /\ ctx_wf ctx` by
    fs[codegen_context_obligations_def, context_plan_layout_wf_def] >>
  `fn_directly_calls ctx fn.fn_name (EL j ctx.ctx_functions).fn_name` by
    metis_tac[invoke_direct_call] >>
  `~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name` by
    metis_tac[invoke_context_no_cycle] >>
  qspecl_then [`spillbase`, `ps`, `inst`, `next_liveness`, `iops`, `prepared`,
    `dfg`, `rops`, `arranged`] mp_tac invoke_entry_structural_marked >>
  impl_tac >- fs[] >> strip_tac >>
  `ALL_DISTINCT inst.inst_outputs` by
    metis_tac[codegen_ready_inst_outputs_distinct] >>
  `EVERY (\x. ~retpc_var fn x) inst.inst_outputs` by
    (simp[listTheory.EVERY_MEM] >> rpt gen_tac >> strip_tac >>
     irule frameViewFactsTheory.noncopy_output_not_retpc >>
     conj_tac >- fs[codegen_ready_fn_def] >> qexists `inst` >> simp[]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
     | SORestore off => off < dimword(:256) | _ => T) (pops ++ opts)` by
    fs[EVERY_APPEND] >>
  `fn_return_state_rel ctx cplan (EL j ctx.ctx_functions) rvs mid asr` by
    (qpat_x_assum `fn_return_state_rel _ _ _ _ _ asr` mp_tac >>
     simp[fn_return_state_rel_def]) >>
  `asm_block_at prog asr.as_pc
     (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts)))` by
    (`asr.as_pc = st.as_pc +
        LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3` by fs[] >>
     pop_assum SUBST1_TAC >> irule invoke_return_block >>
     qexists `(EL j ctx.ctx_functions).fn_name` >> first_assum ACCEPT_TAC) >>
  qspecl_then [`ctx`, `cplan`, `lo`, `o2pc`, `prog`, `fn`, `ra`, `rest`, `mem0`,
    `arranged`, `compute_operands inst`, `args`, `vs`, `mid`, `saved`,
    `ret.iret_values`, `EL j ctx.ctx_functions`, `rvs`, `ret`, `vs'`, `asr`, `r`,
    `inst.inst_outputs`, `next_liveness`, `is_halting`, `dfg`, `inst`,
    `next_is_term`, `ret_lbl`, `called`, `pops`, `popped`, `opts`, `swapped`,
    `release_dead_spills next_liveness swapped`] mp_tac invoke_return_frame_numeric >>
  impl_tac
  >- (rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC, fs[] >> NO_TAC]) >>
  strip_tac >>
  rename1 `asm_steps lo o2pc prog m asr = AsmOK fin` >>
  qexistsl [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3 + n + m`,
    `fin`] >>
  rpt conj_tac
  >- metis_tac[asm_steps_compose_ok]
  >- first_assum ACCEPT_TAC >>
  fs[execute_plan_def, exec_stack_op_def]
QED

Finalise gen_invoke_frame_sim_deep
