Theory generatedReorderSim
Ancestors
  generatedPrefixSim reorderSpillFresh prefixSpillReplay scratchPrefixSim reorderSim doSwapSim foldlSim
  stackPlanOps stackPlanTypes stackModel codegenRel asmSem planExec
  spillSim planWf stackOpSim blockSimHelpers list rich_list finite_map arithmetic

Theorem do_spill_tos_layout_wf:
  do_spill_tos ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  strip_tac >> qpat_x_assum `do_spill_tos _ = _` mp_tac >>
  simp[do_spill_tos_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[spill_alloc_layout_wf_after_alloc]
QED

Theorem do_spill_tos_venom_asm_rel_numeric:
  do_spill_tos ps = (ops,ps') /\
  0 < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        venom_asm_rel lo ps' vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  `EVERY (spill_fresh_for ps.ps_spilled) ops` by
    (mp_tac (Q.SPECL [`0`, `ps`, `ps.ps_spilled`, `ops`, `ps'`]
       do_spill_at_spills_fresh_frame) >> simp[do_spill_at_def]) >>
  qpat_x_assum `do_spill_tos _ = _` mp_tac >>
  simp[do_spill_tos_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `alloc_spill_slot ps.ps_alloc = (off,al)` >>
  `ps.ps_alloc.sa_spill_base <= off` by
    (irule alloc_spill_slot_ge_spill_base >>
     fs[spill_alloc_layout_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `MAX ps.ps_alloc.sa_next_offset (off + 32) = al.sa_next_offset` by
    metis_tac[alloc_spill_slot_max_agree] >>
  gvs[spill_fresh_for_def, execute_plan_def, exec_stack_op_def] >>
  drule spill_op_venom_asm_rel >>
  disch_then (qspecl_then [`o2pc`, `prog`, `off`, `stack_peek 0 ps.ps_stack`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >> qexists `st'` >> simp[] >>
  irule venom_asm_rel_ps_transfer >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[alloc_spill_slot_spill_base]
QED

Theorem do_spill_at_layout_wf:
  do_spill_at dist ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  strip_tac >> Cases_on `dist = 0`
  >- (gvs[do_spill_at_def] >> metis_tac[do_spill_tos_layout_wf]) >>
  qpat_x_assum `do_spill_at _ _ = _` mp_tac >>
  simp[do_spill_at_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule do_spill_tos_layout_wf >> simp[]
QED

Theorem do_spill_at_venom_asm_rel_numeric:
  do_spill_at dist ps = (ops,ps') /\
  dist <= 16 /\ dist < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        venom_asm_rel lo ps' vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> Cases_on `dist = 0`
  >- (gvs[do_spill_at_def] >> drule_all do_spill_tos_venom_asm_rel_numeric >>
      disch_then (qspec_then `o2pc` strip_assume_tac) >>
      qexists `st'` >> asm_rewrite_tac[] >> MATCH_ACCEPT_TAC ADD_COMM) >>
  qpat_x_assum `do_spill_at _ _ = _` mp_tac >>
  simp[do_spill_at_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `do_spill_tos (ps with ps_stack := stack_swap dist ps.ps_stack) = (sops,ps')` >>
  `execute_plan initial_fmp (SOSwap dist::sops) =
   execute_plan initial_fmp [SOSwap dist] ++ execute_plan initial_fmp sops` by
    simp[execute_plan_def] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  asm_rewrite_tac[asm_block_at_append] >> strip_tac >>
  `do_swap dist ps = ([SOSwap dist],ps with ps_stack := stack_swap dist ps.ps_stack)` by
    simp[do_swap_def] >>
  drule_all do_swap_venom_asm_rel_small >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo (ps with ps_stack := _) vs mid` >>
  `asm_block_at prog mid.as_pc (execute_plan initial_fmp sops)` by
    metis_tac[ADD_COMM] >>
  drule do_spill_tos_venom_asm_rel_numeric >>
  simp[stack_swap_length] >>
  disch_then drule_all >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo ps' vs final` >> qexists `final` >>
  simp[execute_plan_append] >> once_rewrite_tac[ADD_COMM] >>
  irule asm_steps_compose_ok >> qexists `mid` >> simp[]
QED

Theorem reduce_depth_plan_venom_asm_rel_numeric:
  !fuel targets op f n ps ops ps' st.
  reduce_depth_plan fuel targets op f n ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        venom_asm_rel lo ps' vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  Induct >> simp[Once reduce_depth_plan_def]
  >- simp[execute_plan_def, asm_steps_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `f + 1 < n` >> gvs[]
  >- simp[execute_plan_def, asm_steps_def] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> gvs[]
  >- simp[execute_plan_def, asm_steps_def] >>
  rename1 `stack_get_unfixed_depth op f n ps.ps_stack = SOME dist` >>
  Cases_on `dist <= 16` >> gvs[]
  >- simp[execute_plan_def, asm_steps_def] >>
  Cases_on `select_spill_candidate ps.ps_stack targets dist n` >> gvs[]
  >- simp[execute_plan_def, asm_steps_def] >>
  rename1 `select_spill_candidate _ _ _ _ = SOME cand` >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `do_spill_at cand ps = (spill_ops,midps)` >>
  `0 < LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> decide_tac) >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    (drule_at (Pat `select_spill_candidate _ _ _ _ = SOME _`)
       select_spill_candidate_bound >> simp[]) >>
  `spill_alloc_layout_wf midps.ps_alloc midps.ps_spilled` by
    (drule do_spill_at_layout_wf >> simp[]) >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[execute_plan_append, asm_block_at_append] >> strip_tac >>
  drule_all do_spill_at_venom_asm_rel_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `asm_steps _ _ _ _ st = AsmOK mid` >>
  `asm_block_at prog mid.as_pc (execute_plan initial_fmp rest_ops)` by
    metis_tac[ADD_COMM] >>
  first_x_assum (qspecl_then [`targets`, `op`, `f`, `n`] mp_tac) >>
  disch_then drule_all >> strip_tac >>
  rename1 `venom_asm_rel lo ps' vs final` >> simp[] >> qexists `final` >>
  simp[] >> once_rewrite_tac[ADD_COMM] >>
  irule asm_steps_compose_ok >> qexists `mid` >> simp[]
QED

Theorem reorder_restore_venom_asm_rel_numeric:
  (case stack_get_unfixed_depth op f n ps.ps_stack of
     SOME d => ([],ps)
   | NONE => (case FLOOKUP ps.ps_spilled op of
       SOME off => do_restore op ps | NONE => ([],ps))) = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        venom_asm_rel lo ps' vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> gvs[]
  >- (Cases_on `FLOOKUP ps.ps_spilled op` >> gvs[]
      >- simp[execute_plan_def, asm_steps_def] >>
      conj_tac >- metis_tac[do_restore_layout_wf] >>
      drule_all do_restore_venom_asm_rel_numeric >>
      disch_then (qspec_then `o2pc` strip_assume_tac) >>
      qexists `st'` >> asm_rewrite_tac[] >> MATCH_ACCEPT_TAC ADD_COMM) >>
  simp[execute_plan_def, asm_steps_def]
QED

Theorem reorder_prepare_venom_asm_rel_numeric:
  residual_budget_wf spill_base pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\ LENGTH pending <= 16 /\
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
  `residual_budget_wf spill_base pending ps1 /\
   LENGTH pending <= LENGTH ps1.ps_stack` by
    (drule_all reorder_restore_residual_budget_wf >>
     disch_then (qspecl_then [`op`, `f`] mp_tac) >> simp[LET_THM] >> gvs[]) >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by fs[residual_budget_wf_def] >>
  gvs[EVERY_APPEND] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[execute_plan_append, asm_block_at_append] >> strip_tac >>
  drule_all reorder_restore_venom_asm_rel_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo ps1 vs mid` >>
  Cases_on `dist > 16` >> gvs[]
  >- ( `LENGTH pending <= LENGTH ps2.ps_stack` by
         (drule reduce_depth_plan_length_floor >> simp[] >> decide_tac) >>
       `asm_block_at prog mid.as_pc (execute_plan initial_fmp reduce_ops)` by
         metis_tac[ADD_COMM] >>
       drule_all reduce_depth_plan_venom_asm_rel_numeric >>
       disch_then (qspec_then `o2pc` strip_assume_tac) >>
       rename1 `venom_asm_rel lo ps2 vs final` >> simp[] >> qexists `final` >>
       simp[] >> once_rewrite_tac[ADD_COMM] >>
       irule asm_steps_compose_ok >> qexists `mid` >> simp[]) >>
  simp[] >> qexists `mid` >> fs[execute_plan_def]
QED

Theorem plan_stack_sem_eq_exchange:
  d < LENGTH stk /\ f < LENGTH stk /\
  op = stack_peek d stk /\
  operand_val vs lo op = operand_val vs lo (stack_peek f stk) /\
  op <> dead_stack_marker /\ stack_peek f stk <> dead_stack_marker ==>
  plan_stack_sem_eq lo vs stk
    (stack_poke f op (stack_poke d (stack_peek f stk) stk))
Proof
  strip_tac >>
  simp[plan_stack_sem_eq_def, stack_poke_def, LENGTH_LUPDATE] >>
  rpt strip_tac >> simp[EL_LUPDATE] >>
  Cases_on `i = LENGTH stk - 1 - f` >> simp[]
  >- (gvs[stack_peek_def] >> metis_tac[]) >>
  Cases_on `i = LENGTH stk - 1 - d` >> simp[] >>
  gvs[stack_peek_def] >> metis_tac[]
QED

Theorem do_swap_pair_venom_asm_rel_numeric:
  do_swap d ps = (ops1,ps1) /\ do_swap f ps1 = (ops2,ps2) /\
  d < LENGTH ps.ps_stack /\ f < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (ops1 ++ ops2) /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (ops1 ++ ops2)) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) st = AsmOK st' /\
        venom_asm_rel lo ps2 vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2))
Proof
  strip_tac >>
  `spill_alloc_layout_wf ps1.ps_alloc ps1.ps_spilled` by
    (mp_tac (Q.SPECL [`d`, `ps`] do_swap_layout_wf) >> simp[]) >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack` by
    (mp_tac (Q.SPECL [`d`, `ps`] do_swap_length) >> simp[]) >>
  gvs[EVERY_APPEND] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[execute_plan_append, asm_block_at_append] >> strip_tac >>
  qpat_assum `do_swap d ps = _`
    (mp_then Any mp_tac do_swap_venom_asm_rel_numeric) >>
  disch_then drule_all >> disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo ps1 vs mid` >>
  `asm_block_at prog mid.as_pc (execute_plan initial_fmp ops2)` by metis_tac[ADD_COMM] >>
  `f < LENGTH ps1.ps_stack` by simp[] >>
  qpat_assum `do_swap f ps1 = _`
    (mp_then Any mp_tac do_swap_venom_asm_rel_numeric) >>
  disch_then drule_all >> disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo ps2 vs final` >> qexists `final` >>
  simp[execute_plan_append] >>
  irule asm_steps_compose_ok >> qexists `mid` >> simp[]
QED

Theorem reorder_one_venom_asm_rel_numeric:
  residual_budget_wf spill_base pending ps /\
  pending_inventory_wf pending ps /\
  (!at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
  op <> dead_stack_marker /\
  idx < LENGTH pending /\ MEM op pending /\
  LENGTH pending <= LENGTH ps.ps_stack /\ LENGTH pending <= 16 /\
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
        residual_budget_wf spill_base pending ps' /\
        pending_inventory_wf pending ps'
Proof
  strip_tac >>
  `residual_budget_wf spill_base pending ps' /\
   LENGTH pending <= LENGTH ps'.ps_stack` by
    (drule_all reorder_one_residual_budget_wf >> simp[]) >>
  `pending_inventory_wf pending ps'` by
    (drule_all reorder_one_pending_inventory_wf >> simp[]) >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[residual_budget_wf_def] >>
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

Resume reorder_one_venom_asm_rel_numeric[restore_only]:
  strip_tac >> gvs[] >>
  drule_all reorder_restore_venom_asm_rel_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists `st'` >> asm_rewrite_tac[] >> MATCH_ACCEPT_TAC ADD_COMM
QED

Resume reorder_one_venom_asm_rel_numeric[after_reduce]:
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
  drule_all reorder_prepare_venom_asm_rel_numeric >>
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
    (qpat_x_assum `residual_budget_wf spill_base pending ps` kall_tac >>
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

Resume reorder_one_venom_asm_rel_numeric[suffix]:
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

Resume reorder_one_venom_asm_rel_numeric[alias_suffix]:
  gvs[] >> simp[execute_plan_def, asm_steps_def] >>
  irule venom_asm_rel_sem_stack_transport >>
  goal_assum (drule_at Any) >> simp[] >>
  irule plan_stack_sem_eq_exchange >>
  `MEM (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)
     ps2.ps_stack` by (irule stack_peek_mem >> decide_tac) >>
  simp[] >> metis_tac[]
QED

Finalise reorder_one_venom_asm_rel_numeric

Theorem plan_steps_reorder_venom_asm_rel_numeric:
  !items ps ops ps' st.
    EVERY (\(idx,op). idx < LENGTH pending /\ MEM op pending) items /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
    residual_budget_wf spill_base pending ps /\ pending_inventory_wf pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack /\ LENGTH pending <= 16 /\
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
          residual_budget_wf spill_base pending ps' /\ pending_inventory_wf pending ps'
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
  drule_all reorder_one_venom_asm_rel_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo ps1 vs mid` >>
  `LENGTH pending <= LENGTH ps1.ps_stack` by
    (drule_all reorder_one_residual_budget_wf >> simp[]) >>
  `asm_block_at prog mid.as_pc (execute_plan initial_fmp rest_ops)` by metis_tac[ADD_COMM] >>
  `!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (drule_at (Pat `reorder_one _ _ _ _ _ = _`)
       reorder_one_inventory_subset >> simp[]) >>
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

Theorem reorder_plan_venom_asm_rel_numeric:
  !dfg target_ops ps ops ps' base lo o2pc prog vs st.
    residual_budget_wf base target_ops ps /\
    pending_inventory_wf target_ops ps /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) target_ops /\
    LENGTH target_ops <= LENGTH ps.ps_stack /\ LENGTH target_ops <= 16 /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    reorder_plan dfg target_ops ps = (ops,ps') /\
    (!op1 at. MEM op1 target_ops /\
              (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
              operand_equiv dfg op1 at ==>
              operand_val vs lo op1 = operand_val vs lo at) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
          venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
          residual_budget_wf base target_ops ps' /\
          pending_inventory_wf target_ops ps'
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\(idx,op). idx < LENGTH target_ops /\ MEM op target_ops)
     (MAPi (\i op. (i,op)) target_ops)` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
     rpt strip_tac >> gvs[] >> simp[MEM_EL] >> qexists_tac `p_1` >> simp[]) >>
  `plan_steps (\(idx,op) ps. reorder_one dfg target_ops idx op ps)
     (MAPi (\i op. (i,op)) target_ops) ps = (ops,ps')` by
    (qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
     simp[reorder_plan_eq_plan_steps]) >>
  drule_all plan_steps_reorder_venom_asm_rel_numeric >> simp[]
QED

(* The spill-ready forms below are corollaries of the address-bound forms:
   spill well-formedness bounds every spill and restore address. *)
Theorem reorder_one_venom_asm_rel_residual:
  !dfg pending idx op ps ops ps' base lo o2pc prog vs st.
    residual_budget_wf base pending ps /\
    pending_inventory_wf pending ps /\
    (!at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
    op <> dead_stack_marker /\
    idx < LENGTH pending /\ MEM op pending /\
    LENGTH pending <= LENGTH ps.ps_stack /\ LENGTH pending <= 16 /\
    reorder_one dfg pending idx op ps = (ops,ps') /\
    (!op1 at. MEM op1 pending /\
              (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
              operand_equiv dfg op1 at ==>
              operand_val vs lo op1 = operand_val vs lo at) /\
    prefix_spill_wf initial_fmp lo ops ps /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
            AsmOK st' /\
          venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
          residual_budget_wf base pending ps' /\
          pending_inventory_wf pending ps'
Proof
  rpt strip_tac >> drule prefix_spill_wf_address_bounds >> strip_tac >>
  drule_all reorder_one_venom_asm_rel_numeric >> simp[]
QED

Theorem reorder_steps_spill_ready_address_bounds:
  !items ps ops ps'.
    reorder_steps_spill_ready initial_fmp dfg pending lo items ps /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps)
      items ps = (ops,ps') ==>
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops
Proof
  Induct >- simp[plan_steps_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[Once plan_steps_def, Once reorder_steps_spill_ready_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  conj_tac >- metis_tac[prefix_spill_wf_address_bounds] >>
  metis_tac[]
QED

Theorem reorder_plan_venom_asm_rel_residual:
  !dfg target_ops ps ops ps' base lo o2pc prog vs st.
    residual_budget_wf base target_ops ps /\
    pending_inventory_wf target_ops ps /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) target_ops /\
    LENGTH target_ops <= LENGTH ps.ps_stack /\ LENGTH target_ops <= 16 /\
    reorder_steps_spill_ready initial_fmp dfg target_ops lo
      (MAPi (\i op. (i,op)) target_ops) ps /\
    reorder_plan dfg target_ops ps = (ops,ps') /\
    (!op1 at. MEM op1 target_ops /\
              (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
              operand_equiv dfg op1 at ==>
              operand_val vs lo op1 = operand_val vs lo at) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
            AsmOK st' /\
          venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
          residual_budget_wf base target_ops ps' /\
          pending_inventory_wf target_ops ps'
Proof
  rpt strip_tac >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
     | SORestore off => off < dimword(:256) | _ => T) ops` by
    (irule reorder_steps_spill_ready_address_bounds >>
     gvs[reorder_plan_eq_plan_steps] >> metis_tac[]) >>
  drule_all reorder_plan_venom_asm_rel_numeric >> simp[]
QED

Theorem reorder_plan_exact_two_venom_asm_rel:
  !base dfg h h' ps ops ps' lo o2pc prog vs st.
    exact_two_planner_ready base h h' ps /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) [h;h'] /\
    reorder_plan dfg [h;h'] ps = (ops,ps') /\
    (!op1 at. MEM op1 [h;h'] /\
              (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
              operand_equiv dfg op1 at ==>
              operand_val vs lo op1 = operand_val vs lo at) /\
    prefix_spill_wf initial_fmp lo ops ps /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
        AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
  simp[reorder_plan_def, indexedListsTheory.MAPi_def,
       indexedListsTheory.MAPi_ACC_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  `exact_two_planner_ready base' h h' ps''` by
    (qspecl_then [`dfg`, `base'`, `h`, `h'`, `0`, `h`, `ps`, `ops'`, `ps''`]
       mp_tac reorder_one_exact_two_planner_ready >> simp[]) >>
  `prefix_spill_wf initial_fmp lo ops' ps` by
    fs[prefix_spill_wf_append_reorder] >>
  `prefix_spill_wf initial_fmp lo step_ops ps''` by
    (qspecl_then [`base'`, `dfg`, `h`, `h'`, `ps`, `ops'`, `ps''`,
                  `step_ops`, `ps'`, `lo`]
       mp_tac reorder_one_exact_two_suffix_prefix_spill_wf >> simp[]) >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp ops') /\
   asm_block_at prog
     (st.as_pc + LENGTH (execute_plan initial_fmp ops'))
     (execute_plan initial_fmp step_ops)` by
    (qpat_x_assum `asm_block_at prog st.as_pc
       (execute_plan initial_fmp (ops' ++ step_ops))` mp_tac >>
     rewrite_tac[execute_plan_append, asm_block_at_append]) >>
  `residual_budget_wf base' [h;h'] ps /\
   pending_inventory_wf [h;h'] ps /\
   2 <= LENGTH ps.ps_stack` by
    fs[exact_two_planner_ready_def] >>
  `?st1.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops')) st =
        AsmOK st1 /\
      venom_asm_rel lo ps'' vs st1 /\
      st1.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops') /\
      residual_budget_wf base' [h;h'] ps'' /\
      pending_inventory_wf [h;h'] ps''` by
    (qspecl_then [`dfg`, `[h;h']`, `0`, `h`, `ps`, `ops'`, `ps''`,
                  `base'`, `lo`, `o2pc`, `prog`, `vs`, `st`]
       mp_tac reorder_one_venom_asm_rel_residual >>
     simp[exact_two_planner_ready_def] >> disch_then irule >>
     metis_tac[]) >>
  `asm_block_at prog st1.as_pc (execute_plan initial_fmp step_ops)` by
    metis_tac[] >>
  `2 <= LENGTH ps''.ps_stack` by
    fs[exact_two_planner_ready_def] >>
  `!at. MEM at ps''.ps_stack \/ at IN FDOM ps''.ps_spilled ==>
        MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (qpat_assum `reorder_one dfg [h;h'] 0 h ps = _`
       (mp_then Any mp_tac reorder_one_inventory_subset) >> simp[]) >>
  `!op1 at. MEM op1 [h;h'] /\
        (MEM at ps''.ps_stack \/ at IN FDOM ps''.ps_spilled) /\
        operand_equiv dfg op1 at ==>
        operand_val vs lo op1 = operand_val vs lo at` by
    (simp[] >> metis_tac[]) >>
  `?st2.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp step_ops)) st1 =
        AsmOK st2 /\
      venom_asm_rel lo ps' vs st2 /\
      st2.as_pc = st1.as_pc + LENGTH (execute_plan initial_fmp step_ops) /\
      residual_budget_wf base' [h;h'] ps' /\
      pending_inventory_wf [h;h'] ps'` by
    (qspecl_then [`dfg`, `[h;h']`, `1`, `h'`, `ps''`, `step_ops`, `ps'`,
                  `base'`, `lo`, `o2pc`, `prog`, `vs`, `st1`]
       mp_tac reorder_one_venom_asm_rel_residual >> simp[] >>
     disch_then irule >> fs[]) >>
  qexists_tac `st2` >>
  ASM_REWRITE_TAC[execute_plan_append, LENGTH_APPEND, asm_steps_add] >>
  simp[]
QED

