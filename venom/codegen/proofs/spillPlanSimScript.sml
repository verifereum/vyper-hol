(* Checked physical spill and restore operations.
   TOP-LEVEL: do_spill_tos_checked_sim, do_restore_checked_sim.
   Helper: fresh-slot separation from the durable allocator layout. *)
Theory spillPlanSim
Ancestors
  doSwapSim doSwapCorrect emitOperandSim spillWordBounds spillSim allocMono
  stackPlanGen stackPlanOps stackPlanTypes stackModel codegenRel asmSem planExec
  planWf stackOpSim mixedPrefixSim prefixExec
  list rich_list finite_map arithmetic

Theorem alloc_spill_slot_separated:
  !al spilled off al'.
    spill_alloc_layout_wf al spilled /\
    alloc_spill_slot al = (off,al') /\ off < dimword(:256) ==>
    al.sa_spill_base <= off /\
    !op old_off. FLOOKUP spilled op = SOME old_off ==>
      old_off + 32 <= off \/ off + 32 <= old_off
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.ISPECL [`[():unit]`,`al:spill_alloc`,
    `spilled:(operand,num) fmap`] spill_alloc_n_slot_facts) >>
  (impl_tac >- asm_simp_tac (srw_ss()) [spill_alloc_n_def, LET_THM]) >>
  simp_tac std_ss [LET_THM] >>
  disch_then (mp_tac o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) >>
  disch_then (qspec_then `0` mp_tac) >>
  asm_simp_tac (srw_ss()) [spill_alloc_n_def, LET_THM] >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Theorem do_spill_tos_checked_sim:
  !ps ops post initial_fmp lo o2pc prog vs st.
    do_spill_tos ps = (ops,post) /\ 0 < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf post.ps_alloc post.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >>
  rename1 `alloc_spill_slot ps.ps_alloc = (off,al')` >>
  `ops = [SOSpill off] /\
   post = ps with <|ps_stack := stack_pop 1 ps.ps_stack;
     ps_spilled := ps.ps_spilled |+ (stack_peek 0 ps.ps_stack,off);
     ps_alloc := al'|>` by fs[do_spill_tos_def, LET_THM] >>
  `off < dimword(:256)` by
    (mp_tac (Q.SPECL [`initial_fmp`,`ops`,`prog`,`st.as_pc`,`off`]
       plan_spill_offset_word_bound) >>
     (impl_tac >- asm_simp_tac (srw_ss()) []) >> simp_tac bool_ss []) >>
  `ps.ps_alloc.sa_spill_base <= off /\
   !op old_off. FLOOKUP ps.ps_spilled op = SOME old_off ==>
     old_off + 32 <= off \/ off + 32 <= old_off` by
    (drule_all alloc_spill_slot_separated >> simp[]) >>
  `MAX ps.ps_alloc.sa_next_offset (off + 32) = al'.sa_next_offset /\
   al'.sa_spill_base = ps.ps_alloc.sa_spill_base` by
    metis_tac[alloc_spill_slot_max_agree, alloc_spill_slot_spill_base] >>
  `spill_alloc_layout_wf post.ps_alloc post.ps_spilled` by
    (mp_tac (Q.SPECL [`ps.ps_alloc`,`ps.ps_spilled`,`off`,`al'`,
       `stack_peek 0 ps.ps_stack`] spill_alloc_layout_wf_after_alloc) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     asm_simp_tac (srw_ss()) []) >>
  mp_tac (Q.SPECL [`lo`,`o2pc`,`prog`,`off`,`stack_peek 0 ps.ps_stack`,
    `ps`,`vs`,`st`] spill_op_venom_asm_rel) >>
  (impl_tac >- (fs[execute_plan_def, exec_stack_op_def] >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac])) >>
  disch_then (qx_choose_then `st'` strip_assume_tac) >>
  qexists_tac `st'` >>
  asm_simp_tac (srw_ss()) [execute_plan_def, exec_stack_op_def] >>
  irule venom_asm_rel_ps_transfer >>
  qexists_tac `ps with <|ps_stack := stack_pop 1 ps.ps_stack;
    ps_spilled := ps.ps_spilled |+ (stack_peek 0 ps.ps_stack,off);
    ps_alloc := ps.ps_alloc with
      sa_next_offset := MAX ps.ps_alloc.sa_next_offset (off + 32)|>` >>
  asm_simp_tac (srw_ss()) []
QED

Theorem do_restore_checked_sim:
  !op ps ops post initial_fmp lo o2pc prog vs st.
    do_restore op ps = (ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  `prefix_spill_wf initial_fmp lo ops ps` by
    (Cases_on `FLOOKUP ps.ps_spilled op`
     >- gvs[do_restore_def, prefix_spill_wf_def] >>
     rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
     `ops = [SORestore off]` by fs[do_restore_def] >>
     `off < dimword(:256)` by
       (mp_tac (Q.SPECL [`initial_fmp`,`ops`,`prog`,`st.as_pc`,`off`]
          plan_restore_offset_word_bound) >>
        (impl_tac >- asm_simp_tac (srw_ss()) []) >> simp_tac bool_ss []) >>
     simp[prefix_spill_wf_def, spill_op_wf_def] >>
     qexists_tac `op` >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`op`,`ps`,`ops`,`post`,`initial_fmp`,`lo`,`o2pc`,
    `prog`,`vs`,`st`] do_restore_venom_asm_rel) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []
QED

Theorem do_restore_layout_wf:
  !op ps ops post.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    do_restore op ps = (ops,post) ==>
    spill_alloc_layout_wf post.ps_alloc post.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP ps.ps_spilled op` >>
  gvs[do_restore_def] >>
  drule_all spill_alloc_layout_wf_after_free >> simp[]
QED

Theorem do_spill_at_plan_decompose:
  !dist ps ops post.
    dist <= 16 /\ do_spill_at dist ps = (ops,post) ==>
    ?swap_ops mid spill_ops.
      do_swap dist ps = (swap_ops,mid) /\
      do_spill_tos mid = (spill_ops,post) /\ ops = swap_ops ++ spill_ops
Proof
  rpt gen_tac >> strip_tac >> Cases_on `dist = 0`
  >- (qexistsl_tac [`[]`,`ps`,`ops`] >>
      fs[do_swap_def, do_spill_at_def]) >>
  Cases_on `do_spill_tos (ps with ps_stack := stack_swap dist ps.ps_stack)` >>
  rename1 `do_spill_tos _ = (spill_ops,mid)` >>
  `ops = [SOSwap dist] ++ spill_ops /\ post = mid` by
    fs[do_spill_at_def, LET_THM] >>
  qexistsl_tac [`[SOSwap dist]`,
    `ps with ps_stack := stack_swap dist ps.ps_stack`,`spill_ops`] >>
  asm_simp_tac (srw_ss()) [do_swap_def]
QED

Theorem do_spill_at_checked_sim:
  !dist ps ops post initial_fmp lo o2pc prog vs st.
    dist <= 16 /\ dist < LENGTH ps.ps_stack /\
    do_spill_at dist ps = (ops,post) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf post.ps_alloc post.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`dist`,`ps`,`ops`,`post`] do_spill_at_plan_decompose) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `swap_ops` (qx_choose_then `mid`
    (qx_choose_then `spill_ops` strip_assume_tac))) >>
  `LENGTH mid.ps_stack = LENGTH ps.ps_stack` by
    (mp_tac (Q.SPECL [`dist`,`ps`] do_swap_length) >> asm_simp_tac (srw_ss()) []) >>
  `spill_alloc_layout_wf mid.ps_alloc mid.ps_spilled` by
    (mp_tac (Q.SPECL [`dist`,`ps`] do_swap_layout_wf) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     asm_simp_tac (srw_ss()) []) >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp swap_ops) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp swap_ops))
     (execute_plan initial_fmp spill_ops)` by
    fs[execute_plan_append, asm_block_at_append] >>
  mp_tac (Q.SPECL [`dist`,`ps`,`swap_ops`,`mid`,`initial_fmp`,`lo`,`o2pc`,
    `prog`,`vs`,`st`] do_swap_checked_sim) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `st1` strip_assume_tac) >>
  mp_tac (Q.SPECL [`mid`,`spill_ops`,`post`,`initial_fmp`,`lo`,`o2pc`,
    `prog`,`vs`,`st1`] do_spill_tos_checked_sim) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >> decide_tac)) >>
  disch_then (qx_choose_then `st2` strip_assume_tac) >>
  qexists_tac `st2` >>
  asm_simp_tac std_ss [execute_plan_append, LENGTH_APPEND, asm_steps_add,
    ADD_ASSOC] >> asm_simp_tac (srw_ss()) [] >> decide_tac
QED

(* Releasing dead spills (freeing spill slots for variables not in the live
   set) preserves the venom-assembly state correspondence. The dead-spill
   release only modifies the plan state's spill map and allocator; the
   stack and memory layout visible to the assembly are unchanged. *)
Theorem venom_asm_rel_release_dead_spills:
  !lo next_liveness ps vs as.
    venom_asm_rel lo ps vs as ==>
    venom_asm_rel lo (release_dead_spills next_liveness ps) vs as
Proof
  rpt gen_tac >> strip_tac >> gvs[venom_asm_rel_def] >>
  `!dead (ps0:plan_state).
     (FOLDL (\ps' (op:operand, off:num).
       ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                   ps_alloc := free_spill_slot off ps'.ps_alloc |>)
       ps0 dead).ps_stack = ps0.ps_stack` by (
    Induct >> simp[] >>
    rpt gen_tac >> PairCases_on `h` >> simp[free_spill_slot_def]) >>
  `!dead (ps0:plan_state) lo' vs' am.
     plan_spill_rel lo' vs' ps0.ps_spilled am ==>
     plan_spill_rel lo' vs'
       (FOLDL (\ps' (op:operand, off:num).
         ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                     ps_alloc := free_spill_slot off ps'.ps_alloc |>)
         ps0 dead).ps_spilled am` by (
    Induct >> simp[] >>
    rpt strip_tac >> Cases_on `h` >> simp[] >>
    first_x_assum match_mp_tac >>
    simp[] >> irule plan_spill_rel_remove_entry >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[release_dead_spills_def, LET_THM] >>
  conj_tac >- (simp[release_dead_spills_def, LET_THM] >> first_x_assum match_mp_tac >> simp[]) >>
  simp[memory_rel_def, release_dead_spills_spill_base, release_dead_spills_next_offset] >> metis_tac[memory_rel_def]
QED
