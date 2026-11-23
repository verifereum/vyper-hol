(* Physical execution of the restore and depth-reduction stages of reorder preparation. *)
Theory reorderPreparationTraceProps
Ancestors
  reorderPreparationProps spillPlanSim doSwapSim foldlSim spillSim planWf
  stackPlanOps stackPlanTypes stackModel codegenRel asmSem planExec
  stackOpSim blockSimHelpers list finite_map arithmetic

Theorem do_restore_venom_asm_rel_numeric:
  do_restore op ps = (ops,ps') /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        venom_asm_rel lo ps' vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  Cases_on `FLOOKUP ps.ps_spilled op`
  >- gvs[do_restore_def, execute_plan_def, asm_steps_def] >>
  rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  gvs[do_restore_def, execute_plan_def, exec_stack_op_def] >>
  drule_all restore_op_venom_asm_rel >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists `st'` >> simp[] >>
  irule venom_asm_rel_ps_transfer >>
  qexists `ps with <|ps_stack := stack_push op ps.ps_stack;
    ps_spilled := ps.ps_spilled \\ op|>` >>
  simp[free_spill_slot_def]
QED

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
  qpat_x_assum `do_spill_tos _ = _` mp_tac >>
  simp[do_spill_tos_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `alloc_spill_slot ps.ps_alloc = (off,al)` >>
  `ps.ps_alloc.sa_spill_base <= off /\
    !key old_off. FLOOKUP ps.ps_spilled key = SOME old_off ==>
      old_off + 32 <= off \/ off + 32 <= old_off` by
    (drule_all alloc_spill_slot_separated >> simp[]) >>
  `MAX ps.ps_alloc.sa_next_offset (off + 32) = al.sa_next_offset` by
    metis_tac[alloc_spill_slot_max_agree] >>
  gvs[execute_plan_def, exec_stack_op_def] >>
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

Theorem reorder_prepass_venom_asm_rel_numeric:
  !targets ps ops post lo o2pc prog vs st.
    reorder_prepare_plan targets ps = (ops,post) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  drule reorder_prepare_plan_split >> strip_tac >> gvs[EVERY_APPEND] >>
  qabbrev_tac `layout = (\st:plan_state. spill_alloc_layout_wf st.ps_alloc st.ps_spilled)` >>
  `plan_steps do_restore (FILTER is_var_operand targets) ps = (restore_ops,restored)` by
    simp[GSYM restore_spilled_plan_steps] >>
  `layout restored` by
    (qspecl_then [`FILTER is_var_operand targets`, `do_restore`, `ps`,
       `restore_ops`, `restored`, `layout`] mp_tac plan_steps_preserves >>
     simp[Abbr `layout`] >> metis_tac[do_restore_layout_wf]) >>
  `(!off. MEM (SOSpill off) restore_ops \/ MEM (SORestore off) restore_ops ==>
          off < dimword(:256)) /\
   (!off. MEM (SOSpill off) spill_ops \/ MEM (SORestore off) spill_ops ==>
          off < dimword(:256))` by
    (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[]) >>
  qspecl_then [`lo`, `o2pc`, `prog`, `vs`, `ps`, `restored`, `post`,
                `restore_ops`, `spill_ops`, `st`] mp_tac plan_seq_sim >>
  simp[] >> impl_tac
  >- (conj_tac
      >- (gen_tac >> strip_tac >>
          qspecl_then [`FILTER is_var_operand targets`, `do_restore`, `restore_ops`,
            `ps`, `restored`, `lo`, `o2pc`, `prog`, `vs`, `st1`, `layout`]
            mp_tac plan_steps_venom_asm_rel_addresses >>
          simp[Abbr `layout`] >> impl_tac
          >- (conj_tac
              >- (rpt gen_tac >> strip_tac >>
                  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
                     | SORestore off => off < dimword(:256) | _ => T) step_ops` by
                    (rewrite_tac[EVERY_MEM] >> Cases >> simp[] >> metis_tac[]) >>
                  drule_all do_restore_venom_asm_rel_numeric >>
                  disch_then (qspec_then `o2pc` strip_assume_tac) >>
                  qexists_tac `st'` >> simp[Once ADD_COMM] >>
                  metis_tac[do_restore_layout_wf]) >>
              metis_tac[]) >> simp[]) >>
      gen_tac >> strip_tac >>
      qspecl_then [`ordered`,
        `\op st. reduce_depth_plan (LENGTH st.ps_stack - LENGTH targets) targets op 0 0 st`,
        `spill_ops`, `restored`, `post`, `lo`, `o2pc`, `prog`, `vs`, `st2`, `layout`]
        mp_tac plan_steps_venom_asm_rel_addresses >>
      simp[Abbr `layout`] >> impl_tac
      >- (conj_tac
          >- (rpt gen_tac >> strip_tac >>
              `EVERY (\s. case s of SOSpill off => off < dimword(:256)
                 | SORestore off => off < dimword(:256) | _ => T) step_ops` by
                 (rewrite_tac[EVERY_MEM] >> Cases >> simp[] >> metis_tac[]) >>
              drule_all reduce_depth_plan_venom_asm_rel_numeric >>
              disch_then (qspec_then `o2pc` strip_assume_tac) >>
              qexists_tac `st'` >> simp[Once ADD_COMM]) >>
          metis_tac[]) >> simp[]) >>
  simp[]
QED
