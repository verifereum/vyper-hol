(* Physical depth reduction with compiler-checked spill addresses.
   TOP-LEVEL: reduce_depth_plan_sim. *)
Theory reduceDepthSim
Ancestors
  spillPlanSim doSwapSim spillWordBounds stackPlanOps stackPlanTypes stackModel
  codegenRel asmSem planExec planWf stackOpSim
  list rich_list finite_map arithmetic

Theorem do_spill_at_stack_length[local]:
  !d ps.
    d < LENGTH ps.ps_stack ==>
    LENGTH (SND (do_spill_at d ps)).ps_stack = LENGTH ps.ps_stack - 1
Proof
  rpt gen_tac >> strip_tac >>
  simp[do_spill_at_def, do_spill_tos_def, LET_THM] >>
  Cases_on `d = 0` >> simp[stack_pop_def] >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[stack_pop_def]
QED

Theorem reduce_depth_plan_length_floor:
  !fuel target_ops target_op f target_len ps ops ps'.
    reduce_depth_plan fuel target_ops target_op f target_len ps = (ops, ps') ==>
    MIN 17 (LENGTH ps.ps_stack) <= LENGTH ps'.ps_stack
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack` >>
  simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x target_len` >>
  simp[] >> pairarg_tac >> simp[] >>
  rename1 `do_spill_at x' ps = (spill_ops, ps1)` >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule stack_get_unfixed_depth_bound >> strip_tac >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  `x' < LENGTH ps.ps_stack` by
    metis_tac[select_spill_candidate_bound] >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack - 1` by (
    qspecl_then [`x'`, `ps`] mp_tac do_spill_at_stack_length >>
    simp[] >> gvs[]) >>
  first_x_assum
    (qspecl_then [`target_ops`, `target_op`, `f`, `target_len`, `ps1`,
                  `rest_ops`, `ps'`] mp_tac) >>
  simp[] >> Cases_on `x <= 16` >> gvs[] >> decide_tac
QED

Theorem reduce_depth_plan_sim:
  !fuel pending target_op final_dist num_ops ps ops post
   initial_fmp lo o2pc prog vs st.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    reduce_depth_plan fuel pending target_op final_dist num_ops ps = (ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf post.ps_alloc post.ps_spilled
Proof
  Induct
  >- (simp[reduce_depth_plan_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `st` >> simp[execute_plan_def, asm_steps_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reduce_depth_plan (SUC fuel) _ _ _ _ _ = _` mp_tac >>
  simp_tac std_ss [Once reduce_depth_plan_def] >>
  Cases_on `final_dist + 1 < num_ops` >> simp[]
  >- (strip_tac >> gvs[] >> qexists_tac `st` >> simp[execute_plan_def, asm_steps_def]) >>
  Cases_on `stack_get_unfixed_depth target_op final_dist num_ops ps.ps_stack` >> simp[]
  >- (strip_tac >> gvs[] >> qexists_tac `st` >> simp[execute_plan_def, asm_steps_def]) >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  Cases_on `dist <= 16` >> simp[]
  >- (strip_tac >> gvs[] >> qexists_tac `st` >> simp[execute_plan_def, asm_steps_def]) >>
  Cases_on `select_spill_candidate ps.ps_stack pending dist num_ops` >> simp[]
  >- (strip_tac >> gvs[] >> qexists_tac `st` >> simp[execute_plan_def, asm_steps_def]) >>
  rename1 `select_spill_candidate _ _ _ _ = SOME cand` >>
  Cases_on `do_spill_at cand ps` >> rename1 `do_spill_at _ _ = (step_ops,mid)` >>
  Cases_on `reduce_depth_plan fuel pending target_op final_dist num_ops mid` >>
  rename1 `reduce_depth_plan fuel _ _ _ _ mid = (rest_ops,last)` >>
  simp[] >> strip_tac >> gvs[] >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    (mp_tac (Q.SPECL [`ps.ps_stack`,`pending`,`dist`,`num_ops`,`cand`]
       select_spill_candidate_bound) >>
     (impl_tac >- (drule stack_get_unfixed_depth_bound >> decide_tac)) >> simp[]) >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp step_ops) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp step_ops))
     (execute_plan initial_fmp rest_ops)` by
    fs[execute_plan_append, asm_block_at_append] >>
  mp_tac (Q.SPECL [`cand`,`ps`,`step_ops`,`mid`,`initial_fmp`,`lo`,`o2pc`,
    `prog`,`vs`,`st`] do_spill_at_checked_sim) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `st1` strip_assume_tac) >>
  first_x_assum (qspecl_then [`pending`,`target_op`,`final_dist`,`num_ops`,`mid`,
    `rest_ops`,`last`,`initial_fmp`,`lo`,`o2pc`,`prog`,`vs`,`st1`] mp_tac) >>
  (impl_tac >- asm_simp_tac (srw_ss()) []) >>
  disch_then (qx_choose_then `st2` strip_assume_tac) >> qexists_tac `st2` >>
  asm_simp_tac std_ss [execute_plan_append, LENGTH_APPEND, asm_steps_add,
    ADD_ASSOC] >> asm_simp_tac (srw_ss()) [] >> decide_tac
QED
