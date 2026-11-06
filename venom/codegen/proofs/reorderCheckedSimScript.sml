(* Checked execution of the planner's restore/reduce/place sequence.
   Helpers: restore and finish phases preserve the actual planner state. *)
Theory reorderCheckedSim
Ancestors
  reorderStages reorderPlaceSim reduceDepthSim spillPlanSim doSwapSim
  stackPlanOps stackPlanTypes stackPlanGen stackModel planWf dfgDefs
  codegenRel asmSem planExec stackOpSim blockSimHelpers
  foldlSim indexedLists list rich_list arithmetic finite_map

Theorem do_restore_length_mono[local]:
  !op ps ops post.
    do_restore op ps = (ops,post) ==> LENGTH ps.ps_stack <= LENGTH post.ps_stack
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP ps.ps_spilled op` >>
  gvs[do_restore_def, stack_push_def]
QED

Theorem reorder_restore_checked_sim:
  !op final_dist num_ops ps ops post initial_fmp lo o2pc prog vs st.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    reorder_restore op final_dist num_ops ps = (ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf post.ps_alloc post.ps_spilled /\
      LENGTH ps.ps_stack <= LENGTH post.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth op final_dist num_ops ps.ps_stack`
  >- (`do_restore op ps = (ops,post)` by fs[reorder_restore_def] >>
      `spill_alloc_layout_wf post.ps_alloc post.ps_spilled /\
       LENGTH ps.ps_stack <= LENGTH post.ps_stack` by
        metis_tac[do_restore_layout_wf, do_restore_length_mono] >>
      mp_tac (Q.SPECL [`op`,`ps`,`ops`,`post`,`initial_fmp`,`lo`,`o2pc`,
        `prog`,`vs`,`st`] do_restore_checked_sim) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (qx_choose_then `st'` strip_assume_tac) >>
      qexists_tac `st'` >> asm_rewrite_tac []) >>
  gvs[reorder_restore_def] >> qexists_tac `st` >>
  simp[execute_plan_def, asm_steps_def]
QED

Theorem reorder_finish_checked_sim:
  !dfg op final_dist num_ops ps ops post initial_fmp lo o2pc prog vs st.
    final_dist < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    op <> dead_stack_marker /\
    (!at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
    (!op1 at. operand_equiv dfg op1 at ==>
       operand_val vs lo op1 = operand_val vs lo at) /\
    reorder_finish dfg op final_dist num_ops ps = (ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf post.ps_alloc post.ps_spilled /\
      LENGTH post.ps_stack = LENGTH ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth op final_dist num_ops ps.ps_stack`
  >- (gvs[reorder_finish_def] >> qexists_tac `st` >>
      simp[execute_plan_def, asm_steps_def]) >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  `dist < LENGTH ps.ps_stack /\ stack_peek dist ps.ps_stack = op` by
    (drule stack_get_unfixed_depth_props >> simp[]) >>
  `~operand_equiv dfg op dead_stack_marker` by
    (CCONTR_TAC >> gvs[]) >>
  mp_tac (Q.SPECL [`dfg`,`op`,`dist`,`final_dist`,`ps`,`ops`,`post`,
    `initial_fmp`,`lo`,`o2pc`,`prog`,`vs`,`st`] reorder_place_checked_sim) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >> rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC,
      qpat_assum `reorder_finish _ _ _ _ _ = _`
        (mp_tac o REWRITE_RULE [reorder_finish_def, reorder_place_def, LET_THM]) >>
      asm_simp_tac (srw_ss()) [LET_THM]])) >>
  simp_tac bool_ss []
QED

Theorem reorder_prepare_checked_sim:
  !pending op final_dist num_ops ps restore_ops mid reduce_ops reduced
   initial_fmp lo o2pc prog vs st.
    num_ops <= 16 /\ num_ops <= LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    reorder_restore op final_dist num_ops ps = (restore_ops,mid) /\
    reduce_depth_plan (LENGTH mid.ps_stack) pending op final_dist num_ops mid =
      (reduce_ops,reduced) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc
      (execute_plan initial_fmp (restore_ops ++ reduce_ops)) ==>
    ?st'. asm_steps lo o2pc prog
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) st = AsmOK st' /\
      venom_asm_rel lo reduced vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops)) /\
      spill_alloc_layout_wf reduced.ps_alloc reduced.ps_spilled /\
      num_ops <= LENGTH reduced.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp restore_ops) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp restore_ops))
     (execute_plan initial_fmp reduce_ops)` by
    fs[execute_plan_append, asm_block_at_append] >>
  mp_tac (Q.SPECL [`op`,`final_dist`,`num_ops`,`ps`,`restore_ops`,`mid`,
    `initial_fmp`,`lo`,`o2pc`,`prog`,`vs`,`st`] reorder_restore_checked_sim) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `st1` strip_assume_tac) >>
  `MIN 17 (LENGTH mid.ps_stack) <= LENGTH reduced.ps_stack` by
    (mp_tac (Q.SPECL [`LENGTH mid.ps_stack`,`pending`,`op`,`final_dist`,
       `num_ops`,`mid`,`reduce_ops`,`reduced`] reduce_depth_plan_length_floor) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp_tac bool_ss []) >>
  `num_ops <= LENGTH reduced.ps_stack` by (fs[MIN_DEF] >> decide_tac) >>
  mp_tac (Q.SPECL [`LENGTH mid.ps_stack`,`pending`,`op`,`final_dist`,`num_ops`,
    `mid`,`reduce_ops`,`reduced`,`initial_fmp`,`lo`,`o2pc`,`prog`,`vs`,`st1`]
    reduce_depth_plan_sim) >>
  (impl_tac >- asm_simp_tac (srw_ss()) []) >>
  disch_then (qx_choose_then `st2` strip_assume_tac) >> qexists_tac `st2` >>
  asm_simp_tac std_ss [execute_plan_append, LENGTH_APPEND, asm_steps_add,
    ADD_ASSOC] >> asm_simp_tac (srw_ss()) [] >> decide_tac
QED

Theorem reorder_one_checked_sim:
  !dfg pending idx op ps ops post initial_fmp lo o2pc prog vs st.
    idx < LENGTH pending /\ LENGTH pending <= LENGTH ps.ps_stack /\
    LENGTH pending <= 16 /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    op <> dead_stack_marker /\
    (!at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
    (!op1 at. operand_equiv dfg op1 at ==>
       operand_val vs lo op1 = operand_val vs lo at) /\
    reorder_one dfg pending idx op ps = (ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf post.ps_alloc post.ps_spilled /\
      LENGTH pending <= LENGTH post.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `reorder_restore op (LENGTH pending - 1 - idx) (LENGTH pending) ps` >>
  rename1 `reorder_restore _ _ _ _ = (restore_ops,mid)` >>
  Cases_on `reduce_depth_plan (LENGTH mid.ps_stack) pending op
    (LENGTH pending - 1 - idx) (LENGTH pending) mid` >>
  rename1 `reduce_depth_plan _ _ _ _ _ mid = (reduce_ops,reduced)` >>
  Cases_on `reorder_finish dfg op (LENGTH pending - 1 - idx) (LENGTH pending) reduced` >>
  rename1 `reorder_finish _ _ _ _ reduced = (place_ops,last)` >>
  `ops = restore_ops ++ reduce_ops ++ place_ops /\ post = last` by
    (qpat_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
     simp_tac std_ss [Once reorder_one_stages, LET_THM] >>
     asm_simp_tac (srw_ss()) []) >> gvs[] >>
  `asm_block_at prog st.as_pc
      (execute_plan initial_fmp (restore_ops ++ reduce_ops)) /\
   asm_block_at prog
      (st.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops)))
      (execute_plan initial_fmp place_ops)` by
    (qpat_assum `asm_block_at prog st.as_pc _` mp_tac >>
     pure_rewrite_tac [execute_plan_append, asm_block_at_append, LENGTH_APPEND] >>
     simp_tac std_ss [ADD_ASSOC]) >>
  mp_tac (Q.SPECL [`pending:operand list`,`op:operand`,
    `LENGTH (pending:operand list) - (idx + 1)`,`LENGTH (pending:operand list)`,
    `ps`,`restore_ops`,`mid`,`reduce_ops`,`reduced`,`initial_fmp`,`lo`,`o2pc`,
    `prog`,`vs`,`st`] reorder_prepare_checked_sim) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `st1` strip_assume_tac) >>
  `LENGTH pending - (idx + 1) < LENGTH reduced.ps_stack` by decide_tac >>
  mp_tac (Q.SPECL [`dfg:dfg_analysis`,`op:operand`,
    `LENGTH (pending:operand list) - (idx + 1)`,`LENGTH (pending:operand list)`,
    `reduced`,`place_ops`,`last`,`initial_fmp`,`lo`,`o2pc`,`prog`,`vs`,`st1`]
    reorder_finish_checked_sim) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `st2` strip_assume_tac) >>
  qpat_assum `asm_steps lo o2pc prog
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) st = AsmOK st1`
    (fn prefix_th => qpat_assum `asm_steps lo o2pc prog
        (LENGTH (execute_plan initial_fmp place_ops)) st1 = AsmOK st2`
      (fn place_th => assume_tac (MATCH_MP (GEN_ALL asm_steps_compose_ok)
        (CONJ prefix_th place_th)))) >>
  qexists_tac `st2` >> fs[execute_plan_append, LENGTH_APPEND] >> decide_tac
QED

Theorem reorder_steps_checked_sim:
  !items dfg pending ps ops post initial_fmp lo o2pc prog vs st.
    EVERY (\(idx,op). idx < LENGTH pending /\ MEM op pending) items /\
    (!op. MEM op pending ==> op <> dead_stack_marker /\
      (!at. operand_equiv dfg op at ==> at <> dead_stack_marker)) /\
    LENGTH pending <= LENGTH ps.ps_stack /\ LENGTH pending <= 16 /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!op1 at. operand_equiv dfg op1 at ==>
      operand_val vs lo op1 = operand_val vs lo at) /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps =
      (ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf post.ps_alloc post.ps_spilled /\
      LENGTH pending <= LENGTH post.ps_stack
Proof
  Induct_on `items`
  >- (simp[plan_steps_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `st` >> simp[execute_plan_def, asm_steps_def]) >>
  rpt gen_tac >> strip_tac >> Cases_on `h` >>
  rename1 `EVERY _ ((idx,op)::items)` >> fs[EVERY_DEF] >>
  `op <> dead_stack_marker /\
   (!at. operand_equiv dfg op at ==> at <> dead_stack_marker)` by
    (qpat_assum `!op. MEM op pending ==> _` (qspec_then `op` mp_tac) >>
     asm_simp_tac (srw_ss()) []) >>
  qpat_assum `plan_steps _ ((idx,op)::items) ps = _`
    (mp_tac o MATCH_MP plan_steps_cons_result) >>
  disch_then (qx_choose_then `first_ops` (qx_choose_then `mid`
    (qx_choose_then `rest_ops` strip_assume_tac))) >> gvs[] >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp first_ops) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp first_ops))
     (execute_plan initial_fmp rest_ops)` by
    fs[execute_plan_append, asm_block_at_append] >>
  mp_tac (Q.SPECL [`dfg`,`pending`,`idx`,`op`,`ps`,`first_ops`,`mid`,
    `initial_fmp`,`lo`,`o2pc`,`prog`,`vs`,`st`] reorder_one_checked_sim) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `st1` strip_assume_tac) >>
  first_x_assum (qspecl_then [`dfg`,`pending`,`mid`,`rest_ops`,`post`,
    `initial_fmp`,`lo`,`o2pc`,`prog`,`vs`,`st1`] mp_tac) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `st2` strip_assume_tac) >> qexists_tac `st2` >>
  asm_simp_tac std_ss [execute_plan_append, LENGTH_APPEND, asm_steps_add,
    ADD_ASSOC] >> asm_simp_tac (srw_ss()) [] >> decide_tac
QED

Theorem reorder_plan_checked_sim:
  !dfg pending ps ops post initial_fmp lo o2pc prog vs st.
    (!op. MEM op pending ==> op <> dead_stack_marker /\
      (!at. operand_equiv dfg op at ==> at <> dead_stack_marker)) /\
    LENGTH pending <= LENGTH ps.ps_stack /\ LENGTH pending <= 16 /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!op1 at. operand_equiv dfg op1 at ==>
      operand_val vs lo op1 = operand_val vs lo at) /\
    reorder_plan dfg pending ps = (ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf post.ps_alloc post.ps_spilled /\
      LENGTH pending <= LENGTH post.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\(idx,op). idx < LENGTH pending /\ MEM op pending)
     (MAPi (\i op. (i,op)) pending)` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD, MEM_MAPi] >>
     qx_gen_tac `idx` >> strip_tac >>
     simp[MEM_EL] >> qexists_tac `idx` >> simp[]) >>
  mp_tac (Q.SPECL [`MAPi (\i op. (i,op)) (pending:operand list)`,`dfg`,
    `pending`,`ps`,`ops`,`post`,`initial_fmp`,`lo`,`o2pc`,`prog`,`vs`,`st`]
    reorder_steps_checked_sim) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [GSYM reorder_plan_eq_plan_steps] >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      gen_tac >> strip_tac >> CCONTR_TAC >> gvs[]])) >> simp_tac bool_ss []
QED
