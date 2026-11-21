(* Split the preparation and placement passes, and compose their operations. *)
Theory reorderPreparationProps
Ancestors
  stackPlanOps stackPlanTypes stackModel planWf dfgDefs
  foldlSim indexedLists sorting list rich_list arithmetic finite_map
  asmSem asmIR codegenRel planExec stackOpSim blockSimHelpers
Libs BasicProvers

Theorem reorder_foldl_body_eq[local]:
  !dfg target_ops.
    foldl_body (\(idx,op) ps. reorder_one dfg target_ops idx op ps) =
    (\(ops, ps) (idx, op).
      (\(step_ops,ps'). (ops ++ step_ops,ps'))
        (reorder_one dfg target_ops idx op ps))
Proof
  rpt gen_tac >>
  simp[FUN_EQ_THM, foldl_body_def, pairTheory.FORALL_PROD]
QED

Theorem foldl_body_initial_ops[local]:
  !items produce_ops acc ps.
    FOLDL (foldl_body produce_ops) (acc,ps) items =
    (\(ops,post). (acc ++ ops,post)) (plan_steps produce_ops items ps)
Proof
  Induct >- simp[plan_steps_def] >>
  rpt gen_tac >>
  PURE_ONCE_REWRITE_TAC[FOLDL] >>
  PURE_ONCE_REWRITE_TAC[plan_steps_def] >>
  Cases_on `produce_ops h ps` >> simp[foldl_body_def] >>
  Cases_on `plan_steps produce_ops items r` >> simp[APPEND_ASSOC]
QED

Theorem reorder_prepare_plan_split:
  !targets ps ops post.
    reorder_prepare_plan targets ps = (ops,post) ==>
    ?restore_ops restored ordered spill_ops.
      restore_spilled_plan (FILTER is_var_operand targets) ps =
        (restore_ops,restored) /\
      EVERY (\op. MEM op targets) ordered /\
      plan_steps (\op st.
        reduce_depth_plan (LENGTH st.ps_stack - LENGTH targets)
          targets op 0 0 st) ordered restored = (spill_ops,post) /\
      ops = restore_ops ++ spill_ops
Proof
  rpt gen_tac >> simp[reorder_prepare_plan_def] >>
  pairarg_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `FOLDL _ _ ordered` >>
  `EVERY (\op. MEM op targets) ordered` by
    (simp[Abbr `ordered`] >> IF_CASES_TAC >> simp[EVERY_MEM, sortingTheory.QSORT_MEM]) >>
  `(\(ops,st) op.
      let (step,st') =
        reduce_depth_plan (LENGTH st.ps_stack - LENGTH targets)
          targets op 0 0 st in (ops ++ step,st')) =
    foldl_body (\op st. reduce_depth_plan (LENGTH st.ps_stack - LENGTH targets)
      targets op 0 0 st)` by
    simp[FUN_EQ_THM, foldl_body_def, pairTheory.FORALL_PROD] >>
  pop_assum (fn eq => simp[REWRITE_RULE [LET_THM] eq, GSYM plan_steps_eq_foldl]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem reorder_prepare_plan_single:
  !op ps.
    reorder_prepare_plan [op] ps =
    (\(restore_ops,restored).
      (\(spill_ops,prepared). (restore_ops ++ spill_ops,prepared))
        (reduce_depth_plan (LENGTH restored.ps_stack - 1) [op] op 0 0 restored))
      (if is_var_operand op then do_restore op ps else ([],ps))
Proof
  rpt gen_tac >> Cases_on `is_var_operand op` >>
  simp[reorder_prepare_plan_def, restore_spilled_plan_def, LET_THM,
       sortingTheory.QSORT_DEF, sortingTheory.PARTITION_DEF, sortingTheory.PART_DEF,
       pairTheory.UNCURRY_VAR]
QED

Theorem reorder_prepare_plan_single_shallow:
  !op ps d.
    (~is_var_operand op \/ FLOOKUP ps.ps_spilled op = NONE) /\
    stack_get_depth op ps.ps_stack = SOME d /\ d <= 16 ==>
    reorder_prepare_plan [op] ps = ([],ps)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_var_operand op` >>
  gvs[reorder_prepare_plan_single, do_restore_def, LET_THM,
      stack_get_unfixed_depth_empty_window, reduce_depth_plan_le_16]
QED

Theorem reorder_plan_single:
  !dfg op ps.
    reorder_plan dfg [op] ps =
    (\(prep,mid).
      (\(placement,post). (prep ++ placement,post)) (reorder_one dfg [op] 0 op mid))
      (reorder_prepare_plan [op] ps)
Proof
  simp[reorder_plan_def, MAPi_def, MAPi_ACC_def, LET_THM]
QED

Theorem reorder_plan_single_shallow:
  !dfg op ps d.
    (~is_var_operand op \/ FLOOKUP ps.ps_spilled op = NONE) /\
    stack_get_depth op ps.ps_stack = SOME d /\ d <= 16 ==>
    reorder_plan dfg [op] ps = reorder_one dfg [op] 0 op ps
Proof
  rpt gen_tac >> strip_tac >>
  `reorder_prepare_plan [op] ps = ([],ps)` by
    metis_tac[reorder_prepare_plan_single_shallow] >>
  simp[reorder_plan_single, LET_THM, pairTheory.UNCURRY_VAR]
QED

Theorem reorder_plan_split:
  !dfg targets ps ops post.
    reorder_plan dfg targets ps = (ops,post) ==>
    ?prep mid rest.
      reorder_prepare_plan targets ps = (prep,mid) /\
      plan_steps (\(idx,op) st. reorder_one dfg targets idx op st)
        (MAPi (\i op. (i,op)) targets) mid = (rest,post) /\
      ops = prep ++ rest
Proof
  rpt gen_tac >>
  simp[reorder_plan_def, GSYM (REWRITE_RULE [LET_THM] reorder_foldl_body_eq),
       foldl_body_initial_ops] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> metis_tac[]
QED


Theorem plan_steps_cons_result:
  !step x xs ps ops ps'.
    plan_steps step (x::xs) ps = (ops,ps') ==>
    ?step_ops ps1 rest_ops.
      step x ps = (step_ops,ps1) /\
      plan_steps step xs ps1 = (rest_ops,ps') /\
      ops = step_ops ++ rest_ops
Proof
  rpt gen_tac >>
  simp[Once plan_steps_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[]
QED


Theorem restore_spilled_plan_steps:
  !targets ps. restore_spilled_plan targets ps = plan_steps do_restore targets ps
Proof
  Induct >> simp[restore_spilled_plan_def, plan_steps_def]
QED

Theorem restore_spilled_plan_absent:
  !targets ps.
    (!op. MEM op targets ==> op NOTIN FDOM ps.ps_spilled) ==>
    restore_spilled_plan targets ps = ([],ps)
Proof
  Induct >- simp[restore_spilled_plan_def] >>
  rpt gen_tac >> strip_tac >>
  `FLOOKUP ps.ps_spilled h = NONE` by
    (simp[flookup_thm] >> metis_tac[MEM]) >>
  `restore_spilled_plan targets ps = ([],ps)` by
    (first_x_assum irule >> metis_tac[MEM]) >>
  simp[restore_spilled_plan_def, do_restore_def]
QED

Theorem plan_steps_trace_relation:
  !items produce_ops ps ops post R.
    (!st. R st [] st) /\
    (!st mid finish first_ops rest_ops.
      R st first_ops mid /\ R mid rest_ops finish ==>
      R st (first_ops ++ rest_ops) finish) /\
    (!item st step_ops finish.
      MEM item items /\ produce_ops item st = (step_ops,finish) ==>
      R st step_ops finish) /\
    plan_steps produce_ops items ps = (ops,post) ==> R ps ops post
Proof
  Induct >- simp[plan_steps_def] >>
  rpt gen_tac >> strip_tac >>
  drule plan_steps_cons_result >> strip_tac >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  `R ps step_ops ps1` by
    (qpat_assum `!item st ops finish. MEM item (_::_) /\ _ ==> _`
       (qspecl_then [`h`, `ps`, `step_ops`, `ps1`] mp_tac) >> simp[]) >>
  `R ps1 rest_ops post` by
    (first_x_assum (qspecl_then [`produce_ops`, `ps1`, `rest_ops`, `post`, `R`] mp_tac) >>
     impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             qpat_assum `!item st ops finish. MEM item (_::_) /\ _ ==> _`
               (qspecl_then [`item`, `st`, `step_ops'`, `finish'`] mp_tac) >> simp[]) >>
         first_assum ACCEPT_TAC) >>
     simp[]) >>
  qpat_assum `!st mid finish first_ops rest_ops. R st _ _ /\ _ ==> _`
    (qspecl_then [`ps`, `ps1`, `post`, `step_ops`, `rest_ops`] mp_tac) >>
  simp[]
QED

Theorem reorder_prepare_trace_relation:
  !targets ps ops post R.
    (!st. R st [] st) /\
    (!st mid finish first_ops rest_ops.
      R st first_ops mid /\ R mid rest_ops finish ==>
      R st (first_ops ++ rest_ops) finish) /\
    (!op st step_ops finish.
      MEM op targets /\ is_var_operand op /\
      do_restore op st = (step_ops,finish) ==> R st step_ops finish) /\
    (!op st step_ops finish.
      MEM op targets /\
      reduce_depth_plan (LENGTH st.ps_stack - LENGTH targets)
        targets op 0 0 st = (step_ops,finish) ==> R st step_ops finish) /\
    reorder_prepare_plan targets ps = (ops,post) ==> R ps ops post
Proof
  rpt gen_tac >> strip_tac >>
  drule reorder_prepare_plan_split >> strip_tac >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  `R ps restore_ops restored` by
    (qspecl_then [`FILTER is_var_operand targets`, `do_restore`, `ps`,
                  `restore_ops`, `restored`, `R`] mp_tac plan_steps_trace_relation >>
     simp[GSYM restore_spilled_plan_steps, MEM_FILTER] >> metis_tac[]) >>
  `R restored spill_ops post` by
    (qspecl_then [`ordered`, `\op st. reduce_depth_plan
        (LENGTH st.ps_stack - LENGTH targets) targets op 0 0 st`,
        `restored`, `spill_ops`, `post`, `R`] mp_tac plan_steps_trace_relation >>
     simp[] >> impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >>
         rpt gen_tac >> strip_tac >>
         `MEM item targets` by fs[EVERY_MEM] >>
         qpat_assum `!op st step_ops finish. MEM op targets /\
                       reduce_depth_plan _ _ _ _ _ _ = _ ==> _`
           (qspecl_then [`item`, `st`, `step_ops`, `finish'`] mp_tac) >>
         simp[]) >>
     simp[]) >>
  qpat_assum `!st mid finish first_ops rest_ops. R st _ _ /\ _ ==> _`
    (qspecl_then [`ps`, `restored`, `post`, `restore_ops`, `spill_ops`] mp_tac) >>
  simp[]
QED

Theorem plan_steps_preserves:
  !items produce_ops ps ops post P.
    P ps /\
    (!item start step_ops finish. MEM item items /\ P start /\
        produce_ops item start = (step_ops,finish) ==> P finish) /\
    plan_steps produce_ops items ps = (ops,post) ==> P post
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`items`, `produce_ops`, `ps`, `ops`, `post`,
    `\start ops finish. P start ==> P finish`]
    (mp_tac o BETA_RULE) plan_steps_trace_relation >>
  simp[] >> metis_tac[]
QED

Theorem reorder_prepare_preserves:
  !targets ps ops post P.
    P ps /\
    (!op start stage_ops finish.
      MEM op targets /\ is_var_operand op /\ P start /\
      do_restore op start = (stage_ops,finish) ==> P finish) /\
    (!op start stage_ops finish.
      MEM op targets /\ P start /\
      reduce_depth_plan (LENGTH start.ps_stack - LENGTH targets)
        targets op 0 0 start = (stage_ops,finish) ==> P finish) /\
    reorder_prepare_plan targets ps = (ops,post) ==> P post
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`targets`, `ps`, `ops`, `post`,
    `\start ops finish. P start ==> P finish`]
    (mp_tac o BETA_RULE) reorder_prepare_trace_relation >>
  simp[] >> metis_tac[]
QED

Theorem reorder_plan_trace_relation:
  !dfg targets ps ops post R.
    (!st. R st [] st) /\
    (!st mid finish first_ops rest_ops.
      R st first_ops mid /\ R mid rest_ops finish ==>
      R st (first_ops ++ rest_ops) finish) /\
    (!op st step_ops finish.
      MEM op targets /\ is_var_operand op /\
      do_restore op st = (step_ops,finish) ==> R st step_ops finish) /\
    (!op st step_ops finish.
      MEM op targets /\
      reduce_depth_plan (LENGTH st.ps_stack - LENGTH targets)
        targets op 0 0 st = (step_ops,finish) ==> R st step_ops finish) /\
    (!idx op st step_ops finish.
      idx < LENGTH targets /\ MEM op targets /\
      reorder_one dfg targets idx op st = (step_ops,finish) ==> R st step_ops finish) /\
    reorder_plan dfg targets ps = (ops,post) ==> R ps ops post
Proof
  rpt gen_tac >> strip_tac >>
  drule reorder_plan_split >> strip_tac >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  `R ps prep mid` by
    (qspecl_then [`targets`, `ps`, `prep`, `mid`, `R`] mp_tac reorder_prepare_trace_relation >>
     simp[] >> disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `R mid rest post` by
    (qspecl_then [`MAPi (\i op. (i,op)) targets`,
      `\(idx,op) st. reorder_one dfg targets idx op st`,
      `mid`, `rest`, `post`, `R`] mp_tac plan_steps_trace_relation >>
     simp[pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
     impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >>
         rpt gen_tac >> strip_tac >> gvs[] >>
         qpat_assum `!idx op st ops finish. idx < LENGTH targets /\ _ ==> _`
           (qspecl_then [`p_1`, `EL p_1 targets`, `st`, `step_ops`, `finish'`] mp_tac) >>
         simp[EL_MEM]) >>
     simp[]) >>
  qpat_assum `!st mid finish first_ops rest_ops. R st _ _ /\ _ ==> _`
    (qspecl_then [`ps`, `mid`, `post`, `prep`, `rest`] mp_tac) >>
  simp[]
QED

Theorem plan_steps_venom_asm_rel_addresses:
  !items produce_ops ops ps post lo o2pc prog vs st P.
    P ps /\
    (!item start step_ops finish ast.
      P start /\ produce_ops item start = (step_ops,finish) /\
      (!off. MEM (SOSpill off) step_ops \/ MEM (SORestore off) step_ops ==>
             off < dimword(:256)) /\
      venom_asm_rel lo start vs ast /\
      asm_block_at prog ast.as_pc (execute_plan initial_fmp step_ops) ==>
      ?ast'. asm_steps lo o2pc prog
               (LENGTH (execute_plan initial_fmp step_ops)) ast = AsmOK ast' /\
             venom_asm_rel lo finish vs ast' /\
             ast'.as_pc = ast.as_pc + LENGTH (execute_plan initial_fmp step_ops) /\
             P finish) /\
    plan_steps produce_ops items ps = (ops,post) /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==>
           off < dimword(:256)) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
            AsmOK st' /\
          venom_asm_rel lo post vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  Induct
  >- (rpt gen_tac >> simp[plan_steps_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `st` >> simp[execute_plan_def, asm_steps_def]) >>
  rpt gen_tac >> strip_tac >>
  drule plan_steps_cons_result >> strip_tac >> gvs[] >>
  qpat_assum `!item start step_ops finish ast. _`
    (qspecl_then [`h`, `ps`, `step_ops`, `ps1`, `st`] mp_tac) >>
  gvs[execute_plan_append, asm_block_at_append, MEM_APPEND] >>
  impl_tac >- metis_tac[] >>
  strip_tac >> rename1 `venom_asm_rel lo ps1 vs mid` >>
  first_x_assum
    (qspecl_then [`produce_ops`, `rest_ops`, `ps1`, `post`, `lo`, `o2pc`,
                  `prog`, `vs`, `mid`, `P`] mp_tac) >>
  simp[] >> impl_tac >- metis_tac[] >>
  strip_tac >>
  rename1 `venom_asm_rel lo post vs final` >>
  `asm_steps lo o2pc prog
      (LENGTH (execute_plan initial_fmp step_ops) +
       LENGTH (execute_plan initial_fmp rest_ops)) st = AsmOK final` by
    (irule asm_steps_compose_ok >> qexists_tac `mid` >> simp[]) >>
  qexists_tac `final` >> simp[] >> metis_tac[ADD_COMM]
QED

Theorem reduce_depth_plan_unfixed_hit:
  !fuel targets op f n ps ops qs.
    MEM op targets /\ IS_SOME (stack_get_unfixed_depth op f n ps.ps_stack) /\
    reduce_depth_plan fuel targets op f n ps = (ops,qs) ==>
    IS_SOME (stack_get_unfixed_depth op f n qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> gvs[] >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME d` >>
  Cases_on `d <= 16`
  >- (`reduce_depth_plan fuel targets op f n ps = ([],ps)` by
        (irule planWfTheory.reduce_depth_plan_le_16 >> simp[]) >> gvs[]) >>
  `d > 16` by decide_tac >>
  drule_all planWfTheory.reduce_depth_plan_dist_ge >>
  disch_then (qspec_then `fuel` mp_tac) >> simp[] >>
  strip_tac >> simp[]
QED

Theorem reduce_depth_plan_spill_free:
  !fuel pending op f n ps ops ps'.
    reduce_depth_plan fuel pending op f n ps = (ops,ps') /\
    (!off. ~MEM (SOSpill off) ops) ==> ps' = ps /\ ops = []
Proof
  Induct >> simp[Once reduce_depth_plan_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  Cases_on `dist <= 16` >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack pending dist n` >> simp[] >>
  rename1 `select_spill_candidate _ _ _ _ = SOME cand` >>
  Cases_on `do_spill_at cand ps` >> rename1 `do_spill_at _ _ = (sops,ps_mid)` >>
  Cases_on `reduce_depth_plan fuel pending op f n ps_mid` >>
  simp[MEM_APPEND] >> strip_tac >>
  qpat_x_assum `do_spill_at _ _ = _`
    (mp_tac o PURE_REWRITE_RULE [do_spill_at_def, do_spill_tos_def]) >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >>
  Cases_on `cand = 0` >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[]
QED


Theorem reorder_prepare_trace_empty:
  !targets ps ops post.
    reorder_prepare_plan targets ps = (ops,post) /\
    (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
    ops = [] /\ post = ps
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`targets`, `ps`, `ops`, `post`,
    `\st trace out. (!off. ~MEM (SOSpill off) trace /\
                           ~MEM (SORestore off) trace) ==> trace = [] /\ out = st`]
    (mp_tac o BETA_RULE) reorder_prepare_trace_relation >>
  impl_tac
  >- (rpt conj_tac
      >- simp[]
      >- metis_tac[MEM_APPEND, APPEND_NIL]
      >- (rpt gen_tac >> Cases_on `FLOOKUP st.ps_spilled op` >>
          simp[do_restore_def] >> strip_tac >> gvs[] >>
          disch_then (qspec_then `x` mp_tac) >> simp[])
      >- metis_tac[reduce_depth_plan_spill_free]
      >- first_assum ACCEPT_TAC) >>
  simp[]
QED
