Theory loweringBudgetPathDeterminism
Ancestors
  loweringCallBudgetHistory loweringBudgetStoreRecorder
  contextCodegenRel venomExecSemantics venomInst venomInstProofs1
  ptrSafeRun lowerDloadPtrRawReachable list rich_list

Theorem budget_path_fn_members[local]:
  !checked cfg root h marks q.
    lower_budget_path checked cfg root h marks q ==>
    !D lo explicit ctx. cfg = (D,lo,explicit,ctx) /\
      MEM root.bp_fn ctx.ctx_functions /\
      EVERY (\fr. MEM fr.cf_fn ctx.ctx_functions) root.bp_stack ==>
      MEM q.bp_fn ctx.ctx_functions /\
      EVERY (\fr. MEM fr.cf_fn ctx.ctx_functions) q.bp_stack
Proof
  ho_match_mp_tac lower_budget_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[] >> metis_tac[lookup_function_MEM]
QED

Theorem lower_budget_path_current_fn_mem:
  !checked D lo explicit ctx p h marks q.
    p.bp_stack = [] /\ MEM p.bp_fn ctx.ctx_functions /\
    lower_budget_path checked (D,lo,explicit,ctx) p h marks q ==>
    MEM q.bp_fn ctx.ctx_functions
Proof
  metis_tac[budget_path_fn_members, EVERY_DEF]
QED

Theorem budget_active_unique[local]:
  !fn i j s.
    ALL_DISTINCT (fn_labels fn) /\ active_inst fn i s /\
    active_inst fn j s ==> i = j
Proof
  metis_tac[active_inst_block_lookup, optionTheory.SOME_11]
QED

Theorem budget_enters_unique[local]:
  !fn s a b. enters_block fn s a /\ enters_block fn s b ==> a = b
Proof
  simp[enters_block_def] >> rpt strip_tac >> gvs[]
QED

Theorem budget_path_sync[local]:
  !checked cfg root h marks q.
    lower_budget_path checked cfg root h marks q ==>
    !D lo explicit ctx checked2 D2 lo2 explicit2 h2 marks2 q2.
      cfg = (D,lo,explicit,ctx) /\
      root.bp_stack = [] /\ MEM root.bp_fn ctx.ctx_functions /\
      (!fn. MEM fn ctx.ctx_functions ==>
        ALL_DISTINCT (fn_labels fn) /\
        !bb. MEM bb fn.fn_blocks ==>
          phi_prefix_length bb.bb_instructions = 0) /\
      lower_budget_path checked2 (D2,lo2,explicit2,ctx) root h2 marks2 q2 /\
      LENGTH h = LENGTH h2 ==>
      q = q2 /\ MAP lower_event_consumes h = MAP lower_event_consumes h2
Proof
  ho_match_mp_tac lower_budget_path_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `lower_budget_path checked2 _ _ _ _ _` mp_tac >>
      once_rewrite_tac[lower_budget_path_cases] >>
      strip_tac >> gvs[]) >>
  gvs[] >>
  qpat_x_assum `lower_budget_path checked2 _ _ _ _ _` mp_tac >>
  once_rewrite_tac[lower_budget_path_cases] >>
  strip_tac >> gvs[LENGTH_APPEND] >>
  `q = p /\ MAP lower_event_consumes h = MAP lower_event_consumes h'`
    by metis_tac[] >>
  `ALL_DISTINCT (fn_labels q.bp_fn)` by
    metis_tac[lower_budget_path_current_fn_mem] >>
  qpat_x_assum `!checked2' D2' lo2' explicit2' h2' marks2' q2'. _` kall_tac >>
  qpat_x_assum `!fn. MEM fn ctx.ctx_functions ==> _` kall_tac >>
  rpt (qpat_x_assum `lower_budget_path _ _ _ _ _ _` kall_tac) >>
  gvs[] >> imp_res_tac budget_active_unique >>
  rpt (qpat_x_assum `a = (b:instruction)` SUBST_ALL_TAC) >>
  imp_res_tac step_inst_intret_not_invoke >>
  `!op. is_terminator op ==> op <> INVOKE` by
    (rpt strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  qpat_assum `!op. is_terminator op ==> _` imp_res_tac >>
  gvs[step_inst_non_invoke, lower_event_consumes_def] >>
  metis_tac[budget_enters_unique]
QED

Theorem lower_budget_path_equal_length_sync:
  !checked1 checked2 D1 lo1 explicit1 D2 lo2 explicit2 ctx p
    h1 marks1 q1 h2 marks2 q2.
    p.bp_stack = [] /\ MEM p.bp_fn ctx.ctx_functions /\
    (!fn. MEM fn ctx.ctx_functions ==>
      ALL_DISTINCT (fn_labels fn) /\
      !bb. MEM bb fn.fn_blocks ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    lower_budget_path checked1 (D1,lo1,explicit1,ctx) p h1 marks1 q1 /\
    lower_budget_path checked2 (D2,lo2,explicit2,ctx) p h2 marks2 q2 /\
    LENGTH h1 = LENGTH h2 ==>
    q1 = q2 /\ MAP lower_event_consumes h1 = MAP lower_event_consumes h2
Proof
  metis_tac[budget_path_sync]
QED
