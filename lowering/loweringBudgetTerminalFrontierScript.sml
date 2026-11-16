Theory loweringBudgetTerminalFrontier
Ancestors
  loweringCallBudgetHistory loweringBudgetStoreRecorder lowerDloadPtrRawReachable
  venomExecSemantics ptrSafeRun fragExec list rich_list

Theorem lower_budget_terminal_no_extension:
  !checked D lo explicit ctx root h marks p i fuel r e marks' q.
    lower_budget_path checked (D,lo,explicit,ctx) root h marks p /\
    ALL_DISTINCT (fn_labels p.bp_fn) /\
    active_inst p.bp_fn i p.bp_state /\ i.inst_opcode <> INVOKE /\
    ((step_inst fuel ctx i p.bp_state = r /\ exit_result r /\
      (!ret t. r = IntRet ret t ==> p.bp_stack = [])) \/
     (?t. step_inst fuel ctx i p.bp_state = OK t /\
       is_terminator i.inst_opcode /\ t.vs_halted)) ==>
    ~lower_budget_path checked (D,lo,explicit,ctx) root (h ++ [e]) marks' q
Proof
  rpt gen_tac >> strip_tac >>
  `!j. active_inst p.bp_fn j p.bp_state ==> j = i` by
    metis_tac[active_inst_block_lookup, optionTheory.SOME_11] >>
  `!m s. lower_budget_path checked (D,lo,explicit,ctx) root h m s ==>
    m = marks /\ s = p` by metis_tac[lower_budget_path_history_unique] >>
  qpat_x_assum `lower_budget_path _ _ _ h marks p` kall_tac >>
  strip_tac >>
  qpat_x_assum `lower_budget_path _ _ _ (_ ++ [_]) _ _` mp_tac >>
  pure_once_rewrite_tac[lower_budget_path_cases] >> strip_tac >>
  full_simp_tac bool_ss [GSYM SNOC_APPEND, SNOC_11, NOT_SNOC_NIL] >>
  gvs[] >>
  qpat_x_assum `!m s. lower_budget_path _ _ _ _ m s ==> _` drule >>
  strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  gvs[step_inst_non_invoke, exit_result_def]
QED
