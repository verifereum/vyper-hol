(* Reading the checks at any point of the recorded prefix, including its endpoint. *)
Theory s1PrefixIssueChecks
Ancestors
  loweringCallBudgetHistory loweringBudgetStoreRecorder loweringBudgetPathDeterminism
  fragGasOriginPtrSafeUpto bodyPtrDefs lowerDloadPtrRawReachable contextCodegenRel
  ptrSafeRun memSafeRun list rich_list

Theorem active_mem_step_facts[local]:
  MEM p.bp_fn ctx.ctx_functions /\ ALL_DISTINCT (fn_labels p.bp_fn) /\
  active_inst p.bp_fn inst p.bp_state /\
  (in_revert_forward p.bp_fn p.bp_state \/ mem_safe_step fuel ctx inst p.bp_state) ==>
  inst_mem_ok_in_fn p.bp_fn inst p.bp_state /\
  inst_dload_in_section inst p.bp_state /\ dalloca_no_wrap inst p.bp_state
Proof
  strip_tac >> drule_all active_inst_block_lookup >>
  fs[in_revert_forward_def] >> metis_tac[mem_step_facts, optionTheory.SOME_11]
QED

(* A checked traversal records a check at the source of its last edge;
   the incoming path need not record the same choice of instruction fuels. *)
Theorem issue_snoc_checks[local]:
  root.bp_stack = [] /\ MEM root.bp_fn ctx.ctx_functions /\
  (!fn. MEM fn ctx.ctx_functions ==>
    ALL_DISTINCT (fn_labels fn) /\
    !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  lower_budget_path T (D,lo,explicit,ctx) root (h ++ [ev]) marks p /\
  lower_budget_path F (D,lo,explicit,ctx) root hr mr q /\
  LENGTH h = LENGTH hr /\
  active_inst q.bp_fn inst q.bp_state ==>
  (!fuel. ptr_inst_ok D lo fuel ctx q.bp_fn q.bp_prov q.bp_taint inst q.bp_state) /\
  inst_mem_ok_in_fn q.bp_fn inst q.bp_state /\
  inst_dload_in_section inst q.bp_state /\ dalloca_no_wrap inst q.bp_state
Proof
  strip_tac >>
  `MEM q.bp_fn ctx.ctx_functions` by metis_tac[lower_budget_path_current_fn_mem] >>
  `ALL_DISTINCT (fn_labels q.bp_fn)` by metis_tac[] >>
  `!i. active_inst q.bp_fn i q.bp_state ==> i = inst` by
    metis_tac[active_inst_block_lookup, optionTheory.SOME_11] >>
  qpat_x_assum `lower_budget_path T _ _ _ _ _` mp_tac >>
  once_rewrite_tac[lower_budget_path_cases] >> strip_tac >>
  gvs[GSYM SNOC_APPEND] >>
  rename1 `lower_budget_path T _ _ h _ before` >>
  `q = before` by metis_tac[lower_budget_path_equal_length_sync] >> gvs[] >>
  metis_tac[ptr_safe_step_inst_ok, ptr_inst_ok_fuel, active_mem_step_facts,
            invoke_mem_facts]
QED

Theorem issue_prefix_frame_checks:
  root.bp_stack = [] /\ MEM root.bp_fn ctx.ctx_functions /\
  (!fn. MEM fn ctx.ctx_functions ==>
    ALL_DISTINCT (fn_labels fn) /\
    !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  lower_budget_path T (D,lo,explicit,ctx) root h marks p /\
  lower_budget_path F (D,lo,explicit,ctx) root hr mr q /\
  LENGTH hr <= LENGTH h /\
  active_inst q.bp_fn inst q.bp_state /\ active_inst p.bp_fn issue p.bp_state /\
  issue.inst_opcode <> INVOKE /\
  ptr_inst_ok D lo 0 ctx p.bp_fn p.bp_prov p.bp_taint issue p.bp_state /\
  stor_taint_ok_at D p.bp_taint p.bp_state /\
  mem_safe_step issue_fuel ctx issue p.bp_state ==>
  (!fuel. ptr_inst_ok D lo fuel ctx q.bp_fn q.bp_prov q.bp_taint inst q.bp_state) /\
  inst_mem_ok_in_fn q.bp_fn inst q.bp_state /\
  inst_dload_in_section inst q.bp_state /\ dalloca_no_wrap inst q.bp_state
Proof
  strip_tac >> Cases_on `LENGTH hr = LENGTH h`
  >- (`p = q` by metis_tac[lower_budget_path_equal_length_sync] >>
      qpat_x_assum `p = q` SUBST_ALL_TAC >>
      `MEM q.bp_fn ctx.ctx_functions` by metis_tac[lower_budget_path_current_fn_mem] >>
      `ALL_DISTINCT (fn_labels q.bp_fn)` by metis_tac[] >>
      `inst = issue` by metis_tac[active_inst_block_lookup, optionTheory.SOME_11] >>
      gvs[] >> metis_tac[ptr_inst_ok_fuel, active_mem_step_facts]) >>
  qpat_x_assum `lower_budget_path T _ _ h _ _` (mp_then Any mp_tac lower_budget_path_take) >>
  disch_then (qspec_then `SUC (LENGTH hr)` mp_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  qspec_then `TAKE (SUC (LENGTH hr)) h` mp_tac listTheory.SNOC_CASES >>
  strip_tac >> gvs[SNOC_APPEND] >>
  rename1 `TAKE (SUC (LENGTH hr)) h = pre ++ [ev]` >>
  `LENGTH pre = LENGTH hr` by
    (qpat_assum `TAKE _ _ = _` (mp_tac o AP_TERM ``LENGTH:lower_budget_event list -> num``) >>
     simp[LENGTH_TAKE, LENGTH_APPEND]) >>
  metis_tac[issue_snoc_checks]
QED
