(* Actual recorder prefixes of the emitted return-word stores. *)
Theory loweringBudgetReturnStorePrefix
Ancestors
  loweringBudgetReturnStoreSem loweringBudgetStoreRecorder intCallResult
  exprLowering exprLoweringProps compileEnv freshWrites fragExec
  contextCodegenRel loweringCallBudgetHistory venomExecSemantics venomState
  valueEncodingDefs immutableMemoryFrame list rich_list arithmetic

Theorem store_multi_results_budget_prefix:
  !ops buf_op off sa sb D lo explicit ctx root h0 marks0 p hs marks q b ws.
    store_multi_results buf_op ops off sa = ((),sb) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. MEM (Var x) ops ==> not_fresh_at sa x) /\
    eval_operand buf_op p.bp_state = SOME (n2w b) /\
    MAP (\op. eval_operand op p.bp_state) ops = MAP SOME ws /\
    b + off + 32 * LENGTH ops < dimword (:256) /\
    lower_budget_path F (D,lo,explicit,ctx) root h0 marks0 p /\
    lower_budget_path F (D,lo,explicit,ctx) root (h0 ++ hs) marks q /\
    fn_has_code sa sb p.bp_fn /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) p.bp_fn.fn_blocks) /\
    p.bp_state.vs_current_bb = sa.cs_current_bb /\
    p.bp_state.vs_inst_idx = LENGTH sa.cs_current_insts /\
    LENGTH hs <= 2 * LENGTH ops ==>
    marks = marks0 /\ q.bp_fn = p.bp_fn /\ q.bp_stack = p.bp_stack /\
    q.bp_params = p.bp_params /\
    EVERY (\e. ~lower_event_consumes e /\ ~lower_event_allocates e) hs /\
    q.bp_state.vs_inst_idx = p.bp_state.vs_inst_idx + LENGTH hs /\
    (!i. i < LENGTH hs DIV 2 ==>
      mem_word_at (b + off + 32 * i) q.bp_state.vs_memory = EL i ws) /\
    (!a len. a + len <= b + off \/ b + off + 32 * (LENGTH hs DIV 2) <= a ==>
      mem_bytes_at a len q.bp_state.vs_memory =
      mem_bytes_at a len p.bp_state.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x q.bp_state = lookup_var x p.bp_state) /\
    (q.bp_state with <|vs_vars := p.bp_state.vs_vars;
       vs_memory := p.bp_state.vs_memory;
       vs_inst_idx := p.bp_state.vs_inst_idx|>) = p.bp_state
Proof
  rpt gen_tac >> strip_tac >>
  drule_all store_multi_results_take_run >> strip_tac >>
  drule store_multi_results_shape >> strip_tac >>
  `LENGTH hs <= LENGTH (emitted_insts sa sb)` by simp[] >>
  drule_all store_code_budget_segment >> strip_tac >>
  gvs[] >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- fs[lookup_var_def] >>
  fs[venom_state_component_equality]
QED

Theorem store_multi_results_budget_endpoint:
  !ops buf_op off sa sb D lo explicit ctx root h0 marks0 p hs marks q b ws.
    store_multi_results buf_op ops off sa = ((),sb) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. MEM (Var x) ops ==> not_fresh_at sa x) /\
    eval_operand buf_op p.bp_state = SOME (n2w b) /\
    MAP (\op. eval_operand op p.bp_state) ops = MAP SOME ws /\
    b + off + 32 * LENGTH ops < dimword (:256) /\
    lower_budget_path F (D,lo,explicit,ctx) root h0 marks0 p /\
    lower_budget_path F (D,lo,explicit,ctx) root (h0 ++ hs) marks q /\
    fn_has_code sa sb p.bp_fn /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) p.bp_fn.fn_blocks) /\
    p.bp_state.vs_current_bb = sa.cs_current_bb /\
    p.bp_state.vs_inst_idx = LENGTH sa.cs_current_insts /\
    LENGTH hs = 2 * LENGTH ops ==>
    marks = marks0 /\ q.bp_fn = p.bp_fn /\ q.bp_stack = p.bp_stack /\
    q.bp_params = p.bp_params /\
    EVERY (\e. ~lower_event_consumes e /\ ~lower_event_allocates e) hs /\
    q.bp_state.vs_current_bb = sb.cs_current_bb /\
    q.bp_state.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!i. i < LENGTH ops ==>
      mem_word_at (b + off + 32 * i) q.bp_state.vs_memory = EL i ws) /\
    (!a len. a + len <= b + off \/ b + off + 32 * LENGTH ops <= a ==>
      mem_bytes_at a len q.bp_state.vs_memory =
      mem_bytes_at a len p.bp_state.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x q.bp_state = lookup_var x p.bp_state) /\
    (q.bp_state with <|vs_vars := p.bp_state.vs_vars;
       vs_memory := p.bp_state.vs_memory;
       vs_inst_idx := p.bp_state.vs_inst_idx|>) = p.bp_state
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH hs <= 2 * LENGTH ops` by simp[] >>
  drule_all store_multi_results_budget_prefix >> strip_tac >>
  drule store_multi_results_shape >> strip_tac >>
  drule store_multi_results_code_shape >> strip_tac >>
  fs[same_blocks_def, venom_state_component_equality] >>
  gvs[]
QED
