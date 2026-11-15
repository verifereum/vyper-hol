(* Normal exits expose the actual terminal instruction, including in callees. *)
Theory loweringTerminalHistory
Ancestors
  loweringJointPrefixHistory loweringCallBudgetHistory
  ptrSafeRun ptrDiscipline memSafeRun gasEvents
  contextCodegenRel contextCodegenRelProps venomExecSemantics venomExecProofs
  venomInstProofs venomInst venomState finite_map list arithmetic

Theorem step_inst_invoke_exit:
  !fuel ctx call_inst s r.
    call_inst.inst_opcode = INVOKE /\ step_inst fuel ctx call_inst s = r /\
    exit_result r ==>
    ?name ops callee args cs.
      decode_invoke call_inst = SOME (name,ops) /\
      lookup_function name ctx.ctx_functions = SOME callee /\
      eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
      run_blocks fuel ctx callee cs = r /\
      (!returned final_state. r <> IntRet returned final_state)
Proof
  rpt gen_tac >> simp[Once step_inst_def] >> strip_tac >>
  gvs[AllCaseEqs(), fragExecTheory.exit_result_def] >>
  metis_tac[venomExecSemanticsTheory.exec_result_distinct]
QED

Theorem lower_budget_checked_callee_entry:
  !D lo explicit ctx root h marks p call_inst name ops callee args cs fuel r.
    lower_budget_path T (D,lo,explicit,ctx) root h marks p /\
    active_inst p.bp_fn call_inst p.bp_state /\ call_inst.inst_opcode = INVOKE /\
    decode_invoke call_inst = SOME (name,ops) /\
    lookup_function name ctx.ctx_functions = SOME callee /\
    eval_operands ops p.bp_state = SOME args /\
    setup_callee callee args p.bp_state = SOME cs /\
    run_blocks fuel ctx callee cs = r /\ exit_result r /\
    ptr_safe_step D lo fuel ctx p.bp_fn p.bp_params p.bp_prov p.bp_taint
      call_inst p.bp_state /\ mem_safe_step fuel ctx call_inst p.bp_state ==>
    ?child_fuel target entered callee_point call_history.
      fuel = SUC child_fuel /\
      lookup_block entered.vs_current_bb callee.fn_blocks = SOME target /\
      frame_run child_fuel ctx callee entered = r /\
      callee_point = <|
        bp_stack := <| cf_fn := p.bp_fn; cf_inst := call_inst; cf_state := p.bp_state;
          cf_params := p.bp_params; cf_prov := p.bp_prov;
          cf_tvar := p.bp_taint.t_var |> :: p.bp_stack;
        bp_params := MAP (op_prov p.bp_prov) ops; bp_prov := FEMPTY;
        bp_taint := p.bp_taint with t_var := FEMPTY;
        bp_fn := callee; bp_state := entered |> /\
      lower_budget_path T (D,lo,explicit,ctx) root call_history marks callee_point /\
      ptr_safe_run D lo child_fuel ctx callee callee_point.bp_params
        callee_point.bp_prov callee_point.bp_taint entered /\
      mem_safe_run child_fuel ctx callee entered /\
      gas_events_step fuel ctx p.bp_fn.fn_name call_inst p.bp_state =
        gas_events_block child_fuel ctx callee.fn_name target entered ++
        case exec_block child_fuel ctx target entered of
          OK t => if t.vs_halted then [] else gas_events_blocks child_fuel ctx callee t
        | _ => []
Proof
  rpt gen_tac >> strip_tac >> Cases_on `fuel`
  >- (qpat_x_assum `run_blocks 0 _ _ _ = _` mp_tac >>
      simp[Once run_blocks_def] >> strip_tac >> gvs[fragExecTheory.exit_result_def] >>
      metis_tac[fragExecTheory.exit_result_not_error]) >>
  rename1 `run_blocks (SUC child_fuel) ctx callee cs = r` >>
  Cases_on `lookup_block cs.vs_current_bb callee.fn_blocks`
  >- (qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
      simp[Once run_blocks_def] >> strip_tac >> gvs[fragExecTheory.exit_result_def] >>
      metis_tac[fragExecTheory.exit_result_not_error]) >>
  rename1 `lookup_block cs.vs_current_bb callee.fn_blocks = SOME target` >>
  qspecl_then [`cs`, `target.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >~ [`eval_phis _ _ = Error _`]
  >- (qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
      simp[Once run_blocks_def] >> strip_tac >> gvs[fragExecTheory.exit_result_def] >>
      metis_tac[fragExecTheory.exit_result_not_error]) >>
  rename1 `eval_phis cs target.bb_instructions = OK phi` >>
  qabbrev_tac `entered = phi with vs_inst_idx := phi_prefix_length target.bb_instructions` >>
  `lookup_block entered.vs_current_bb callee.fn_blocks = SOME target` by
    (simp[Abbr`entered`] >> drule eval_phis_preserves_current_bb >> simp[]) >>
  `enters_block callee cs entered` by
    (rewrite_tac[enters_block_def] >> qexistsl_tac [`target`, `phi`] >> simp[Abbr`entered`]) >>
  `frame_run child_fuel ctx callee entered = r` by
    (qspecl_then [`ctx`, `callee`, `p.bp_params`, `p.bp_prov`, `p.bp_taint`,
       `cs`, `entered`, `child_fuel`] mp_tac frame_run_enters_block >> simp[]) >>
  Cases_on `get_instruction target entered.vs_inst_idx`
  >- (qpat_x_assum `frame_run _ _ _ _ = _` mp_tac >>
      simp[frame_run_def, block_run_def, Once exec_block_def] >> strip_tac >>
      gvs[fragExecTheory.exit_result_def] >>
      metis_tac[fragExecTheory.exit_result_not_error]) >>
  rename1 `get_instruction target entered.vs_inst_idx = SOME head_inst` >>
  `active_inst callee head_inst entered` by
    (irule lookup_instruction_active >> simp[]) >> suspend "call"
QED

Resume lower_budget_checked_callee_entry[call]:
  qabbrev_tac `callee_point = <|
    bp_stack := <| cf_fn := p.bp_fn; cf_inst := call_inst; cf_state := p.bp_state;
      cf_params := p.bp_params; cf_prov := p.bp_prov;
      cf_tvar := p.bp_taint.t_var |> :: p.bp_stack;
    bp_params := MAP (op_prov p.bp_prov) ops; bp_prov := FEMPTY;
    bp_taint := p.bp_taint with t_var := FEMPTY;
    bp_fn := callee; bp_state := entered |>` >>
  qabbrev_tac `call_history = h ++ [BudgetCall (LENGTH h) p call_inst callee cs callee_point]` >>
  `lower_budget_path T (D,lo,explicit,ctx) root call_history marks callee_point` by
    (simp[Abbr`call_history`] >> irule lower_budget_path_call >> simp[Abbr`callee_point`] >>
     metis_tac[ptr_safe_step_inst_ok, ptr_inst_ok_fuel]) >>
  `ptr_safe_blocks D lo (SUC child_fuel) ctx callee
    (MAP (op_prov p.bp_prov) ops) FEMPTY (p.bp_taint with t_var := FEMPTY) cs` by
    (qspecl_then [`D`, `lo`, `SUC child_fuel`, `ctx`, `p.bp_fn`, `p.bp_params`,
       `p.bp_prov`, `p.bp_taint`, `call_inst`, `p.bp_state`, `name`, `ops`,
       `callee`, `args`, `cs`] mp_tac ptr_safe_step_invoke >> simp[]) >>
  `ptr_safe_run D lo child_fuel ctx callee callee_point.bp_params
    callee_point.bp_prov callee_point.bp_taint entered` by
    (qpat_x_assum `ptr_safe_blocks _ _ _ _ callee _ _ _ cs` mp_tac >>
     simp[Once ptr_safe_blocks_def, ptr_safe_run_def, Abbr`callee_point`, Abbr`entered`]) >>
  `mem_safe_blocks (SUC child_fuel) ctx callee cs` by
    (qspecl_then [`SUC child_fuel`, `ctx`, `call_inst`, `p.bp_state`, `name`, `ops`,
       `callee`, `args`, `cs`] mp_tac mem_safe_step_invoke >> simp[]) >>
  `mem_safe_run child_fuel ctx callee entered` by
    (qpat_x_assum `mem_safe_blocks _ _ callee cs` mp_tac >>
     simp[Once mem_safe_blocks_def, mem_safe_run_def, Abbr`entered`]) >>
  qexistsl_tac [`child_fuel`, `target`, `entered`, `callee_point`, `call_history`] >>
  simp[Abbr`callee_point`, gas_events_step_def, Once gas_events_blocks_def, Abbr`entered`]
QED

Finalise lower_budget_checked_callee_entry

Theorem lower_budget_checked_terminal:
  !fuel ctx func bb s r.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    frame_run fuel ctx func s = r /\ exit_result r /\
    (!returned final_state. r <> IntRet returned final_state) ==>
    !D lo explicit root h marks p.
      lower_budget_path T (D,lo,explicit,ctx) root h marks p /\
      p.bp_fn = func /\ p.bp_state = s /\
      ptr_safe_run D lo fuel ctx func p.bp_params p.bp_prov p.bp_taint s /\
      mem_safe_run fuel ctx func s ==>
      ?history premarks q terminal terminal_fuel.
        lower_budget_path T (D,lo,explicit,ctx) root history (marks ++ premarks) q /\
        active_inst q.bp_fn terminal q.bp_state /\ terminal.inst_opcode <> INVOKE /\
        MAP (\key. key IN explicit)
          (gas_events_block fuel ctx func.fn_name bb s ++
           case exec_block fuel ctx bb s of
             OK t => if t.vs_halted then [] else gas_events_blocks fuel ctx func t
           | _ => []) =
          premarks ++ MAP (\key. key IN explicit)
            (gas_events_step terminal_fuel ctx q.bp_fn.fn_name terminal q.bp_state) /\
        (step_inst terminal_fuel ctx terminal q.bp_state = r \/
         ?t. step_inst terminal_fuel ctx terminal q.bp_state = OK t /\
             is_terminator terminal.inst_opcode /\ t.vs_halted /\ r = Halt t)
Proof
  completeInduct_on `fuel` >> rpt gen_tac >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >> rpt strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `frame_run _ _ _ _ = _` mp_tac >>
      simp[frame_run_def, block_run_def, Once exec_block_def] >> strip_tac >>
      gvs[fragExecTheory.exit_result_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME current` >>
  `active_inst func current s` by (irule lookup_instruction_active >> simp[]) >>
  `ptr_safe_block D lo fuel ctx func p.bp_params p.bp_prov p.bp_taint bb s` by
    (qpat_x_assum `ptr_safe_run _ _ _ _ _ _ _ _ _` mp_tac >> simp[ptr_safe_run_def]) >>
  `ptr_safe_step D lo fuel ctx func p.bp_params p.bp_prov p.bp_taint current s` by
    metis_tac[ptr_safe_block_head] >>
  qspecl_then [`fuel`, `ctx`, `func`, `s`, `bb`, `current`]
    mp_tac mem_safe_run_head >> simp[] >> disch_tac >>
  qpat_x_assum `frame_run _ _ _ _ = _` mp_tac >>
  simp[frame_run_def, block_run_def] >> once_rewrite_tac[exec_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx current s` >> simp[]
  >~ [`step_inst _ _ _ _ = Error _`]
  >- (strip_tac >> gvs[fragExecTheory.exit_result_def] >>
      metis_tac[fragExecTheory.exit_result_not_error])
  >~ [`step_inst _ _ _ _ = Halt _`]
  >- suspend "halt"
  >~ [`step_inst _ _ _ _ = Abort _ _`]
  >- suspend "abort" >>
  suspend "ok"
QED

Resume lower_budget_checked_terminal[halt]:
  rename1 `step_inst fuel ctx current s = Halt stopped` >> strip_tac >>
  qpat_x_assum `Halt stopped = r` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `p.bp_fn = func` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `p.bp_state = s` (SUBST_ALL_TAC o SYM) >>
  Cases_on `current.inst_opcode = INVOKE` >- suspend "halt_call" >>
  qexistsl_tac [`h`, `[]`, `p`, `current`, `fuel`] >>
  simp[Once gas_events_block_def, Once exec_block_def]
QED

Resume lower_budget_checked_terminal[abort]:
  rename1 `step_inst fuel ctx current s = Abort abort_reason stopped` >> strip_tac >>
  qpat_x_assum `Abort abort_reason stopped = r` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `p.bp_fn = func` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `p.bp_state = s` (SUBST_ALL_TAC o SYM) >>
  Cases_on `current.inst_opcode = INVOKE` >- suspend "abort_call" >>
  qexistsl_tac [`h`, `[]`, `p`, `current`, `fuel`] >>
  simp[Once gas_events_block_def, Once exec_block_def]
QED

Resume lower_budget_checked_terminal[halt_call]:
  `mem_safe_step fuel ctx current p.bp_state` by
    (Cases_on `revert_forward_at bb p.bp_state.vs_inst_idx` >> fs[] >>
     drule_all revert_forward_at_opcode >> simp[]) >>
  qspecl_then [`fuel`, `ctx`, `current`, `p.bp_state`, `Halt stopped`]
    mp_tac step_inst_invoke_exit >> simp[] >> strip_tac >>
  rename1 `decode_invoke current = SOME (name,ops)` >>
  rename1 `lookup_function name ctx.ctx_functions = SOME callee` >>
  rename1 `eval_operands ops p.bp_state = SOME args` >>
  rename1 `setup_callee callee args p.bp_state = SOME cs` >>
  qspecl_then [`D`, `lo`, `explicit`, `ctx`, `root`, `h`, `marks`, `p`,
    `current`, `name`, `ops`, `callee`, `args`, `cs`, `fuel`, `Halt stopped`]
    mp_tac lower_budget_checked_callee_entry >> simp[] >> strip_tac >>
  rename1 `frame_run child_fuel ctx callee entered = Halt stopped` >>
  rename1 `lookup_block entered.vs_current_bb callee.fn_blocks = SOME target` >>
  rename1 `lower_budget_path T (D,lo,explicit,ctx) root call_history marks _` >>
  qmatch_assum_abbrev_tac
    `lower_budget_path T (D,lo,explicit,ctx) root call_history marks callee_point` >>
  qpat_x_assum `fuel = SUC child_fuel` SUBST_ALL_TAC >>
  `gas_events_block (SUC child_fuel) ctx p.bp_fn.fn_name bb p.bp_state =
    gas_events_step (SUC child_fuel) ctx p.bp_fn.fn_name current p.bp_state` by
    simp[Once gas_events_block_def] >>
  `exec_block (SUC child_fuel) ctx bb p.bp_state = Halt stopped` by simp[Once exec_block_def] >>
  qpat_x_assum `!smaller. smaller < SUC child_fuel ==> _`
    (qspec_then `child_fuel` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`ctx`, `callee`, `target`, `entered`] mp_tac) >>
  simp[] >> disch_then (qspecl_then
    [`D`, `lo`, `explicit`, `root`, `call_history`, `marks`, `callee_point`] mp_tac) >>
  simp[Abbr`callee_point`]
QED

Resume lower_budget_checked_terminal[abort_call]:
  `mem_safe_step fuel ctx current p.bp_state` by
    (Cases_on `revert_forward_at bb p.bp_state.vs_inst_idx` >> fs[] >>
     drule_all revert_forward_at_opcode >> simp[]) >>
  qspecl_then [`fuel`, `ctx`, `current`, `p.bp_state`, `Abort abort_reason stopped`]
    mp_tac step_inst_invoke_exit >> simp[] >> strip_tac >>
  rename1 `decode_invoke current = SOME (name,ops)` >>
  rename1 `lookup_function name ctx.ctx_functions = SOME callee` >>
  rename1 `eval_operands ops p.bp_state = SOME args` >>
  rename1 `setup_callee callee args p.bp_state = SOME cs` >>
  qspecl_then [`D`, `lo`, `explicit`, `ctx`, `root`, `h`, `marks`, `p`,
    `current`, `name`, `ops`, `callee`, `args`, `cs`, `fuel`, `Abort abort_reason stopped`]
    mp_tac lower_budget_checked_callee_entry >> simp[] >> strip_tac >>
  rename1 `frame_run child_fuel ctx callee entered = Abort abort_reason stopped` >>
  rename1 `lookup_block entered.vs_current_bb callee.fn_blocks = SOME target` >>
  rename1 `lower_budget_path T (D,lo,explicit,ctx) root call_history marks _` >>
  qmatch_assum_abbrev_tac
    `lower_budget_path T (D,lo,explicit,ctx) root call_history marks callee_point` >>
  qpat_x_assum `fuel = SUC child_fuel` SUBST_ALL_TAC >>
  `gas_events_block (SUC child_fuel) ctx p.bp_fn.fn_name bb p.bp_state =
    gas_events_step (SUC child_fuel) ctx p.bp_fn.fn_name current p.bp_state` by
    simp[Once gas_events_block_def] >>
  `exec_block (SUC child_fuel) ctx bb p.bp_state = Abort abort_reason stopped` by simp[Once exec_block_def] >>
  qpat_x_assum `!smaller. smaller < SUC child_fuel ==> _`
    (qspec_then `child_fuel` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`ctx`, `callee`, `target`, `entered`] mp_tac) >>
  simp[] >> disch_then (qspecl_then
    [`D`, `lo`, `explicit`, `root`, `call_history`, `marks`, `callee_point`] mp_tac) >>
  simp[Abbr`callee_point`]
QED

Resume lower_budget_checked_terminal[ok]:
  rename1 `step_inst fuel ctx current s = OK mid` >>
  Cases_on `is_terminator current.inst_opcode` >> simp[]
  >- (Cases_on `mid.vs_halted` >> simp[]
      >- suspend "ok_halt" >> suspend "block") >> suspend "within"
QED

Resume lower_budget_checked_terminal[ok_halt]:
  strip_tac >> gnvs[] >>
  `current.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
  qexistsl_tac [`h`, `[]`, `p`, `current`, `fuel`] >>
  simp[Once gas_events_block_def, Once exec_block_def]
QED

Resume lower_budget_checked_terminal[block]:
  strip_tac >> Cases_on `fuel`
  >- (qpat_x_assum `run_blocks 0 _ _ _ = _` mp_tac >>
      simp[Once run_blocks_def] >> strip_tac >> gvs[fragExecTheory.exit_result_def] >>
      metis_tac[fragExecTheory.exit_result_not_error]) >>
  rename1 `run_blocks (SUC rest_fuel) ctx func mid = r` >>
  Cases_on `lookup_block mid.vs_current_bb func.fn_blocks`
  >- (qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
      simp[Once run_blocks_def] >> strip_tac >> gvs[fragExecTheory.exit_result_def] >>
      metis_tac[fragExecTheory.exit_result_not_error]) >>
  rename1 `lookup_block mid.vs_current_bb func.fn_blocks = SOME target` >>
  qspecl_then [`mid`, `target.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >~ [`eval_phis _ _ = Error _`]
  >- (qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
      simp[Once run_blocks_def] >> strip_tac >> gvs[fragExecTheory.exit_result_def] >>
      metis_tac[fragExecTheory.exit_result_not_error]) >>
  rename1 `eval_phis mid target.bb_instructions = OK phi` >>
  qabbrev_tac `entered = phi with vs_inst_idx := phi_prefix_length target.bb_instructions` >>
  `lookup_block entered.vs_current_bb func.fn_blocks = SOME target` by
    (simp[Abbr`entered`] >> drule eval_phis_preserves_current_bb >> simp[]) >>
  `frame_run rest_fuel ctx func entered = r` by
    (qspecl_then [`rest_fuel`, `ctx`, `func`, `mid`, `target`, `phi`]
       mp_tac run_blocks_block_run >> simp[frame_run_def, Abbr`entered`]) >>
  Cases_on `get_instruction target entered.vs_inst_idx`
  >- (qpat_x_assum `frame_run rest_fuel _ _ _ = _` mp_tac >>
      simp[frame_run_def, block_run_def, Once exec_block_def] >> strip_tac >>
      gvs[fragExecTheory.exit_result_def] >>
      metis_tac[fragExecTheory.exit_result_not_error]) >>
  rename1 `get_instruction target entered.vs_inst_idx = SOME head_inst` >>
  `active_inst func head_inst entered` by (irule lookup_instruction_active >> simp[]) >>
  `enters_block func mid entered` by
    (rewrite_tac[enters_block_def] >> qexistsl_tac [`target`, `phi`] >> simp[Abbr`entered`]) >>
  suspend "block_continue"
QED

Resume lower_budget_checked_terminal[block_continue]:
  qabbrev_tac `next_point = p with <| bp_state := entered;
    bp_prov := entry_prov func mid p.bp_prov;
    bp_taint := entry_taint_vars func mid p.bp_taint |>` >>
  qabbrev_tac `step_marks = MAP (\key. key IN explicit)
    (gas_events_step (SUC rest_fuel) ctx func.fn_name current s)` >>
  qabbrev_tac `history1 = h ++ [BudgetStep (LENGTH h) p current
    (SUC rest_fuel) (OK mid) next_point]` >>
  `lower_budget_path T (D,lo,explicit,ctx) root history1 (marks ++ step_marks) next_point` by
    (gvs[Abbr`history1`, Abbr`step_marks`] >> irule lower_budget_path_block >>
     simp[Abbr`next_point`] >> metis_tac[in_revert_forward_def]) >>
  `ptr_safe_blocks D lo (SUC rest_fuel) ctx func p.bp_params
    (entry_prov func mid p.bp_prov) (entry_taint_vars func mid p.bp_taint) mid` by
    (qspecl_then [`D`, `lo`, `SUC rest_fuel`, `ctx`, `func`, `p.bp_params`,
       `p.bp_prov`, `p.bp_taint`, `bb`, `s`, `current`, `mid`]
       mp_tac ptr_safe_block_terminator >> simp[]) >>
  `ptr_safe_run D lo rest_fuel ctx func next_point.bp_params
    next_point.bp_prov next_point.bp_taint entered` by
    (qpat_x_assum `ptr_safe_blocks _ _ _ _ _ _ _ _ mid` mp_tac >>
     simp[Once ptr_safe_blocks_def, ptr_safe_run_def, Abbr`next_point`, Abbr`entered`]) >>
  `mem_safe_blocks (SUC rest_fuel) ctx func mid` by
    (qspecl_then [`SUC rest_fuel`, `ctx`, `func`, `s`, `bb`, `current`, `mid`]
       mp_tac mem_safe_run_terminator >> simp[]) >>
  `mem_safe_run rest_fuel ctx func entered` by
    (qpat_x_assum `mem_safe_blocks _ _ _ mid` mp_tac >>
     simp[Once mem_safe_blocks_def, mem_safe_run_def, Abbr`entered`]) >>
  qpat_x_assum `!smaller. smaller < SUC rest_fuel ==> _`
    (qspec_then `rest_fuel` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`ctx`, `func`, `target`, `entered`] mp_tac) >>
  simp[] >> disch_then (qspecl_then
    [`D`, `lo`, `explicit`, `root`, `history1`, `marks ++ step_marks`, `next_point`] mp_tac) >>
  simp[Abbr`next_point`] >> suspend "block_finish"
QED

Resume lower_budget_checked_terminal[block_finish]:
  `gas_events_blocks (SUC rest_fuel) ctx func mid =
    gas_events_block rest_fuel ctx func.fn_name target entered ++
    case exec_block rest_fuel ctx target entered of
      OK t => if t.vs_halted then [] else gas_events_blocks rest_fuel ctx func t
    | _ => []` by simp[Once gas_events_blocks_def, Abbr`entered`] >>
  `gas_events_block (SUC rest_fuel) ctx func.fn_name bb s =
    gas_events_step (SUC rest_fuel) ctx func.fn_name current s` by
    simp[Once gas_events_block_def] >>
  strip_tac >>
  rename1 `_ = suffix ++ MAP _
    (gas_events_step last_fuel ctx endpoint.bp_fn.fn_name last_inst endpoint.bp_state)` >>
  rename1 `lower_budget_path T (D,lo,explicit,ctx) root final_history _ endpoint` >>
  qexistsl_tac [`final_history`, `step_marks ++ suffix`, `endpoint`, `last_inst`, `last_fuel`] >>
  simp[Abbr`step_marks`, Abbr`entered`, APPEND_ASSOC]
QED

Resume lower_budget_checked_terminal[within]:
  strip_tac >>
  `mid.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  qabbrev_tac `next_state = mid with vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_block next_state.vs_current_bb func.fn_blocks = SOME bb` by simp[Abbr`next_state`] >>
  `frame_run fuel ctx func next_state = r` by
    simp[frame_run_def, block_run_def, Abbr`next_state`] >>
  Cases_on `get_instruction bb next_state.vs_inst_idx`
  >- (qpat_x_assum `frame_run _ _ _ _ = _` mp_tac >>
      simp[frame_run_def, block_run_def, Once exec_block_def] >> strip_tac >>
      gvs[fragExecTheory.exit_result_def] >> metis_tac[fragExecTheory.exit_result_not_error]) >>
  rename1 `get_instruction bb next_state.vs_inst_idx = SOME following` >>
  `active_inst func following next_state` by (irule lookup_instruction_active >> simp[]) >>
  qabbrev_tac `next_point = p with <| bp_state := next_state;
    bp_prov := FST (ghost_step fuel ctx p.bp_params p.bp_prov p.bp_taint current s);
    bp_taint := SND (ghost_step fuel ctx p.bp_params p.bp_prov p.bp_taint current s) |>` >>
  qabbrev_tac `step_marks = MAP (\key. key IN explicit)
    (gas_events_step fuel ctx func.fn_name current s)` >>
  `?history1. lower_budget_path T (D,lo,explicit,ctx) root history1
    (marks ++ step_marks) next_point` by
    (Cases_on `current.inst_opcode = INVOKE`
     >- suspend "within_invoke" >> suspend "within_step") >>
  suspend "within_continue"
QED

Resume lower_budget_checked_terminal[within_invoke]:
  `mem_safe_step fuel ctx current s` by
    (Cases_on `revert_forward_at bb s.vs_inst_idx` >> fs[] >>
     drule_all revert_forward_at_opcode >> simp[]) >>
  qspecl_then [`D`, `lo`, `explicit`, `ctx`, `root`, `h`, `marks`, `p`,
    `func`, `bb`, `s`, `fuel`, `current`, `mid`, `following`]
    mp_tac lower_budget_checked_invoke >>
  simp[Abbr`next_point`, Abbr`next_state`, Abbr`step_marks`]
QED

Resume lower_budget_checked_terminal[within_step]:
  qspecl_then [`fuel`, `ctx`, `p.bp_params`, `p.bp_prov`, `p.bp_taint`,
    `current`, `s`, `mid`] assume_tac ghost_step_non_invoke >>
  gvs[Abbr`step_marks`] >>
  qexists_tac `h ++ [BudgetStep (LENGTH h) p current fuel (OK mid) next_point]` >>
  irule lower_budget_path_next >> simp[Abbr`next_point`, Abbr`next_state`] >>
  metis_tac[in_revert_forward_def]
QED

Resume lower_budget_checked_terminal[within_continue]:
  `ptr_safe_run D lo fuel ctx func next_point.bp_params
    next_point.bp_prov next_point.bp_taint next_state` by
    (qspecl_then [`D`, `lo`, `fuel`, `ctx`, `func`, `p.bp_params`,
       `p.bp_prov`, `p.bp_taint`, `bb`, `s`, `current`, `mid`]
       mp_tac ptr_safe_block_step >>
     simp[ptr_safe_run_def, Abbr`next_point`, Abbr`next_state`]) >>
  `mem_safe_run fuel ctx func next_state` by
    (qspecl_then [`fuel`, `ctx`, `func`, `s`, `bb`, `current`, `mid`]
       mp_tac mem_safe_run_step >> simp[Abbr`next_state`]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by fs[get_instruction_def] >>
  qpat_x_assum `_ = s.vs_inst_idx` SUBST_ALL_TAC >>
  qpat_x_assum `!y. LENGTH bb.bb_instructions - y < _ ==> _`
    (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then (qspec_then `next_state` mp_tac) >> simp[Abbr`next_state`] >>
  disch_then (qspecl_then [`D`, `lo`, `explicit`, `root`, `history1`,
    `marks ++ step_marks`, `next_point`] mp_tac) >>
  simp[Abbr`next_point`] >> suspend "within_finish"
QED

Resume lower_budget_checked_terminal[within_finish]:
  `gas_events_block fuel ctx func.fn_name bb s =
    gas_events_step fuel ctx func.fn_name current s ++
    gas_events_block fuel ctx func.fn_name bb
      (mid with vs_inst_idx := SUC s.vs_inst_idx)` by simp[Once gas_events_block_def] >>
  `exec_block fuel ctx bb s =
    exec_block fuel ctx bb (mid with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Once exec_block_def] >>
  strip_tac >>
  rename1 `_ = suffix ++ MAP _
    (gas_events_step last_fuel ctx endpoint.bp_fn.fn_name last_inst endpoint.bp_state)` >>
  rename1 `lower_budget_path T (D,lo,explicit,ctx) root final_history _ endpoint` >>
  qexistsl_tac [`final_history`, `step_marks ++ suffix`, `endpoint`, `last_inst`, `last_fuel`] >>
  simp[Abbr`step_marks`, APPEND_ASSOC]
QED

Finalise lower_budget_checked_terminal
