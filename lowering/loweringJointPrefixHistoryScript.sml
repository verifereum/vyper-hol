(* Checked joint prefixes retain their actual instruction history and ghosts. *)
Theory loweringJointPrefixHistory
Ancestors
  loweringCallBudgetHistory fragGasOriginPtr fragGasFocus fragExec
  typedCopyArrayPtr
  entryReachBodyFmp vyperLoweringCorrect vyperCompiler
  ptrSafeRun ptrDiscipline memSafeRun gasEvents
  contextCodegenRel contextCodegenRelProps venomExecSemantics venomExecProofs
  venomInstProofs venomInst venomState finite_map list arithmetic

Theorem gas_origin_ptr_path_start:
  !D lo explicit ctx func PG s G tn marks finish G' tn' inst.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) marks (OK finish,G',tn') /\
    active_inst func inst finish ==>
    ~s.vs_halted /\ ?first_inst. active_inst func first_inst s
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_origin_ptr_path _ _ _ _` mp_tac >>
  simp[Once gas_origin_ptr_path_cases] >> rw[] >>
  gvs[exit_result_def]
  >- metis_tac[] >>
  drule gas_origin_ptr_edge_common_fuel >> strip_tac >>
  metis_tac[lookup_instruction_active]
QED

Theorem gas_events_blocks_frame_return:
  !fuel ctx func s bb phi returned final_state.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK phi /\
    run_blocks (SUC fuel) ctx func s = IntRet returned final_state ==>
    gas_events_blocks (SUC fuel) ctx func s =
      gas_events_block fuel ctx func.fn_name bb
        (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) ++
      case exec_block fuel ctx bb
        (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) of
        OK t => gas_events_blocks fuel ctx func t
      | _ => []
Proof
  rpt gen_tac >> strip_tac >> simp[Once gas_events_blocks_def] >>
  Cases_on `exec_block fuel ctx bb
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  gvs[Once run_blocks_def] >>
  rename1 `exec_block _ _ _ _ = OK block_end` >>
  Cases_on `block_end.vs_halted` >> gvs[]
QED

(* A completed callee is expanded before restoring the suspended caller. *)
Theorem step_inst_invoke_return:
  !fuel ctx inst s t.
    inst.inst_opcode = INVOKE /\ step_inst fuel ctx inst s = OK t ==>
    ?name ops callee args cs returned final_state.
      decode_invoke inst = SOME (name,ops) /\
      lookup_function name ctx.ctx_functions = SOME callee /\
      eval_operands ops s = SOME args /\
      setup_callee callee args s = SOME cs /\
      run_blocks fuel ctx callee cs = IntRet returned final_state /\
      bind_outputs inst.inst_outputs returned.iret_values
        (adopt_return_fmp returned (merge_callee_state s final_state)) = SOME t
Proof
  rpt gen_tac >> simp[Once step_inst_def] >> strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

(* A successful atomic INVOKE exposes its actual checked callee entry. *)
Theorem lower_budget_checked_call:
  !D lo explicit ctx root h marks p func bb s fuel inst mid.
    lower_budget_path T (D,lo,explicit,ctx) root h marks p /\
    p.bp_fn = func /\ p.bp_state = s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    active_inst func inst s /\ inst.inst_opcode = INVOKE /\
    step_inst fuel ctx inst s = OK mid /\
    mem_safe_step fuel ctx inst s /\
    ptr_safe_step D lo fuel ctx func p.bp_params p.bp_prov p.bp_taint inst s ==>
    ?child_fuel callee entry_bb entered inner_ret inner_end
      saved callee_point call_history.
      fuel = SUC child_fuel /\
      lookup_block entered.vs_current_bb callee.fn_blocks = SOME entry_bb /\
      frame_run child_fuel ctx callee entered = IntRet inner_ret inner_end /\
      saved = <| cf_fn := p.bp_fn; cf_inst := inst; cf_state := p.bp_state;
        cf_params := p.bp_params; cf_prov := p.bp_prov;
        cf_tvar := p.bp_taint.t_var |> /\
      lower_budget_path T (D,lo,explicit,ctx) root call_history marks callee_point /\
      callee_point.bp_fn = callee /\ callee_point.bp_state = entered /\
      callee_point.bp_stack = saved::p.bp_stack /\
      ptr_safe_run D lo child_fuel ctx callee callee_point.bp_params
        callee_point.bp_prov callee_point.bp_taint entered /\
      mem_safe_run child_fuel ctx callee entered /\
      bind_outputs inst.inst_outputs inner_ret.iret_values
        (adopt_return_fmp inner_ret (merge_callee_state s inner_end)) = SOME mid /\
      ghost_step fuel ctx p.bp_params p.bp_prov p.bp_taint inst s =
        (DRESTRICT p.bp_prov (COMPL (set inst.inst_outputs)),
         SND (ghost_run child_fuel ctx callee callee_point.bp_params
           callee_point.bp_prov callee_point.bp_taint entered) with t_var :=
           DRESTRICT p.bp_taint.t_var (COMPL (set inst.inst_outputs))) /\
      gas_events_step fuel ctx func.fn_name inst s =
        gas_events_block child_fuel ctx callee.fn_name entry_bb entered ++
        case exec_block child_fuel ctx entry_bb entered of
          OK t => gas_events_blocks child_fuel ctx callee t
        | _ => []
Proof
  rpt gen_tac >> strip_tac >>
  drule_all step_inst_invoke_return >> strip_tac >>
  rename1 `decode_invoke inst = SOME (name,ops)` >>
  rename1 `lookup_function name ctx.ctx_functions = SOME callee` >>
  rename1 `eval_operands ops s = SOME args` >>
  rename1 `setup_callee callee args s = SOME cs` >>
  rename1 `run_blocks fuel ctx callee cs = IntRet inner_ret inner_end` >>
  Cases_on `fuel`
  >- (qpat_x_assum `run_blocks 0 _ _ _ = _` mp_tac >>
      simp[Once run_blocks_def]) >>
  rename1 `run_blocks (SUC child_fuel) ctx callee cs = IntRet inner_ret inner_end` >>
  Cases_on `lookup_block cs.vs_current_bb callee.fn_blocks`
  >- (qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
      simp[Once run_blocks_def]) >>
  rename1 `lookup_block cs.vs_current_bb callee.fn_blocks = SOME entry_bb` >>
  qspecl_then [`cs`, `entry_bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >~ [`eval_phis _ _ = Error _`]
  >- (qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
      simp[Once run_blocks_def]) >>
  rename1 `eval_phis cs entry_bb.bb_instructions = OK phi` >>
  qabbrev_tac `entered = phi with vs_inst_idx :=
    phi_prefix_length entry_bb.bb_instructions` >>
  `enters_block callee cs entered` by
    (rewrite_tac[enters_block_def] >>
     qexistsl_tac [`entry_bb`, `phi`] >> simp[Abbr`entered`]) >>
  `lookup_block entered.vs_current_bb callee.fn_blocks = SOME entry_bb` by
    (simp[Abbr`entered`] >>
     drule eval_phis_preserves_current_bb >> simp[]) >>
  `frame_run child_fuel ctx callee entered = IntRet inner_ret inner_end` by
    (qspecl_then [`ctx`, `callee`, `p.bp_params`, `FEMPTY`, `p.bp_taint`,
       `cs`, `entered`, `child_fuel`] mp_tac frame_run_enters_block >> simp[]) >>
  Cases_on `get_instruction entry_bb entered.vs_inst_idx`
  >- (qpat_x_assum `frame_run child_fuel _ _ _ = _` mp_tac >>
      simp[frame_run_def, block_run_def, Once exec_block_def]) >>
  rename1 `get_instruction entry_bb entered.vs_inst_idx = SOME head_inst` >>
  `active_inst callee head_inst entered` by
    (irule lookup_instruction_active >> simp[]) >>
  qabbrev_tac `saved = <| cf_fn := p.bp_fn; cf_inst := inst;
    cf_state := p.bp_state; cf_params := p.bp_params;
    cf_prov := p.bp_prov; cf_tvar := p.bp_taint.t_var |>` >>
  qabbrev_tac `callee_point = <| bp_stack := saved::p.bp_stack;
    bp_params := MAP (op_prov p.bp_prov) ops;
    bp_prov := FEMPTY; bp_taint := p.bp_taint with t_var := FEMPTY;
    bp_fn := callee; bp_state := entered |>` >>
  qabbrev_tac `call_history = h ++
    [BudgetCall (LENGTH h) p inst callee cs callee_point]` >>
  `lower_budget_path T (D,lo,explicit,ctx) root call_history marks callee_point` by
    (gvs[Abbr`call_history`] >> irule lower_budget_path_call >>
     simp[Abbr`callee_point`, Abbr`saved`] >>
     metis_tac[ptr_safe_step_inst_ok, ptr_inst_ok_fuel]) >>
  `ptr_safe_blocks D lo (SUC child_fuel) ctx callee
    (MAP (op_prov p.bp_prov) ops) FEMPTY (p.bp_taint with t_var := FEMPTY) cs` by
    (qspecl_then [`D`, `lo`, `SUC child_fuel`, `ctx`, `func`, `p.bp_params`,
       `p.bp_prov`, `p.bp_taint`, `inst`, `s`, `name`, `ops`, `callee`,
       `args`, `cs`] mp_tac ptr_safe_step_invoke >> simp[]) >>
  `ptr_safe_run D lo child_fuel ctx callee callee_point.bp_params
    callee_point.bp_prov callee_point.bp_taint entered` by
    (qpat_x_assum `ptr_safe_blocks _ _ _ _ callee _ _ _ cs` mp_tac >>
     simp[Once ptr_safe_blocks_def, ptr_safe_run_def,
          Abbr`callee_point`, Abbr`entered`]) >>
  `mem_safe_blocks (SUC child_fuel) ctx callee cs` by
    (qspecl_then [`SUC child_fuel`, `ctx`, `inst`, `s`, `name`, `ops`,
       `callee`, `args`, `cs`] mp_tac mem_safe_step_invoke >> simp[]) >>
  `mem_safe_run child_fuel ctx callee entered` by
    (qpat_x_assum `mem_safe_blocks _ _ callee cs` mp_tac >>
     simp[Once mem_safe_blocks_def, mem_safe_run_def, Abbr`entered`]) >>
  qspecl_then [`ctx`, `callee`, `MAP (op_prov p.bp_prov) ops`, `FEMPTY`,
    `p.bp_taint with t_var := FEMPTY`, `cs`, `entered`, `child_fuel`]
    assume_tac frame_run_enters_block >>
  qspecl_then [`SUC child_fuel`, `ctx`, `p.bp_params`, `p.bp_prov`,
    `p.bp_taint`, `inst`, `s`, `name`, `ops`, `callee`, `args`, `cs`]
    assume_tac ghost_step_invoke >>
  qspecl_then [`child_fuel`, `ctx`, `callee`, `cs`, `entry_bb`, `phi`,
    `inner_ret`, `inner_end`] assume_tac gas_events_blocks_frame_return >>
  qexistsl_tac [`child_fuel`, `callee`, `entry_bb`, `entered`,
    `inner_ret`, `inner_end`, `saved`, `callee_point`, `call_history`] >>
  simp[Abbr`saved`, Abbr`callee_point`, Abbr`entered`, gas_events_step_def]
QED

Theorem lower_budget_checked_return:
  !fuel ctx func bb s ret finish.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    frame_run fuel ctx func s = IntRet ret finish ==>
    !D lo explicit root h marks p frame stack bound next_inst.
      lower_budget_path T (D,lo,explicit,ctx) root h marks p /\
      p.bp_fn = func /\ p.bp_state = s /\
      p.bp_stack = frame::stack /\
      ptr_safe_run D lo fuel ctx func p.bp_params p.bp_prov p.bp_taint s /\
      mem_safe_run fuel ctx func s /\
      bind_outputs frame.cf_inst.inst_outputs ret.iret_values
        (adopt_return_fmp ret (merge_callee_state frame.cf_state finish)) =
          SOME bound /\
      active_inst frame.cf_fn next_inst
        (bound with vs_inst_idx := SUC frame.cf_state.vs_inst_idx) ==>
      ?history.
        lower_budget_path T (D,lo,explicit,ctx) root history
          (marks ++ MAP (\key. key IN explicit)
            (gas_events_block fuel ctx func.fn_name bb s ++
              case exec_block fuel ctx bb s of
                OK t => gas_events_blocks fuel ctx func t
              | _ => []))
          <| bp_stack := stack; bp_params := frame.cf_params;
             bp_prov := DRESTRICT frame.cf_prov
               (COMPL (set frame.cf_inst.inst_outputs));
             bp_taint := (SND (ghost_run fuel ctx func p.bp_params
               p.bp_prov p.bp_taint s) with t_var :=
                 DRESTRICT frame.cf_tvar
                   (COMPL (set frame.cf_inst.inst_outputs)));
             bp_fn := frame.cf_fn;
             bp_state := (bound with vs_inst_idx :=
               SUC frame.cf_state.vs_inst_idx) |>
Proof
  completeInduct_on `fuel` >> rpt gen_tac >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  rename1 `frame_run fuel ctx func s = IntRet result_ret result_state` >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `frame_run _ _ _ _ = _` mp_tac >>
      simp[frame_run_def, block_run_def, Once exec_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `active_inst func inst s` by
    (irule lookup_instruction_active >> simp[]) >>
  `ptr_safe_block D lo fuel ctx func p.bp_params p.bp_prov
     p.bp_taint bb s` by
    (qpat_x_assum `ptr_safe_run _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_safe_run_def]) >>
  `ptr_safe_step D lo fuel ctx func p.bp_params p.bp_prov
     p.bp_taint inst s` by metis_tac[ptr_safe_block_head] >>
  qspecl_then [`fuel`, `ctx`, `func`, `s`, `bb`, `inst`]
    mp_tac mem_safe_run_head >> simp[] >> disch_tac >>
  qpat_x_assum `frame_run _ _ _ _ = _` mp_tac >>
  simp[frame_run_def, block_run_def] >>
  once_rewrite_tac[exec_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[]
  >~ [`step_inst _ _ _ _ = IntRet _ _`]
  >- (strip_tac >> gvs[] >>
      rename1 `step_inst fuel ctx inst p.bp_state = IntRet returned final_state` >>
      qspecl_then [`fuel`, `ctx`, `p.bp_fn`, `p.bp_params`, `p.bp_prov`,
        `p.bp_taint`, `bb`, `p.bp_state`, `inst`, `returned`, `final_state`]
        assume_tac ghost_block_intret >>
      simp[Once gas_events_block_def, ghost_run_def] >>
      qmatch_goalsub_abbrev_tac `lower_budget_path _ _ _ _ _ restored` >>
      qexists_tac `h ++ [BudgetReturn (LENGTH h) p inst fuel returned
        final_state bound restored]` >>
      irule lower_budget_path_ret >> simp[Abbr`restored`] >>
      metis_tac[in_revert_forward_def]) >>
  rename1 `step_inst fuel ctx inst s = OK mid` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
  >- suspend "term" >> suspend "within"
QED

Resume lower_budget_checked_return[term]:
  Cases_on `mid.vs_halted` >> simp[] >> strip_tac >>
  Cases_on `fuel`
  >- (qpat_x_assum `run_blocks 0 _ _ _ = _` mp_tac >>
      simp[Once run_blocks_def]) >>
  rename1 `run_blocks (SUC rest_fuel) ctx func mid =
    IntRet returned final_state` >>
  Cases_on `lookup_block mid.vs_current_bb func.fn_blocks`
  >- (qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
      simp[Once run_blocks_def]) >>
  rename1 `lookup_block mid.vs_current_bb func.fn_blocks = SOME target` >>
  qspecl_then [`mid`, `target.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >~ [`eval_phis _ _ = Error _`]
  >- (qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
      simp[Once run_blocks_def]) >>
  rename1 `eval_phis mid target.bb_instructions = OK phi` >>
  qabbrev_tac `entered = phi with vs_inst_idx :=
    phi_prefix_length target.bb_instructions` >>
  `lookup_block entered.vs_current_bb func.fn_blocks = SOME target` by
    (simp[Abbr`entered`] >>
     drule eval_phis_preserves_current_bb >> simp[]) >>
  `frame_run rest_fuel ctx func entered = IntRet returned final_state` by
    (qspecl_then [`rest_fuel`, `ctx`, `func`, `mid`, `target`, `phi`]
       mp_tac run_blocks_block_run >>
     simp[frame_run_def, Abbr`entered`]) >>
  Cases_on `get_instruction target entered.vs_inst_idx`
  >- (qpat_x_assum `frame_run rest_fuel _ _ _ = _` mp_tac >>
      simp[frame_run_def, block_run_def, Once exec_block_def]) >>
  rename1 `get_instruction target entered.vs_inst_idx = SOME head_inst` >>
  `active_inst func head_inst entered` by
    (irule lookup_instruction_active >> simp[]) >>
  `enters_block func mid entered` by
    (rewrite_tac[enters_block_def] >>
     qexistsl_tac [`target`, `phi`] >> simp[Abbr`entered`]) >>
  suspend "block_return"
QED

Resume lower_budget_checked_return[block_return]:
  qabbrev_tac `next_point = p with <|
    bp_state := entered;
    bp_prov := entry_prov func mid p.bp_prov;
    bp_taint := entry_taint_vars func mid p.bp_taint |>` >>
  qabbrev_tac `step_marks = MAP (\key. key IN explicit)
    (gas_events_step (SUC rest_fuel) ctx func.fn_name inst s)` >>
  qabbrev_tac `history1 = h ++ [BudgetStep (LENGTH h) p inst
    (SUC rest_fuel) (OK mid) next_point]` >>
  `lower_budget_path T (D,lo,explicit,ctx) root history1
     (marks ++ step_marks) next_point` by
    (gvs[Abbr`history1`, Abbr`step_marks`] >>
     irule lower_budget_path_block >> simp[Abbr`next_point`] >>
     metis_tac[in_revert_forward_def]) >>
  `ptr_safe_blocks D lo (SUC rest_fuel) ctx func p.bp_params
     (entry_prov func mid p.bp_prov)
     (entry_taint_vars func mid p.bp_taint) mid` by
    (qspecl_then [`D`, `lo`, `SUC rest_fuel`, `ctx`, `func`,
       `p.bp_params`, `p.bp_prov`, `p.bp_taint`, `bb`, `s`, `inst`, `mid`]
       mp_tac ptr_safe_block_terminator >> simp[]) >>
  `ptr_safe_run D lo rest_fuel ctx func next_point.bp_params
     next_point.bp_prov next_point.bp_taint entered` by
    (qpat_x_assum `ptr_safe_blocks _ _ _ _ _ _ _ _ mid` mp_tac >>
     simp[Once ptr_safe_blocks_def, ptr_safe_run_def,
          Abbr`next_point`, Abbr`entered`]) >>
  `mem_safe_blocks (SUC rest_fuel) ctx func mid` by
    (qspecl_then [`SUC rest_fuel`, `ctx`, `func`, `s`, `bb`, `inst`, `mid`]
       mp_tac mem_safe_run_terminator >> simp[]) >>
  `mem_safe_run rest_fuel ctx func entered` by
    (qpat_x_assum `mem_safe_blocks _ _ _ mid` mp_tac >>
     simp[Once mem_safe_blocks_def, mem_safe_run_def, Abbr`entered`]) >>
  rename1 `active_inst frame.cf_fn caller_next
    (bound with vs_inst_idx := SUC frame.cf_state.vs_inst_idx)` >>
  qpat_x_assum `!smaller. smaller < SUC rest_fuel ==> _`
    (qspec_then `rest_fuel` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`ctx`, `func`, `target`, `entered`, `returned`, `final_state`] mp_tac) >>
  simp[] >> disch_then (qspecl_then
    [`D`, `lo`, `explicit`, `root`, `history1`, `marks ++ step_marks`,
     `next_point`, `frame`, `stack`, `bound`, `caller_next`] mp_tac) >>
  simp[Abbr`next_point`] >> suspend "block_return_finish"
QED

Resume lower_budget_checked_return[block_return_finish]:
  qspecl_then [`rest_fuel`, `ctx`, `func`, `mid`, `target`, `phi`,
    `returned`, `final_state`] mp_tac gas_events_blocks_frame_return >>
  simp[] >> disch_tac >>
  `ghost_run (SUC rest_fuel) ctx func p.bp_params p.bp_prov p.bp_taint s =
   ghost_run rest_fuel ctx func p.bp_params (entry_prov func mid p.bp_prov)
     (entry_taint_vars func mid p.bp_taint) entered` by
    (qspecl_then [`SUC rest_fuel`, `ctx`, `func`, `p.bp_params`,
       `p.bp_prov`, `p.bp_taint`, `bb`, `s`, `inst`, `mid`]
       assume_tac ghost_block_terminator >>
     qspecl_then [`rest_fuel`, `ctx`, `func`, `p.bp_params`,
       `entry_prov func mid p.bp_prov`, `entry_taint_vars func mid p.bp_taint`,
       `mid`, `target`, `phi`] assume_tac ghost_blocks_block >>
     simp[ghost_run_def, Abbr`entered`]) >>
  `gas_events_block (SUC rest_fuel) ctx func.fn_name bb s =
   gas_events_step (SUC rest_fuel) ctx func.fn_name inst s` by
    simp[Once gas_events_block_def] >>
  simp[Abbr`step_marks`, Abbr`entered`, APPEND_ASSOC]
QED

Resume lower_budget_checked_return[within]:
  strip_tac >>
  `mid.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  qabbrev_tac `next_state = mid with vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_block next_state.vs_current_bb func.fn_blocks = SOME bb` by
    simp[Abbr`next_state`] >>
  `frame_run fuel ctx func next_state = IntRet result_ret result_state` by
    simp[frame_run_def, block_run_def, Abbr`next_state`] >>
  Cases_on `get_instruction bb next_state.vs_inst_idx`
  >- (qpat_x_assum `frame_run _ _ _ _ = _` mp_tac >>
      simp[frame_run_def, block_run_def, Once exec_block_def]) >>
  rename1 `get_instruction bb next_state.vs_inst_idx = SOME following` >>
  `active_inst func following next_state` by
    (irule lookup_instruction_active >> simp[]) >>
  qabbrev_tac `next_point = p with <|
    bp_state := next_state;
    bp_prov := FST (ghost_step fuel ctx p.bp_params p.bp_prov p.bp_taint inst s);
    bp_taint := SND (ghost_step fuel ctx p.bp_params p.bp_prov p.bp_taint inst s) |>` >>
  qabbrev_tac `step_marks = MAP (\key. key IN explicit)
    (gas_events_step fuel ctx func.fn_name inst s)` >>
  `?history1. lower_budget_path T (D,lo,explicit,ctx) root history1
     (marks ++ step_marks) next_point` by
    (Cases_on `inst.inst_opcode = INVOKE`
     >- suspend "within_invoke" >> suspend "within_step") >>
  suspend "within_continue"
QED

Resume lower_budget_checked_return[within_step]:
  qspecl_then [`fuel`, `ctx`, `p.bp_params`, `p.bp_prov`, `p.bp_taint`,
    `inst`, `s`, `mid`] assume_tac ghost_step_non_invoke >>
  gvs[Abbr`step_marks`] >>
  qexists_tac `h ++ [BudgetStep (LENGTH h) p inst fuel (OK mid) next_point]` >>
  irule lower_budget_path_next >>
  simp[Abbr`next_point`, Abbr`next_state`] >>
  metis_tac[in_revert_forward_def]
QED

Resume lower_budget_checked_return[within_continue]:
  `ptr_safe_run D lo fuel ctx func next_point.bp_params
    next_point.bp_prov next_point.bp_taint next_state` by
    (qspecl_then [`D`, `lo`, `fuel`, `ctx`, `func`, `p.bp_params`,
       `p.bp_prov`, `p.bp_taint`, `bb`, `s`, `inst`, `mid`]
       mp_tac ptr_safe_block_step >>
     simp[ptr_safe_run_def, Abbr`next_point`, Abbr`next_state`]) >>
  `mem_safe_run fuel ctx func next_state` by
    (qspecl_then [`fuel`, `ctx`, `func`, `s`, `bb`, `inst`, `mid`]
       mp_tac mem_safe_run_step >> simp[Abbr`next_state`]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    fs[get_instruction_def] >>
  qpat_x_assum `_ = s.vs_inst_idx` SUBST_ALL_TAC >>
  qpat_x_assum `!y. LENGTH bb.bb_instructions - y < _ ==> _`
    (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then (qspec_then `next_state` mp_tac) >>
  simp[Abbr`next_state`] >>
  rename1 `active_inst frame.cf_fn caller_next
    (bound with vs_inst_idx := SUC frame.cf_state.vs_inst_idx)` >>
  disch_then (qspecl_then
    [`D`, `lo`, `explicit`, `root`, `history1`, `marks ++ step_marks`,
     `next_point`, `frame`, `stack`, `bound`, `caller_next`] mp_tac) >>
  simp[Abbr`next_point`] >> suspend "within_finish"
QED

Resume lower_budget_checked_return[within_finish]:
  `ghost_run fuel ctx func p.bp_params p.bp_prov p.bp_taint s =
   ghost_run fuel ctx func p.bp_params
     (FST (ghost_step fuel ctx p.bp_params p.bp_prov p.bp_taint inst s))
     (SND (ghost_step fuel ctx p.bp_params p.bp_prov p.bp_taint inst s))
     (mid with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qspecl_then [`fuel`, `ctx`, `func`, `p.bp_params`, `p.bp_prov`,
       `p.bp_taint`, `bb`, `s`, `inst`, `mid`] assume_tac ghost_block_step >>
     simp[ghost_run_def]) >>
  `gas_events_block fuel ctx func.fn_name bb s =
   gas_events_step fuel ctx func.fn_name inst s ++
   gas_events_block fuel ctx func.fn_name bb
     (mid with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Once gas_events_block_def] >>
  simp[Abbr`step_marks`, APPEND_ASSOC]
QED

Resume lower_budget_checked_return[within_invoke]:
  `mem_safe_step fuel ctx inst s` by
    (Cases_on `revert_forward_at bb s.vs_inst_idx` >> fs[] >>
     drule_all revert_forward_at_opcode >> simp[]) >>
  drule_all lower_budget_checked_call >> strip_tac >>
  rename1 `frame_run child_fuel ctx callee entered = IntRet inner_ret inner_end` >>
  rename1 `lookup_block entered.vs_current_bb callee.fn_blocks = SOME entry_bb` >>
  rename1 `lower_budget_path T (D,lo,explicit,ctx) root call_history marks callee_point` >>
  rename1 `callee_point.bp_stack = saved::p.bp_stack` >>
  qpat_x_assum `!smaller. smaller < fuel ==> _`
    (qspec_then `child_fuel` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`ctx`, `callee`, `entry_bb`, `entered`,
    `inner_ret`, `inner_end`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`D`, `lo`, `explicit`, `root`, `call_history`, `marks`,
    `callee_point`, `saved`, `p.bp_stack`, `mid`, `following`] mp_tac) >>
  simp[Abbr`next_point`, Abbr`step_marks`, Abbr`next_state`] >>
  qmatch_goalsub_abbrev_tac
    `(?history. lower_budget_path _ _ _ history _ before) ==> _` >>
  qmatch_goalsub_abbrev_tac
    `_ ==> ?history. lower_budget_path _ _ _ history _ after` >>
  `before = after` by
    simp[Abbr`before`, Abbr`after`, lower_budget_point_component_equality] >>
  simp[]
QED

Finalise lower_budget_checked_return

Theorem lower_budget_checked_invoke:
  !D lo explicit ctx root h marks p func bb s fuel inst mid following.
    lower_budget_path T (D,lo,explicit,ctx) root h marks p /\
    p.bp_fn = func /\ p.bp_state = s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    active_inst func inst s /\ inst.inst_opcode = INVOKE /\
    step_inst fuel ctx inst s = OK mid /\
    mem_safe_step fuel ctx inst s /\
    ptr_safe_step D lo fuel ctx func p.bp_params p.bp_prov p.bp_taint inst s /\
    active_inst func following (mid with vs_inst_idx := SUC s.vs_inst_idx) ==>
    ?history.
      lower_budget_path T (D,lo,explicit,ctx) root history
        (marks ++ MAP (\key. key IN explicit)
          (gas_events_step fuel ctx func.fn_name inst s))
        (p with <| bp_state := mid with vs_inst_idx := SUC s.vs_inst_idx;
          bp_prov := FST (ghost_step fuel ctx p.bp_params p.bp_prov p.bp_taint inst s);
          bp_taint := SND (ghost_step fuel ctx p.bp_params p.bp_prov p.bp_taint inst s) |> )
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lower_budget_checked_call >> strip_tac >>
  rename1 `frame_run child_fuel ctx callee entered = IntRet inner_ret inner_end` >>
  rename1 `lookup_block entered.vs_current_bb callee.fn_blocks = SOME entry_bb` >>
  rename1 `lower_budget_path T (D,lo,explicit,ctx) root call_history marks callee_point` >>
  rename1 `callee_point.bp_stack = saved::p.bp_stack` >>
  qspecl_then [`child_fuel`, `ctx`, `callee`, `entry_bb`, `entered`,
    `inner_ret`, `inner_end`] mp_tac lower_budget_checked_return >> simp[] >>
  disch_then (qspecl_then [`D`, `lo`, `explicit`, `root`, `call_history`, `marks`,
    `callee_point`, `saved`, `p.bp_stack`, `mid`, `following`] mp_tac) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac
    `(?history. lower_budget_path _ _ _ history _ before) ==> _` >>
  qmatch_goalsub_abbrev_tac
    `_ ==> ?history. lower_budget_path _ _ _ history _ after` >>
  `before = after` by
    simp[Abbr`before`, Abbr`after`, lower_budget_point_component_equality] >>
  simp[]
QED

Theorem lower_budget_checked_edge:
  !D lo explicit ctx root h prefix p marks t G' tn' following.
    ALL_DISTINCT (fn_labels p.bp_fn) /\
    (!bb. MEM bb p.bp_fn.fn_blocks ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    gas_origin_ptr_edge (D,lo,explicit,ctx,p.bp_fn,p.bp_params)
      (p.bp_state,p.bp_prov,p.bp_taint) marks (OK t,G',tn') /\
    active_inst p.bp_fn following t /\
    lower_budget_path T (D,lo,explicit,ctx) root h prefix p ==>
    ?history.
      lower_budget_path T (D,lo,explicit,ctx) root history (prefix ++ marks)
        (p with <| bp_state := t; bp_prov := G'; bp_taint := tn' |> )
Proof
  rpt gen_tac >> strip_tac >>
  drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 ASSUME_TAC
    (qx_choose_then `fuel` (qx_choose_then `bb` (qx_choose_then `current`
      (qx_choose_then `middle` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))))) >>
  qpat_x_assum `_ \/ _ \/ _ \/ _ \/ _` mp_tac >> strip_tac >>
  gnvs[exit_result_def] >>
  rename1 `get_instruction bb p.bp_state.vs_inst_idx = SOME current` >>
  `active_inst p.bp_fn current p.bp_state` by
    (irule lookup_instruction_active >> simp[])
  >~ [`~is_terminator current.inst_opcode`] >- suspend "next"
  >~ [`eval_phis _ _ = OK _`] >- suspend "block"
  >~ [`exit_result _`] >- metis_tac[exit_result_def] >>
  suspend "jump"
QED

Resume lower_budget_checked_edge[next]:
  rename1 `step_inst fuel ctx current p.bp_state = OK mid` >>
  `FST (ghost_step fuel ctx p.bp_params p.bp_prov p.bp_taint current p.bp_state) = G' /\
   SND (ghost_step fuel ctx p.bp_params p.bp_prov p.bp_taint current p.bp_state) = tn'` by
    metis_tac[pairTheory.FST, pairTheory.SND] >>
  Cases_on `current.inst_opcode = INVOKE`
  >- (`mem_safe_step fuel ctx current p.bp_state` by
        (Cases_on `revert_forward_at bb p.bp_state.vs_inst_idx` >> fs[] >>
         drule_all revert_forward_at_opcode >> simp[]) >>
      qspecl_then [`D`, `lo`, `explicit`, `ctx`, `root`, `h`, `prefix`, `p`,
        `p.bp_fn`, `bb`, `p.bp_state`, `fuel`, `current`, `mid`, `following`]
        mp_tac lower_budget_checked_invoke >> simp[]) >>
  qspecl_then [`fuel`, `ctx`, `p.bp_params`, `p.bp_prov`, `p.bp_taint`,
    `current`, `p.bp_state`, `mid`] assume_tac ghost_step_non_invoke >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `lower_budget_path _ _ _ _ _ endpoint` >>
  qexists_tac `h ++ [BudgetStep (LENGTH h) p current fuel (OK mid) endpoint]` >>
  irule lower_budget_path_next >> simp[Abbr`endpoint`] >>
  metis_tac[in_revert_forward_def]
QED

Resume lower_budget_checked_edge[block]:
  rename1 `eval_phis mid target.bb_instructions = OK phi` >>
  rename1 `step_inst fuel ctx current p.bp_state = OK mid` >>
  `enters_block p.bp_fn mid
    (phi with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (rewrite_tac[enters_block_def] >> qexistsl_tac [`target`, `phi`] >> simp[]) >>
  qmatch_goalsub_abbrev_tac `lower_budget_path _ _ _ _ _ endpoint` >>
  qexists_tac `h ++ [BudgetStep (LENGTH h) p current fuel (OK mid) endpoint]` >>
  irule lower_budget_path_block >> simp[Abbr`endpoint`] >>
  metis_tac[in_revert_forward_def]
QED

Resume lower_budget_checked_edge[jump]:
  rename1 `step_inst fuel ctx current p.bp_state = OK (jump_to label p.bp_state)` >>
  qpat_assum `active_inst p.bp_fn following (jump_to label p.bp_state)`
    (strip_assume_tac o SRULE [active_inst_def, jump_to_def]) >>
  rename1 `MEM target p.bp_fn.fn_blocks` >>
  `lookup_block label p.bp_fn.fn_blocks = SOME target` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `phi_prefix_length target.bb_instructions = 0` by metis_tac[] >>
  `eval_phis (jump_to label p.bp_state) target.bb_instructions =
    OK (jump_to label p.bp_state)` by
    (qspecl_then [`jump_to label p.bp_state`, `target.bb_instructions`,
       `[]:instruction list`] mp_tac eval_phis_same_phi_prefix >>
     simp[phi_prefix_length_def, eval_phis_def]) >>
  `enters_block p.bp_fn (jump_to label p.bp_state) (jump_to label p.bp_state)` by
    (rewrite_tac[enters_block_def] >>
     qexistsl_tac [`target`, `jump_to label p.bp_state`] >> simp[jump_to_def]) >>
  `entry_prov p.bp_fn (jump_to label p.bp_state) p.bp_prov = p.bp_prov /\
   entry_taint_vars p.bp_fn (jump_to label p.bp_state) p.bp_taint = p.bp_taint` by
    (irule entry_ghost_no_phi >> qexists_tac `target` >> simp[jump_to_def]) >>
  qmatch_goalsub_abbrev_tac `lower_budget_path _ _ _ _ _ endpoint` >>
  qexists_tac `h ++ [BudgetStep (LENGTH h) p current fuel
    (OK (jump_to label p.bp_state)) endpoint]` >>
  `~(jump_to label p.bp_state).vs_halted` by simp[jump_to_def] >>
  irule lower_budget_path_block >> simp[Abbr`endpoint`] >>
  conj_tac >- metis_tac[in_revert_forward_def] >>
  conj_tac >- (qexists_tac `following` >> simp[]) >>
  qexists_tac `jump_to label p.bp_state` >> simp[]
QED

Finalise lower_budget_checked_edge

Theorem gas_origin_ptr_path_history:
  !D lo explicit ctx func PG s G tn marks finish G' tn'.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) marks (OK finish,G',tn') ==>
    !root h prefix p following.
      ALL_DISTINCT (fn_labels func) /\
      (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
      lower_budget_path T (D,lo,explicit,ctx) root h prefix p /\
      p.bp_fn = func /\ p.bp_params = PG /\ p.bp_state = s /\
      p.bp_prov = G /\ p.bp_taint = tn /\ active_inst func following finish ==>
      ?history q.
        lower_budget_path T (D,lo,explicit,ctx) root history (prefix ++ marks) q /\
        q.bp_stack = p.bp_stack /\ q.bp_fn = func /\ q.bp_params = PG /\
        q.bp_state = finish /\ q.bp_prov = G' /\ q.bp_taint = tn'
Proof
  qsuff_tac
    `!cx st marks out.
      gas_origin_ptr_path cx st marks out ==>
      !D lo explicit ctx func PG s G tn finish G' tn' root h prefix p following.
        cx = (D,lo,explicit,ctx,func,PG) /\ st = (s,G,tn) /\
        out = (OK finish,G',tn') /\ ALL_DISTINCT (fn_labels func) /\
        (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
        lower_budget_path T (D,lo,explicit,ctx) root h prefix p /\
        p.bp_fn = func /\ p.bp_params = PG /\ p.bp_state = s /\
        p.bp_prov = G /\ p.bp_taint = tn /\ active_inst func following finish ==>
        ?history q.
          lower_budget_path T (D,lo,explicit,ctx) root history (prefix ++ marks) q /\
          q.bp_stack = p.bp_stack /\ q.bp_fn = func /\ q.bp_params = PG /\
          q.bp_state = finish /\ q.bp_prov = G' /\ q.bp_taint = tn'`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_ptr_path_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[exit_result_def]
  >- (qexistsl_tac [`h`, `p`] >> simp[]) >> suspend "next"
QED

Resume gas_origin_ptr_path_history[next]:
  rename1 `gas_origin_ptr_edge (D,lo,explicit,ctx,p.bp_fn,p.bp_params)
    (p.bp_state,p.bp_prov,p.bp_taint) left (OK mid,G1,tn1)` >>
  drule_all gas_origin_ptr_path_start >> strip_tac >>
  rename1 `active_inst p.bp_fn middle_inst mid` >>
  qspecl_then [`D`, `lo`, `explicit`, `ctx`, `root`, `h`, `prefix`, `p`,
    `left`, `mid`, `G1`, `tn1`, `middle_inst`] mp_tac lower_budget_checked_edge >>
  simp[] >> strip_tac >>
  rename1 `lower_budget_path T (D,lo,explicit,ctx) root history1 (prefix ++ left) _` >>
  qmatch_assum_abbrev_tac
    `lower_budget_path T (D,lo,explicit,ctx) root history1 (prefix ++ left) middle_point` >>
  qpat_x_assum `!root h prefix p following. _`
    (qspecl_then [`root`, `history1`, `prefix ++ left`, `middle_point`, `following`]
      mp_tac) >>
  simp[Abbr`middle_point`, APPEND_ASSOC]
QED

Finalise gas_origin_ptr_path_history

Theorem gas_origin_ptr_focus_start:
  !D lo explicit ctx func PG s G tn marks leaf leaf_pg leaf_g leaf_tn finish inst.
    gas_origin_ptr_focus (D,lo,explicit,ctx,func,PG)
      (s,G,tn) marks (leaf,leaf_pg,leaf_g,leaf_tn,finish) /\
    active_inst leaf inst finish ==>
    ~s.vs_halted /\ ?first_inst. active_inst func first_inst s
Proof
  qsuff_tac
    `!cx st marks out.
      gas_origin_ptr_focus cx st marks out ==>
      !D lo explicit ctx func PG s G tn leaf leaf_pg leaf_g leaf_tn finish inst.
        cx = (D,lo,explicit,ctx,func,PG) /\ st = (s,G,tn) /\
        out = (leaf,leaf_pg,leaf_g,leaf_tn,finish) /\
        active_inst leaf inst finish ==>
        ~s.vs_halted /\ ?first_inst. active_inst func first_inst s`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_ptr_focus_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- metis_tac[gas_origin_ptr_path_start]
  >- metis_tac[gas_origin_ptr_path_start] >>
  gvs[gas_invoke_entry_def] >> metis_tac[lookup_instruction_active]
QED

Theorem gas_origin_ptr_focus_history:
  !D lo explicit ctx func PG s G tn marks leaf leaf_pg leaf_g leaf_tn finish.
    gas_origin_ptr_focus (D,lo,explicit,ctx,func,PG)
      (s,G,tn) marks (leaf,leaf_pg,leaf_g,leaf_tn,finish) ==>
    !root h prefix p following.
      MEM func ctx.ctx_functions /\
      (!fn. MEM fn ctx.ctx_functions ==>
        ALL_DISTINCT (fn_labels fn) /\
        !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
      lower_budget_path T (D,lo,explicit,ctx) root h prefix p /\
      p.bp_fn = func /\ p.bp_params = PG /\ p.bp_state = s /\
      p.bp_prov = G /\ p.bp_taint = tn /\ active_inst leaf following finish ==>
      ?history q.
        lower_budget_path T (D,lo,explicit,ctx) root history (prefix ++ marks) q /\
        q.bp_fn = leaf /\ q.bp_params = leaf_pg /\ q.bp_state = finish /\
        q.bp_prov = leaf_g /\ q.bp_taint = leaf_tn
Proof
  qsuff_tac
    `!cx st marks out.
      gas_origin_ptr_focus cx st marks out ==>
      !D lo explicit ctx func PG s G tn leaf leaf_pg leaf_g leaf_tn finish
        root h prefix p following.
        cx = (D,lo,explicit,ctx,func,PG) /\ st = (s,G,tn) /\
        out = (leaf,leaf_pg,leaf_g,leaf_tn,finish) /\
        MEM func ctx.ctx_functions /\
        (!fn. MEM fn ctx.ctx_functions ==>
          ALL_DISTINCT (fn_labels fn) /\
          !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
        lower_budget_path T (D,lo,explicit,ctx) root h prefix p /\
        p.bp_fn = func /\ p.bp_params = PG /\ p.bp_state = s /\
        p.bp_prov = G /\ p.bp_taint = tn /\ active_inst leaf following finish ==>
        ?history q.
          lower_budget_path T (D,lo,explicit,ctx) root history (prefix ++ marks) q /\
          q.bp_fn = leaf /\ q.bp_params = leaf_pg /\ q.bp_state = finish /\
          q.bp_prov = leaf_g /\ q.bp_taint = leaf_tn`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_ptr_focus_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- suspend "path"
  >- suspend "prefix" >> suspend "call"
QED

Resume gas_origin_ptr_focus_history[path]:
  drule gas_origin_ptr_path_history >>
  disch_then (qspecl_then [`root`, `h`, `prefix`, `p`, `following`] mp_tac) >>
  impl_tac >- metis_tac[] >> metis_tac[]
QED

Resume gas_origin_ptr_focus_history[prefix]:
  rename1 `gas_origin_ptr_path (D,lo,explicit,ctx,p.bp_fn,p.bp_params)
    (p.bp_state,p.bp_prov,p.bp_taint) left (OK mid,G1,tn1)` >>
  drule_all gas_origin_ptr_focus_start >> strip_tac >>
  rename1 `active_inst p.bp_fn middle_inst mid` >>
  drule gas_origin_ptr_path_history >>
  disch_then (qspecl_then [`root`, `h`, `prefix`, `p`, `middle_inst`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  rename1 `lower_budget_path T (D,lo,explicit,ctx) root history1 (prefix ++ left) middle_point` >>
  qpat_x_assum `!root h prefix p following. _`
    (qspecl_then [`root`, `history1`, `prefix ++ left`, `middle_point`, `following`]
      mp_tac) >> simp[APPEND_ASSOC] >> metis_tac[]
QED

Resume gas_origin_ptr_focus_history[call]:
  gvs[gas_invoke_entry_def] >>
  rename1 `get_instruction bb p.bp_state.vs_inst_idx = SOME call_inst` >>
  rename1 `decode_invoke call_inst = SOME (name,ops)` >>
  rename1 `setup_callee callee args p.bp_state = SOME cs` >>
  rename1 `eval_phis cs first.bb_instructions = OK phi` >>
  qabbrev_tac `entered = phi with vs_inst_idx := phi_prefix_length first.bb_instructions` >>
  drule_all gas_origin_ptr_focus_start >> strip_tac >>
  rename1 `active_inst callee head_inst entered` >>
  `active_inst p.bp_fn call_inst p.bp_state` by
    (irule lookup_instruction_active >> simp[]) >>
  `enters_block callee cs entered` by
    (rewrite_tac[enters_block_def] >> qexistsl_tac [`first`, `phi`] >>
     simp[Abbr`entered`]) >>
  `MEM callee ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  qabbrev_tac `callee_point = <|
    bp_stack := <| cf_fn := p.bp_fn; cf_inst := call_inst; cf_state := p.bp_state;
      cf_params := p.bp_params; cf_prov := p.bp_prov;
      cf_tvar := p.bp_taint.t_var |> :: p.bp_stack;
    bp_params := MAP (op_prov p.bp_prov) ops; bp_prov := FEMPTY;
    bp_taint := p.bp_taint with t_var := FEMPTY;
    bp_fn := callee; bp_state := entered |>` >>
  qabbrev_tac `call_history = h ++ [BudgetCall (LENGTH h) p call_inst callee cs callee_point]` >>
  `lower_budget_path T (D,lo,explicit,ctx) root call_history prefix callee_point` by
    (simp[Abbr`call_history`] >> irule lower_budget_path_call >>
     simp[Abbr`callee_point`] >> metis_tac[]) >>
  qpat_x_assum `!root h prefix p following. _`
    (qspecl_then [`root`, `call_history`, `prefix`, `callee_point`, `following`]
      mp_tac) >> simp[Abbr`callee_point`, Abbr`entered`] >> metis_tac[]
QED

Finalise gas_origin_ptr_focus_history

Theorem gas_origin_ptr_focus_certificate:
  !D lo explicit ctx root marks leaf leaf_pg leaf_g leaf_tn finish following.
    MEM root.bp_fn ctx.ctx_functions /\
    (!fn. MEM fn ctx.ctx_functions ==>
      ALL_DISTINCT (fn_labels fn) /\
      !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    gas_origin_ptr_focus (D,lo,explicit,ctx,root.bp_fn,root.bp_params)
      (root.bp_state,root.bp_prov,root.bp_taint) marks
      (leaf,leaf_pg,leaf_g,leaf_tn,finish) /\
    active_inst leaf following finish ==>
    ?history. lower_budget_certificate (D,lo,explicit,ctx) root history marks
      (INL (leaf,leaf_pg,leaf_g,leaf_tn,finish))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all gas_origin_ptr_focus_start >> strip_tac >>
  `lower_budget_path T (D,lo,explicit,ctx) root [] [] root` by
    (irule lower_budget_path_entry >> simp[] >> metis_tac[]) >>
  drule gas_origin_ptr_focus_history >>
  disch_then (qspecl_then [`root`, `[]`, `[]`, `root`, `following`] mp_tac) >>
  impl_tac >- metis_tac[] >> simp[] >> strip_tac >>
  rename1 `lower_budget_path T (D,lo,explicit,ctx) root history marks endpoint` >>
  qexists_tac `history` >> simp[lower_budget_certificate_def] >> metis_tac[]
QED

(* Only this runtime supplier uses the current compiler's shape restriction. *)
Theorem lower_vyper_runtime_unit_recorder_shape:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops ==>
    !fn. MEM fn unit.cu_context.ctx_functions ==>
      ALL_DISTINCT (fn_labels fn) /\
      !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >> strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  `~ctx_has_dalloca unit.cu_context` by metis_tac[entry_runtime_no_dalloca] >>
  rpt gen_tac >> strip_tac >>
  rename1 `MEM func unit.cu_context.ctx_functions` >> conj_tac
  >- fs[lowering_context_ok_def, EVERY_MEM] >>
  rpt gen_tac >> strip_tac >> irule no_phis_phi_prefix_length_zero >>
  qsuff_tac `EVERY (\inst. inst.inst_opcode <> PHI) (fn_insts func)`
  >- (rewrite_tac[fn_insts_def, EVERY_fn_insts_blocks] >>
      simp[EVERY_MEM] >> metis_tac[]) >>
  fs[lowering_context_ok_def, ptr_ok_check_def, ctx_has_dalloca_def,
     EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

Theorem lower_vyper_runtime_unit_focus_certificate:
  !tops rpolicy unit D explicit fn vs marks leaf leaf_pg leaf_g leaf_tn finish following.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    gas_origin_ptr_focus (D,0,explicit,unit.cu_context,fn,[])
      ((vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                   vs_inst_idx := 0 |>),FEMPTY,entry_taint)
      marks (leaf,leaf_pg,leaf_g,leaf_tn,finish) /\
    active_inst leaf following finish ==>
    ?p history.
      p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
        bp_taint := entry_taint; bp_fn := fn;
        bp_state := vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                               vs_inst_idx := 0 |> |> /\
      lower_budget_certificate (D,0,explicit,unit.cu_context) p history marks
        (INL (leaf,leaf_pg,leaf_g,leaf_tn,finish))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `active_inst leaf following end_state` >>
  `MEM fn unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  qspecl_then [`tops`, `rpolicy`, `unit`] mp_tac lower_vyper_runtime_unit_recorder_shape >>
  impl_tac >- simp[] >> disch_tac >>
  qabbrev_tac `p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
    bp_taint := entry_taint; bp_fn := fn;
    bp_state := vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                           vs_inst_idx := 0 |> |>` >>
  qexists_tac `p` >> simp[] >>
  qspecl_then [`D`, `0`, `explicit`, `unit.cu_context`, `p`, `marks`,
    `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `end_state`, `following`]
    mp_tac gas_origin_ptr_focus_certificate >> simp[Abbr`p`] >> metis_tac[]
QED
