(* Checked joint prefixes retain their actual instruction history and ghosts. *)
Theory loweringJointPrefixHistory
Ancestors
  loweringOriginHistory loweringBudgetRunHistory loweringTerminalHistory
  loweringCallBudgetHistory fragGasOriginPtr fragGasFocus fragExec
  typedCopyArrayPtr
  entryReachBodyFmp vyperLoweringCorrect vyperCompiler
  ptrSafeRun ptrDiscipline memSafeRun gasEvents
  contextCodegenRel contextCodegenRelProps venomExecSemantics venomExecProofs
  venomInstProofs venomInst venomState finite_map list arithmetic

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

(* Transport an already recorded prefix up to the actual terminal leaf. *)
Theorem gas_origin_ptr_exit_history[local]:
  !cx st marks out.
    gas_origin_ptr_path cx st marks out ==>
    !D lo explicit ctx func PG s G tn r G' tn' root h prefix p.
      cx = (D,lo,explicit,ctx,func,PG) /\ st = (s,G,tn) /\
      out = (r,G',tn') /\ exit_result r /\
      ALL_DISTINCT (fn_labels func) /\
      (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
      lower_budget_path T (D,lo,explicit,ctx) root h prefix p /\
      p.bp_stack = [] /\ p.bp_fn = func /\ p.bp_params = PG /\
      p.bp_state = s /\ p.bp_prov = G /\ p.bp_taint = tn ==>
      ?history premarks q i fuel.
        lower_budget_path T (D,lo,explicit,ctx) root history premarks q /\
        active_inst q.bp_fn i q.bp_state /\ i.inst_opcode <> INVOKE /\
        prefix ++ marks = premarks ++ MAP (\key. key IN explicit)
          (gas_events_step fuel ctx q.bp_fn.fn_name i q.bp_state) /\
        ((step_inst fuel ctx i q.bp_state = r /\
          (!ret t. r = IntRet ret t ==> q.bp_stack = [])) \/
         (?t. step_inst fuel ctx i q.bp_state = OK t /\
           is_terminator i.inst_opcode /\ t.vs_halted /\ r = Halt t))
Proof
  ho_match_mp_tac gas_origin_ptr_path_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[exit_result_def]
  >- suspend "next" >> suspend "terminal"
QED

Resume gas_origin_ptr_exit_history[next]:
  rename1 `gas_origin_ptr_path (D,lo,explicit,ctx,p.bp_fn,p.bp_params)
    (mid,G1,tn1) right (r,G',tn')` >>
  `?following. active_inst p.bp_fn following mid` by
    (qpat_x_assum `gas_origin_ptr_path _ _ _ _` mp_tac >>
     simp[Once gas_origin_ptr_path_cases] >> strip_tac >>
     gvs[exit_result_def] >> drule gas_origin_ptr_edge_common_fuel >>
     strip_tac >> metis_tac[lookup_instruction_active]) >>
  drule_all lower_budget_checked_edge >> strip_tac >>
  rename1 `lower_budget_path T (D,lo,explicit,ctx) root history1 (prefix ++ left) _` >>
  qmatch_assum_abbrev_tac
    `lower_budget_path T (D,lo,explicit,ctx) root history1 (prefix ++ left) middle_point` >>
  first_x_assum (qspecl_then [`root`, `history1`, `prefix ++ left`,
    `middle_point`] mp_tac) >>
  simp[Abbr`middle_point`, APPEND_ASSOC, exit_result_def]
QED

Resume gas_origin_ptr_exit_history[terminal]:
  drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `fuel` (qx_choose_then `bb` (qx_choose_then `current`
      (qx_choose_then `middle` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  `active_inst p.bp_fn current p.bp_state` by
    (irule lookup_instruction_active >> simp[]) >>
  qpat_x_assum `_ \/ _ \/ _ \/ _ \/ _` mp_tac >> strip_tac >>
  gvs[exit_result_def] >> suspend "leaf"
QED

Resume gas_origin_ptr_exit_history[leaf]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  (Cases_on `current.inst_opcode = INVOKE`
   >- (gvs[is_terminator_def] >> suspend "invoke") >>
   qexistsl_tac [`h`, `prefix`, `p`, `current`, `fuel`] >> simp[])
QED

Resume gas_origin_ptr_exit_history[invoke]:
  markerLib.RESUME_TAC >> rpt strip_tac >> (
  `mem_safe_step fuel ctx current p.bp_state` by
    (fs[] >> drule_all revert_forward_at_opcode >> simp[]) >>
  qmatch_asmsub_abbrev_tac `exit_result result` >>
  `step_inst fuel ctx current p.bp_state = result` by simp[Abbr`result`] >>
  drule_all step_inst_invoke_exit >> strip_tac >>
  drule_all lower_budget_checked_callee_entry >> strip_tac >>
  rename1 `frame_run child_fuel ctx callee entered = result` >>
  rename1 `lower_budget_path T (D,lo,explicit,ctx) root call_history prefix _` >>
  qmatch_assum_abbrev_tac
    `lower_budget_path T (D,lo,explicit,ctx) root call_history prefix callee_point` >>
  qspecl_then [`child_fuel`, `ctx`, `callee`, `target`, `entered`, `result`]
    mp_tac lower_budget_checked_terminal >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`D`, `lo`, `explicit`, `root`, `call_history`, `prefix`,
    `callee_point`] mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  rename1 `lower_budget_path T (D,lo,explicit,ctx) root history (prefix ++ suffix) endpoint` >>
  rename1 `active_inst endpoint.bp_fn terminal endpoint.bp_state` >>
  rename1 `_ = suffix ++ MAP _ (gas_events_step last_fuel ctx _ terminal _)` >>
  qexistsl_tac [`history`, `prefix ++ suffix`, `endpoint`, `terminal`, `last_fuel`] >>
  gvs[Abbr`result`, MAP_APPEND, APPEND_ASSOC] >> metis_tac[])
QED

Finalise gas_origin_ptr_exit_history
Theorem gas_origin_ptr_ok_certificate:
  !D lo explicit ctx root marks end_state G' tn' following.
    root.bp_stack = [] /\ MEM root.bp_fn ctx.ctx_functions /\
    (!fn. MEM fn ctx.ctx_functions ==>
      ALL_DISTINCT (fn_labels fn) /\
      !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    gas_origin_ptr_path (D,lo,explicit,ctx,root.bp_fn,root.bp_params)
      (root.bp_state,root.bp_prov,root.bp_taint) marks (OK end_state,G',tn') /\
    active_inst root.bp_fn following end_state ==>
    ?history. lower_budget_certificate (D,lo,explicit,ctx) root history marks
      (INR (OK end_state,G',tn'))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all gas_origin_ptr_path_start >> strip_tac >>
  `lower_budget_path T (D,lo,explicit,ctx) root [] [] root` by
    (irule lower_budget_path_entry >> simp[] >> metis_tac[]) >>
  drule gas_origin_ptr_path_history >>
  disch_then (qspecl_then [`root`, `[]`, `[]`, `root`, `following`] mp_tac) >>
  impl_tac >- metis_tac[] >> simp[] >> strip_tac >>
  qexists_tac `history` >> simp[lower_budget_certificate_def] >> metis_tac[]
QED

(* Certificates retain the selected terminal history and actual terminal marks. *)
Theorem gas_origin_ptr_exit_certificate:
  !D lo explicit ctx root marks r G' tn'.
    root.bp_stack = [] /\ MEM root.bp_fn ctx.ctx_functions /\
    (!fn. MEM fn ctx.ctx_functions ==>
      ALL_DISTINCT (fn_labels fn) /\
      !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    gas_origin_ptr_path (D,lo,explicit,ctx,root.bp_fn,root.bp_params)
      (root.bp_state,root.bp_prov,root.bp_taint) marks (r,G',tn') /\
    exit_result r ==>
    ?history. lower_budget_certificate (D,lo,explicit,ctx) root history marks
      (INR (r,G',tn'))
Proof
  rpt gen_tac >> strip_tac >>
  `~root.bp_state.vs_halted /\ ?first. active_inst root.bp_fn first root.bp_state` by
    (qpat_x_assum `gas_origin_ptr_path _ _ _ _` mp_tac >>
     simp[Once gas_origin_ptr_path_cases] >> strip_tac >>
     gvs[exit_result_def] >> drule gas_origin_ptr_edge_common_fuel >>
     strip_tac >> metis_tac[lookup_instruction_active]) >>
  `lower_budget_path T (D,lo,explicit,ctx) root [] [] root` by
    (irule lower_budget_path_entry >> simp[] >> metis_tac[]) >>
  drule gas_origin_ptr_exit_history >> simp[] >>
  disch_then (qspecl_then [`root`, `[]`, `[]`, `root`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> simp[] >> strip_tac >>
  qexists_tac `history` >> simp[lower_budget_certificate_def] >> metis_tac[]
QED

Theorem lower_vyper_runtime_unit_exit_certificate:
  !tops rpolicy unit D explicit fn vs marks r G' tn'.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      ((vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                   vs_inst_idx := 0 |>),FEMPTY,entry_taint) marks (r,G',tn') /\
    exit_result r ==>
    ?p history.
      p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
        bp_taint := entry_taint; bp_fn := fn;
        bp_state := vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                               vs_inst_idx := 0 |> |> /\
      lower_budget_certificate (D,0,explicit,unit.cu_context) p history marks
        (INR (r,G',tn'))
Proof
  NO_TAC
QED
