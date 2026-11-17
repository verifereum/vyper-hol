(* Joint paths and focused calls retain their exact recorder cursors. *)
Theory loweringOriginHistory
Ancestors
  loweringBudgetRunHistory loweringCallBudgetHistory
  fragGasOriginPtr fragGasFocus fragExec typedCopyArrayPtr
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
