Theory makeSsaCurrentExecutionHistory
Ancestors makeSsaCurrentSemanticHistory venomExecProofs venomExecSemantics venomInstProofs
  venomInst venomState list rich_list

Theorem current_step_noninvoke_fuel:
  inst.inst_opcode <> INVOKE ==>
  step_inst fuel ctx inst st = step_inst other ctx inst st
Proof
  simp[step_inst_non_invoke]
QED

Theorem current_eval_phis_take:
  !insts. eval_phis st (TAKE (phi_prefix_length insts) insts) =
    eval_phis st insts
Proof
  Induct >- simp[phi_prefix_length_def, eval_phis_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[phi_prefix_length_def, eval_phis_def]
QED

Theorem current_phi_prefix_every:
  !insts. EVERY (\inst. inst.inst_opcode = PHI)
    (TAKE (phi_prefix_length insts) insts)
Proof
  Induct >- simp[phi_prefix_length_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[phi_prefix_length_def]
QED

Definition current_phase_occurs_def:
  (current_phase_occurs fn (CurrentBatch l phis) <=>
    ?bb. lookup_block l fn.fn_blocks = SOME bb /\
      phis = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
  (current_phase_occurs fn (CurrentOrdinary l i inst) <=>
    ?bb. lookup_block l fn.fn_blocks = SOME bb /\ get_instruction bb i = SOME inst) /\
  (current_phase_occurs fn CurrentControl <=> T)
End

(* Modes prevent store-only control records from inventing reachable steps.
   Fuel in Body is the fuel actually passed to step_inst. *)
Datatype:
  current_execution_location = CurrentEntry num | CurrentBody num basic_block
End

Definition current_history_result_def:
  current_history_result result raw after <=>
    result = raw \/ (result = Halt after /\ raw = OK after)
End

(* Each edge contains the actual index update, not an unconstrained control.
   NONE has no successor.  Entry consumes dispatch fuel; non-INVOKE body
   execution is normalized to any common history fuel by the theorem above. *)
Inductive current_execution_edge:
  (!fuel bb before post.
    lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis before bb.bb_instructions = OK post ==>
    current_execution_edge fn ctx (CurrentEntry (SUC fuel)) before
      [CurrentBatch before.vs_current_bb
         (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions);
       CurrentControl]
      (SOME (CurrentBody fuel bb))
      (OK (post with vs_inst_idx := phi_prefix_length bb.bb_instructions))
      (post with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
  (!fuel bb inst before post.
    lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb before.vs_inst_idx = SOME inst /\
    inst_wf inst /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst before = OK post /\ ~is_terminator inst.inst_opcode ==>
    current_execution_edge fn ctx (CurrentBody fuel bb) before
      [CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst; CurrentControl]
      (SOME (CurrentBody fuel bb))
      (OK (post with vs_inst_idx := SUC before.vs_inst_idx))
      (post with vs_inst_idx := SUC before.vs_inst_idx)) /\
  (!fuel bb inst before post.
    lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb before.vs_inst_idx = SOME inst /\
    inst_wf inst /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst before = OK post /\ is_terminator inst.inst_opcode ==>
    current_execution_edge fn ctx (CurrentBody fuel bb) before
      [CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst]
      (if post.vs_halted then NONE else SOME (CurrentEntry fuel))
      (if post.vs_halted then Halt post else OK post) post) /\
  (!fuel bb inst before result after.
    lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb before.vs_inst_idx = SOME inst /\
    inst_wf inst /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst before = result /\
    current_state_result result after /\ result <> OK after ==>
    current_execution_edge fn ctx (CurrentBody fuel bb) before
      [CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst]
      NONE result after)
End

Inductive current_actual_prefix:
  (!loc st. current_actual_prefix fn ctx loc st [] (SOME loc) (OK st) st) /\
  (!loc before phases next result after.
    current_execution_edge fn ctx loc before phases next result after ==>
    current_actual_prefix fn ctx loc before phases next result after) /\
  (!loc before phases loc' middle rest next result after.
    current_execution_edge fn ctx loc before phases (SOME loc') (OK middle) middle /\
    current_actual_prefix fn ctx loc' middle rest next result after ==>
    current_actual_prefix fn ctx loc before (phases ++ rest) next result after) /\
  (* A stopped prefix may end immediately after an ordinary instruction,
     before the semantic index update.  It has no continuation location. *)
  (!fuel bb inst before result after.
    lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb before.vs_inst_idx = SOME inst /\
    inst_wf inst /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst before = result /\ current_state_result result after ==>
    current_actual_prefix fn ctx (CurrentBody fuel bb) before
      [CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst] NONE result after)
End

Theorem current_execution_edge_occurs:
  !loc before phases next result after.
  current_execution_edge fn ctx loc before phases next result after ==>
  EVERY (current_phase_occurs fn) phases
Proof
  ho_match_mp_tac current_execution_edge_ind >>
  simp[current_phase_occurs_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem current_history_control:
  after.vs_vars = before.vs_vars ==>
  current_semantic_history k ctx [CurrentControl] before [] (OK after) after
Proof
  strip_tac >> irule (cj 2 current_semantic_history_rules) >>
  simp[current_semantic_phase_def]
QED

Theorem current_history_batch_init:
  lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis before bb.bb_instructions = OK post ==>
  ?writes. current_semantic_history k ctx
    [CurrentBatch before.vs_current_bb
       (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions);
     CurrentControl] before writes
    (OK (post with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    (post with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  strip_tac >>
  `eval_phis before (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = OK post`
    by simp[current_eval_phis_take] >>
  `?writes. current_semantic_phase k ctx
     (CurrentBatch before.vs_current_bb
       (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions))
     before writes (OK post) post`
    by metis_tac[current_semantic_batch, current_phi_prefix_every] >>
  qexists_tac `writes ++ []` >>
  irule (cj 3 current_semantic_history_rules) >>
  qexists_tac `post` >> simp[] >>
  irule current_history_control >> simp[]
QED

Theorem current_history_noninvoke_increment:
  inst_wf inst /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst before = OK post ==>
  ?writes. current_semantic_history k ctx
    [CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst; CurrentControl]
    before writes (OK (post with vs_inst_idx := SUC before.vs_inst_idx))
    (post with vs_inst_idx := SUC before.vs_inst_idx)
Proof
  strip_tac >>
  `step_inst k ctx inst before = OK post` by metis_tac[current_step_noninvoke_fuel] >>
  `?writes. current_semantic_phase k ctx
    (CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst)
    before writes (OK post) post`
    by metis_tac[current_semantic_noninvoke, current_state_result_def] >>
  qexists_tac `writes ++ []` >>
  irule (cj 3 current_semantic_history_rules) >>
  qexists_tac `post` >> simp[] >>
  irule current_history_control >> simp[]
QED

Theorem current_history_noninvoke_single:
  inst_wf inst /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
  current_state_result (step_inst fuel ctx inst before) after ==>
  ?writes. current_semantic_history k ctx
    [CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst]
    before writes (step_inst fuel ctx inst before) after
Proof
  strip_tac >>
  `step_inst fuel ctx inst before = step_inst k ctx inst before`
    by simp[step_inst_non_invoke] >>
  `?writes. current_semantic_phase k ctx
    (CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst)
    before writes (step_inst k ctx inst before) after`
    by metis_tac[current_semantic_noninvoke] >>
  qexists_tac `writes` >>
  irule (cj 2 current_semantic_history_rules) >> metis_tac[]
QED

Theorem current_execution_edge_history:
  !loc before phases next result after.
  current_execution_edge fn ctx loc before phases next result after ==>
  ?writes raw. current_semantic_history k ctx phases before writes raw after /\
    current_history_result result raw after
Proof
  ho_match_mp_tac current_execution_edge_ind >> rpt strip_tac
  >- (drule_all current_history_batch_init >>
      disch_then (qspecl_then [`k`, `ctx`] strip_assume_tac) >>
      qexistsl_tac [`writes`, `OK (post with vs_inst_idx := phi_prefix_length bb.bb_instructions)`] >>
      simp[current_history_result_def])
  >- (drule_all current_history_noninvoke_increment >>
      disch_then (qspec_then `k` strip_assume_tac) >>
      qexistsl_tac [`writes`, `OK (post with vs_inst_idx := SUC before.vs_inst_idx)`] >>
      simp[current_history_result_def])
  >- suspend "terminator"
  >> suspend "terminal"
QED

Resume current_execution_edge_history[terminator]:
  `current_state_result (step_inst fuel ctx inst before) after`
    by simp[current_state_result_def] >>
  drule_all current_history_noninvoke_single >>
  disch_then (qspec_then `k` strip_assume_tac) >>
  qexistsl_tac [`writes`, `OK after`] >>
  Cases_on `after.vs_halted` >> simp[current_history_result_def] >> metis_tac[]
QED

Resume current_execution_edge_history[terminal]:
  `current_state_result (step_inst fuel ctx inst before) after` by metis_tac[] >>
  drule_all current_history_noninvoke_single >>
  disch_then (qspec_then `k` strip_assume_tac) >>
  qexistsl_tac [`writes`, `result`] >> simp[current_history_result_def] >> metis_tac[]
QED

Finalise current_execution_edge_history

Theorem current_actual_prefix_occurs:
  !loc before phases next result after.
  current_actual_prefix fn ctx loc before phases next result after ==>
  EVERY (current_phase_occurs fn) phases
Proof
  ho_match_mp_tac current_actual_prefix_ind >> simp[EVERY_APPEND, current_phase_occurs_def] >>
  metis_tac[current_execution_edge_occurs]
QED

Theorem current_actual_prefix_history:
  !loc before phases next result after.
  current_actual_prefix fn ctx loc before phases next result after ==>
  ?writes raw. current_semantic_history k ctx phases before writes raw after /\
    current_history_result result raw after
Proof
  ho_match_mp_tac current_actual_prefix_ind >> rpt strip_tac
  >- (qexistsl_tac [`[]`, `OK before`] >>
      simp[current_history_result_def, current_semantic_history_rules])
  >- metis_tac[current_execution_edge_history]
  >- (drule current_execution_edge_history >>
      disch_then (qspec_then `k` strip_assume_tac) >>
      gvs[current_history_result_def] >>
      metis_tac[current_semantic_history_append, current_history_result_def]) >>
  metis_tac[current_history_noninvoke_single, current_history_result_def]
QED

Theorem current_actual_prefix_append:
  !loc before phases next result0 middle.
  current_actual_prefix fn ctx loc before phases next result0 middle ==>
  !loc'. next = SOME loc' /\ result0 = OK middle ==>
  !rest final result after.
    current_actual_prefix fn ctx loc' middle rest final result after ==>
    current_actual_prefix fn ctx loc before (phases ++ rest) final result after
Proof
  ho_match_mp_tac current_actual_prefix_ind >> rpt strip_tac >> gvs[] >>
  metis_tac[current_actual_prefix_rules, APPEND_ASSOC]
QED

Definition current_execution_wf_def:
  current_execution_wf fn <=>
    !l bb inst. lookup_block l fn.fn_blocks = SOME bb /\
      MEM inst bb.bb_instructions ==> inst_wf inst /\ inst.inst_opcode <> INVOKE
End

Theorem current_execution_wf_instruction:
  current_execution_wf fn /\ lookup_block l fn.fn_blocks = SOME bb /\
  get_instruction bb i = SOME inst ==>
  inst_wf inst /\ inst.inst_opcode <> INVOKE
Proof
  simp[current_execution_wf_def, get_instruction_def] >> rpt strip_tac >>
  metis_tac[MEM_EL]
QED

Definition current_completed_location_def:
  current_completed_location fuel result after =
    if result = OK after then SOME (CurrentEntry fuel) else NONE
End

Theorem current_state_result_not_phi:
  current_state_result (step_inst fuel ctx inst before) after ==>
  inst.inst_opcode <> PHI
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule step_inst_phi_error >>
  disch_then (qspecl_then [`fuel`, `ctx`, `before`] mp_tac) >>
  metis_tac[current_state_result_def]
QED

Theorem current_terminal_prefix:
  lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb before.vs_inst_idx = SOME inst /\
  inst_wf inst /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst before = result /\
  current_state_result result after /\ result <> OK after ==>
  current_actual_prefix fn ctx (CurrentBody fuel bb) before
    [CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst]
    NONE result after
Proof
  strip_tac >> irule (cj 2 current_actual_prefix_rules) >>
  irule (cj 4 current_execution_edge_rules) >>
  simp[] >> metis_tac[current_state_result_not_phi]
QED

Theorem current_terminator_prefix:
  lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb before.vs_inst_idx = SOME inst /\
  inst_wf inst /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst before = OK post /\ is_terminator inst.inst_opcode ==>
  current_actual_prefix fn ctx (CurrentBody fuel bb) before
    [CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst]
    (if post.vs_halted then NONE else SOME (CurrentEntry fuel))
    (if post.vs_halted then Halt post else OK post) post
Proof
  strip_tac >> irule (cj 2 current_actual_prefix_rules) >>
  irule (cj 3 current_execution_edge_rules) >> simp[] >>
  metis_tac[current_state_result_not_phi, current_state_result_def]
QED

Theorem current_exec_block_prefix:
  !n before result after.
  n = LENGTH bb.bb_instructions - before.vs_inst_idx /\
  current_execution_wf fn /\
  lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel ctx bb before = result /\ current_state_result result after ==>
  ?phases. current_actual_prefix fn ctx (CurrentBody fuel bb) before phases
    (current_completed_location fuel result after) result after
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb before.vs_inst_idx` >>
  simp[] >- (strip_tac >> gvs[current_state_result_def]) >>
  rename1 `get_instruction bb before.vs_inst_idx = SOME inst` >>
  `inst_wf inst /\ inst.inst_opcode <> INVOKE`
    by metis_tac[current_execution_wf_instruction] >>
  Cases_on `step_inst fuel ctx inst before` >> simp[]
  >- suspend "ok"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "return"
  >> strip_tac >> metis_tac[current_state_result_def]
QED

Resume current_exec_block_prefix[halt]:
  strip_tac >> gvs[current_state_result_def, current_completed_location_def] >>
  `step_inst fuel ctx inst before <> OK after` by metis_tac[exec_result_distinct] >>
  simp[] >>
  qexists_tac `[CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst]` >>
  irule current_terminal_prefix >> metis_tac[]
QED

Resume current_exec_block_prefix[abort]:
  strip_tac >> gvs[current_state_result_def, current_completed_location_def] >>
  `step_inst fuel ctx inst before <> OK after` by metis_tac[exec_result_distinct] >>
  simp[] >>
  qexists_tac `[CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst]` >>
  irule current_terminal_prefix >> metis_tac[]
QED

Resume current_exec_block_prefix[return]:
  strip_tac >> gvs[current_state_result_def, current_completed_location_def] >>
  `step_inst fuel ctx inst before <> OK after` by metis_tac[exec_result_distinct] >>
  simp[] >>
  qexists_tac `[CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst]` >>
  irule current_terminal_prefix >> metis_tac[]
QED

Resume current_exec_block_prefix[ok]:
  Cases_on `is_terminator inst.inst_opcode`
  >- (drule_all current_terminator_prefix >> strip_tac >>
      Cases_on `v.vs_halted` >> simp[] >> strip_tac >>
      qpat_x_assum `_ = result` (SUBST_ALL_TAC o SYM) >>
      fs[current_state_result_def, current_completed_location_def] >>
      metis_tac[]) >>
  simp[] >> strip_tac >>
  `v.vs_current_bb = before.vs_current_bb`
    by (drule_all step_preserves_control_flow >> simp[]) >>
  `LENGTH bb.bb_instructions - SUC before.vs_inst_idx < n`
    by gvs[get_instruction_def] >>
  first_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC before.vs_inst_idx` mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`v with vs_inst_idx := SUC before.vs_inst_idx`, `after`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `[CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst; CurrentControl] ++ phases` >>
  irule (cj 3 current_actual_prefix_rules) >>
  qexistsl_tac [`CurrentBody fuel bb`, `v with vs_inst_idx := SUC before.vs_inst_idx`] >>
  simp[] >> irule (cj 2 current_execution_edge_rules) >> simp[] >>
  metis_tac[current_state_result_not_phi, current_state_result_def]
QED

Finalise current_exec_block_prefix

Theorem current_run_block_prefix:
  current_execution_wf fn /\
  lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block fuel ctx bb before = result /\ current_state_result result after ==>
  ?phases. current_actual_prefix fn ctx (CurrentEntry (SUC fuel)) before phases
    (current_completed_location fuel result after) result after
Proof
  strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  rewrite_tac[run_block_def] >>
  Cases_on `eval_phis before bb.bb_instructions` >> simp[]
  >- suspend "entry"
  >- metis_tac[eval_phis_ok_or_error_defs, exec_result_distinct]
  >- metis_tac[eval_phis_ok_or_error_defs, exec_result_distinct]
  >- metis_tac[eval_phis_ok_or_error_defs, exec_result_distinct]
  >> strip_tac >> metis_tac[current_state_result_def]
QED

Resume current_run_block_prefix[entry]:
  strip_tac >>
  `v.vs_current_bb = before.vs_current_bb`
    by metis_tac[eval_phis_preserves_current_bb] >>
  `?phases. current_actual_prefix fn ctx (CurrentBody fuel bb)
      (v with vs_inst_idx := phi_prefix_length bb.bb_instructions) phases
      (current_completed_location fuel result after) result after`
    by (irule current_exec_block_prefix >> simp[] >> metis_tac[]) >>
  qexists_tac `[CurrentBatch before.vs_current_bb
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions);
      CurrentControl] ++ phases` >>
  irule (cj 3 current_actual_prefix_rules) >>
  qexistsl_tac [`CurrentBody fuel bb`,
    `v with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
  simp[] >> irule (cj 1 current_execution_edge_rules) >> simp[]
QED

Finalise current_run_block_prefix

Theorem current_run_blocks_prefix:
  !fuel before result after.
  current_execution_wf fn /\ run_blocks fuel ctx fn before = result /\
  current_state_result result after ==>
  ?phases. current_actual_prefix fn ctx (CurrentEntry fuel) before phases
    NONE result after
Proof
  Induct >- simp[Once run_blocks_def, current_state_result_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  rewrite_tac[run_blocks_unfold] >>
  Cases_on `lookup_block before.vs_current_bb fn.fn_blocks` >> simp[]
  >- (strip_tac >> gvs[current_state_result_def]) >>
  rename1 `lookup_block before.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `run_block fuel ctx bb before` >> simp[]
  >- suspend "next"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "return"
  >> strip_tac >> metis_tac[current_state_result_def]
QED

Resume current_run_blocks_prefix[halt]:
  strip_tac >> qpat_x_assum `Halt _ = result` (SUBST_ALL_TAC o SYM) >>
  fs[current_state_result_def] >>
  drule_at Any current_run_block_prefix >>
  disch_then (qspecl_then [`fn`, `after`] mp_tac) >>
  simp[current_state_result_def, current_completed_location_def] >>
  metis_tac[]
QED

Resume current_run_blocks_prefix[abort]:
  strip_tac >> qpat_x_assum `Abort _ _ = result` (SUBST_ALL_TAC o SYM) >>
  fs[current_state_result_def] >>
  drule_at Any current_run_block_prefix >>
  disch_then (qspecl_then [`fn`, `after`] mp_tac) >>
  simp[current_state_result_def, current_completed_location_def] >>
  metis_tac[]
QED

Resume current_run_blocks_prefix[return]:
  strip_tac >> qpat_x_assum `IntRet _ _ = result` (SUBST_ALL_TAC o SYM) >>
  fs[current_state_result_def] >>
  drule_at Any current_run_block_prefix >>
  disch_then (qspecl_then [`fn`, `after`] mp_tac) >>
  simp[current_state_result_def, current_completed_location_def] >>
  metis_tac[]
QED

Resume current_run_blocks_prefix[next]:
  `~v.vs_halted` by metis_tac[run_block_OK_not_halted] >>
  simp[] >> strip_tac >>
  `?rest. current_actual_prefix fn ctx (CurrentEntry fuel) v rest NONE result after`
    by (first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule_at Any current_run_block_prefix >>
  disch_then (qspecl_then [`fn`, `v`] mp_tac) >>
  simp[current_state_result_def, current_completed_location_def] >> strip_tac >>
  qexists_tac `phases ++ rest` >>
  irule current_actual_prefix_append >>
  goal_assum (drule_at Any) >> simp[]
QED

Finalise current_run_blocks_prefix

(* Terminal OK-to-Halt wrapping does not execute an extra instruction.  The
   semantic history records the raw step result; current_history_result records
   precisely this one permitted wrapper and no store change. *)
Theorem current_run_blocks_history:
  current_execution_wf fn /\ run_blocks fuel ctx fn before = result /\
  current_state_result result after ==>
  ?phases writes raw.
    current_actual_prefix fn ctx (CurrentEntry fuel) before phases NONE result after /\
    EVERY (current_phase_occurs fn) phases /\
    current_semantic_history k ctx phases before writes raw after /\
    current_history_result result raw after
Proof
  strip_tac >> drule_all current_run_blocks_prefix >> strip_tac >>
  metis_tac[current_actual_prefix_occurs, current_actual_prefix_history]
QED

Theorem current_exec_block_history:
  current_execution_wf fn /\
  lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel ctx bb before = result /\ current_state_result result after ==>
  ?phases writes raw.
    current_actual_prefix fn ctx (CurrentBody fuel bb) before phases
      (current_completed_location fuel result after) result after /\
    EVERY (current_phase_occurs fn) phases /\
    current_semantic_history k ctx phases before writes raw after /\
    current_history_result result raw after
Proof
  strip_tac >>
  `?phases. current_actual_prefix fn ctx (CurrentBody fuel bb) before phases
    (current_completed_location fuel result after) result after`
    by (irule current_exec_block_prefix >> simp[] >> metis_tac[]) >>
  metis_tac[current_actual_prefix_occurs, current_actual_prefix_history]
QED
