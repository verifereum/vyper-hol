(* Checked GAS focuses and the source request-count invariant. *)
Theory s1PrefixProps
Ancestors
  s1PrefixDefs fragGasOriginPtr fragGasOriginEvents fragGasOrigin fragGasPath fragGasPathPtr
  fragExec gasEvents gasEventsFuel gasSummary gasOutcomeFull
  ptrSafeRun memSafeRun fragGasFocus venomExecSemantics venomExecProofs
  venomInstProofs venomInst venomState e2eRequestCutDefs extCallOracle
  vyperState vyperCallOutcome vyperCallOutcomeProps vyperCallOutcomeFrame
  vyperMachineFrame vyperStatePreservation vyperInterpreter vyperCreate
  vyperPlaceFrames vyperStorageTrace exprLoweringProps loweringStateRelDefs
  list pair sum rich_list arithmetic option
Libs monadsyntax s1PrefixRequestFrameLib

Theorem gas_origin_ptr_focus_marks_comparable:
  gas_origin_ptr_focus (D1, lo1, explicit, ctx, func, PG1)
    (s, G1, tn1) marks1 (leaf1, leaf_pg1, leaf_g1, leaf_tn1, finish1) /\
  gas_origin_ptr_focus (D2, lo2, explicit, ctx, func, PG2)
    (s, G2, tn2) marks2 (leaf2, leaf_pg2, leaf_g2, leaf_tn2, finish2) ==>
  isPREFIX marks1 marks2 \/ isPREFIX marks2 marks1
Proof
  strip_tac >>
  qpat_assum `gas_origin_ptr_focus _ _ marks1 _`
    (assume_tac o MATCH_MP gas_origin_ptr_focus_origin) >>
  qpat_assum `gas_origin_ptr_focus _ _ marks2 _`
    (assume_tac o MATCH_MP gas_origin_ptr_focus_origin) >>
  qpat_x_assum `gas_origin_focus _ _ _ _ marks1 _`
    (qx_choose_then `fuel1` strip_assume_tac o MATCH_MP gas_origin_focus_events_prefix) >>
  qpat_x_assum `gas_origin_focus _ _ _ _ marks2 _`
    (qx_choose_then `fuel2` strip_assume_tac o MATCH_MP gas_origin_focus_events_prefix) >>
  `fuel1 <= MAX fuel1 fuel2 /\ fuel2 <= MAX fuel1 fuel2` by simp[] >>
  qspecl_then [`fuel1`, `MAX fuel1 fuel2`, `s`, `func`, `ctx`] mp_tac
    (Q.GENL [`n`, `m`, `s`, `func`, `ctx`] gas_events_current_fuel_prefix) >>
  simp[] >> strip_tac >>
  qspecl_then [`fuel2`, `MAX fuel1 fuel2`, `s`, `func`, `ctx`] mp_tac
    (Q.GENL [`n`, `m`, `s`, `func`, `ctx`] gas_events_current_fuel_prefix) >>
  simp[] >> strip_tac >>
  irule prefixes_is_prefix_total >>
  simp[IS_PREFIX_APPEND] >>
  metis_tac[MAP_APPEND, APPEND_ASSOC]
QED

Triviality terminal_events_fuel:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  exit_result (run_from n ctx func s) /\ n <= m ==>
  gas_events_block m ctx func.fn_name bb s ++
    (case exec_block m ctx bb s of
       OK u => if u.vs_halted then [] else gas_events_blocks m ctx func u
     | _ => []) =
  gas_events_block n ctx func.fn_name bb s ++
    (case exec_block n ctx bb s of
       OK u => if u.vs_halted then [] else gas_events_blocks n ctx func u
     | _ => [])
Proof
  rw[run_from_def] >>
  `!e. exec_block n ctx bb s <> Error e` by
    (strip_tac >> CCONTR_TAC >> gvs[exit_result_def]) >>
  drule_then (qspecl_then [`ctx`, `func.fn_name`, `bb`, `s`]
    strip_assume_tac) (cj 2 gas_events_fuel_extension) >>
  Cases_on `exec_block n ctx bb s` >> gvs[] >>
  rename1 `exec_block n ctx bb s = OK u` >>
  Cases_on `u.vs_halted` >> gvs[] >>
  `!e. run_blocks n ctx func u <> Error e` by metis_tac[exit_result_not_error] >>
  drule_then (qspecl_then [`ctx`, `func`, `u`] strip_assume_tac)
    (cj 3 gas_events_fuel_extension) >>
  gvs[]
QED

Theorem gas_origin_path_exit_bounds_focus:
  gas_origin_path T explicit ctx func s marks1 r /\ exit_result r /\
  gas_origin_focus T explicit (ctx, func) s marks2 out ==>
  isPREFIX marks2 marks1
Proof
  strip_tac >> PairCases_on `out` >>
  drule_all_then (qx_choose_then `path_fuel` strip_assume_tac) gas_origin_path_events >>
  drule_then (qx_choose_then `focus_fuel` strip_assume_tac) gas_origin_focus_events_prefix >>
  `path_fuel <= MAX path_fuel focus_fuel /\ focus_fuel <= MAX path_fuel focus_fuel` by simp[] >>
  `exit_result (run_from path_fuel ctx func s)` by simp[] >>
  drule_all terminal_events_fuel >> strip_tac >>
  qspecl_then [`focus_fuel`, `MAX path_fuel focus_fuel`, `s`, `func`, `ctx`] mp_tac
    (Q.GENL [`n`, `m`, `s`, `func`, `ctx`] gas_events_current_fuel_prefix) >>
  simp[] >> strip_tac >>
  once_rewrite_tac[GSYM MAP_APPEND] >>
  qpat_assum `gas_events_block path_fuel _ _ _ _ ++ _ = _ ++ _`
    (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `MAP _ (case lookup_block _ _ of NONE => [] | SOME bb => _) = _`
    mp_tac >>
  simp[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem gas_prefix_claims_extend:
  !claims marks readings ext.
    (!tail. claims (gas_explicit marks readings ++ tail)) ==>
    !tail. claims (gas_explicit (marks ++ ext) readings ++ tail)
Proof
  PURE_REWRITE_TAC[gas_explicit_append, GSYM APPEND_ASSOC] >> metis_tac[]
QED

Triviality path_at_checked_edge:
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn)
    marks (OK t,G',tn') /\ ~t.vs_halted ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn)
    marks (OK t,G',tn')
Proof
  strip_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G',tn') []
    (OK t,G',tn')` by simp[gas_origin_ptr_path_rules] >>
  drule_all (cj 2 gas_origin_ptr_path_rules) >> simp[]
QED

(* Reconstruct a focus from a completed, checked run. An ordinary exit
   contributes no GAS event, but an exiting INVOKE contributes its
   callee's events and needs a focus inside that callee. *)
Triviality invoke_step_checked:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step fuel ctx inst s) /\
  inst.inst_opcode = INVOKE ==>
  mem_safe_step fuel ctx inst s
Proof
  strip_tac >> fs[] >>
  drule_all revert_forward_at_opcode >> simp[]
QED

Theorem checked_run_focus:
  (!D lo fuel ctx func PG G tn inst s.
     ~s.vs_halted /\ ptr_safe_step D lo fuel ctx func PG G tn inst s /\
     (?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
           get_instruction bb s.vs_inst_idx = SOME inst) /\
     (inst.inst_opcode = INVOKE ==> mem_safe_step fuel ctx inst s) /\
     exit_result (step_inst fuel ctx inst s) ==>
     ?focus. gas_origin_ptr_focus (D, lo, explicit, ctx, func, PG) (s,G,tn)
       (MAP (\key. key IN explicit) (gas_events_step fuel ctx func.fn_name inst s))
       focus) /\
  (!D lo fuel ctx func PG G tn bb s.
     ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     ptr_safe_block D lo fuel ctx func PG G tn bb s /\
     mem_safe_block fuel ctx bb s /\
     (case exec_block fuel ctx bb s of
        OK t => t.vs_halted \/
                (mem_safe_blocks fuel ctx func t /\ exit_result (run_blocks fuel ctx func t))
      | r => exit_result r) ==>
     ?focus. gas_origin_ptr_focus (D, lo, explicit, ctx, func, PG) (s,G,tn)
       (MAP (\key. key IN explicit)
         (gas_events_block fuel ctx func.fn_name bb s ++
          case exec_block fuel ctx bb s of
            OK t => if t.vs_halted then [] else gas_events_blocks fuel ctx func t
          | _ => []))
       focus) /\
  (!D lo fuel ctx func PG G tn s.
     ~s.vs_halted /\ ptr_safe_blocks D lo fuel ctx func PG G tn s /\
     mem_safe_blocks fuel ctx func s /\ exit_result (run_blocks fuel ctx func s) ==>
     ?bb phi focus. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       eval_phis s bb.bb_instructions = OK phi /\ ~phi.vs_halted /\
       gas_origin_ptr_focus (D, lo, explicit, ctx, func, PG)
         (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions,G,tn)
         (MAP (\key. key IN explicit) (gas_events_blocks fuel ctx func s)) focus)
Proof
  ho_match_mp_tac ptr_safe_defs_ind >> conj_tac >- suspend "step" >>
  conj_tac >- suspend "block" >> suspend "blocks"
QED

Resume checked_run_focus[step]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (Cases_on `decode_invoke inst` >> fs[Once step_inst_def, exit_result_def] >>
      rename1 `decode_invoke inst = SOME call` >> PairCases_on `call` >> gvs[] >>
      Cases_on `lookup_function call0 ctx.ctx_functions` >> fs[Once step_inst_def, exit_result_def] >>
      rename1 `lookup_function call0 ctx.ctx_functions = SOME callee` >>
      Cases_on `eval_operands call1 s` >> fs[Once step_inst_def, exit_result_def] >>
      rename1 `eval_operands call1 s = SOME args` >>
      Cases_on `setup_callee callee args s` >> fs[Once step_inst_def, exit_result_def] >>
      rename1 `setup_callee callee args s = SOME setup` >>
      `exit_result (run_blocks fuel ctx callee setup)` by
        (Cases_on `run_blocks fuel ctx callee setup` >> gvs[exit_result_def]) >>
      `~setup.vs_halted` by
        (qpat_assum `setup_callee callee args s = SOME setup` mp_tac >>
         PURE_REWRITE_TAC[setup_callee_def] >>
         Cases_on `NULL callee.fn_blocks` >> simp[] >>
         disch_then (SUBST1_TAC o SYM) >> simp[]) >>
      `ptr_inst_ok D lo fuel ctx func G tn inst s /\
       ptr_safe_blocks D lo fuel ctx callee (MAP (op_prov G) call1) FEMPTY
         (tn with t_var := FEMPTY) setup` by fs[Once ptr_safe_step_def] >>
      `mem_safe_blocks fuel ctx callee setup` by fs[Once mem_safe_step_def] >>
      qpat_x_assum `_ ==> ?bb phi focus. _` mp_tac >>
      simp[] >> disch_then (qx_choose_then `entry_bb` (qx_choose_then `phi`
        (qx_choose_then `focus` strip_assume_tac))) >>
      simp[gas_events_step_def] >> qexists_tac `focus` >>
      PairCases_on `focus` >>
      irule (cj 3 gas_origin_ptr_focus_rules) >>
      simp[] >>
      qexistsl_tac [`callee`,
        `phi with vs_inst_idx := phi_prefix_length entry_bb.bb_instructions`] >>
      simp[] >> conj_tac
      >- (rewrite_tac[gas_invoke_entry_def] >> simp[] >>
          qexistsl_tac [`bb`, `inst`, `call0`, `call1`, `args`, `setup`, `entry_bb`, `phi`] >>
          simp[]) >>
      metis_tac[ptr_inst_ok_fuel]) >>
  `inst.inst_opcode <> GAS` by
    (strip_tac >>
     qpat_x_assum `exit_result (step_inst _ _ _ _)` mp_tac >>
     simp[step_inst_non_invoke, exit_result_def, Once step_inst_base_def] >>
     Cases_on `exec_gas inst s` >> gvs[exit_result_def, exec_gas_not_terminal]) >>
  simp[gas_events_step_def] >>
  qexists_tac `(func,PG,G,tn,s)` >> simp[gas_origin_ptr_focus_nil]
QED

Resume checked_run_focus[block]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- gvs[Once exec_block_def, exit_result_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  qpat_x_assum `ptr_safe_block _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `mem_safe_block _ _ _ _` mp_tac >>
  qpat_x_assum `exec_result_CASE (exec_block _ _ _ _) _ _ _ _ _` mp_tac >>
  simp[Once exec_block_def, Once gas_events_block_def] >>
  simp[Once ptr_safe_block_def, Once mem_safe_block_def] >>
  Cases_on `step_inst fuel ctx inst s`
  >- suspend "ok"
  >> (
    simp[exit_result_def] >> rpt strip_tac >>
    `exec_block fuel ctx bb s = step_inst fuel ctx inst s` by
      simp[Once exec_block_def] >>
    fs[exit_result_def] >>
    `inst.inst_opcode = INVOKE ==> mem_safe_step fuel ctx inst s` by
      metis_tac[invoke_step_checked] >>
    metis_tac[])
QED

Resume checked_run_focus[blocks]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  namedCases_on `fuel` ["", "inner"] >- gvs[Once run_blocks_def, exit_result_def] >>
  Cases_on `lookup_block s.vs_current_bb func.fn_blocks`
  >- gvs[Once run_blocks_def, exit_result_def] >>
  rename1 `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions`
  >>~ [`eval_phis s bb.bb_instructions = OK phi`]
  >- (drule venomExecProofsTheory.eval_phis_preserves_halted >> strip_tac >>
      drule venomExecProofsTheory.eval_phis_preserves_current_bb >> strip_tac >>
      simp[Once gas_events_blocks_def] >>
      qpat_x_assum `exit_result (run_blocks _ _ _ _)` mp_tac >>
      simp[Once run_blocks_def] >>
      qpat_x_assum `ptr_safe_blocks _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[Once ptr_safe_blocks_def] >>
      qpat_x_assum `mem_safe_blocks _ _ _ _` mp_tac >>
      simp[Once mem_safe_blocks_def] >>
      rpt strip_tac >>
      qpat_x_assum `!n bb phi. _ ==> _ ==> _`
        (qspecl_then [`inner`, `bb`, `phi`] mp_tac) >>
      simp[] >> impl_tac
      >- (qmatch_asmsub_abbrev_tac `exec_block inner ctx bb entrance` >>
          Cases_on `exec_block inner ctx bb entrance` >>
          gvs[exit_result_def] >> metis_tac[]) >>
      simp[]) >>
  mp_tac (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  qpat_x_assum `exit_result (run_blocks _ _ _ _)` mp_tac >>
  simp[run_blocks_unfold, run_block_def, exit_result_def]
QED

Resume checked_run_focus[ok]:
  rename1 `step_inst fuel ctx inst s = OK next` >>
  Cases_on `is_terminator inst.inst_opcode`
  >- suspend "jump" >>
  suspend "continue"
QED

Resume checked_run_focus[continue]:
  simp[] >> rpt (disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) >>
  `exec_block fuel ctx bb s =
    exec_block fuel ctx bb (next with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Once exec_block_def] >>
  asm_rewrite_tac[] >>
  drule_all step_preserves_control_flow >> strip_tac >>
  `~next.vs_halted` by (drule_all step_preserves_halted >> simp[]) >>
  qabbrev_tac `next_at = next with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `next_g = FST (ghost_step fuel ctx PG G tn inst s)` >>
  qabbrev_tac `next_tn = SND (ghost_step fuel ctx PG G tn inst s)` >>
  `?focus. gas_origin_ptr_focus (D, lo, explicit, ctx, func, PG)
     (next_at,next_g,next_tn)
     (MAP (\key. key IN explicit)
       (gas_events_block fuel ctx func.fn_name bb next_at ++
        case exec_block fuel ctx bb next_at of
          OK t => if t.vs_halted then [] else gas_events_blocks fuel ctx func t
        | _ => [])) focus` by
    (qpat_x_assum `!i t. _ /\ _ /\ ~is_terminator _ ==> _`
       (qspecl_then [`inst`, `next`] mp_tac) >>
     simp[Abbr `next_g`, Abbr `next_tn`]) >>
  `gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s,G,tn)
     (MAP (\key. key IN explicit) (gas_events_step fuel ctx func.fn_name inst s))
     (OK next_at,next_g,next_tn)` by
    (irule path_at_checked_edge >>
     simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def,
          Abbr `next_at`, Abbr `next_g`, Abbr `next_tn`] >>
     conj_tac >> qexists_tac `fuel` >> simp[gas_events_length]) >>
  qexists_tac `focus` >> PairCases_on `focus` >>
  PURE_REWRITE_TAC[MAP_APPEND, GSYM APPEND_ASSOC] >>
  irule (cj 2 gas_origin_ptr_focus_rules) >>
  qexistsl_tac [`next_g`, `next_at`, `next_tn`] >> fs[MAP_APPEND]
QED

Resume checked_run_focus[jump]:
  simp[] >> rpt (disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) >>
  Cases_on `next.vs_halted`
  >- (`inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
      simp[Once exec_block_def, gas_events_step_def] >>
      qexists_tac `(func,PG,G,tn,s)` >>
      simp[gas_origin_ptr_focus_nil]) >>
  `exec_block fuel ctx bb s = OK next` by simp[Once exec_block_def] >>
  fs[] >>
  qmatch_asmsub_abbrev_tac `ptr_safe_blocks D lo fuel ctx func PG next_g next_tn next` >>
  qabbrev_tac `next_at = phi with vs_inst_idx := phi_prefix_length bb'.bb_instructions` >>
  `gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s,G,tn)
     (MAP (\key. key IN explicit) (gas_events_step fuel ctx func.fn_name inst s))
     (OK next_at,next_g,next_tn)` by
    (irule path_at_checked_edge >>
     simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def,
          Abbr `next_at`, Abbr `next_g`, Abbr `next_tn`] >>
     conj_tac >> qexists_tac `fuel` >> simp[gas_events_length] >>
     metis_tac[]) >>
  qexists_tac `focus` >> PairCases_on `focus` >>
  PURE_REWRITE_TAC[MAP_APPEND] >>
  irule (cj 2 gas_origin_ptr_focus_rules) >>
  qexistsl_tac [`next_g`, `next_at`, `next_tn`] >> simp[Abbr `next_at`]
QED

Finalise checked_run_focus[local]

Theorem gas_origin_ptr_path_focus:
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s,G,tn) marks (r,G',tn') ==>
  ?leaf leaf_pg leaf_g leaf_tn finish.
    gas_origin_ptr_focus (D, lo, explicit, ctx, func, PG)
      (s,G,tn) marks (leaf,leaf_pg,leaf_g,leaf_tn,finish)
Proof
  qsuff_tac `!P st marks out. gas_origin_ptr_path P st marks out ==>
      ?focus. gas_origin_ptr_focus P st marks focus`
  >- (strip_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
      PairCases_on `focus` >> metis_tac[]) >>
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> metis_tac[gas_origin_ptr_focus_nil])
  >- (rpt strip_tac >> PairCases_on `focus` >>
      `~mid.vs_halted` by
        (qpat_assum `gas_origin_ptr_edge _ _ _ _`
           (mp_tac o CONJUNCT1 o REWRITE_RULE[gas_origin_ptr_edge_def]) >>
         disch_then (mp_tac o CONJUNCT1 o MATCH_MP gas_origin_edge_erase) >>
         MATCH_ACCEPT_TAC (SPEC_ALL gas_path_edge_normal)) >>
      drule_all path_at_checked_edge >> strip_tac >>
      qexists_tac `(focus0,focus1,focus2,focus3,focus4)` >>
      irule (cj 2 gas_origin_ptr_focus_rules) >>
      qexistsl_tac [`G1`, `mid`, `tn1`] >> simp[]) >>
  rpt gen_tac >> strip_tac >> drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `fuel` (qx_choose_then `bb` (qx_choose_then `inst`
      (qx_choose_then `middle` (map_every assume_tac o CONJUNCTS)))))) >>
  qpat_x_assum `(?t. middle = OK t /\ ~is_terminator _ /\ _) \/ _` strip_assume_tac >>
  gvs[exit_result_def]
  >>~- ([`is_terminator inst.inst_opcode`],
        Cases_on `inst.inst_opcode` >> gvs[is_terminator_def, gas_events_step_def] >>
        metis_tac[gas_origin_ptr_focus_nil]) >>
  `inst.inst_opcode = INVOKE ==> mem_safe_step fuel ctx inst s` by
    metis_tac[invoke_step_checked] >>
  irule (cj 1 checked_run_focus) >> simp[] >>
  qexists_tac `bb` >> simp[]
QED

(* The source records an oracle request and its StorageOutcome together. *)
val () = monadsyntax.enable_monad "vyper_evaluation";

Theorem take_request_gas_obs:
  take_request_outcome rq (es with gas_obs := readings) =
    (FST (take_request_outcome rq es),
     SND (take_request_outcome rq es) with gas_obs := readings)
Proof
  Cases_on `es.outcomes` >> simp[take_request_outcome_def] >>
  rename1 `es.outcomes = SOME os` >> Cases_on `os` >> simp[] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem take_delegate_gas_obs:
  take_delegate_outcome gas_cap target calldata value (es with gas_obs := readings) =
    (FST (take_delegate_outcome gas_cap target calldata value es),
     SND (take_delegate_outcome gas_cap target calldata value es) with gas_obs := readings)
Proof
  PURE_REWRITE_TAC[take_delegate_outcome_def, delegate_outcome_request_def,
                   call_outcome_request_def] >>
  simp[take_request_gas_obs]
QED

Theorem observed_take_at_start:
  take_request_outcome rq0 es = (INL (rq,outcome),es1) /\
  es1.storage_trace = obs_pre ++ StorageOutcome request observed :: sfx /\
  LENGTH es.storage_trace <= LENGTH obs_pre ==>
  obs_pre = es.storage_trace /\ request = rq /\ observed = outcome
Proof
  strip_tac >>
  drule take_request_outcome_success >> strip_tac >>
  `es.storage_trace ++ [StorageOutcome rq outcome] =
    obs_pre ++ StorageOutcome request observed :: sfx` by gvs[] >>
  qpat_x_assum `es.storage_trace ++ [_] = _` mp_tac >>
  simp[APPEND_EQ_APPEND] >> strip_tac >> gvs[] >>
  Cases_on `l` >> gvs[]
QED

Theorem call_step_checks:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),G',tn') /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL] ==>
  ptr_inst_ok D lo 0 ctx func G tn inst s /\ mem_safe_step 0 ctx inst s
Proof
  strip_tac >>
  qpat_x_assum `gas_origin_ptr_path _ _ _ _` mp_tac >>
  simp[Once gas_origin_ptr_path_cases, exit_result_def] >> strip_tac
  >- (qpat_x_assum `_ = s`
        (mp_tac o Q.AP_TERM `\t. t.vs_inst_idx`) >> simp[]) >>
  drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `fuel` (qx_choose_then `edge_bb` (qx_choose_then `edge_inst`
     (qx_choose_then `step_result` (map_every assume_tac o CONJUNCTS)))))) >>
  `edge_bb = bb /\ edge_inst = inst` by metis_tac[SOME_11] >>
  fs[is_terminator_def] >>
  `inst.inst_opcode <> INVOKE /\ ~revert_forward_at bb s.vs_inst_idx` by
    (fs[] >> rpt strip_tac >> drule_all revert_forward_at_opcode >> fs[]) >>
  `mem_safe_step fuel ctx inst s` by metis_tac[] >>
  (conj_tac
   >- metis_tac[ptr_safe_step_inst_ok, ptr_inst_ok_fuel] >>
   fs[mem_safe_step_non_invoke])
QED

Theorem ordinary_request_index:
  stmt_state_rel H ctx func cenv cx es s /\
  stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
  take_request_outcome rq0 es = (INL (rq,outcome),es1) /\
  ~computed_precompile rq /\ LENGTH es.requests = k ==>
  LENGTH s.vs_requests = k /\ k < LENGTH u.vs_requests /\
  request_agree H cx.txn.target rq (EL k u.vs_requests) /\
  outcome = (if s.vs_outcomes = [] then failed_outcome rq else HD s.vs_outcomes)
Proof
  strip_tac >>
  drule take_request_outcome_success >> strip_tac >>
  ` (SND (adopt_call_outcome rq outcome es1)).requests = es1.requests` by
    (Cases_on `adopt_call_outcome rq outcome es1` >>
     rename1 `adopt_call_outcome rq outcome es1 = (answer,adopted)` >>
     drule adopt_call_outcome_frame >> strip_tac >>
     qpat_x_assum `adopted = _` (mp_tac o Q.AP_TERM `\st. st.requests`) >> simp[]) >>
  fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  `LENGTH s.vs_requests = LENGTH es.requests` by metis_tac[LIST_REL_LENGTH] >>
  `LIST_REL (request_agree H cx.txn.target) (es.requests ++ [rq]) u.vs_requests` by
    gvs[record_request_def] >>
  `LENGTH u.vs_requests = SUC (LENGTH es.requests) /\
   request_agree H cx.txn.target rq (EL (LENGTH es.requests) u.vs_requests)` by
    (qpat_assum `LIST_REL _ (es.requests ++ [rq]) _` mp_tac >>
     rewrite_tac[LIST_REL_EL_EQN] >>
     disch_then (CONJUNCTS_THEN2 assume_tac
       (qspec_then `LENGTH es.requests` mp_tac)) >>
     fs[EL_APPEND_EQN, ADD1]) >>
  Cases_on `s.vs_outcomes` >> gvs[take_outcome_ordinary, take_outcome_exhausted]
QED

Definition requests_outcomes_frame_def:
  requests_outcomes_frame f <=>
    state_rel_frame
      (\s t. LENGTH s.requests = recorded_outcomes_count s.storage_trace ==>
             LENGTH t.requests = recorded_outcomes_count t.storage_trace) f
End

Theorem requests_outcomes_frame_result:
  requests_outcomes_frame f /\ f st = (res,st') /\
  LENGTH st.requests = recorded_outcomes_count st.storage_trace ==>
  LENGTH st'.requests = recorded_outcomes_count st'.storage_trace
Proof
  simp[requests_outcomes_frame_def, state_rel_frame_result] >> metis_tac[]
QED

Triviality request_count_appends[simp]:
  recorded_outcomes_count (obs ++ [StorageOutcome rq outcome]) =
    SUC (recorded_outcomes_count obs) /\
  recorded_outcomes_count (obs ++ [StorageRoot b slot ty]) =
    recorded_outcomes_count obs /\
  recorded_outcomes_count (obs ++ [StorageLock slot]) =
    recorded_outcomes_count obs /\
  recorded_outcomes_count (obs ++ [StorageBackend accounts transient]) =
    recorded_outcomes_count obs
Proof
  simp[recorded_outcomes_count_def, FILTER_APPEND_DISTRIB, ADD1]
QED

Triviality request_count_paired:
  (LENGTH rqs = recorded_outcomes_count obs) ==>
  LENGTH (rqs ++ [rq]) = recorded_outcomes_count (obs ++ [StorageOutcome rq outcome])
Proof
  simp[request_count_appends]
QED

structure RF = s1PrefixRequestFrameLib
val frame_def = requests_outcomes_frame_def

Triviality requests_outcomes_frame_bind:
  requests_outcomes_frame f /\
  (!v. (?s t. f s = (INL v,t)) ==> requests_outcomes_frame (g v)) ==>
  requests_outcomes_frame (bind f g)
Proof
  RF.bind_tac frame_def
QED

Theorem requests_outcomes_frame_bind_all:
  requests_outcomes_frame f /\ (!v. requests_outcomes_frame (g v)) ==>
  requests_outcomes_frame (bind f g)
Proof
  simp[requests_outcomes_frame_bind]
QED

Triviality request_frame_try:
  requests_outcomes_frame f /\ (!e. requests_outcomes_frame (h e)) ==>
  requests_outcomes_frame (try f h)
Proof
  RF.try_tac frame_def
QED

Triviality request_frame_finally:
  requests_outcomes_frame f /\ requests_outcomes_frame h ==>
  requests_outcomes_frame (finally f h)
Proof
  RF.finally_tac frame_def
QED

Triviality request_frame_finally_unless_halt:
  requests_outcomes_frame f /\ requests_outcomes_frame h ==>
  requests_outcomes_frame (finally_unless_halt f h)
Proof
  RF.finally_unless_halt_tac frame_def
QED

Triviality request_frame_choice:
  (b ==> requests_outcomes_frame f) /\ (~b ==> requests_outcomes_frame g) ==>
  requests_outcomes_frame (if b then f else g)
Proof
  RF.choice_tac
QED

Theorem request_frame_primitives:
  requests_outcomes_frame (return v) /\
  requests_outcomes_frame (\s. return (f s) s) /\
  requests_outcomes_frame (\s. (INL (IS_SOME s.outcomes),s)) /\
  requests_outcomes_frame (raise e) /\
  requests_outcomes_frame (type_check b msg) /\
  requests_outcomes_frame (check b msg) /\
  requests_outcomes_frame (check_not_static cx) /\
  requests_outcomes_frame (lift_option opt msg) /\
  requests_outcomes_frame (lift_option_type opt msg) /\
  requests_outcomes_frame (lift_sum sum) /\
  requests_outcomes_frame (lift_sum_runtime rs) /\
  requests_outcomes_frame get_accounts /\
  requests_outcomes_frame get_transient_storage /\
  requests_outcomes_frame get_pending_deletions /\
  requests_outcomes_frame get_scopes /\
  requests_outcomes_frame (update_accounts fa) /\
  requests_outcomes_frame (update_transient ft) /\
  requests_outcomes_frame (update_pending_deletions fp) /\
  requests_outcomes_frame (push_log lg) /\
  requests_outcomes_frame (append_logs ls) /\
  requests_outcomes_frame (set_scopes scs) /\
  requests_outcomes_frame push_scope /\
  requests_outcomes_frame (push_scope_with_var nm ty value) /\
  requests_outcomes_frame (set_address_immutables cx imms) /\
  requests_outcomes_frame pop_scope /\
  requests_outcomes_frame (push_function fn sc cx) /\
  requests_outcomes_frame (pop_function scs) /\
  requests_outcomes_frame next_gas_reading /\
  requests_outcomes_frame record_storage_backend /\
  requests_outcomes_frame (record_storage_event (StorageRoot b' slot ty)) /\
  requests_outcomes_frame (record_storage_event (StorageLock slot))
Proof
  RF.primitives_tac frame_def request_count_appends
QED

Triviality request_frame_take_request:
  requests_outcomes_frame (take_request_outcome rq)
Proof
  RF.take_request_tac frame_def request_count_paired
QED

Triviality request_frame_take_create:
  requests_outcomes_frame (take_create_outcome kind amount code)
Proof
  RF.take_create_tac frame_def request_count_paired
QED

Triviality request_frame_take:
  requests_outcomes_frame (take_call_outcome gas_cap target data value) /\
  requests_outcomes_frame (take_delegate_outcome gas_cap target data value)
Proof
  RF.take_tac frame_def request_frame_take_request
QED

Triviality request_frame_adopt:
  requests_outcomes_frame (adopt_call_outcome rq outcome)
Proof
  RF.adopt_tac frame_def request_count_appends
QED

Triviality request_frame_state_unchanged:
  (!s res t. f s = (res,t) ==> t = s) ==> requests_outcomes_frame f
Proof
  RF.state_unchanged_tac frame_def
QED

Theorem requests_outcomes_frame_read_result:
  requests_outcomes_frame (read_result cx result)
Proof
  RF.read_result_tac request_frame_state_unchanged
QED

Triviality request_frame_reads:
  requests_outcomes_frame (read_place cx p) /\
  requests_outcomes_frame (place_type_value cx p) /\
  requests_outcomes_frame (read_results cx results) /\
  requests_outcomes_frame (conditional_result cx result) /\
  requests_outcomes_frame (get_place result)
Proof
  RF.reads_tac request_frame_state_unchanged
QED

val request_rules = [requests_outcomes_frame_bind, request_frame_try,
  request_frame_finally, request_frame_finally_unless_halt, request_frame_choice];
val request_step = RF.primitive_step request_rules;
val request_primitive_frames =
  [request_frame_primitives, request_frame_reads,
   requests_outcomes_frame_read_result, request_frame_take,
   request_frame_take_create, request_frame_adopt];
val REQUEST_PRIMITIVE_STEP = request_step request_primitive_frames;

Triviality request_frame_storage_backend:
  requests_outcomes_frame (get_storage_backend cx transient) /\
  requests_outcomes_frame (set_storage_backend cx transient backend)
Proof
  RF.storage_backend_tac REQUEST_PRIMITIVE_STEP
QED

Triviality request_frame_address_immutables:
  requests_outcomes_frame (get_address_immutables cx)
Proof
  RF.address_immutables_tac frame_def
QED

val request_storage_frames =
  request_frame_storage_backend :: request_frame_address_immutables ::
  request_primitive_frames;
val REQUEST_STORAGE_STEP = request_step request_storage_frames;

Triviality request_frame_resolve_array:
  requests_outcomes_frame (resolve_array_element cx tr slot ty subs)
Proof
  RF.resolve_array_tac request_frame_state_unchanged
QED

Triviality request_frame_storage_and_locals:
  requests_outcomes_frame (write_place cx place v) /\
  requests_outcomes_frame (lookup_flag_mem cx nsid mid) /\
  requests_outcomes_frame (set_variable nm v) /\
  requests_outcomes_frame (lookup_global cx src nm) /\
  requests_outcomes_frame (set_global cx src nm v)
Proof
  RF.storage_and_locals_tac REQUEST_STORAGE_STEP
QED

Triviality request_frame_extend_storage:
  !cx tr slot ty sb. requests_outcomes_frame (extend_storage_place cx tr slot ty sb)
Proof
  RF.extend_storage_tac
    (request_step (request_frame_resolve_array :: request_storage_frames))
QED

Triviality request_frame_extend_place:
  !cx result sb. requests_outcomes_frame (extend_place cx result sb)
Proof
  RF.extend_place_tac
    (request_step (request_frame_extend_storage :: request_storage_frames))
QED

Triviality request_frame_select:
  !cx ty result sb. requests_outcomes_frame (select_result cx ty result sb)
Proof
  RF.select_tac (request_step (request_frame_extend_place :: request_storage_frames))
QED

Triviality request_frame_array_length:
  !cx result. requests_outcomes_frame (result_array_length cx result)
Proof
  RF.array_length_tac REQUEST_STORAGE_STEP
QED

val request_place_frames =
  [request_frame_storage_and_locals, request_frame_extend_place,
   request_frame_select, request_frame_array_length] @ request_storage_frames;
val REQUEST_PLACE_STEP = request_step request_place_frames;

Triviality request_frame_append_place:
  !cx place v. requests_outcomes_frame (append_place cx place v)
Proof
  RF.append_place_tac REQUEST_PLACE_STEP
QED

Triviality request_frame_pop_place:
  !cx place. requests_outcomes_frame (pop_place cx place)
Proof
  RF.pop_place_tac REQUEST_PLACE_STEP
QED

Theorem request_frame_raw_call:
  requests_outcomes_frame (eval_raw_call cx flags target calldata amount gas)
Proof
  RF.raw_call_tac REQUEST_PRIMITIVE_STEP
QED

Triviality request_frame_ext_call:
  requests_outcomes_frame (eval_ext_call cx static_flag skip_check sigt opts vs)
Proof
  RF.ext_call_tac request_rules request_primitive_frames
QED

Triviality request_frame_send:
  requests_outcomes_frame (eval_send cx gas vs)
Proof
  RF.send_tac REQUEST_PRIMITIVE_STEP
QED

Triviality request_frame_create_oracle:
  requests_outcomes_frame (create_oracle_result salt value initcode rof)
Proof
  RF.create_oracle_tac frame_def requests_outcomes_frame_result
    request_frame_take_create request_frame_adopt
QED

Triviality request_frame_create:
  requests_outcomes_frame (eval_create cx kind has_salt rof arg_tys vs blueprint_size)
Proof
  RF.create_tac (request_step (request_frame_create_oracle :: request_primitive_frames))
QED

Triviality request_frame_precompile:
  requests_outcomes_frame (precompile_call_success bt vs)
Proof
  RF.precompile_tac frame_def requests_outcomes_frame_result request_frame_take
QED

Triviality request_frame_handle_function:
  requests_outcomes_frame (handle_function ex)
Proof
  RF.handle_function_tac REQUEST_PRIMITIVE_STEP
QED

val REQUEST_EVAL_CASE =
  RF.evaluate_case request_rules
    ([request_frame_precompile, request_frame_raw_call, request_frame_ext_call,
      request_frame_send, request_frame_create, request_frame_handle_function,
      request_frame_append_place, request_frame_pop_place] @ request_place_frames);

Theorem evaluate_requests_outcomes_frame:
  (!cx s. requests_outcomes_frame (eval_stmt cx s)) /\
  (!cx ss. requests_outcomes_frame (eval_stmts cx ss)) /\
  (!cx it. requests_outcomes_frame (eval_iterator cx it)) /\
  (!cx tyv nm body vs. requests_outcomes_frame (eval_for cx tyv nm body vs)) /\
  (!cx e. requests_outcomes_frame (eval_expr cx e)) /\
  (!cx es. requests_outcomes_frame (eval_exprs cx es)) /\
  (!cx t. requests_outcomes_frame (eval_base_place cx t)) /\
  (!cx t. requests_outcomes_frame (eval_target_place cx t)) /\
  (!cx t v. requests_outcomes_frame (assign_tuple_targets cx t v)) /\
  (!cx ts vs. requests_outcomes_frame (assign_tuple_target_list cx ts vs))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> REQUEST_EVAL_CASE
QED
