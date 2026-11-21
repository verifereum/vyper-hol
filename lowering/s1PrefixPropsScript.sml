(* Checked GAS focuses and the source request-count invariant. *)
Theory s1PrefixProps
Ancestors
  s1PrefixDefs fragGasOriginPtr fragGasOriginEvents fragGasOrigin fragGasPath fragGasPathPtr
  fragExec gasEvents gasEventsFuel gasSummary gasOutcomeFull
  ptrSafeRun memSafeRun fragGasFocus venomExecSemantics venomExecProofs
  venomInstProofs venomInst venomState e2eRequestCutDefs extCallOracle
  vyperState vyperCallOutcome vyperCallOutcomeProps vyperCallOutcomeFrame
  vyperMachineFrame vyperStatePreservation vyperInterpreter vyperCreate
  vyperPlaceFrames vyperStorageTrace list pair sum rich_list arithmetic
Libs monadsyntax evalWalkLib

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
  (!tail res ee obs_pre rq outcome sfx H.
     LENGTH es.requests = recorded_outcomes_count es.storage_trace /\
     source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (res, ee) /\
     ee.storage_trace = obs_pre ++ StorageOutcome rq outcome :: sfx /\
     LENGTH es.storage_trace <= LENGTH obs_pre /\
     valid_horizon cx st0 H obs_pre /\ ~computed_precompile rq ==>
     request_site (DF H, lo, explicit, ctx, func, PG) cx H (s, G, tn)
       (recorded_outcomes_count obs_pre) rq outcome) ==>
  !tail res ee obs_pre rq outcome sfx H.
    LENGTH es.requests = recorded_outcomes_count es.storage_trace /\
    source (es with gas_obs := gas_explicit (marks ++ ext) s.vs_gas_readings ++ tail) =
      (res, ee) /\
    ee.storage_trace = obs_pre ++ StorageOutcome rq outcome :: sfx /\
    LENGTH es.storage_trace <= LENGTH obs_pre /\
    valid_horizon cx st0 H obs_pre /\ ~computed_precompile rq ==>
    request_site (DF H, lo, explicit, ctx, func, PG) cx H (s, G, tn)
      (recorded_outcomes_count obs_pre) rq outcome
Proof
  PURE_REWRITE_TAC[gas_explicit_append, GSYM APPEND_ASSOC] >>
  metis_tac[]
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

Triviality requests_outcomes_frame_bind:
  requests_outcomes_frame f /\
  (!v. (?s t. f s = (INL v,t)) ==> requests_outcomes_frame (g v)) ==>
  requests_outcomes_frame (bind f g)
Proof
  simp[requests_outcomes_frame_def] >> strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[] >> metis_tac[]
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
  simp[requests_outcomes_frame_def] >> strip_tac >>
  irule state_rel_frame_try >> simp[]
QED

Triviality request_frame_finally:
  requests_outcomes_frame f /\ requests_outcomes_frame h ==>
  requests_outcomes_frame (finally f h)
Proof
  simp[requests_outcomes_frame_def] >> strip_tac >>
  irule state_rel_frame_finally >> simp[]
QED

Triviality request_frame_finally_unless_halt:
  requests_outcomes_frame f /\ requests_outcomes_frame h ==>
  requests_outcomes_frame (finally_unless_halt f h)
Proof
  simp[requests_outcomes_frame_def] >> strip_tac >>
  irule state_rel_frame_finally_unless_halt >> simp[]
QED

Triviality request_frame_choice:
  (b ==> requests_outcomes_frame f) /\ (~b ==> requests_outcomes_frame g) ==>
  requests_outcomes_frame (if b then f else g)
Proof
  Cases_on `b` >> simp[]
QED

Triviality request_frame_primitives:
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
  rpt conj_tac >> simp[requests_outcomes_frame_def, state_rel_frame_def,
    return_def, raise_def, type_check_def, check_def, assert_def,
    check_not_static_def, lift_option_def, lift_option_type_def,
    lift_sum_def, lift_sum_runtime_def, get_accounts_def,
    get_transient_storage_def, get_pending_deletions_def, get_scopes_def,
    update_accounts_def, update_transient_def, update_pending_deletions_def,
    push_log_def, append_logs_def, set_scopes_def, push_scope_def,
    push_scope_with_var_def, set_address_immutables_def, pop_scope_def,
    push_function_def, pop_function_def, next_gas_reading_def,
    record_storage_backend_def, record_storage_event_def] >>
  rpt strip_tac >> rpt BasicProvers.TOP_CASE_TAC >> simp[return_def, raise_def]
QED

Triviality request_frame_take_request:
  requests_outcomes_frame (take_request_outcome rq)
Proof
  simp[requests_outcomes_frame_def, state_rel_frame_def] >>
  qx_gen_tac `st` >> Cases_on `st.outcomes` >> simp[take_request_outcome_def] >>
  rename1 `st.outcomes = SOME os` >> Cases_on `os` >>
  simp[take_request_outcome_def] >> pairarg_tac >>
  simp[record_request_def] >> IF_CASES_TAC >> simp[]
QED

Triviality request_frame_take_create:
  requests_outcomes_frame (take_create_outcome kind amount code)
Proof
  simp[requests_outcomes_frame_def, state_rel_frame_def] >>
  qx_gen_tac `st` >> Cases_on `st.outcomes` >> simp[take_create_outcome_def] >>
  rename1 `st.outcomes = SOME os` >> Cases_on `os` >>
  simp[take_create_outcome_def] >> pairarg_tac >>
  simp[record_request_def] >> IF_CASES_TAC >> simp[]
QED

Triviality request_frame_take:
  requests_outcomes_frame (take_call_outcome gas_cap target data value) /\
  requests_outcomes_frame (take_delegate_outcome gas_cap target data value)
Proof
  simp[requests_outcomes_frame_def, state_rel_frame_def,
       take_call_outcome_def, take_delegate_outcome_def] >>
  metis_tac[REWRITE_RULE[requests_outcomes_frame_def, state_rel_frame_def]
    (GEN_ALL request_frame_take_request)]
QED

Triviality request_frame_adopt:
  requests_outcomes_frame (adopt_call_outcome rq outcome)
Proof
  Cases_on `rq.cr_static` >> Cases_on `outcome.co_success` >>
  Cases_on `rq.cr_kind = MessageCall` >> Cases_on `rq.cr_kind = DelegateMessageCall` >>
  simp[requests_outcomes_frame_def, state_rel_frame_def, adopt_call_outcome_equation]
QED

Triviality request_frame_state_unchanged:
  (!s res t. f s = (res,t) ==> t = s) ==> requests_outcomes_frame f
Proof
  simp[requests_outcomes_frame_def, state_rel_frame_result] >> metis_tac[]
QED

Triviality request_frame_reads:
  requests_outcomes_frame (read_place cx p) /\
  requests_outcomes_frame (place_type_value cx p) /\
  requests_outcomes_frame (read_result cx result) /\
  requests_outcomes_frame (read_results cx results) /\
  requests_outcomes_frame (conditional_result cx result) /\
  requests_outcomes_frame (get_place result)
Proof
  rpt conj_tac >> irule request_frame_state_unchanged >>
  metis_tac[read_place_state, place_type_value_state, read_result_state,
            read_results_state, conditional_result_state, get_place_state]
QED

fun request_walk leaves unfolds =
  let
    val rules = [requests_outcomes_frame_bind, request_frame_try,
      request_frame_finally, request_frame_finally_unless_halt, request_frame_choice]
    val atoms = List.concat (map (CONJUNCTS o SPEC_ALL) leaves)
    val net = evalWalkLib.walk_net (map SPEC_ALL rules)
      (map (fn th => (concl th, MATCH_ACCEPT_TAC th)) atoms)
    val ih = evalWalkLib.IH_TAC {stop = K false,
      normalise = SIMP_RULE bool_ss
        [oneTheory.one, ignore_bind_def, FST, SND, pair_case_thm, UNCURRY,
         lock_if_nr_def, unlock_if_nr_def]}
  in
    evalWalkLib.STEP {net = net, at = RAND_CONV, unfolds = unfolds,
      intros = [CONV_TAC (HO_REWR_CONV FORALL_PROD), gen_tac, strip_tac, conj_tac,
        CONV_TAC (RAND_CONV ETA_CONV),
        CHANGED_TAC (fn (asl,w) => simp_tac bool_ss
          (pair_case_thm :: UNCURRY :: List.map ASSUME (List.filter is_eq asl)) (asl,w))],
      fallbacks = [ih, evalWalkLib.NORMALISE_IH_TAC ih]}
  end;

val request_primitive_frames =
  [request_frame_primitives, request_frame_reads, request_frame_take,
   request_frame_take_create, request_frame_adopt];

val request_common_unfolds =
  [ignore_bind_def, switch_BoolV_def, check_not_static_def,
   get_storage_backend_def, set_storage_backend_def, read_storage_slot_def,
   write_storage_slot_def, get_address_immutables_def, get_immutables_def,
   set_immutable_def, new_variable_def, transfer_value_def,
   send_call_value_def, frame_call_value_def, handle_loop_exception_def,
   handle_function_def, acquire_nonreentrant_lock_def,
   release_nonreentrant_lock_def, lock_if_nr_def, unlock_if_nr_def,
   create_soft_failure_def, check_create_blueprint_def];

val REQUEST_PRIMITIVE_STEP =
  request_walk request_primitive_frames request_common_unfolds;

Triviality request_frame_storage_backend:
  requests_outcomes_frame (get_storage_backend cx transient) /\
  requests_outcomes_frame (set_storage_backend cx transient backend)
Proof
  Cases_on `transient` >> simp[get_storage_backend_def, set_storage_backend_def] >>
  rpt REQUEST_PRIMITIVE_STEP
QED

Triviality request_frame_address_immutables:
  requests_outcomes_frame (get_address_immutables cx)
Proof
  simp[requests_outcomes_frame_def, state_rel_frame_def,
       get_address_immutables_def, lift_option_type_def] >>
  qx_gen_tac `st` >> Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  simp[return_def, raise_def]
QED

val request_storage_frames =
  request_frame_storage_backend :: request_frame_address_immutables ::
  request_primitive_frames;

val REQUEST_STORAGE_STEP = request_walk request_storage_frames request_common_unfolds;

Triviality request_frame_resolve_array:
  requests_outcomes_frame (resolve_array_element cx tr slot ty subs)
Proof
  irule request_frame_state_unchanged >> metis_tac[resolve_array_element_state]
QED

Triviality request_frame_storage_and_locals:
  requests_outcomes_frame (write_place cx place v) /\
  requests_outcomes_frame (lookup_flag_mem cx nsid mid) /\
  requests_outcomes_frame (set_variable nm v) /\
  requests_outcomes_frame (lookup_global cx src nm) /\
  requests_outcomes_frame (set_global cx src nm v)
Proof
  rpt conj_tac >>
  PURE_REWRITE_TAC[write_place_def, lookup_flag_mem_def, set_variable_def,
                   lookup_global_def, set_global_def]
  >- (Cases_on `place` >> pure_rewrite_tac[write_place_def] >>
      rpt REQUEST_STORAGE_STEP)
  >- (PairCases_on `nsid` >> pure_rewrite_tac[lookup_flag_mem_def] >>
      rpt REQUEST_STORAGE_STEP) >>
  rpt REQUEST_STORAGE_STEP
QED

Triviality request_frame_extend_storage:
  !cx tr slot ty sb. requests_outcomes_frame (extend_storage_place cx tr slot ty sb)
Proof
  recInduct extend_storage_place_ind >> rpt strip_tac >>
  pure_rewrite_tac[extend_storage_place_def] >>
  rpt (request_walk (request_frame_resolve_array :: request_storage_frames)
    request_common_unfolds)
QED

Triviality request_frame_extend_place:
  !cx result sb. requests_outcomes_frame (extend_place cx result sb)
Proof
  recInduct extend_place_ind >> rpt strip_tac >>
  pure_rewrite_tac[extend_place_def] >>
  rpt (request_walk (request_frame_extend_storage :: request_storage_frames)
    request_common_unfolds)
QED

Triviality request_frame_select:
  !cx ty result sb. requests_outcomes_frame (select_result cx ty result sb)
Proof
  recInduct select_result_ind >> rpt strip_tac >>
  pure_rewrite_tac[select_result_def] >>
  rpt (request_walk (request_frame_extend_place :: request_storage_frames)
    request_common_unfolds)
QED

Triviality request_frame_array_length:
  !cx result. requests_outcomes_frame (result_array_length cx result)
Proof
  recInduct result_array_length_ind >> rpt strip_tac >>
  pure_rewrite_tac[result_array_length_def] >> rpt REQUEST_STORAGE_STEP
QED

val request_place_frames =
  [request_frame_storage_and_locals, request_frame_extend_place,
   request_frame_select, request_frame_array_length] @ request_storage_frames;

val REQUEST_PLACE_STEP = request_walk request_place_frames request_common_unfolds;

Triviality request_frame_append_place:
  !cx place v. requests_outcomes_frame (append_place cx place v)
Proof
  recInduct append_place_ind >> rpt strip_tac >>
  pure_rewrite_tac[append_place_def] >> rpt REQUEST_PLACE_STEP
QED

Triviality request_frame_pop_place:
  !cx place. requests_outcomes_frame (pop_place cx place)
Proof
  recInduct pop_place_ind >> rpt strip_tac >>
  pure_rewrite_tac[pop_place_def] >> rpt REQUEST_PLACE_STEP
QED

Triviality request_frame_raw_call:
  requests_outcomes_frame (eval_raw_call cx flags target calldata amount gas)
Proof
  pure_rewrite_tac[eval_raw_call_def] >> rpt REQUEST_PRIMITIVE_STEP
QED

Triviality request_frame_ext_call:
  requests_outcomes_frame (eval_ext_call cx static_flag skip_check sigt opts vs)
Proof
  PairCases_on `sigt` >> Cases_on `vs` >>
  simp[eval_ext_call_def] >>
  rpt (request_walk request_primitive_frames
    (eval_ext_call_effects_def :: request_common_unfolds))
QED

Triviality request_frame_send:
  requests_outcomes_frame (eval_send cx gas vs)
Proof
  Cases_on `vs` >> simp[eval_send_def]
  >- rpt REQUEST_PRIMITIVE_STEP >>
  Cases_on `t` >> simp[eval_send_def] >> rpt REQUEST_PRIMITIVE_STEP
QED

Triviality request_frame_create_oracle:
  requests_outcomes_frame (create_oracle_result salt value initcode rof)
Proof
  simp[requests_outcomes_frame_def, state_rel_frame_def] >>
  qx_gen_tac `st` >> strip_tac >>
  qabbrev_tac `kind = case salt of NONE => CreateCall | SOME s => Create2Call s` >>
  Cases_on `take_create_outcome kind value initcode st` >>
  rename1 `take_create_outcome kind value initcode st = (res,mid)` >>
  `LENGTH mid.requests = recorded_outcomes_count mid.storage_trace` by
    metis_tac[requests_outcomes_frame_result, request_frame_take_create] >>
  pure_rewrite_tac[create_oracle_result_def] >> qpat_assum `Abbrev (kind = _)`
    (fn th => simp [GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
  Cases_on `res` >> gvs[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `adopt_call_outcome x0 x1 mid` >>
  `LENGTH r.requests = recorded_outcomes_count r.storage_trace` by
    metis_tac[requests_outcomes_frame_result, request_frame_adopt] >>
  rw[]
QED

Triviality request_frame_create:
  requests_outcomes_frame (eval_create cx kind has_salt rof arg_tys vs blueprint_size)
Proof
  pure_rewrite_tac[eval_create_def] >>
  rpt (request_walk (request_frame_create_oracle :: request_primitive_frames)
    request_common_unfolds)
QED

Triviality request_frame_precompile:
  requests_outcomes_frame (precompile_call_success bt vs)
Proof
  rewrite_tac[requests_outcomes_frame_def, state_rel_frame_def] >>
  qx_gen_tac `st` >>
  Cases_on `precompile_builtin bt` >> simp[precompile_call_success_def, return_def] >>
  Cases_on `st.outcomes` >> simp[return_def] >>
  rename1 `st.outcomes = SOME os` >> Cases_on `os` >>
  simp[check_def, assert_def, bind_def, take_call_outcome_def,
       take_request_outcome_def, call_outcome_request_def] >>
  pairarg_tac >> simp[bind_def, check_def, assert_def, record_request_def, AllCaseEqs()] >>
  Cases_on `outcome.co_success` >> simp[]
QED

Triviality request_frame_handle_function:
  requests_outcomes_frame (handle_function ex)
Proof
  Cases_on `ex` >> simp[handle_function_def] >> rpt REQUEST_PRIMITIVE_STEP
QED

val REQUEST_EVAL_STEP =
  request_walk
    ([request_frame_precompile, request_frame_raw_call, request_frame_ext_call,
      request_frame_send, request_frame_create, request_frame_handle_function,
      request_frame_append_place, request_frame_pop_place] @ request_place_frames)
    ([conditional_result_def, array_iterator_results_def, eval_create_operands_def] @
     request_common_unfolds);

val REQUEST_EVAL_CASE = evalWalkLib.EVAL_CASE (rpt strip_tac) REQUEST_EVAL_STEP;

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
