(* Context transport for reached GAS prefixes, including failing calls. *)
Theory gasEventsContext
Ancestors
  gasEventsFuel o1PassLift gasEvents venomExecSemantics venomExecProofs
  venomInstProps venomInst venomState stateFrame list rich_list arithmetic
  option pair passSimulationDefs

Theorem gas_events_istep_continue:
  get_instruction bb s.vs_inst_idx = SOME i /\
  ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u ==>
  ?m extra.
    gas_events_block m C owner bb s = gas_events_step k C owner i s ++
      gas_events_block n C owner bb (u with vs_inst_idx := SUC s.vs_inst_idx) ++ extra /\
    ((!e. exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx) <> Error e) ==>
      extra = [] /\ exec_block m C bb s =
        exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  qspecl_then [`k`, `C`, `owner`, `i`, `s`, `MAX k n`] mp_tac
    (cj 1 gas_events_fuel_extension) >>
  simp[] >> strip_tac >> gvs[] >>
  qspecl_then [`n`, `C`, `owner`, `bb`,
    `u with vs_inst_idx := SUC s.vs_inst_idx`, `MAX k n`] mp_tac
    (cj 2 gas_events_fuel_extension) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`MAX k n`, `extra`] >>
  simp[Once gas_events_block_def] >>
  strip_tac >> gvs[] >> simp[Once exec_block_def]
QED


Theorem invoke_result_terminates_callee[local]:
  terminates (invoke_result outs s r) ==> terminates r
Proof
  Cases_on `r` >> simp[invoke_result_def, terminates_def]
QED

Theorem gas_events_step_same_caller:
  (!nm. OPTREL (\f g. fn_entry_label g = fn_entry_label f)
    (lookup_function nm C.ctx_functions) (lookup_function nm D.ctx_functions)) /\
  (!nm f g cs.
    lookup_function nm C.ctx_functions = SOME f /\
    lookup_function nm D.ctx_functions = SOME g /\ fn_entry_state f cs ==>
    ?m extra. gas_events_blocks m D g cs = gas_events_blocks n C f cs ++ extra /\
      (terminates (run_blocks n C f cs) ==> extra = [] /\
        frame_result_rel (run_blocks n C f cs) (run_blocks m D g cs))) ==>
  ?m extra.
    gas_events_step m D owner i s = gas_events_step n C owner i s ++ extra /\
    (terminates (step_inst n C i s) ==> extra = [] /\
      step_result_rel (step_inst n C i s) (step_inst m D i s)) /\
    (!u. step_inst n C i s = OK u ==> step_inst m D i s = OK u)
Proof
  strip_tac >> reverse (Cases_on `i.inst_opcode = INVOKE`)
  >- (qexistsl_tac [`n`, `[]`] >>
      simp[gas_events_step_def, step_inst_non_invoke] >>
      Cases_on `step_inst_base i s` >>
      simp[terminates_def, step_result_rel_def, frame_result_rel_def]) >>
  Cases_on `decode_invoke i`
  >- (qexistsl_tac [`n`, `[]`] >>
      simp[gas_events_step_def, step_inst_def, terminates_def]) >>
  PairCases_on `x` >>
  qpat_x_assum `!nm. OPTREL _ _ _` (qspec_then `x0` mp_tac) >>
  Cases_on `lookup_function x0 C.ctx_functions` >>
  Cases_on `lookup_function x0 D.ctx_functions` >> simp[OPTREL_def]
  >- (qexistsl_tac [`n`, `[]`] >>
      simp[gas_events_step_def, step_inst_def, terminates_def]) >>
  strip_tac >> rename1 `fn_entry_label g = fn_entry_label f` >>
  `setup_callee g = setup_callee f` by
    (simp[FUN_EQ_THM] >> metis_tac[setup_callee_entry_label]) >>
  Cases_on `eval_operands x1 s`
  >- (qexistsl_tac [`n`, `[]`] >>
      simp[gas_events_step_def, step_inst_def, terminates_def]) >>
  Cases_on `setup_callee f x s`
  >- (qexistsl_tac [`n`, `[]`] >>
      simp[gas_events_step_def, step_inst_def, terminates_def]) >>
  suspend "callee"
QED

Resume gas_events_step_same_caller[callee]:
  drule setup_callee_fn_entry_state >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`m`, `extra`] >>
  simp[gas_events_step_def] >>
  simp[step_inst_def, GSYM invoke_result_def] >>
  `terminates (invoke_result i.inst_outputs s (run_blocks n C f x')) ==>
    extra = [] /\ step_result_rel
      (invoke_result i.inst_outputs s (run_blocks n C f x'))
      (invoke_result i.inst_outputs s (run_blocks m D g x'))` by
    (strip_tac >>
     drule invoke_result_terminates_callee >> strip_tac >>
     first_x_assum drule >> strip_tac >>
     simp[] >> irule frame_result_rel_invoke >> simp[]) >>
  conj_tac >- simp[] >>
  rpt strip_tac >>
  `terminates (invoke_result i.inst_outputs s (run_blocks n C f x'))` by
    simp[terminates_def] >>
  first_x_assum drule >>
  Cases_on `invoke_result i.inst_outputs s (run_blocks m D g x')` >>
  simp[step_result_rel_def, frame_result_rel_def]
QED
Finalise gas_events_step_same_caller

Theorem gas_events_block_same_caller_distance[local]:
  !d C D n owner bb s.
  LENGTH bb.bb_instructions - s.vs_inst_idx = d /\
  (!nm. OPTREL (\f g. fn_entry_label g = fn_entry_label f)
    (lookup_function nm C.ctx_functions) (lookup_function nm D.ctx_functions)) /\
  (!nm f g cs.
    lookup_function nm C.ctx_functions = SOME f /\
    lookup_function nm D.ctx_functions = SOME g /\ fn_entry_state f cs ==>
    ?m extra. gas_events_blocks m D g cs = gas_events_blocks n C f cs ++ extra /\
      (terminates (run_blocks n C f cs) ==> extra = [] /\
        frame_result_rel (run_blocks n C f cs) (run_blocks m D g cs))) ==>
  ?m extra.
    gas_events_block m D owner bb s = gas_events_block n C owner bb s ++ extra /\
    (terminates (exec_block n C bb s) ==> extra = [] /\
      step_result_rel (exec_block n C bb s) (exec_block m D bb s)) /\
    (!u. exec_block n C bb s = OK u ==> exec_block m D bb s = OK u)
Proof
  completeInduct_on `d` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qexistsl_tac [`n`, `[]`] >>
      ntac 2 (once_rewrite_tac[gas_events_block_def, exec_block_def] >> simp[terminates_def])) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME i` >>
  drule_all gas_events_step_same_caller >>
  disch_then (qspecl_then [`s`, `owner`, `i`] strip_assume_tac) >>
  Cases_on `step_inst n C i s`
  >- suspend "ok" >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  qpat_x_assum `!nm f g cs. _` kall_tac >>
  qpat_x_assum `!nm. OPTREL _ _ _` kall_tac >>
  qexists_tac `m` >>
  Cases_on `step_inst m D i s` >>
  gvs[terminates_def, step_result_rel_def, frame_result_rel_def] >>
  ntac 2 (once_rewrite_tac[gas_events_block_def, exec_block_def] >> simp[]) >>
  metis_tac[APPEND_ASSOC]
QED

Resume gas_events_block_same_caller_distance[ok]:
  rename1 `step_inst n C i s = OK u` >>
  `step_inst m D i s = OK u /\ extra = []` by
    simp[terminates_def] >>
  Cases_on `is_terminator i.inst_opcode`
  >- (qexistsl_tac [`m`, `[]`] >>
      ntac 2 (once_rewrite_tac[gas_events_block_def, exec_block_def] >> simp[]) >>
      Cases_on `u.vs_halted` >> simp[step_result_rel_def, frame_result_rel_def]) >>
  suspend "continue"
QED

Resume gas_events_block_same_caller_distance[continue]:
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `?j tail.
    gas_events_block j D owner bb (u with vs_inst_idx := SUC s.vs_inst_idx) =
      gas_events_block n C owner bb (u with vs_inst_idx := SUC s.vs_inst_idx) ++ tail /\
    (terminates (exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx)) ==>
      tail = [] /\ step_result_rel
        (exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx))
        (exec_block j D bb (u with vs_inst_idx := SUC s.vs_inst_idx))) /\
    (!z. exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx) = OK z ==>
      exec_block j D bb (u with vs_inst_idx := SUC s.vs_inst_idx) = OK z)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule_all gas_events_istep_continue >>
  disch_then (qspecl_then [`owner`, `j`] strip_assume_tac) >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  qpat_x_assum `!nm f g cs. _` kall_tac >>
  qpat_x_assum `!nm. OPTREL _ _ _` kall_tac >>
  qexistsl_tac [`m'`, `tail ++ extra'`] >>
  `gas_events_block n C owner bb s = gas_events_step n C owner i s ++
     gas_events_block n C owner bb (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Once gas_events_block_def] >>
  `exec_block n C bb s = exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Once exec_block_def, SimpLHS] >>
  conj_tac >- gvs[APPEND_ASSOC] >>
  `terminates (exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx)) ==>
    (!err. exec_block j D bb (u with vs_inst_idx := SUC s.vs_inst_idx) <> Error err)` by
    (Cases_on `exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx)` >>
     Cases_on `exec_block j D bb (u with vs_inst_idx := SUC s.vs_inst_idx)` >>
     gvs[terminates_def, step_result_rel_def, frame_result_rel_def]) >>
  conj_tac >- (strip_tac >> gvs[]) >>
  rpt strip_tac >>
  `terminates (exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (Cases_on `exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx)` >>
     fs[terminates_def]) >>
  gvs[] >> metis_tac[]
QED
Finalise gas_events_block_same_caller_distance

Theorem gas_events_block_same_caller:
  (!nm. OPTREL (\f g. fn_entry_label g = fn_entry_label f)
    (lookup_function nm C.ctx_functions) (lookup_function nm D.ctx_functions)) /\
  (!nm f g cs.
    lookup_function nm C.ctx_functions = SOME f /\
    lookup_function nm D.ctx_functions = SOME g /\ fn_entry_state f cs ==>
    ?m extra. gas_events_blocks m D g cs = gas_events_blocks n C f cs ++ extra /\
      (terminates (run_blocks n C f cs) ==> extra = [] /\
        frame_result_rel (run_blocks n C f cs) (run_blocks m D g cs))) ==>
  ?m extra.
    gas_events_block m D owner bb s = gas_events_block n C owner bb s ++ extra /\
    (terminates (exec_block n C bb s) ==> extra = [] /\
      step_result_rel (exec_block n C bb s) (exec_block m D bb s)) /\
    (!u. exec_block n C bb s = OK u ==> exec_block m D bb s = OK u)
Proof
  strip_tac >> irule gas_events_block_same_caller_distance >>
  simp[] >> metis_tac[]
QED

Theorem gas_events_blocks_same_caller:
  !N C D h s.
  (!nm. OPTREL (\f g. fn_entry_label g = fn_entry_label f)
    (lookup_function nm C.ctx_functions) (lookup_function nm D.ctx_functions)) /\
  (!j nm f g cs. j < N /\
    lookup_function nm C.ctx_functions = SOME f /\
    lookup_function nm D.ctx_functions = SOME g /\ fn_entry_state f cs ==>
    ?m extra. gas_events_blocks m D g cs = gas_events_blocks j C f cs ++ extra /\
      (terminates (run_blocks j C f cs) ==> extra = [] /\
        frame_result_rel (run_blocks j C f cs) (run_blocks m D g cs))) ==>
  ?m extra. gas_events_blocks m D h s = gas_events_blocks N C h s ++ extra /\
    (terminates (run_blocks N C h s) ==> extra = [] /\
      frame_result_rel (run_blocks N C h s) (run_blocks m D h s))
Proof
  Induct_on `N`
  >- (rpt strip_tac >> qexistsl_tac [`0`, `[]`] >>
      ntac 2 (once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >> simp[terminates_def])) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb h.fn_blocks`
  >- (qexistsl_tac [`SUC N`, `[]`] >>
      ntac 2 (once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >> simp[terminates_def])) >>
  rename1 `lookup_block s.vs_current_bb h.fn_blocks = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions`
  >- suspend "phis_ok" >>
  mp_tac (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >> simp[] >>
  qexistsl_tac [`SUC N`, `[]`] >>
  ntac 2 (once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >> simp[terminates_def])
QED

Resume gas_events_blocks_same_caller[phis_ok]:
  rename1 `eval_phis s bb.bb_instructions = OK p` >>
  `?k extra. gas_events_block k D h.fn_name bb
       (p with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
     gas_events_block N C h.fn_name bb
       (p with vs_inst_idx := phi_prefix_length bb.bb_instructions) ++ extra /\
    (terminates (exec_block N C bb (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)) ==>
      extra = [] /\ step_result_rel
        (exec_block N C bb (p with vs_inst_idx := phi_prefix_length bb.bb_instructions))
        (exec_block k D bb (p with vs_inst_idx := phi_prefix_length bb.bb_instructions))) /\
    (!u. exec_block N C bb (p with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK u ==>
      exec_block k D bb (p with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK u)` by
    (irule gas_events_block_same_caller >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  Cases_on `exec_block N C bb (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)`
  >- suspend "ok" >>
  qpat_x_assum `!j nm f g cs. j < _ /\ _ ==> _` kall_tac >>
  qpat_x_assum `!C D h s. _ /\ _ ==> _` kall_tac >>
  qpat_x_assum `!nm. OPTREL _ _ _` kall_tac >>
  qexists_tac `SUC k` >>
  qexists_tac `extra ++ (case exec_block k D bb
    (p with vs_inst_idx := phi_prefix_length bb.bb_instructions) of
      OK u => if u.vs_halted then [] else gas_events_blocks k D h u
    | _ => [])` >>
  pure_once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >>
  simp[terminates_def, APPEND_ASSOC] >>
  Cases_on `exec_block k D bb (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  gvs[terminates_def, step_result_rel_def, frame_result_rel_def] >>
  simp[Once gas_events_blocks_def]
QED

Resume gas_events_blocks_same_caller[ok]:
  rename1 `exec_block N C bb (p with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK u` >>
  `exec_block k D bb (p with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK u` by metis_tac[] >>
  `extra = []` by fs[terminates_def] >>
  gvs[] >>
  Cases_on `u.vs_halted`
  >- (qexistsl_tac [`SUC k`, `[]`] >>
      pure_once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >>
      simp[frame_result_rel_def]) >>
  `?m tail. gas_events_blocks m D h u = gas_events_blocks N C h u ++ tail /\
    (terminates (run_blocks N C h u) ==> tail = [] /\
      frame_result_rel (run_blocks N C h u) (run_blocks m D h u))` by
    (qpat_x_assum `!C D h s. _ /\ _ ==> _` irule >> simp[] >> rpt strip_tac >>
     `j < SUC N` by simp[] >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  suspend "sync"
QED

Resume gas_events_blocks_same_caller[sync]:
  qpat_x_assum `!j nm f g cs. j < _ /\ _ ==> _` kall_tac >>
  qpat_x_assum `!C D h s. _ /\ _ ==> _` kall_tac >>
  qpat_x_assum `!nm. OPTREL _ _ _` kall_tac >>
  `k <= MAX k m` by simp[] >>
  drule (cj 2 gas_events_fuel_extension) >>
  disch_then (qspecl_then [`D`, `h.fn_name`, `bb`,
    `p with vs_inst_idx := phi_prefix_length bb.bb_instructions`] mp_tac) >>
  simp[] >> strip_tac >>
  `m <= MAX k m` by simp[] >>
  drule (cj 3 gas_events_fuel_extension) >>
  disch_then (qspecl_then [`D`, `h`, `u`] strip_assume_tac) >>
  rename1 `gas_events_blocks (MAX k m) D h u = gas_events_blocks m D h u ++ more` >>
  qexistsl_tac [`SUC (MAX k m)`, `tail ++ more`] >>
  pure_once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >>
  simp[APPEND_ASSOC] >>
  suspend "exact"
QED

Resume gas_events_blocks_same_caller[exact]:
  strip_tac >>
  `frame_result_rel (run_blocks N C h u) (run_blocks m D h u)` by metis_tac[] >>
  drule frame_result_rel_terminates >> strip_tac >>
  `!err. run_blocks m D h u <> Error err` by
    (Cases_on `run_blocks m D h u` >> gvs[terminates_def]) >>
  gvs[]
QED

Finalise gas_events_blocks_same_caller
