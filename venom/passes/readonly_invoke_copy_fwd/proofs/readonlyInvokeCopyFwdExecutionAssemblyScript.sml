(* Raw positional execution, NOP removal, and the indexed recursive family. *)
Theory readonlyInvokeCopyFwdExecutionAssembly
Ancestors
  readonlyInvokeCopyFwdExecutionForward
  readonlyInvokeCopyFwdExecutionSteps readonlyInvokeCopyFwdExecutionReturnBridge
  readonlyInvokeCopyFwdExecutionBoundary readonlyInvokeCopyFwdExecutionCoverage
  readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionShape
  readonlyInvokeCopyFwdAnalyzedOrigins readonlyInvokeCopyFwdExecutionHistory
  readonlyInvokeCopyFwdDefs invokeCopyFwdCommonDefs
  reachableFnSim passSharedProps passSharedDefs passSimulationProps ptrDisciplineControl
  passSimulationDefs o1PassContract unitShapeDefs ptrDiscipline
  venomWf contextCodegenRel ctxLookupAgreeHelpers venomExecProps venomExecProofs venomRetProps
  venomExecSemantics venomState venomInst list finite_map arithmetic

Theorem ricf_inst_edit_phi[local]:
  ricf_inst_edit inst target ==>
  (target.inst_opcode = PHI <=> inst.inst_opcode = PHI)
Proof
  rw[ricf_inst_edit_def] >> gvs[]
QED

Theorem ricf_block_edit_well_formed:
  ricf_block_edit bb tb /\ bb_well_formed bb ==> bb_well_formed tb
Proof
  strip_tac >> drule ricf_block_edit_EL >> strip_tac >>
  `!i. i < LENGTH bb.bb_instructions ==>
    (is_terminator (EL i tb.bb_instructions).inst_opcode <=>
      is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    ((EL i tb.bb_instructions).inst_opcode = PHI <=>
      (EL i bb.bb_instructions).inst_opcode = PHI)` by
    metis_tac[ricf_inst_edit_terminator, ricf_inst_edit_phi] >>
  `tb.bb_instructions <> [] /\ bb.bb_instructions <> []` by
    (fs[bb_well_formed_def] >> metis_tac[LENGTH_NIL]) >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  gvs[bb_well_formed_def, LAST_EL] >> metis_tac[]
QED

(* Exported lookup/PHI facts are shared with Boundary, so there is only one
   induction proving that function edits preserve the positional block map. *)
Theorem ricf_execution_raw_block:
  ricf_function_edit fn mid /\ wf_function fn /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  ?tb. lookup_block lbl mid.fn_blocks = SOME tb /\
    ricf_block_edit bb tb /\ bb_well_formed tb /\
    phi_prefix_length bb.bb_instructions = phi_prefix_length tb.bb_instructions /\
    (!s. eval_phis s bb.bb_instructions = eval_phis s tb.bb_instructions)
Proof
  rw[ricf_function_edit_def] >>
  drule_all readonlyInvokeCopyFwdExecutionBoundaryTheory.ricf_block_edits_lookup >>
  strip_tac >> qexists_tac `bc` >> simp[] >>
  `bb_well_formed bb` by
    (fs[wf_function_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  conj_tac >- metis_tac[ricf_block_edit_well_formed] >>
  metis_tac[ricf_block_edit_def,
    readonlyInvokeCopyFwdExecutionBoundaryTheory.ricf_inst_edits_phis]
QED

(* This enters the raw target from the actual source PHI evaluation, not
   from an assumed post-entry relation.  Coverage is vacuous at that prefix. *)
Theorem ricf_execution_run_entry:
  ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn s t /\
  ricf_function_edit fn (mid_of fn) /\ wf_function fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  terminates (run_block k C bb s) ==>
  ?tb s1 t1 inst.
    lookup_block t.vs_current_bb (mid_of fn).fn_blocks = SOME tb /\
    ricf_block_edit bb tb /\ bb_well_formed tb /\
    enters_block fn s s1 /\ enters_block (mid_of fn) t t1 /\
    get_instruction bb s1.vs_inst_idx = SOME inst /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG G tn fn inst s1 t1 /\
    run_block k C bb s = exec_block k C bb s1 /\
    (!m. run_block m Ct tb t = exec_block m Ct tb t1)
Proof
  strip_tac >>
  `?sp. eval_phis s bb.bb_instructions = OK sp` by
    (qpat_x_assum `terminates (run_block _ _ _ _)` mp_tac >>
     qspecl_then [`s`,`bb.bb_instructions`] strip_assume_tac
       eval_phis_ok_or_error_defs >> simp[run_block_def, terminates_def]) >>
  qabbrev_tac `s1 = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  `sp.vs_current_bb = s.vs_current_bb` by
    (drule eval_phis_only_updates_vs_vars >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `enters_block fn s s1 /\ terminates (exec_block k C bb s1)` by
    fs[enters_block_def, run_block_def, Abbr `s1`] >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
    (spose_not_then assume_tac >>
     qpat_x_assum `terminates (exec_block _ _ _ _)` mp_tac >>
     simp[Once exec_block_def, get_instruction_def, terminates_def, Abbr `s1`]) >>
  qabbrev_tac `inst = EL (phi_prefix_length bb.bb_instructions) bb.bb_instructions` >>
  `active_inst fn inst s1 /\ get_instruction bb s1.vs_inst_idx = SOME inst` by
    (simp[active_inst_def, get_instruction_def, Abbr `inst`, Abbr `s1`] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `?t1 n B HP H history certificates E.
    enters_block (mid_of fn) t t1 /\
    DRESTRICT B {id | FST id <> a} = B0 /\
    {id | id IN E /\ FST id <> a} = E0 /\
    FILTER (\entry. SND entry <> []) history = outer_history /\
    FILTER (\entry. SND entry <> []) certificates = outer_certificates /\
    ricf_execution_invariant vs C D stk PG G tn fn inst s1 t1
      n a U B HP H certificates E sites maps targets tn /\
    ricf_mapped_support a B E PG G sites /\
    ricf_analyzed_origins vs C stk PG G tn fn inst s1 a U B history sites maps /\
    ricf_history_certificates vs C log_of stk PG G tn fn inst s1 a U B
      history certificates /\
    ricf_chosen_support vs C log_of a fn B E` by
    (qpat_x_assum `ricf_execution_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [ricf_execution_boundary_def]) >>
     disch_then (qspecl_then [`s1`,`inst`] mp_tac) >> simp[]) >>
  `ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s1 t1` by
    (simp[ricf_execution_point_def] >>
     qexistsl_tac [`n`,`B`,`HP`,`H`,`history`,`certificates`,`E`] >> simp[] >>
     metis_tac[ricf_copy_coverage_entry]) >>
  `s.vs_current_bb = t.vs_current_bb` by
    metis_tac[ricf_execution_point_control, enters_block_current_bb] >>
  drule_all ricf_execution_raw_block >> strip_tac >>
  qexistsl_tac [`tb`,`s1`,`t1`,`inst`] >> simp[run_block_def, Abbr `s1`] >>
  qpat_x_assum `enters_block (mid_of fn) t t1` mp_tac >>
  simp[enters_block_def] >> strip_tac >> gvs[run_block_def]
QED

(* Block entry and instruction recursion share the same source log, current
   map and inherited projection.  The dispatcher sees each actual raw edit. *)
Theorem ricf_execution_run_block:
  ((!bb tb G tn inst ti s t.
      ricf_block_edit bb tb /\
      ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
        stk PG G tn fn inst s t /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      get_instruction tb t.vs_inst_idx = SOME ti /\
      terminates (step_inst k C inst s) /\
      (!u. step_inst k C inst s = OK u ==> is_terminator inst.inst_opcode) ==>
      ?m. block_step_rel D vs C
        (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
        (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
        stk PG fn (step_inst k C inst s) (step_inst m Ct ti t)) /\
   (!bb tb G tn inst ti s t u next.
      ricf_block_edit bb tb /\
      ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
        stk PG G tn fn inst s t /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      get_instruction tb t.vs_inst_idx = SOME ti /\
      ~is_terminator inst.inst_opcode /\ step_inst k C inst s = OK u /\
      active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
      ?h v G1 tn1.
        step_inst h Ct ti t = OK v /\
        ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
          stk PG G1 tn1 fn next
          (u with vs_inst_idx := SUC s.vs_inst_idx)
          (v with vs_inst_idx := SUC s.vs_inst_idx))) ==>
  !G tn s t bb.
    ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG G tn fn s t /\
    ricf_function_edit fn (mid_of fn) /\ wf_function fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    terminates (run_block k C bb s) ==>
    ?m tb. lookup_block t.vs_current_bb (mid_of fn).fn_blocks = SOME tb /\
      bb_well_formed tb /\ block_step_rel D vs C
        (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
        (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
        stk PG fn (run_block k C bb s) (run_block m Ct tb t)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all ricf_execution_run_entry >>
  disch_then (qspec_then `Ct` strip_assume_tac) >>
  `terminates (exec_block k C bb s1)` by fs[] >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[enters_block_current_bb] >>
  `?m. block_step_rel D vs C
    (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    stk PG fn (exec_block k C bb s1) (exec_block m Ct tb t1)` by
    (mp_tac ricf_execution_exec_block >>
     impl_tac >- (conj_tac >> rpt strip_tac >> metis_tac[]) >>
     disch_then (qspecl_then [`G`,`tn`,`inst`,`s1`,`t1`] mp_tac) >>
     impl_tac >- simp[] >> metis_tac[]) >>
  qexistsl_tac [`m`,`tb`] >> metis_tac[]
QED

Theorem ricf_execution_run_block_forward:
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ vs.vs_allocas = FEMPTY /\
  ((!bb tb G tn inst ti s t.
      ricf_block_edit bb tb /\
      ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
        stk PG G tn fn inst s t /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      get_instruction tb t.vs_inst_idx = SOME ti /\
      terminates (step_inst k C inst s) /\
      (!u. step_inst k C inst s = OK u ==> is_terminator inst.inst_opcode) ==>
      ?m. block_step_rel D vs C
        (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
        (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
        stk PG fn (step_inst k C inst s) (step_inst m Ct ti t)) /\
   (!bb tb G tn inst ti s t u next.
      ricf_block_edit bb tb /\
      ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
        stk PG G tn fn inst s t /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      get_instruction tb t.vs_inst_idx = SOME ti /\
      ~in_revert_forward fn s /\
      ~is_terminator inst.inst_opcode /\ step_inst k C inst s = OK u /\
      active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
      ?h v G1 tn1.
        step_inst h Ct ti t = OK v /\
        ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
          stk PG G1 tn1 fn next
          (u with vs_inst_idx := SUC s.vs_inst_idx)
          (v with vs_inst_idx := SUC s.vs_inst_idx))) ==>
  !G tn s t bb.
    ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG G tn fn s t /\
    ricf_function_edit fn (mid_of fn) /\ wf_function fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    terminates (run_block k C bb s) ==>
    ?m tb. lookup_block t.vs_current_bb (mid_of fn).fn_blocks = SOME tb /\
      bb_well_formed tb /\ block_step_rel D vs C
        (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
        (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
        stk PG fn (run_block k C bb s) (run_block m Ct tb t)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all ricf_execution_run_entry >>
  disch_then (qspec_then `Ct` strip_assume_tac) >>
  `terminates (exec_block k C bb s1)` by fs[] >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[enters_block_current_bb] >>
  `?m. block_step_rel D vs C
    (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    stk PG fn (exec_block k C bb s1) (exec_block m Ct tb t1)` by
    (mp_tac ricf_execution_exec_block_forward >>
     impl_tac
     >- (conj_tac
         >- (rpt strip_tac >>
             drule_all ricf_execution_point_revert_forward >>
             disch_then (qspec_then `Ct` strip_assume_tac) >>
             qexistsl_tac [`reason`,`se`,`0`,`te`] >> simp[]) >>
         conj_tac >> rpt strip_tac >> metis_tac[]) >>
     disch_then (qspecl_then [`G`,`tn`,`inst`,`s1`,`t1`] mp_tac) >>
     impl_tac >- simp[] >> metis_tac[]) >>
  qexistsl_tac [`m`,`tb`] >> metis_tac[]
QED



Theorem ricf_execution_block_target_transport:
  target = (if (mid_of fn).fn_blocks <> fn.fn_blocks
            then clear_nops_function (mid_of fn) else mid_of fn) /\
  lookup_block t.vs_current_bb (mid_of fn).fn_blocks = SOME tb /\
  bb_well_formed tb /\
  block_step_rel D vs C
    (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    stk PG fn r (run_block m Ct tb t) ==>
  ?bb'. lookup_block t.vs_current_bb target.fn_blocks = SOME bb' /\
    block_step_rel D vs C
      (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
      (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
      stk PG fn r (run_block m Ct bb' t)
Proof
  strip_tac >> Cases_on `(mid_of fn).fn_blocks <> fn.fn_blocks` >> gvs[]
  >- (qexists_tac `clear_nops_block tb` >> conj_tac
      >- simp[clear_nops_function_def, lookup_block_map, clear_nops_block_def] >>
      irule ricf_execution_block_clear_nops >> simp[]) >>
  qexists_tac `tb` >> simp[]
QED

(* The tuple indexes only existing boundary parameters.  It is essential to
   quantify over every tuple in the recursive hypothesis: a selected call
   installs a different current map and suspends the caller's map. *)
Theorem ricf_execution_family_from_raw_blocks:
  R = (\(a,U,B0,E0,outer_history,outer_certificates,sites,maps,targets).
    ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets) /\
  Rret = (\(a,U,B0,E0,outer_history,outer_certificates,sites,maps,targets).
    ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets) /\
  (!fn fn'. MEM fn C.ctx_functions /\
    lookup_function fn.fn_name Ct.ctx_functions = SOME fn' ==>
    fn' = if (mid_of fn).fn_blocks <> fn.fn_blocks
          then clear_nops_function (mid_of fn) else mid_of fn) /\
  (!idx k stk PG G tn fn fn' s t bb.
    (!idx'. fn_sim_below D vs C Ct (R idx') (Rret idx') (SUC k)) /\
    MEM fn C.ctx_functions /\
    lookup_function fn.fn_name Ct.ctx_functions = SOME fn' /\
    R idx stk PG G tn fn s t /\ block_reach vs C stk PG G tn fn s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    terminates (run_block k C bb s) ==>
    ?m tb. lookup_block t.vs_current_bb (mid_of fn).fn_blocks = SOME tb /\
      bb_well_formed tb /\ block_step_rel D vs C (R idx) (Rret idx) stk PG fn
        (run_block k C bb s) (run_block m Ct tb t)) ==>
  !n idx. fn_sim_below D vs C Ct (R idx) (Rret idx) n
Proof
  strip_tac >> irule block_sim_fn_sim_below_family >>
  rpt strip_tac >>
  `?m tb. lookup_block t.vs_current_bb (mid_of fn).fn_blocks = SOME tb /\
    bb_well_formed tb /\ block_step_rel D vs C (R idx) (Rret idx) stk PG fn
      (run_block k C bb s) (run_block m Ct tb t)` by metis_tac[] >>
  `fn' = if (mid_of fn).fn_blocks <> fn.fn_blocks
         then clear_nops_function (mid_of fn) else mid_of fn` by metis_tac[] >>
  PairCases_on `idx` >> gvs[] >>
  qexists_tac `m` >> irule ricf_execution_block_target_transport >> simp[]
QED

(* Once the internal opcode obligation has closed the family, the published
   context simulation uses the empty root tuple and the existing generic
  root function run.  No operational witness becomes a top-level premise. *)
Theorem ricf_execution_context_from_family:
  o1_ctx_shape C /\ Ct.ctx_entry = C.ctx_entry /\
  R = (\(a,U,B0,E0,outer_history,outer_certificates,sites,maps,targets).
    ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets) /\
  Rret = (\(a,U,B0,E0,outer_history,outer_certificates,sites,maps,targets).
    ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets) /\
  (!fn. MEM fn C.ctx_functions ==> ricf_function_edit fn (mid_of fn) /\
    ?fn'. lookup_function fn.fn_name Ct.ctx_functions = SOME fn' /\
      fn_entry_label fn' = fn_entry_label fn) /\
  (!n idx. fn_sim_below D vs C Ct (R idx) (Rret idx) n) ==>
  ctx_sim D C Ct vs vs
Proof
  strip_tac >> rw[ctx_sim_def] >>
  `!ret se. run_context fuel C vs <> IntRet ret se` by
    (rpt gen_tac >> irule run_context_not_int_ret >> rpt strip_tac >>
     `MEM fn C.ctx_functions /\ fn.fn_name = name` by
       metis_tac[lookup_function_MEM, lookup_function_selected_name] >>
     gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM,
       entry_fn_no_return_def] >> metis_tac[]) >>
  Cases_on `C.ctx_entry` >- gvs[run_context_def, terminates_def] >>
  rename1 `C.ctx_entry = SOME name` >>
  Cases_on `lookup_function name C.ctx_functions`
  >- gvs[run_context_def, terminates_def] >>
  rename1 `lookup_function name C.ctx_functions = SOME fn` >>
  Cases_on `fn_entry_label fn`
  >- gvs[run_context_def, run_function_def, terminates_def] >>
  rename1 `fn_entry_label fn = SOME lbl` >>
  `MEM fn C.ctx_functions /\ fn.fn_name = name` by
    metis_tac[lookup_function_MEM, lookup_function_selected_name] >>
  `?fn'. lookup_function name Ct.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl` by metis_tac[] >>
  qabbrev_tac `s0 = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                             vs_inst_idx := 0|>` >>
  `!f. run_context f C vs = run_blocks f C fn s0 /\
    run_context f Ct vs = run_blocks f Ct fn' s0` by
    gvs[run_context_def, run_function_def, Abbr `s0`] >>
  `block_reach vs C [] [] FEMPTY entry_taint fn s0` by
    (rw[block_reach_def, Abbr `s0`] >> irule frame_reachable_entry >> metis_tac[]) >>
  `ricf_execution_boundary vs C mid_of log_of D 0 [] FEMPTY {} [] [] FEMPTY [] []
     [] [] FEMPTY entry_taint fn s0 s0` by
    (gvs[Abbr `s0`] >> irule ricf_execution_boundary_initial >> metis_tac[]) >>
  qpat_x_assum `!n idx. fn_sim_below _ _ _ _ _ _ _`
    (qspecl_then [`SUC fuel`,`(0,[],FEMPTY,{},[],[],FEMPTY,[],[])`]
      (mp_tac o SIMP_RULE std_ss [fn_sim_below_def])) >>
  disch_then (qspecl_then [`fuel`,`[]`,`[]`,`FEMPTY`,`entry_taint`,
    `fn`,`fn'`,`s0`,`s0`] mp_tac) >>
  impl_tac >- (gvs[] >> metis_tac[]) >> strip_tac >>
  qexists_tac `m` >> gvs[] >>
  Cases_on `run_blocks fuel C fn s0` >> gvs[fn_run_rel_def] >>
  Cases_on `run_blocks m Ct fn' s0` >> gvs[]
QED
