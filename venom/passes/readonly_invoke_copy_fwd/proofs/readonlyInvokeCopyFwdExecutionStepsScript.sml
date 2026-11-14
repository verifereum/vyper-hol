(* Instruction-index induction for the raw positional function.  The two
   local dispatch obligations are discharged by opcode and call producers;
   they are not assumptions of the public pass-correctness statement. *)
Theory readonlyInvokeCopyFwdExecutionSteps
Ancestors
  readonlyInvokeCopyFwdExecutionCoverage
  readonlyInvokeCopyFwdExecutionBoundary readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdMapCoverage readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdExecutionHistory
  invokeCopyFwdCommonDefs readonlyMemoryArgsDefs
  reachableFnSim taintAgree contextCodegenRel venomInstProofs
  venomExecProps venomExecProofs venomExecSemantics venomWf venomInst venomState
  passSimulationDefs list finite_map arithmetic

(* All witnesses vary along a block; its inherited caller projection stays
   fixed.  Copy coverage uses the one source log chosen for the function. *)
Definition ricf_execution_point_def:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG G tn fn inst s t <=>
    ?n B HP H history certificates E.
      DRESTRICT B {id | FST id <> a} = B0 /\
      {id | id IN E /\ FST id <> a} = E0 /\
      FILTER (\entry. SND entry <> []) history = outer_history /\
      FILTER (\entry. SND entry <> []) certificates = outer_certificates /\
      ricf_execution_invariant vs C D stk PG G tn fn inst s t
        n a U B HP H certificates E sites maps targets tn /\
      ricf_mapped_support a B E PG G sites /\
      ricf_analyzed_origins vs C stk PG G tn fn inst s a U B history sites maps /\
      ricf_history_certificates vs C log_of stk PG G tn fn inst s a U B
        history certificates /\
      ricf_chosen_support vs C log_of a fn B E /\
      ricf_copy_coverage
        (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) fn)
        fn (log_of fn) a history s
End

Theorem ricf_execution_point_control:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t ==>
  s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx
Proof
  rw[ricf_execution_point_def] >>
  fs[ricf_execution_invariant_def, ricf_opaque_frame_agree_def,
     ricf_frame_agree_def] >> drule taint_agree_frame >>
  disch_then (fn th =>
    assume_tac (Q.AP_TERM `\st. st.vs_current_bb` th) >>
    assume_tac (Q.AP_TERM `\st. st.vs_inst_idx` th)) >>
  gvs[ricf_opaque_view_def]
QED

Theorem ricf_inst_edit_terminator:
  ricf_inst_edit inst target ==>
  (is_terminator target.inst_opcode <=> is_terminator inst.inst_opcode)
Proof
  rw[ricf_inst_edit_def] >> gvs[is_terminator_def]
QED

Theorem ricf_block_edit_fetch:
  ricf_block_edit bb tb /\ get_instruction bb pc = SOME inst ==>
  ?ti. get_instruction tb pc = SOME ti /\ ricf_inst_edit inst ti /\
       (is_terminator ti.inst_opcode <=> is_terminator inst.inst_opcode)
Proof
  strip_tac >> drule ricf_block_edit_EL >> strip_tac >>
  qexists_tac `EL pc tb.bb_instructions` >>
  gvs[get_instruction_def] >> metis_tac[ricf_inst_edit_terminator]
QED

(* A terminal step is also the terminal suffix of exec_block.  In particular
   its halted OK arm is converted to Halt on both sides. *)
Theorem ricf_execution_terminal_suffix:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction tb t.vs_inst_idx = SOME ti /\
  (is_terminator ti.inst_opcode <=> is_terminator inst.inst_opcode) /\
  (!u. step_inst k C inst s = OK u ==> is_terminator inst.inst_opcode) /\
  block_step_rel D vs C R Rret stk PG fn
    (step_inst k C inst s) (step_inst m Ct ti t) ==>
  block_step_rel D vs C R Rret stk PG fn
    (exec_block k C bb s) (exec_block m Ct tb t)
Proof
  strip_tac >> once_rewrite_tac[exec_block_def] >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >>
  Cases_on `step_inst k C inst s` >> Cases_on `step_inst m Ct ti t` >>
  gvs[block_step_rel_def, fn_run_rel_def] >>
  BasicProvers.every_case_tac >> gvs[block_step_rel_def, fn_run_rel_def] >>
  metis_tac[]
QED

(* The induction really follows exec_block's successful non-terminator arm.
   Recursive INVOKEs may choose a larger target fuel; MAX preserves both
   the first target step and the already-constructed continuation. *)
Theorem ricf_execution_exec_block:
  ((!G tn inst ti s t.
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
   (!G tn inst ti s t u next.
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
  !G tn inst s t.
    ricf_block_edit bb tb /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG G tn fn inst s t /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    terminates (exec_block k C bb s) ==>
    ?m. block_step_rel D vs C
      (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
      (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
      stk PG fn (exec_block k C bb s) (exec_block m Ct tb t)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "terminal") (mk_asm "next")) >>
  rpt gen_tac >> map_every qid_spec_tac [`inst`,`t`,`tn`,`G`] >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  `s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx` by
    metis_tac[ricf_execution_point_control] >>
  `?ti. get_instruction tb t.vs_inst_idx = SOME ti /\
    (is_terminator ti.inst_opcode <=> is_terminator inst.inst_opcode)` by
    metis_tac[ricf_block_edit_fetch] >>
  `terminates (step_inst k C inst s)` by
    (qpat_x_assum `terminates (exec_block _ _ _ _)` mp_tac >>
     simp[Once exec_block_def] >> Cases_on `step_inst k C inst s` >>
     simp[terminates_def]) >>
  Cases_on `!u. step_inst k C inst s = OK u ==> is_terminator inst.inst_opcode`
  >- (asm "terminal" (qspecl_then [`G`,`tn`,`inst`,`ti`,`s`,`t`] mp_tac) >>
      impl_tac >- simp[] >> strip_tac >> qexists_tac `m` >>
      irule ricf_execution_terminal_suffix >> metis_tac[]) >>
  gvs[] >> rename1 `step_inst k C inst s = OK u` >>
  `u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `terminates (exec_block k C bb (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (qpat_x_assum `terminates (exec_block _ _ _ s)` mp_tac >>
     simp[Once exec_block_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   SUC s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (conj_tac >- fs[get_instruction_def] >> spose_not_then assume_tac >>
     qpat_x_assum `terminates (exec_block _ _ _ _)` mp_tac >>
     simp[Once exec_block_def, get_instruction_def, terminates_def]) >>
  `active_inst fn (EL (SUC s.vs_inst_idx) bb.bb_instructions)
    (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[active_inst_def] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  asm "next" (qspecl_then [`G`,`tn`,`inst`,`ti`,`s`,`t`,`u`,
    `EL (SUC s.vs_inst_idx) bb.bb_instructions`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  asm_x "terminal" kall_tac >> asm_x "next" kall_tac >>
  qpat_x_assum `!y. _` (qspec_then `SUC s.vs_inst_idx` mp_tac) >> simp[] >>
  disch_then (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then (qspecl_then [`G1`,`tn1`,
    `v with vs_inst_idx := SUC s.vs_inst_idx`,
    `EL (SUC s.vs_inst_idx) bb.bb_instructions`] mp_tac) >>
  simp[get_instruction_def] >> impl_tac >- metis_tac[] >> strip_tac >>
  `!e. exec_block m Ct tb (v with vs_inst_idx := SUC s.vs_inst_idx) <> Error e` by
    (Cases_on `exec_block k C bb (u with vs_inst_idx := SUC s.vs_inst_idx)` >>
     Cases_on `exec_block m Ct tb (v with vs_inst_idx := SUC s.vs_inst_idx)` >>
     gvs[block_step_rel_def, fn_run_rel_def]) >>
  `step_inst (MAX h m) Ct ti t = OK v` by
    (irule (CONJUNCT1 fuel_mono) >> simp[] >> qexists_tac `h` >> simp[]) >>
  `exec_block (MAX h m) Ct tb (v with vs_inst_idx := SUC s.vs_inst_idx) =
    exec_block m Ct tb (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (CONJUNCT1 (CONJUNCT2 fuel_mono)) >> simp[] >>
     qexists_tac `m` >> simp[]) >>
  qexists_tac `MAX h m` >> once_rewrite_tac[exec_block_def] >> simp[] >> gvs[]
QED
