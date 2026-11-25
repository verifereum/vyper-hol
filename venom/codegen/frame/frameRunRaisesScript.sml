(* How a root frame's run ends: at an instruction of that frame.
 * TOP-LEVEL: run_call_root_ends_at_inst (used by
 * deploy_frame_gas_sufficient).
 *)
Theory frameRunRaises
Ancestors
  frameGas frameOutcome frameRootReach frameRootTerminal
  vfmExecution vfmExecutionProp vfmContext vfmAccountFrame relation

(* With one context whose output does not go to code (no deposit), a run
   that ends in OutOfGas has an instruction of that frame raising it: a
   callee's exceptions return to it, inc_pc_or_jump raises only
   InvalidJumpDest, the root's halt handler re-raises, and wf_state keeps
   the root's charge of its remaining gas from failing.  A run that halts
   ends in the state its halting instruction left: the halt handlers of a
   root whose output is not code change nothing. *)
Theorem run_call_root_ends_at_inst:
  !es c rb r es'.
    wf_state es /\ es.contexts = [(c, rb)] /\
    (!a. c.msgParams.outputTo <> Code a) /\
    run_call es = SOME (r, es')
    ==>
    (r = INR (SOME OutOfGas) ==> ?op. frame_inst_raises es OutOfGas op) /\
    (r = INR NONE ==>
     ?s op. frame_inst_at es s op /\ step_inst op s = (INR NONE, es') /\
            LENGTH es'.contexts = 1)
Proof
  rpt gen_tac >> strip_tac >> conj_tac >> strip_tac >> gvs[] >>
  drule_at (Pat `run_call _ = _`) root_run_terminal_source >>
  simp[] >> strip_tac >>
  drule_all root_step_ends_at_inst >> simp[] >> strip_tac >>
  rename1 `frame_inst_at s s op` >>
  rename1 `s.contexts = [(c1,rb1)]` >>
  `frame_inst_at es s op` by
    (gvs[frame_inst_at_step] >>
     qexistsl_tac [`c1`,`rb1`,`[]`] >> simp[]) >>
  simp[frame_inst_raises_def] >>
  goal_assum $ drule_at Any >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem run_call_root_exception_raises:
  wf_state es /\ LENGTH es.contexts = 1 /\
  ~vfm_abort (SOME exc) /\ run_call es = SOME (INR (SOME exc),es') ==>
  frame_raises es exc
Proof
  strip_tac >>
  drule_all root_run_nonabort_terminal_source >> strip_tac >>
  `?c rb. s.contexts = [(c,rb)]` by
    (Cases_on `s.contexts` >> gvs[] >> Cases_on `h` >> simp[]) >>
  drule_all root_step_exception_raises >> strip_tac >>
  `es.contexts <> []` by (Cases_on `es.contexts` >> gvs[]) >>
  `run_frame es = run_frame s` by
    (irule run_frame_prefix >> gvs[run_call_reaches_def, arithmeticTheory.GREATER_EQ]) >>
  gvs[frame_raises_def]
QED

Theorem run_call_root_frame_outcome_raises:
  wf_state es /\ LENGTH es.contexts = 1 /\ ~vfm_abort (SOME exc) /\
  run_call es = SOME (r,es') /\ frame_outcome es r es' (SOME exc) out lgs ==>
  frame_raises es exc
Proof
  strip_tac >>
  `r = INR (SOME exc)` by gvs[frame_outcome_def] >>
  metis_tac[run_call_root_exception_raises]
QED
