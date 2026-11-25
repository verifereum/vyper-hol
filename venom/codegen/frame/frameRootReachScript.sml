(* Reachability of the terminal source of a root-frame run. *)
Theory frameRootReach
Ancestors
  arithmetic combin pair list rich_list relation
  frameGas vfmAccountFrame vfmContextLength vfmRunCall vfmWfState

Theorem root_run_last_step[local]:
  run_call es = SOME (INR e,t) ==>
  ?s. run_call_reaches es s /\
      LENGTH es.contexts <= LENGTH s.contexts /\ step s = (INR e,t)
Proof
  strip_tac >> drule run_call_finite_trace >> strip_tac >>
  Cases_on `n` >- gvs[] >>
  rename1 `FUNPOW (step o SND) (SUC n) (INL (),es) = _` >>
  `ISL (FST (FUNPOW (step o SND) n (INL (),es))) /\
   LENGTH es.contexts <=
     LENGTH (SND (FUNPOW (step o SND) n (INL (),es))).contexts`
    by (first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  `run_call_reaches es (SND (FUNPOW (step o SND) n (INL (),es)))`
    by (irule run_call_trace_reaches >> simp[] >>
        rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qexists_tac `SND (FUNPOW (step o SND) n (INL (),es))` >>
  gvs[FUNPOW_SUC]
QED

Theorem root_reaches_bottom_msgParams[local]:
  wf_state es /\ run_call_reaches es s ==>
  wf_state s /\
  DROP (LENGTH s.contexts - 1) (MAP (\p. (FST p).msgParams) s.contexts) =
  DROP (LENGTH es.contexts - 1) (MAP (\p. (FST p).msgParams) es.contexts)
Proof
  strip_tac >>
  irule (BETA_RULE (Q.INST [`Q` |-> `\t. wf_state t /\
    DROP (LENGTH t.contexts - 1) (MAP (\p. (FST p).msgParams) t.contexts) =
    DROP (LENGTH es.contexts - 1) (MAP (\p. (FST p).msgParams) es.contexts)`]
    run_call_reaches_inv)) >>
  simp[] >> rpt strip_tac
  >- metis_tac[step_preserves_wf_state, SND] >>
  rename1 `step current = (INL (),next)` >>
  `wf_state next` by metis_tac[step_preserves_wf_state, SND] >>
  `1 <= LENGTH current.contexts /\ 1 <= LENGTH next.contexts` by
    (Cases_on `current.contexts` >> Cases_on `next.contexts` >>
     gvs[vfmExecutionPropTheory.wf_state_def]) >>
  mp_tac (Q.INST [`n` |-> `1`, `s` |-> `current`, `t` |-> `next`,
    `r` |-> `INL ()`] step_frame_msg_params) >>
  simp[]
QED

(* A non-abort terminal step of a singleton run occurs at the root. *)
Theorem root_run_nonabort_terminal_source:
  wf_state es /\ LENGTH es.contexts = 1 /\
  run_call es = SOME (INR e,es') /\ ~vfm_abort e ==>
  ?s. run_call_reaches es s /\ wf_state s /\
      LENGTH s.contexts = 1 /\ step s = (INR e,es')
Proof
  strip_tac >> drule root_run_last_step >> strip_tac >>
  drule_all root_reaches_bottom_msgParams >> strip_tac >>
  `outputTo_consistent s` by
    metis_tac[outputTo_consistent_stack_imp_consistent,
              vfmExecutionPropTheory.wf_state_def] >>
  `~(LENGTH s.contexts >= 2)` by
    (strip_tac >> drule step_ge2_inr_is_abort >> simp[]) >>
  `LENGTH s.contexts = 1` by decide_tac >>
  qexists_tac `s` >> simp[]
QED

Theorem root_run_terminal_source:
  !es c rb r es'.
    wf_state es /\ es.contexts = [(c,rb)] /\
    (!a. c.msgParams.outputTo <> Code a) /\
    run_call es = SOME (r,es') /\
    (r = INR (SOME OutOfGas) \/ r = INR NONE) ==>
    ?s c1 rb1.
      RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\
                   step a = (INL (),b)) es s /\
      wf_state s /\ s.contexts = [(c1,rb1)] /\
      (!a. c1.msgParams.outputTo <> Code a) /\ step s = (r,es')
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_at (Pat `run_call _ = _`) root_run_nonabort_terminal_source >>
  simp[] >> strip_tac >>
  drule_all root_reaches_bottom_msgParams >> strip_tac >>
  `?c1 rb1. s.contexts = [(c1,rb1)]`
    by (Cases_on `s.contexts` >> gvs[] >>
        rename1 `s.contexts = h::cs` >> Cases_on `cs` >> gvs[] >>
        Cases_on `h` >> simp[]) >>
  qexistsl_tac [`s`,`c1`,`rb1`] >>
  gvs[vfmAccountFrameTheory.run_call_reaches_def, GREATER_EQ]
QED
