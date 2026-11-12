(* Reachability of the terminal source of a root-frame run. *)
Theory frameRootReach
Ancestors
  arithmetic combin pair list rich_list relation
  frameGas vfmAccountFrame vfmContextLength vfmRunCall

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

Theorem step_bottom_msgParams[local]:
  wf_state s /\ step s = (r,t) ==>
  DROP (LENGTH t.contexts - 1) (MAP (\p. (FST p).msgParams) t.contexts) =
  DROP (LENGTH s.contexts - 1) (MAP (\p. (FST p).msgParams) s.contexts)
Proof
  strip_tac >>
  Cases_on `1 < LENGTH s.contexts`
  >- (mp_tac (Q.INST [`k` |-> `1`] step_outer_msgParams) >> simp[] >>
      disch_then drule_all >> simp[]) >>
  `s.contexts <> []` by gvs[vfmExecutionPropTheory.wf_state_def] >>
  `wf_state t` by metis_tac[step_preserves_wf_state, SND] >>
  `t.contexts <> []` by gvs[vfmExecutionPropTheory.wf_state_def] >>
  `LENGTH s.contexts = 1`
    by (Cases_on `s.contexts` >> gvs[] >>
        rename1 `s.contexts = h::cs` >> Cases_on `cs` >> gvs[]) >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (drule_all step_same_frame_foreign >> strip_tac >>
      Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[] >>
      rename1 `LENGTH cs = 0` >> gvs[]) >>
  `LENGTH s.contexts < LENGTH t.contexts`
    by (Cases_on `t.contexts` >> gvs[] >>
        rename1 `t.contexts = h::cs` >> Cases_on `cs` >> gvs[]) >>
  drule_all step_push_foreign >> strip_tac >>
  Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[] >>
  rename1 `LENGTH cs = 1` >> Cases_on `cs` >> gvs[]
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
  drule_all step_bottom_msgParams >> simp[]
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
  rpt gen_tac >> strip_tac >>
  `?e. r = INR e /\ ~vfm_abort e`
    by (gvs[vfmExecutionTheory.vfm_abort_def]) >>
  gvs[] >> drule root_run_last_step >> strip_tac >>
  drule_all root_reaches_bottom_msgParams >> strip_tac >>
  `outputTo_consistent s`
    by metis_tac[outputTo_consistent_stack_imp_consistent,
                 vfmExecutionPropTheory.wf_state_def] >>
  `~(LENGTH s.contexts >= 2)`
    by (strip_tac >> drule step_ge2_inr_is_abort >>
        simp[vfmExecutionTheory.vfm_abort_def]) >>
  `?c1 rb1. s.contexts = [(c1,rb1)]`
    by (Cases_on `s.contexts` >> gvs[] >>
        rename1 `s.contexts = h::cs` >> Cases_on `cs` >> gvs[] >>
        Cases_on `h` >> simp[]) >>
  qexistsl_tac [`s`,`c1`,`rb1`] >>
  gvs[vfmAccountFrameTheory.run_call_reaches_def, GREATER_EQ]
QED
