Theory frameFiniteJointEndpoints
Ancestors frameFiniteExecution frameFiniteJointTrace frameJointTrace
  frameJointTransition contextCodegenRel venomExecSemantics venomState venomInst

Theorem finite_intret_noninvoke:
  finite_step C inst s (IntRet ret send) ==> inst.inst_opcode <> INVOKE
Proof
  simp[Once finite_step_cases] >> rpt strip_tac >> gvs[]
QED

Theorem finite_joint_ordinary_extension:
  joint_trace vs0 C q0 es qs
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ finite_step C inst s (OK post) /\
  active_inst fn next (post with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?fuel q'. step_inst fuel C inst s = OK post /\
    joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
      (SOME (OriginOrdinary fuel post)) q' /\
    q' = JointConfig stk PG (step_prov PG G inst post)
      (step_taint inst s post tn) fn next
      (post with vs_inst_idx := SUC s.vs_inst_idx) oms
      (origin_step PG om inst post) hs
      (h ++ [OriginOrdinary fuel post; OriginObserve
        (OriginSnapshot fn PG (step_prov PG G inst post)
          (origin_step PG om inst post) next
          (post with vs_inst_idx := SUC s.vs_inst_idx))]) /\
    joint_trace vs0 C q0 (es ++ [SOME (OriginOrdinary fuel post)])
      (qs ++ [q']) q'
Proof
  strip_tac >> drule (cj 1 finite_execution_realizable) >> strip_tac >>
  `step_inst n C inst s = OK post` by simp[] >>
  qexists_tac `n` >> simp[] >>
  qmatch_goalsub_abbrev_tac `joint_transition C _ _ dest` >>
  `joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
     (SOME (OriginOrdinary n post)) dest` by
    (simp[joint_transition_ordinary, Abbr `dest`] >> metis_tac[]) >>
  simp[] >> metis_tac[joint_trace_snoc]
QED

Theorem finite_joint_call_extension:
  joint_trace vs0 C q0 es qs
    (JointConfig stk PG G tn caller callinst s oms om hs h) /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  finite_run C callee cs r ==>
  ?p inst q'. enters_block callee cs p /\ active_inst callee inst p /\
    joint_transition C (JointConfig stk PG G tn caller callinst s oms om hs h) NONE q' /\
    q' = JointConfig
      (<| cf_fn := caller; cf_inst := callinst; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst p
      (om::oms) FEMPTY (h::hs)
      [OriginCallee cs; OriginObserve
        (OriginSnapshot callee (MAP (op_prov G) ops) FEMPTY FEMPTY inst p)] /\
    joint_trace vs0 C q0 (es ++ [NONE]) (qs ++ [q']) q'
Proof
  strip_tac >> drule finite_run_entry_active >> strip_tac >>
  qexistsl_tac [`p`, `inst'`] >> simp[] >>
  qmatch_goalsub_abbrev_tac `joint_transition C _ _ dest` >>
  `joint_transition C (JointConfig stk PG G tn caller callinst s oms om hs h)
     NONE dest` by
    (simp[joint_transition_call_iff, Abbr `dest`] >> metis_tac[]) >>
  simp[] >> metis_tac[joint_trace_snoc]
QED

Theorem finite_joint_resume_extension:
  joint_trace vs0 C q0 es qs
    (JointConfig (f::stk) PG G tn fn rinst s (caller_om::oms) om (caller_h::hs) h) /\
  active_inst fn rinst s /\ finite_step C rinst s (IntRet ret send) /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state send)) = SOME post /\
  active_inst f.cf_fn next (post with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ?fuel q'. step_inst fuel C rinst s = IntRet ret send /\
    joint_transition C
      (JointConfig (f::stk) PG G tn fn rinst s (caller_om::oms) om (caller_h::hs) h)
      (SOME (OriginResume fuel fn rinst s ret send post)) q' /\
    q' = JointConfig stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn next (post with vs_inst_idx := SUC f.cf_state.vs_inst_idx) oms
      (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))) hs
      (caller_h ++ [OriginResume fuel fn rinst s ret send post; OriginObserve
        (OriginSnapshot f.cf_fn f.cf_params
          (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
          (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))) next
          (post with vs_inst_idx := SUC f.cf_state.vs_inst_idx))]) /\
    joint_trace vs0 C q0 (es ++ [SOME (OriginResume fuel fn rinst s ret send post)])
      (qs ++ [q']) q'
Proof
  strip_tac >> drule (cj 1 finite_execution_realizable) >> strip_tac >>
  `step_inst n C rinst s = IntRet ret send` by simp[] >>
  qexists_tac `n` >> simp[] >>
  qmatch_goalsub_abbrev_tac `joint_transition C _ _ dest` >>
  `joint_transition C
      (JointConfig (f::stk) PG G tn fn rinst s (caller_om::oms) om (caller_h::hs) h)
      (SOME (OriginResume n fn rinst s ret send post)) dest` by
    (simp[joint_transition_return, Abbr `dest`] >> metis_tac[]) >>
  simp[] >> metis_tac[joint_trace_snoc]
QED

val _ = export_theory();
