(* CALL-family contracts via the observation-preserving prefix interface. *)
Theory stackBoundCalls
Ancestors
  stackBoundDefs stackBoundInterface stackBoundCallObs stackBoundCallPrefix stackBoundCallTerminal
  vfmExecution vfmExecutionProp vfmContext vfmState vfmOperation vfmConstants
  list rich_list pair option finite_map words

Definition sb_call_post_def:
  sb_call_post code pc jd ws rest r t <=>
    ~(r = INR (SOME StackOverflow) /\
      LENGTH t.contexts = SUC (LENGTH rest)) /\
    (r = INL () \/ SUC (LENGTH rest) < LENGTH t.contexts ==>
      (?w. sb_call_obs t = (code,pc+1,jd,w::ws)::rest) \/
      (?h. sb_call_obs t = h::(code,pc,jd,ws)::rest))
End

Theorem sb_call_post_error[local]:
  sb_call_obs t = (code,pc,jd,ws)::rest /\ e <> SOME StackOverflow ==>
  sb_call_post code pc jd ws rest (INR e) t
Proof
  strip_tac >>
  `LENGTH t.contexts = SUC (LENGTH rest)` by
    metis_tac[sb_call_obs_length,LENGTH] >>
  simp[sb_call_post_def]
QED

Theorem sb_call_wp_keep[local]:
  sb_call_prefix m /\ s.contexts <> [] /\
  sb_call_obs s = (code,pc,jd,ws)::rest /\
  (!x t. sb_call_obs t = (code,pc,jd,ws)::rest /\ t.contexts <> [] ==>
    sb_call_wp (k x) (sb_call_post code pc jd ws rest) t) ==>
  sb_call_wp (bind m k) (sb_call_post code pc jd ws rest) s
Proof
  strip_tac >> irule sb_call_wp_prefix >>
  simp[] >> metis_tac[sb_call_post_error]
QED

Theorem sb_call_abort_post[local]:
  sb_call_obs s = (code,pc,jd,ws)::rest /\ LENGTH ws < stack_limit ==>
  sb_call_wp (abort_unuse n) (sb_call_post code pc jd ws rest) s /\
  sb_call_wp (abort_call_value n) (sb_call_post code pc jd ws rest) s
Proof
  strip_tac >> Cases_on `s.contexts` >>
  gvs[sb_call_obs_def] >> PairCases_on `h` >>
  gvs[sb_call_context_obs_def] >>
  conj_tac
  >- (rw[sb_call_wp_def] >> drule_all (SRULE [stack_limit_def] sb_call_abort_unuse) >>
      simp[sb_call_post_def,sb_call_context_obs_def,sb_call_obs_def] >>
      metis_tac[]) >>
  rw[sb_call_wp_def] >> drule_all (SRULE [stack_limit_def] sb_call_abort_value) >>
  simp[sb_call_post_def,sb_call_context_obs_def,sb_call_obs_def] >>
  metis_tac[]
QED

Theorem sb_call_proceed_post[local]:
  sb_call_obs s = (code,pc,jd,ws)::rest ==>
  sb_call_wp (proceed_call op sender address value ao az bytes gas output)
    (sb_call_post code pc jd ws rest) s
Proof
  strip_tac >> `s.contexts <> []` by metis_tac[sb_call_obs_empty,NOT_CONS_NIL] >>
  rw[sb_call_wp_def] >> drule_all sb_call_proceed_observation >> strip_tac >>
  `LENGTH t.contexts = SUC (SUC (LENGTH rest))` by
    metis_tac[sb_call_obs_length,LENGTH] >>
  simp[sb_call_post_def] >> metis_tac[]
QED

Theorem sb_call_prepared_post[local]:
  s.contexts = (c,rb)::rest /\ LENGTH c.stack <= stack_limit /\
  n = 6 + (if call_has_value op then 1 else 0) /\ n <= LENGTH c.stack ==>
  sb_call_wp (step_call op)
    (sb_call_post c.msgParams.code c.pc c.jumpDest (DROP n c.stack)
      (MAP (sb_call_context_obs o FST) rest)) s
Proof
  strip_tac >>
  `LENGTH (DROP n c.stack) < stack_limit` by
    (Cases_on `call_has_value op` >> gvs[]) >>
  gvs[] >> simp[step_call_def,sb_call_wp_bind] >>
  qmatch_goalsub_abbrev_tac `sb_call_wp (pop_stack _) postpop s` >>
  simp[sb_call_wp_def,pop_stack_def,get_current_context_def,
       set_current_context_def,bind_def,ignore_bind_def,assert_def,
       return_def,fail_def] >>
  simp[Abbr `postpop`] >> pairarg_tac >> simp[] >>
  irule sb_call_wp_keep >>
  reverse conj_tac >- simp[sb_call_obs_def,sb_call_context_obs_def] >>
  rpt gen_tac >> strip_tac >> simp[] >>
  ntac 2 (irule sb_call_wp_keep >> (reverse conj_tac >- simp[]) >>
          rpt gen_tac >> strip_tac >> simp[]) >>
  irule sb_call_wp_keep >>
  (reverse conj_tac >- (simp[] >> qmatch_goalsub_abbrev_tac `get_delegate acode` >>
                        Cases_on `get_delegate acode` >> simp[sb_call_prefix_bind])) >>
  qx_gen_tac `cd` >> Cases_on `cd` >> rpt gen_tac >> strip_tac >> simp[] >>
  irule sb_call_wp_keep >> (reverse conj_tac >- simp[]) >>
  rpt gen_tac >> strip_tac >> simp[] >> pairarg_tac >> simp[] >>
  rewrite_tac[ignore_bind_def] >>
  irule sb_call_wp_keep >> (reverse conj_tac >- simp[]) >>
  rpt gen_tac >> strip_tac >> simp[] >>
  irule sb_call_wp_keep >>
  (reverse conj_tac >- (simp[] >>
    qmatch_goalsub_abbrev_tac `sb_call_prefix (if test then _ else _)` >>
    Cases_on `test` >> simp[])) >>
  rpt gen_tac >> strip_tac >> simp[] >>
  ntac 2 (irule sb_call_wp_keep >> (reverse conj_tac >- simp[]) >>
          rpt gen_tac >> strip_tac >> simp[]) >>
  qmatch_goalsub_abbrev_tac `sb_call_wp (if abort then _ else _) _ _` >>
  Cases_on `abort` >> simp[]
  >- (irule (cj 2 sb_call_abort_post) >> simp[]) >>
  ntac 2 (irule sb_call_wp_keep >> (reverse conj_tac >- simp[]) >>
          rpt gen_tac >> strip_tac >> simp[]) >>
  IF_CASES_TAC >> simp[]
  >- (irule (cj 1 sb_call_abort_post) >> simp[]) >>
  irule sb_call_proceed_post >> simp[]
QED

Theorem sb_call_raw_view[local]:
  s.contexts = (c,rb)::rest /\ LENGTH c.stack <= stack_limit /\
  n = 6 + (if call_has_value op then 1 else 0) /\
  step_call op s = (r,t) ==>
  ~(r = INR (SOME StackOverflow) /\ LENGTH t.contexts = LENGTH s.contexts) /\
  (r = INL () \/ LENGTH s.contexts < LENGTH t.contexts ==>
    n <= LENGTH c.stack /\
    sb_call_post c.msgParams.code c.pc c.jumpDest (DROP n c.stack)
      (MAP (sb_call_context_obs o FST) rest) r t)
Proof
  strip_tac >> Cases_on `n <= LENGTH c.stack`
  >- (drule_all sb_call_prepared_post >>
      simp[sb_call_wp_def,sb_call_post_def] >> metis_tac[]) >>
  qpat_x_assum `step_call _ _ = _` mp_tac >>
  gvs[] >>
  simp[step_call_def,pop_stack_def,get_current_context_def,
       set_current_context_def,bind_def,ignore_bind_def,assert_def,
       return_def,fail_def] >>
  strip_tac >> gvs[]
QED

Theorem sb_call_obs_at[local]:
  bytecode_stack_describes b ws /\ LENGTH rest = d /\
  ((?w. sb_call_obs t = (code,pc+1,NONE,w::ws)::rest) \/
   (?h. sb_call_obs t = h::(code,pc,NONE,ws)::rest)) ==>
  sb_at code (pc+1,NONE::b) (SUC d) t
Proof
  strip_tac >>
  Cases_on `t.contexts` >> gvs[sb_call_obs_def] >>
  rename1 `t.contexts = head::tail` >> PairCases_on `head` >>
  gvs[sb_call_context_obs_def,sb_at_def,bytecode_stack_describes_def] >>
  `LENGTH tail = SUC (LENGTH rest)` by metis_tac[LENGTH_MAP,LENGTH] >>
  Cases_on `tail` >> gvs[] >>
  rename1 `sb_call_context_obs (FST saved) = _` >>
  PairCases_on `saved` >> gvs[sb_call_context_obs_def]
QED

Theorem sb_call_inner[local]:
  op = Call \/ op = CallCode \/ op = DelegateCall \/ op = StaticCall ==>
  sb_inner op s = step_call op s
Proof
  strip_tac >> Cases_on `step_call op s` >> Cases_on `q` >>
  gvs[sb_inner_def,step_inst_def,inc_pc_or_jump_def,is_call_def,
      bind_def,return_def]
QED

Theorem sb_call_contracts:
  sb_opcode_contract Call /\ sb_opcode_contract CallCode /\
  sb_opcode_contract DelegateCall /\ sb_opcode_contract StaticCall
Proof
  `(!op. op = Call \/ op = CallCode \/ op = DelegateCall \/ op = StaticCall ==>
     sb_opcode_contract op)` suffices_by metis_tac[] >>
  gen_tac >> disch_tac >> rewrite_tac[sb_opcode_contract_def] >>
  map_every qx_gen_tac [`s`,`a`] >> strip_tac >>
  Cases_on `s.contexts` >- gvs[] >> PairCases_on `h` >>
  rename1 `s.contexts = (c,rb)::rest` >>
  `LENGTH c.stack <= stack_limit /\
   c.msgParams.parsed = parse_code 0 FEMPTY c.msgParams.code` by
    gvs[wf_state_def,wf_context_def] >>
  `bytecode_stack_describes a c.stack /\ c.jumpDest = NONE /\
   sb_decoded c op` by gvs[] >>
  `LENGTH a = LENGTH c.stack` by metis_tac[bytecode_stack_describes_length] >>
  conj_tac
  >- (strip_tac >> gen_tac >> strip_tac >>
      `step_call op s = (INR (SOME StackOverflow),t)` by
        (qpat_x_assum `op = _ \/ _` strip_assume_tac >> gvs[step_inst_def]) >>
      drule_at (Pat `step_call _ _ = _`) sb_call_raw_view >>
      simp[stack_limit_def] >> metis_tac[]) >>
  map_every qx_gen_tac [`r`,`t`] >>
  `sb_inner op s = step_call op s` by metis_tac[sb_call_inner] >>
  simp[] >> strip_tac >>
  (drule_at (Pat `step_call _ _ = _`) sb_call_raw_view >>
  simp[] >> (impl_tac >- gvs[stack_limit_def]) >> strip_tac >>
  `FLOOKUP (parse_code 0 FEMPTY c.msgParams.code) c.pc = SOME op` by
    (qpat_x_assum `sb_decoded c op` mp_tac >>
     simp[sb_decoded_def] >>
     Cases_on `FLOOKUP (parse_code 0 FEMPTY c.msgParams.code) c.pc` >>
     gvs[] >> Cases_on `LENGTH c.msgParams.code <= c.pc` >> gvs[]) >>
  qexists_tac `(c.pc+1,NONE::DROP (6+(if call_has_value op then 1 else 0)) a)` >>
  conj_tac
  >- (simp[sb_successors_def,bytecode_stack_successors_def] >>
      qpat_x_assum `op = _ \/ _` strip_assume_tac >>
      gvs[bytecode_stack_io_def,call_has_value_def,opcode_def,REPLICATE_compute]) >>
  `bytecode_stack_describes
     (DROP (6+(if call_has_value op then 1 else 0)) a)
     (DROP (6+(if call_has_value op then 1 else 0)) c.stack)` by
    metis_tac[bytecode_stack_describes_drop] >>
  gvs[sb_call_post_def] >>
  metis_tac[sb_call_obs_at,LENGTH_MAP])
QED
