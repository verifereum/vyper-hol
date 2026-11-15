Theory loweringBudgetOraclePrefix
Ancestors
  loweringCallBudgetHistory loweringBudgetRecorderOutcomes
  loweringBudgetCallOracleTransport loweringBudgetCreateOracleTransport
  loweringBudgetNonconsumingOracleTransport loweringBudgetFrameOracleTransport
  oracleExecProps ptrSafeRun opcodeClass contextCodegenRel list rich_list

Theorem budget_frame_restore[local]:
  (f' with cf_state := f'.cf_state with vs_outcomes := []) =
  (f with cf_state := f.cf_state with vs_outcomes := []) ==>
  f' = f with cf_state := f.cf_state with vs_outcomes := f'.cf_state.vs_outcomes
Proof
  disch_then (mp_tac o Q.AP_TERM
    `\u. u with cf_state := u.cf_state with vs_outcomes := f'.cf_state.vs_outcomes`) >>
  simp[]
QED

Theorem budget_step_append[local]:
  i.inst_opcode <> INVOKE /\
  step_inst fuel ctx i s = OK t /\
  (MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
    s.vs_outcomes <> []) ==>
  step_inst fuel ctx i (s with vs_outcomes := s.vs_outcomes ++ extra) =
    OK (t with vs_outcomes := t.vs_outcomes ++ extra) /\
  step_taint i (s with vs_outcomes := s.vs_outcomes ++ extra)
    (t with vs_outcomes := t.vs_outcomes ++ extra) tn = step_taint i s t tn
Proof
  strip_tac >>
  Cases_on `MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`
  >- (Cases_on `s.vs_outcomes` >- metis_tac[] >>
      rename1 `s.vs_outcomes = oc::os` >>
      `s with vs_outcomes := oc::os = s` by
        (qpat_x_assum `s.vs_outcomes = _` (fn th => simp[GSYM th])) >>
      `step_inst fuel ctx i s = OK (t with vs_outcomes := os)` by
        (Cases_on `MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL]`
         >- (drule_all call_step_same_outcome_head >>
             disch_then (qspec_then `os` mp_tac) >> simp[]) >>
         `MEM i.inst_opcode [CREATE; CREATE2]` by gvs[MEM] >>
         drule_all create_step_same_outcome_head >>
         disch_then (qspec_then `os` mp_tac) >> simp[]) >>
      `t.vs_outcomes = os` by
        (gvs[] >> qpat_x_assum `t with vs_outcomes := os = t`
          (mp_tac o Q.AP_TERM `\u. u.vs_outcomes`) >> simp[]) >>
      conj_tac
      >- (simp[] >> Cases_on `MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL]` >>
          metis_tac[call_step_same_outcome_head, create_step_same_outcome_head, MEM]) >>
      simp[step_taint_same_head_outcomes_update])
  >> conj_tac
  >- (drule_all nonconsuming_step_outcomes_update >>
      disch_then (qspec_then `s.vs_outcomes` mp_tac) >> simp[] >>
      disch_then (mp_tac o Q.AP_TERM `\u. u.vs_outcomes`) >>
      simp[] >> strip_tac >>
      drule_all nonconsuming_step_outcomes_update >>
      disch_then (qspec_then `s.vs_outcomes ++ extra` mp_tac) >> simp[])
  >> irule step_taint_noncall_outcomes_update >> gvs[MEM]
QED

Theorem budget_enters_append[local]:
  enters_block fn s t ==>
  enters_block fn (s with vs_outcomes := s.vs_outcomes ++ extra)
    (t with vs_outcomes := t.vs_outcomes ++ extra)
Proof
  strip_tac >>
  `t.vs_outcomes = s.vs_outcomes` by
    (fs[enters_block_def] >> drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
     disch_then (mp_tac o Q.AP_TERM `\u. u.vs_outcomes`) >> simp[]) >>
  drule enters_block_outcomes_update >>
  disch_then (qspec_then `s.vs_outcomes ++ extra` mp_tac) >> simp[]
QED

Theorem budget_path_append[local]:
  !checked cfg root h marks p.
    lower_budget_path checked cfg root h marks p ==>
    checked = F ==>
    !extra stack.
      lower_history_count h <= LENGTH root.bp_state.vs_outcomes /\
      MAP (\f. f with cf_state := f.cf_state with vs_outcomes := []) stack =
      MAP (\f. f with cf_state := f.cf_state with vs_outcomes := []) root.bp_stack ==>
      ?h' stack'.
        lower_budget_path F cfg
          (root with <| bp_stack := stack; bp_state := root.bp_state with
            vs_outcomes := root.bp_state.vs_outcomes ++ extra |>)
          h' marks
          (p with <| bp_stack := stack'; bp_state := p.bp_state with
            vs_outcomes := p.bp_state.vs_outcomes ++ extra |>) /\
        LENGTH h' = LENGTH h /\
        lower_history_count h' = lower_history_count h /\
        LENGTH (FILTER lower_event_allocates h') =
          LENGTH (FILTER lower_event_allocates h) /\
        MAP (\e. case e of
            BudgetStep n a i fuel r b => (n,i)
          | BudgetCall n a i fn cs b => (n,i)
          | BudgetReturn n a i fuel ret se sb b => (n,i)) h' =
        MAP (\e. case e of
            BudgetStep n a i fuel r b => (n,i)
          | BudgetCall n a i fn cs b => (n,i)
          | BudgetReturn n a i fuel ret se sb b => (n,i)) h /\
        MAP (\f. f with cf_state := f.cf_state with vs_outcomes := []) stack' =
        MAP (\f. f with cf_state := f.cf_state with vs_outcomes := []) p.bp_stack
Proof
  ho_match_mp_tac lower_budget_path_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume budget_path_append[entry]:
  qexists_tac `stack` >>
  simp[lower_history_count_def] >>
  irule lower_budget_path_entry >>
  simp[active_inst_outcomes_update] >> metis_tac[]
QED

Resume budget_path_append[next]:
  first_x_assum (qspecl_then [`extra`, `stack`] mp_tac) >>
      impl_tac >- (gvs[lower_history_count_def, FILTER_APPEND,
        lower_event_consumes_def] >> decide_tac) >>
      strip_tac >>
      `MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
       p.bp_state.vs_outcomes <> []` by
        (strip_tac >>
         qpat_assum `lower_budget_path F _ root h marks p`
           (mp_then Any mp_tac lower_budget_path_outcomes) >> strip_tac >>
         qpat_x_assum `lower_history_count (_ ++ _) <= _` mp_tac >>
         simp[lower_history_count_def, FILTER_APPEND, lower_event_consumes_def] >>
         strip_tac >> strip_tac >>
         qpat_x_assum `_ = []` (mp_tac o Q.AP_TERM `LENGTH`) >>
         simp[LENGTH_DROP] >> decide_tac) >>
      drule_all budget_step_append >>
      disch_then (qspecl_then [`p.bp_taint`, `extra`] strip_assume_tac) >>
      qmatch_asmsub_abbrev_tac `lower_budget_path F _ _ h' marks pp` >>
      qabbrev_tac `tt = t with vs_outcomes := t.vs_outcomes ++ extra` >>
      qabbrev_tac `qq = pp with <|
        bp_state := tt with vs_inst_idx := SUC pp.bp_state.vs_inst_idx;
        bp_prov := step_prov pp.bp_params pp.bp_prov i tt;
        bp_taint := step_taint i pp.bp_state tt pp.bp_taint |>` >>
      `lower_budget_path F (D,lo,explicit,ctx)
        (root with <| bp_stack := stack; bp_state := root.bp_state with
          vs_outcomes := root.bp_state.vs_outcomes ++ extra |>)
        (h' ++ [BudgetStep (LENGTH h') pp i fuel (OK tt) qq])
        (marks ++ MAP (\key. key IN explicit)
          (gas_events_step fuel ctx pp.bp_fn.fn_name i pp.bp_state)) qq` by
        (irule lower_budget_path_next >>
         simp[Abbr `qq`] >> fs[Abbr `pp`, Abbr `tt`, active_inst_def] >>
         metis_tac[]) >>
      qexistsl [`h' ++ [BudgetStep (LENGTH h') pp i fuel (OK tt) qq]`, `stack'`] >>
      fs[Abbr `qq`, Abbr `pp`, Abbr `tt`, step_prov_outcomes_update,
        gas_events_step_outcomes_update, lower_history_count_def, FILTER_APPEND,
        lower_event_consumes_def, lower_event_allocates_def, COND_RAND] >>
      gvs[gas_events_step_outcomes_update]
QED

Resume budget_path_append[block]:
  first_x_assum (qspecl_then [`extra`, `stack`] mp_tac) >>
      impl_tac >- (gvs[lower_history_count_def, FILTER_APPEND,
        lower_event_consumes_def] >> decide_tac) >> strip_tac >>
      `i.inst_opcode <> INVOKE /\
       ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]` by
        (Cases_on `i.inst_opcode` >> gvs[venomInstTheory.is_terminator_def]) >>
      qpat_assum `step_inst fuel ctx i p.bp_state = OK t`
        (mp_then Any mp_tac budget_step_append) >>
      simp[] >> disch_then (qspecl_then [`p.bp_taint`, `extra`] strip_assume_tac) >>
      drule budget_enters_append >> disch_then (qspec_then `extra` assume_tac) >>
      qmatch_asmsub_abbrev_tac `lower_budget_path F _ _ h' marks pp` >>
      qabbrev_tac `tt = t with vs_outcomes := t.vs_outcomes ++ extra` >>
      qabbrev_tac `ee = entered with vs_outcomes := entered.vs_outcomes ++ extra` >>
      qabbrev_tac `qq = pp with <|bp_state := ee;
        bp_prov := entry_prov pp.bp_fn tt pp.bp_prov;
        bp_taint := entry_taint_vars pp.bp_fn tt pp.bp_taint |>` >>
      `lower_budget_path F (D,lo,explicit,ctx)
        (root with <| bp_stack := stack; bp_state := root.bp_state with
          vs_outcomes := root.bp_state.vs_outcomes ++ extra |>)
        (h' ++ [BudgetStep (LENGTH h') pp i fuel (OK tt) qq])
        (marks ++ MAP (\key. key IN explicit)
          (gas_events_step fuel ctx pp.bp_fn.fn_name i pp.bp_state)) qq` by
        (irule lower_budget_path_block >>
         simp[Abbr `qq`] >> fs[Abbr `pp`, Abbr `tt`, Abbr `ee`, active_inst_def] >>
         metis_tac[]) >>
      qexistsl [`h' ++ [BudgetStep (LENGTH h') pp i fuel (OK tt) qq]`, `stack'`] >>
      fs[Abbr `qq`, Abbr `pp`, Abbr `tt`, Abbr `ee`, entry_prov_outcomes_update,
        entry_taint_outcomes_update, gas_events_step_outcomes_update,
        lower_history_count_def, FILTER_APPEND,
        lower_event_consumes_def, lower_event_allocates_def, COND_RAND] >>
      gvs[gas_events_step_outcomes_update]
QED

Resume budget_path_append[call]:
  rename1 `decode_invoke ii = SOME (nm,ops)` >>
      first_x_assum (qspecl_then [`extra`, `stack`] mp_tac) >>
      impl_tac >- gvs[lower_history_count_def, FILTER_APPEND,
        lower_event_consumes_def] >> strip_tac >>
      `cs.vs_outcomes = p.bp_state.vs_outcomes` by
        metis_tac[calleeTransportTheory.setup_callee_oracle] >>
      drule setup_callee_outcomes_update >>
      disch_then (qspec_then `p.bp_state.vs_outcomes ++ extra` assume_tac) >>
      drule budget_enters_append >> disch_then (qspec_then `extra` assume_tac) >>
      qmatch_asmsub_abbrev_tac `lower_budget_path F _ _ h' marks pp` >>
      qabbrev_tac `cc = cs with vs_outcomes := cs.vs_outcomes ++ extra` >>
      qabbrev_tac `ee = entered with vs_outcomes := entered.vs_outcomes ++ extra` >>
      qabbrev_tac `ff = <|cf_fn := pp.bp_fn; cf_inst := ii;
        cf_state := pp.bp_state; cf_params := pp.bp_params;
        cf_prov := pp.bp_prov; cf_tvar := pp.bp_taint.t_var|>` >>
      qabbrev_tac `qq = <|bp_stack := ff::pp.bp_stack;
        bp_params := MAP (op_prov pp.bp_prov) ops;
        bp_prov := FEMPTY; bp_taint := pp.bp_taint with t_var := FEMPTY;
        bp_fn := callee; bp_state := ee|>` >>
      `lower_budget_path F (D,lo,explicit,ctx)
        (root with <| bp_stack := stack; bp_state := root.bp_state with
          vs_outcomes := root.bp_state.vs_outcomes ++ extra |>)
        (h' ++ [BudgetCall (LENGTH h') pp ii callee cc qq]) marks qq` by
        (irule lower_budget_path_call >>
         simp[Abbr `qq`, Abbr `ff`] >>
         fs[Abbr `pp`, Abbr `cc`, Abbr `ee`, active_inst_def,
            eval_operands_outcomes_update] >> metis_tac[]) >>
      qexistsl [`h' ++ [BudgetCall (LENGTH h') pp ii callee cc qq]`,
        `ff::stack'`] >>
      fs[Abbr `qq`, Abbr `pp`, Abbr `cc`, Abbr `ee`, Abbr `ff`,
        lower_history_count_def, FILTER_APPEND,
        lower_event_consumes_def, lower_event_allocates_def] >> gvs[]
QED

Resume budget_path_append[ret]:
  first_x_assum (qspecl_then [`extra`, `stack`] mp_tac) >>
  (impl_tac >- gvs[lower_history_count_def, FILTER_APPEND,
    lower_event_consumes_def]) >> strip_tac >>
  rename1 `MAP _ saved = _::_` >>
  Cases_on `saved` >- gvs[] >>
  rename1 `MAP _ (ff::tail) = _::_` >> gvs[] >>
  `ff.cf_state.vs_inst_idx = f.cf_state.vs_inst_idx` by
    (qpat_assum `ff with cf_state := _ = _`
      (mp_tac o Q.AP_TERM `\u. u.cf_state.vs_inst_idx`) >> simp[]) >>
  `ff = f with cf_state := f.cf_state with vs_outcomes := ff.cf_state.vs_outcomes`
    by metis_tac[budget_frame_restore] >>
  `s_end with vs_outcomes := p.bp_state.vs_outcomes = s_end` by
    (drule intret_outcomes_update >>
     disch_then (qspec_then `p.bp_state.vs_outcomes` mp_tac) >> simp[]) >>
  `s_end.vs_outcomes = p.bp_state.vs_outcomes` by
    (qpat_x_assum `s_end with vs_outcomes := _ = s_end`
       (mp_tac o Q.AP_TERM `\u. u.vs_outcomes`) >> simp[]) >>
  `s'.vs_outcomes = p.bp_state.vs_outcomes` by
    (drule calleeTransportTheory.bind_outputs_oracle >>
     simp[]) >>
  `i.inst_opcode <> INVOKE` by metis_tac[step_inst_intret_not_invoke] >>
  drule intret_outcomes_update >>
  disch_then (qspec_then `p.bp_state.vs_outcomes ++ extra` assume_tac) >>
  drule bind_outputs_outcomes_update >>
  disch_then (qspec_then `p.bp_state.vs_outcomes ++ extra` assume_tac) >>
  qmatch_asmsub_abbrev_tac `lower_budget_path F _ _ h' marks pp` >>
  qabbrev_tac `ee = s_end with vs_outcomes := p.bp_state.vs_outcomes ++ extra` >>
  qabbrev_tac `bb = s' with vs_outcomes := s'.vs_outcomes ++ extra` >>
  qabbrev_tac `qq = <|bp_stack := tail; bp_params := ff.cf_params;
    bp_prov := DRESTRICT ff.cf_prov (COMPL (set ff.cf_inst.inst_outputs));
    bp_taint := pp.bp_taint with t_var :=
      DRESTRICT ff.cf_tvar (COMPL (set ff.cf_inst.inst_outputs));
    bp_fn := ff.cf_fn;
    bp_state := bb with vs_inst_idx := SUC ff.cf_state.vs_inst_idx|>` >>
  `lower_budget_path F (D,lo,explicit,ctx)
    (root with <| bp_stack := stack; bp_state := root.bp_state with
      vs_outcomes := root.bp_state.vs_outcomes ++ extra |>)
    (h' ++ [BudgetReturn (LENGTH h') pp i fuel ret ee bb qq])
    (marks ++ MAP (\key. key IN explicit)
      (gas_events_step fuel ctx pp.bp_fn.fn_name i pp.bp_state)) qq` by
    (irule lower_budget_path_ret >>
     simp[Abbr `qq`] >>
     fs[Abbr `pp`, Abbr `ee`, Abbr `bb`, active_inst_def] >>
     qpat_assum `ff = _` (fn th => once_rewrite_tac[th]) >>
     simp[merge_callee_outcomes_update, adopt_return_outcomes_update] >>
     metis_tac[]) >>
  qexistsl [`h' ++ [BudgetReturn (LENGTH h') pp i fuel ret ee bb qq]`, `tail`] >>
  fs[Abbr `qq`, Abbr `pp`, Abbr `ee`, Abbr `bb`,
    lower_history_count_def, FILTER_APPEND,
    lower_event_consumes_def, lower_event_allocates_def] >>
  gvs[ptrDisciplineTheory.call_frame_component_equality,
    gas_events_step_outcomes_update]
QED

Finalise budget_path_append

Theorem lower_budget_path_append_outcomes:
  !D lo explicit ctx p h marks q extra.
    lower_budget_path F (D,lo,explicit,ctx) p h marks q /\
    lower_history_count h <= LENGTH p.bp_state.vs_outcomes ==>
    ?h' q'.
      lower_budget_path F (D,lo,explicit,ctx)
        (p with bp_state := p.bp_state with vs_outcomes :=
          p.bp_state.vs_outcomes ++ extra) h' marks q' /\
      LENGTH h' = LENGTH h /\
      lower_history_count h' = lower_history_count h /\
      LENGTH (FILTER lower_event_allocates h') =
        LENGTH (FILTER lower_event_allocates h) /\
      MAP (\e. case e of
          BudgetStep n a i fuel r b => (n,i)
        | BudgetCall n a i fn cs b => (n,i)
        | BudgetReturn n a i fuel ret se sb b => (n,i)) h' =
      MAP (\e. case e of
          BudgetStep n a i fuel r b => (n,i)
        | BudgetCall n a i fn cs b => (n,i)
        | BudgetReturn n a i fuel ret se sb b => (n,i)) h /\
      q'.bp_fn = q.bp_fn /\ q'.bp_params = q.bp_params /\
      q'.bp_prov = q.bp_prov /\ q'.bp_taint = q.bp_taint /\
      (q'.bp_state with vs_outcomes := []) =
        (q.bp_state with vs_outcomes := []) /\
      q'.bp_state.vs_outcomes =
        DROP (lower_history_count h) p.bp_state.vs_outcomes ++ extra /\
      MAP (\f. f with cf_state := f.cf_state with vs_outcomes := [])
        q'.bp_stack =
      MAP (\f. f with cf_state := f.cf_state with vs_outcomes := [])
        q.bp_stack
Proof
  rpt strip_tac >>
  drule lower_budget_path_outcomes >> strip_tac >>
  drule budget_path_append >> simp[] >>
  disch_then (qspecl_then [`extra`, `p.bp_stack`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`h'`, `q with <|bp_stack := stack'; bp_state :=
    q.bp_state with vs_outcomes := q.bp_state.vs_outcomes ++ extra|>`] >>
  Cases_on `p` >> gvs[lower_budget_point_fn_updates]
QED
