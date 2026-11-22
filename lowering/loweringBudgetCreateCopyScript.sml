(* The create_copy_of allocation window on an unchecked recorder path. *)
Theory loweringBudgetCreateCopy
Ancestors
  runtimePeakMemoryCode loweringBudgetDallocaWindows loweringBudgetAccountCodes
  dallocaCreateGeometry
  loweringBudgetPathDeterminism loweringBudgetStoreRecorder
  loweringCallBudgetHistory exprLoweringProps venomExecProofs
  fnBlockBodySteps contextCodegenRel contextCodegenRelProps lowerDloadPtrRawReachable
  instIdxIndep fragExec venomExecSemantics
  venomInst venomState list rich_list arithmetic words

Theorem create_copy_dalloca_window_parts[local]:
  create_copy_dalloca_window fn i s ==>
  ?bb prefix prologue middle effect suffix chunk.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = prefix ++ chunk ++ suffix /\
    chunk = prologue ++ i :: middle ++ [effect] /\
    create_copy_dalloca_chunk chunk 5 /\
    s.vs_inst_idx = LENGTH prefix + 5 /\
    LENGTH prologue = 5 /\ LENGTH middle = 5 /\
    i.inst_opcode = DALLOCA /\
    MEM effect.inst_opcode [CREATE; CREATE2] /\
    DROP s.vs_inst_idx bb.bb_instructions = i :: middle ++ effect :: suffix /\
    EL (LENGTH prefix + 4) bb.bb_instructions = EL 4 chunk /\
    (EL 4 chunk).inst_opcode <> PHI /\ (EL 4 chunk).inst_opcode <> INVOKE /\
    ~is_terminator (EL 4 chunk).inst_opcode /\
    EVERY (\j. ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
               ~MEM j.inst_opcode [DALLOCA;CALL;STATICCALL;DELEGATECALL;
                                   CREATE;CREATE2]) middle
Proof
  pure_rewrite_tac[create_copy_dalloca_window_def] >> strip_tac >>
  drule create_copy_dalloca_chunk_parts >> strip_tac >>
  `i = alloc` by gvs[EL_APPEND_EQN] >>
  `DROP (LENGTH prefix + 5) bb.bb_instructions = i :: middle ++ effect :: suffix` by
    (`bb.bb_instructions = (prefix ++ prologue) ++ (i :: middle ++ effect :: suffix)` by
       fs[APPEND_ASSOC] >>
     `LENGTH prefix + 5 = LENGTH (prefix ++ prologue)` by simp[] >>
     pop_assum SUBST1_TAC >>
     asm_rewrite_tac[DROP_LENGTH_APPEND]) >>
  qexistsl_tac [`bb`, `prefix`, `prologue`, `middle`, `effect`, `suffix`, `chunk`] >>
  simp[EL_APPEND_EQN] >>
  fs[EVERY_EL] >> metis_tac[DECIDE ``4 < 5``]
QED

Theorem lower_budget_raw_call_current_size[local]:
  root.bp_stack = [] /\ enters_block root.bp_fn start root.bp_state /\
  lower_budget_path F (D,lo,explicit,ctx) root h marks q /\
  LENGTH root.bp_state.vs_call_ctx.cc_calldata < 2 ** 64 /\
  ALL_DISTINCT (fn_labels q.bp_fn) /\
  raw_call_dalloca_window q.bp_fn i q.bp_state /\
  i.inst_operands = [op] /\ eval_operand op q.bp_state = SOME sz ==>
  w2n sz < 2 ** 64
Proof
  rewrite_tac[raw_call_dalloca_window_def] >> BETA_TAC >> strip_tac >>
  `k < LENGTH bb.bb_instructions /\
   EL k bb.bb_instructions = mk_inst size_id CALLDATASIZE [] [x]` by
    metis_tac[DROP_EQ_CONS] >>
  drule_all lower_budget_dalloca_calldata_size >> strip_tac >>
  `op = Var x` by gvs[mk_inst_def] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem lower_budget_create_copy_size:
  root.bp_stack = [] /\ enters_block root.bp_fn start root.bp_state /\
  lower_budget_path F (D,lo,explicit,ctx) root h marks q /\
  account_code_lengths_ok root.bp_state.vs_accounts /\
  outcomes_accounts_typed (SOME root.bp_state.vs_outcomes) /\
  ALL_DISTINCT (fn_labels q.bp_fn) /\
  create_copy_dalloca_window q.bp_fn i q.bp_state ==>
  ?op sz. i.inst_operands = [op] /\
          eval_operand op q.bp_state = SOME sz /\ w2n sz < 2 ** 64
Proof
  pure_rewrite_tac[create_copy_dalloca_window_def] >> strip_tac >>
  drule create_copy_dalloca_chunk_parts >> strip_tac >>
  `LENGTH prefix + 5 < LENGTH bb.bb_instructions` by simp[] >>
  `!j. LENGTH prefix <= j /\ j < LENGTH prefix + 5 ==>
       (EL j bb.bb_instructions).inst_opcode <> PHI /\
       (EL j bb.bb_instructions).inst_opcode <> INVOKE` by
    (gen_tac >> strip_tac >>
     `~(j < LENGTH prefix) /\ j - LENGTH prefix < LENGTH prologue` by decide_tac >>
     `EL j bb.bb_instructions = EL (j - LENGTH prefix) prologue` by
       (full_simp_tac pure_ss [GSYM APPEND_ASSOC, APPEND] >> simp[EL_APPEND_EQN]) >>
     qpat_x_assum `EVERY _ prologue` (mp_tac o REWRITE_RULE [EVERY_EL]) >>
     disch_then (qspec_then `j - LENGTH prefix` mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`5`, `LENGTH (prefix:instruction list)`, `root`, `h`, `marks`, `q`,
                  `start`, `bb`] lower_budget_before_window) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `ALL_DISTINCT (fn_labels p.bp_fn) /\
   lookup_block p.bp_state.vs_current_bb p.bp_fn.fn_blocks = SOME bb` by metis_tac[] >>
  `TAKE (LENGTH h0) h = h0` by metis_tac[IS_PREFIX_APPEND, TAKE_LENGTH_APPEND] >>
  `isPREFIX prologue (DROP p.bp_state.vs_inst_idx bb.bb_instructions)` by
    (full_simp_tac pure_ss [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prologue` by
    fs[EVERY_MEM] >>
  mp_tac (Q.SPECL [`prologue`, `LENGTH (h0:lower_budget_event list)`, `m`, `p`]
    (Q.INST [`last` |-> `q`] lower_budget_run_window)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `TAKE (LENGTH h0 + LENGTH prologue) h = h` by simp[TAKE_LENGTH_ID] >>
  `q' = q` by metis_tac[lower_budget_path_history_unique] >>
  `account_code_lengths_ok p.bp_state.vs_accounts` by
    metis_tac[lower_budget_path_account_code_lengths] >>
  `TAKE 5 chunk = prologue` by simp[TAKE_APPEND1] >>
  mp_tac (Q.INST [`s` |-> `p.bp_state`, `t` |-> `t`]
    create_copy_dalloca_chunk_size) >>
  impl_tac >- metis_tac[] >>
  qpat_x_assum `q' = q` SUBST_ALL_TAC >>
  asm_rewrite_tac[] >> simp[eval_op_inst_idx]
QED

Theorem lower_budget_create_copy_alloc_record:
  root.bp_stack = [] /\ enters_block root.bp_fn start root.bp_state /\
  lower_budget_path F (D,lo,explicit,ctx) root h marks last /\
  account_code_lengths_ok root.bp_state.vs_accounts /\
  outcomes_accounts_typed (SOME root.bp_state.vs_outcomes) /\
  n < LENGTH h /\ EL n h = BudgetStep n p i fuel (OK t) q /\
  i.inst_opcode = DALLOCA /\ ALL_DISTINCT (fn_labels p.bp_fn) /\
  create_copy_dalloca_window p.bp_fn i p.bp_state ==>
  ?op sz. lower_alloc_record h n p.bp_fn i p.bp_state op sz t
Proof
  strip_tac >> drule_all lower_budget_path_at_base_step >> strip_tac >>
  drule_all lower_budget_create_copy_size >> strip_tac >>
  qexistsl_tac [`op`, `sz`] >> simp[lower_alloc_record_def] >>
  qpat_x_assum `w2n sz < _` mp_tac >> simp[] >> decide_tac
QED

Theorem lower_budget_create_copy_effect_record[local]:
  root.bp_stack = [] /\ enters_block root.bp_fn start root.bp_state /\
  lower_budget_path F (D,lo,explicit,ctx) root h marks last /\
  lower_budget_path F (D,lo,explicit,ctx) root (TAKE n h) m p /\
  n + 6 < LENGTH h /\ ALL_DISTINCT (fn_labels p.bp_fn) /\
  lookup_block p.bp_state.vs_current_bb p.bp_fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ chunk ++ suffix /\
  chunk = prologue ++ i :: middle ++ [effect] /\
  create_copy_dalloca_chunk chunk 5 /\
  p.bp_state.vs_inst_idx = LENGTH prefix + 5 /\
  LENGTH prologue = 5 /\ LENGTH middle = 5 /\
  i.inst_opcode = DALLOCA /\ MEM effect.inst_opcode [CREATE; CREATE2] /\
  DROP p.bp_state.vs_inst_idx bb.bb_instructions = i :: middle ++ effect :: suffix /\
  EL (LENGTH prefix + 4) bb.bb_instructions = EL 4 chunk /\
  (EL 4 chunk).inst_opcode <> PHI /\ (EL 4 chunk).inst_opcode <> INVOKE /\
  ~is_terminator (EL 4 chunk).inst_opcode /\
  EVERY (\j. ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
             ~MEM j.inst_opcode [DALLOCA;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2])
    middle /\
  i.inst_operands = [op] /\ eval_operand op p.bp_state = SOME sz ==>
  ?ep ef et eq ws.
    EL (n + 6) h = BudgetStep (n + 6) ep effect ef (OK et) eq /\
    ep.bp_fn = p.bp_fn /\ ep.bp_stack = p.bp_stack /\
    eval_operands effect.inst_operands ep.bp_state = SOME ws /\
    ?v len salt.
      ((effect.inst_opcode = CREATE /\ ws = [v;p.bp_state.vs_fmp + 21w;len]) \/
       (effect.inst_opcode = CREATE2 /\ ws = [v;p.bp_state.vs_fmp + 21w;len;salt])) /\
      sz = len + 21w
Proof
  strip_tac >>
  `EVERY (\j. ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE)
     (i :: middle)` by fs[EVERY_MEM, is_terminator_def] >>
  `isPREFIX (i :: middle) (DROP p.bp_state.vs_inst_idx bb.bb_instructions)` by
    (simp[] >> metis_tac[IS_PREFIX_APPEND, APPEND]) >>
  mp_tac (Q.SPECL [`i :: middle`, `n`, `m`, `p`] lower_budget_run_window) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `DROP q.bp_state.vs_inst_idx bb.bb_instructions = effect :: suffix` by
    (`q.bp_state.vs_inst_idx = LENGTH (i :: middle) + p.bp_state.vs_inst_idx`
       by simp[ADD_COMM] >>
     pop_assum (fn th => rewrite_tac[th]) >>
     once_rewrite_tac[GSYM DROP_DROP_T] >>
     qpat_assum `DROP p.bp_state.vs_inst_idx bb.bb_instructions = _`
       (fn th => rewrite_tac[th]) >>
     `i :: (middle ++ effect :: suffix) = (i :: middle) ++ effect :: suffix` by simp[] >>
     pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
     REWRITE_TAC[DROP_LENGTH_APPEND]) >>
  `ALL_DISTINCT (fn_labels q.bp_fn) /\
   lookup_block q.bp_state.vs_current_bb q.bp_fn.fn_blocks = SOME bb` by metis_tac[] >>
  `active_inst q.bp_fn effect q.bp_state` by
    (drule DROP_EQ_CONS >> strip_tac >> irule lookup_instruction_active >>
     qexists_tac `bb` >> simp[get_instruction_def]) >>
  `~is_terminator effect.inst_opcode /\ effect.inst_opcode <> INVOKE` by
    fs[MEM, is_terminator_def] >>
  `lower_budget_path F (D,lo,explicit,ctx) root (TAKE (n + 6) h) m' q` by
    (`LENGTH (i :: middle) = 6` by simp[] >>
     pop_assum (fn len =>
       qpat_assum `lower_budget_path _ _ _ (TAKE (n + LENGTH (i :: middle)) h) m' q`
         (ACCEPT_TAC o PURE_REWRITE_RULE [len]))) >>
  drule_all (Q.INST [`n` |-> `n + 6`, `i` |-> `effect`, `p` |-> `q`]
    lower_budget_window_index_next) >> strip_tac >>
  `?ws. eval_operands effect.inst_operands q.bp_state = SOME ws` by
    (qpat_x_assum `step_inst_base effect q.bp_state = _` mp_tac >>
     fs[MEM, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rpt strip_tac >> fs[eval_operands_def]) >>
  `p.bp_state.vs_inst_idx = SUC (LENGTH prefix + 4) /\
    LENGTH prefix + 4 < LENGTH bb.bb_instructions` by fs[] >>
  mp_tac (Q.INST [`k` |-> `LENGTH (prefix:instruction list) + 4`,
                  `q` |-> `p`, `h` |-> `TAKE n h`, `marks` |-> `m`]
    lower_budget_window_has_prev) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[])) >>
  strip_tac >>
  `?seed. run_inst_seq [EL 4 chunk] seed = OK p.bp_state` by
    (rename1 `step_inst_base _ prev.bp_state = OK u` >>
     qexists_tac `prev.bp_state with vs_inst_idx := p.bp_state.vs_inst_idx` >>
     qpat_assum `EL (LENGTH prefix + 4) bb.bb_instructions = _` (fn el =>
       qpat_assum `step_inst_base _ prev.bp_state = OK u`
         (ASSUME_TAC o PURE_REWRITE_RULE [el])) >>
     qpat_assum `p.bp_state = _` (fn eq => PURE_ONCE_REWRITE_TAC [eq]) >>
     asm_simp_tac bool_ss [run_inst_seq_def, step_inst_inst_idx_indep,
       exec_result_map_def, exec_result_case_def, combinTheory.K_THM,
       venomStateTheory.venom_state_accfupds]) >>
  `TAKE 6 (DROP 5 chunk) = i :: middle /\
   EL 5 chunk = i /\ EL 11 chunk = effect` by
    simp[EL_APPEND_EQN, TAKE_APPEND1, DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
  `eval_operands effect.inst_operands t = SOME ws` by
    (qpat_assum `q.bp_state = _` (fn eq =>
       qpat_assum `eval_operands _ q.bp_state = SOME ws`
         (ACCEPT_TAC o PURE_REWRITE_RULE [eq, eval_ops_inst_idx]))) >>
  mp_tac (Q.INST [`pre` |-> `p.bp_state`, `ready` |-> `t`]
    create_copy_dalloca_chunk_geometry) >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >>
  qexistsl_tac [`q`, `fuel`, `t'`, `q'`, `ws`] >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED

Theorem lower_budget_create_copy_recorded_window:
  root.bp_stack = [] /\ enters_block root.bp_fn start root.bp_state /\
  lower_budget_path F (D,lo,explicit,ctx) root h marks last /\
  account_code_lengths_ok root.bp_state.vs_accounts /\
  outcomes_accounts_typed (SOME root.bp_state.vs_outcomes) /\
  n < LENGTH h /\ EL n h = BudgetStep n p i fuel (OK t) q /\
  i.inst_opcode = DALLOCA /\ ALL_DISTINCT (fn_labels p.bp_fn) /\
  create_copy_dalloca_window p.bp_fn i p.bp_state ==>
  lower_history_window h last n
Proof
  strip_tac >>
  drule_all lower_budget_create_copy_alloc_record >> strip_tac >>
  drule create_copy_dalloca_window_parts >> strip_tac >>
  drule_all lower_budget_path_at_base_step >> strip_tac >>
  `i.inst_operands = [op] /\ eval_operand op p.bp_state = SOME sz` by
    fs[lower_alloc_record_def] >>
  `EVERY (\j. ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE)
     (i :: middle)` by fs[EVERY_MEM, is_terminator_def] >>
  `DROP p.bp_state.vs_inst_idx bb.bb_instructions = (i :: middle) ++ effect :: suffix`
    by simp[] >>
  pure_rewrite_tac[lower_history_window_def] >> BETA_TAC >>
  Cases_on `n + 6 < LENGTH h`
  >- (mp_tac lower_budget_create_copy_effect_record >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (qx_choosel_then [`ep`,`ef`,`et`,`eq`,`ws`]
        (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
      qexists_tac `n + 6` >>
      rpt conj_tac
      >- decide_tac
      >- decide_tac
      >- (strip_tac >> conj_tac >- fs[lower_event_consumes_def, MEM] >>
          qexistsl_tac [`p.bp_fn`, `i`, `p.bp_state`, `op`, `sz`, `t`,
                        `p`, `fuel`, `q`, `ep`, `effect`, `ef`, `et`, `eq`, `ws`] >>
          asm_rewrite_tac[] >> metis_tac[])
      >- (`n + 6 <> LENGTH h` by decide_tac >> simp[])
      >- (qexistsl_tac [`p.bp_fn`, `i`, `p.bp_state`, `op`, `sz`, `t`] >>
          first_assum ACCEPT_TAC) >>
      rpt strip_tac >>
      `isPREFIX (i :: middle) (DROP p.bp_state.vs_inst_idx bb.bb_instructions)` by
        (simp[] >> metis_tac[IS_PREFIX_APPEND, APPEND]) >>
      mp_tac (Q.SPECL [`i :: middle`, `n`, `m`, `p`] lower_budget_run_window) >>
      (impl_tac >- simp[]) >> strip_tac >>
      `0 < j - n /\ j - n < LENGTH (i :: middle) /\ n + (j - n) = j` by
        simp[] >> qpat_x_assum `!j. j < _ ==> _`
          (qspec_then `j - n` mp_tac) >> simp[] >> strip_tac >>
      `MEM (EL (j - n) (i :: middle)) middle` by
        (Cases_on `j - n` >> fs[] >> metis_tac[EL_MEM]) >>
      fs[EVERY_MEM] >> rpt (goal_assum (drule_at Any)) >>
      metis_tac[lower_event_allocates_def, lower_event_consumes_def, MEM]) >>
  qexists_tac `LENGTH h` >> simp[] >>
  `LENGTH h <= n + LENGTH (i :: middle)` by simp[] >>
  mp_tac (Q.INST [`steps` |-> `i :: middle`, `effect` |-> `effect`,
                  `rest` |-> `suffix`]
    lower_budget_pending_before_effect) >>
  (impl_tac >- simp[]) >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. active_inst _ i _ ==> _` drule >> strip_tac >>
      Cases_on `LENGTH h - n = LENGTH (i :: middle)`
      >- fs[EL_APPEND_EQN, MEM] >>
      `0 < LENGTH h - n /\ LENGTH h - n < LENGTH (i :: middle)` by decide_tac >>
      `MEM (EL (LENGTH h - n) ((i :: middle) ++ [effect])) middle` by
        (simp[EL_APPEND_EQN] >>
         Cases_on `LENGTH h - n` >> fs[] >> metis_tac[EL_MEM]) >>
      fs[EVERY_MEM, MEM] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `0 < j - n /\ j - n < LENGTH (i :: middle)` by simp[] >>
  qpat_x_assum `!j. n < j /\ j < LENGTH h ==> _` drule_all >> strip_tac >>
  `MEM (EL (j - n) (i :: middle)) middle` by
    (Cases_on `j - n` >> fs[] >> metis_tac[EL_MEM]) >>
  fs[EVERY_MEM] >> rpt (goal_assum (drule_at Any)) >>
  metis_tac[lower_event_allocates_def, lower_event_consumes_def, MEM]
QED

(* At a live DALLOCA, any prior Blueprint reservation has already reached
   its consuming CREATE. A prefix still in the window cannot reach a
   second DALLOCA. *)
Theorem lower_budget_blueprint_recorded_window:
  lower_budget_path F (D,lo,explicit,ctx) root h marks last /\
  active_inst last.bp_fn current last.bp_state /\ current.inst_opcode = DALLOCA /\
  n < LENGTH h /\ EL n h = BudgetStep n p i fuel (OK t) q /\
  ALL_DISTINCT (fn_labels p.bp_fn) /\
  create_blueprint_dalloca_window p.bp_fn i p.bp_state ==>
  lower_history_window h last n
Proof
  strip_tac >> drule create_blueprint_dalloca_window_parts >> strip_tac >>
  drule_all lower_budget_path_at_base_step >> strip_tac >>
  `EVERY (\j. ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE)
     (i :: middle)` by fs[EVERY_MEM, is_terminator_def] >>
  `!k. 0 < k /\ k < LENGTH (i :: middle) ==>
      MEM (EL k (i :: middle)) middle` by
    (Cases >> simp[] >> metis_tac[EL_MEM]) >>
  qabbrev_tac `b = n + LENGTH (i :: middle)` >>
  `n < b` by simp[Abbr `b`] >>
  `b < LENGTH h` by
    (CCONTR_TAC >>
     mp_tac (Q.INST [`steps` |-> `i :: middle`, `effect` |-> `effect`,
                     `rest` |-> `suffix`] lower_budget_pending_before_effect) >>
     impl_tac >- (fs[Abbr `b`] >> decide_tac) >> strip_tac >>
     `current = EL (LENGTH h - n) ((i :: middle) ++ [effect])` by metis_tac[] >>
     Cases_on `LENGTH h - n = LENGTH (i :: middle)`
     >- fs[EL_APPEND_EQN, MEM] >>
     `0 < LENGTH h - n /\ LENGTH h - n < LENGTH (i :: middle)` by
       (fs[Abbr `b`] >> decide_tac) >>
     `MEM current middle` by fs[EL_APPEND_EQN] >>
     fs[EVERY_MEM, MEM]) >>
  `isPREFIX (i :: middle) (DROP p.bp_state.vs_inst_idx bb.bb_instructions)` by
    metis_tac[IS_PREFIX_APPEND] >>
  mp_tac (Q.SPECL [`i :: middle`, `n`, `m`, `p`] lower_budget_run_window) >>
  (impl_tac >- (fs[Abbr `b`] >> decide_tac)) >> strip_tac >>
  rename1 `run_inst_seq (i :: middle) p.bp_state = OK ready` >>
  rename1 `lower_budget_path _ _ _ (TAKE (n + LENGTH (i :: middle)) h) em ep` >>
  `DROP ep.bp_state.vs_inst_idx bb.bb_instructions = effect :: suffix` by
    (simp[ADD_COMM, GSYM DROP_DROP_T, DROP_LENGTH_APPEND]) >>
  `active_inst ep.bp_fn effect ep.bp_state` by
    (drule DROP_EQ_CONS >> strip_tac >> irule lookup_instruction_active >>
     qexists_tac `bb` >> simp[get_instruction_def]) >>
  `ALL_DISTINCT (fn_labels ep.bp_fn) /\
   ~is_terminator effect.inst_opcode /\ effect.inst_opcode <> INVOKE` by
    fs[MEM, is_terminator_def] >>
  `lower_budget_path F (D,lo,explicit,ctx) root (TAKE b h) em ep` by
    simp[Abbr `b`] >>
  drule_all (Q.INST [`n` |-> `b`, `p` |-> `ep`, `i` |-> `effect`]
    lower_budget_window_index_next) >> strip_tac >>
  rename1 `EL b h = BudgetStep b ep effect ef (OK et) eq` >>
  `step_inst_base effect ready = OK et` by
    (fs[step_inst_inst_idx_indep, exec_result_map_def] >> metis_tac[]) >>
  drule_all create_blueprint_dalloca_chunk_geometry >> strip_tac >>
  `eval_operands effect.inst_operands ep.bp_state = SOME ws` by
    fs[eval_ops_inst_idx] >>
  `lower_alloc_record h n p.bp_fn i p.bp_state op sz t` by
    (simp[lower_alloc_record_def] >>
     qexistsl_tac [`p`, `fuel`, `q`] >>
     asm_rewrite_tac[] >> decide_tac) >>
  pure_rewrite_tac[lower_history_window_def] >> BETA_TAC >>
  qexists_tac `b` >> rpt conj_tac
  >- decide_tac
  >- decide_tac
  >- (strip_tac >> conj_tac >- fs[lower_event_consumes_def, MEM] >>
      qexistsl_tac [`p.bp_fn`, `i`, `p.bp_state`, `op`, `sz`, `t`,
                    `p`, `fuel`, `q`, `ep`, `effect`, `ef`, `et`, `eq`, `ws`] >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  TRY (decide_tac >> NO_TAC) >>
  TRY (qexistsl_tac [`p.bp_fn`, `i`, `p.bp_state`, `op`, `sz`, `t`] >>
       first_assum ACCEPT_TAC >> NO_TAC) >>
  rpt strip_tac >>
  `0 < j - n /\ j - n < LENGTH (i :: middle) /\ n + (j - n) = j` by
    fs[Abbr `b`] >>
  qpat_x_assum `!j. j < LENGTH (i :: middle) ==> _`
    (qspec_then `j - n` mp_tac) >> simp[] >> strip_tac >>
  `MEM (EL (j - n) (i :: middle)) middle` by metis_tac[] >>
  fs[EVERY_MEM] >> rpt (goal_assum (drule_at Any)) >>
  metis_tac[lower_event_allocates_def, lower_event_consumes_def, MEM]
QED

Theorem lower_budget_headroom_history_certificate:
  root.bp_stack = [] /\ MEM root.bp_fn ctx.ctx_functions /\
  enters_block root.bp_fn start root.bp_state /\
  lower_budget_path F (D,lo,explicit,ctx) root h marks q /\
  LENGTH root.bp_state.vs_call_ctx.cc_calldata < 2 ** 64 /\
  account_code_lengths_ok root.bp_state.vs_accounts /\
  outcomes_accounts_typed (SOME root.bp_state.vs_outcomes) /\
  (!fn. MEM fn ctx.ctx_functions ==> ALL_DISTINCT (fn_labels fn)) /\
  (!fn i s. MEM fn ctx.ctx_functions /\ active_inst fn i s /\
    i.inst_opcode = DALLOCA ==>
      raw_call_dalloca_window fn i s \/ create_copy_dalloca_window fn i s \/
      create_blueprint_dalloca_window fn i s) /\
  active_inst q.bp_fn current q.bp_state /\ current.inst_opcode = DALLOCA ==>
  ?pair. lower_history_pairs h pair /\
    (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==> pair n < LENGTH h) /\
    (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
      ?fn ai pre op sz post. lower_alloc_record h n fn ai pre op sz post)
Proof
  strip_tac >>
  `!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
       lower_history_window h q n` by
    (rpt strip_tac >> drule_all lower_budget_alloc_event >> strip_tac >>
     drule_all lower_budget_path_at_base_step >> strip_tac >>
     `MEM p.bp_fn ctx.ctx_functions` by metis_tac[lower_budget_path_current_fn_mem] >>
     `ALL_DISTINCT (fn_labels p.bp_fn)` by metis_tac[] >>
     `raw_call_dalloca_window p.bp_fn i p.bp_state \/
       create_copy_dalloca_window p.bp_fn i p.bp_state \/
       create_blueprint_dalloca_window p.bp_fn i p.bp_state` by metis_tac[]
     >- metis_tac[lower_budget_raw_call_recorded_window]
     >- metis_tac[lower_budget_create_copy_recorded_window] >>
     metis_tac[lower_budget_blueprint_recorded_window]) >>
  fs[lower_history_window_def] >>
  drule (BETA_RULE lower_history_pairs_before_allocation) >>
  metis_tac[]
QED

Theorem lower_budget_dynamic_history_certificate:
  root.bp_stack = [] /\ MEM root.bp_fn ctx.ctx_functions /\
  enters_block root.bp_fn start root.bp_state /\
  lower_budget_path F (D,lo,explicit,ctx) root h marks q /\
  LENGTH root.bp_state.vs_call_ctx.cc_calldata < 2 ** 64 /\
  account_code_lengths_ok root.bp_state.vs_accounts /\
  outcomes_accounts_typed (SOME root.bp_state.vs_outcomes) /\
  (!fn. MEM fn ctx.ctx_functions ==> ALL_DISTINCT (fn_labels fn)) /\
  (!fn i s. MEM fn ctx.ctx_functions /\ active_inst fn i s /\
    i.inst_opcode = DALLOCA ==>
      raw_call_dalloca_window fn i s \/ create_copy_dalloca_window fn i s) ==>
  ?pair. lower_history_pairs h pair /\ lower_history_current h pair q /\
    (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
      ?fn ai pre op sz post. lower_alloc_record h n fn ai pre op sz post)
Proof
  strip_tac >> match_mp_tac lower_history_pairs_from_recorded_windows >>
  conj_tac
  >- (rpt strip_tac >> drule_all lower_budget_alloc_event >> strip_tac >>
      drule_all lower_budget_path_at_base_step >> strip_tac >>
      `MEM p.bp_fn ctx.ctx_functions` by metis_tac[lower_budget_path_current_fn_mem] >>
      `ALL_DISTINCT (fn_labels p.bp_fn)` by metis_tac[] >>
      `raw_call_dalloca_window p.bp_fn i p.bp_state \/
       create_copy_dalloca_window p.bp_fn i p.bp_state` by metis_tac[]
      >- metis_tac[lower_budget_raw_call_recorded_window] >>
      metis_tac[lower_budget_create_copy_recorded_window]) >>
  rpt strip_tac >>
  `MEM q.bp_fn ctx.ctx_functions` by metis_tac[lower_budget_path_current_fn_mem] >>
  `ALL_DISTINCT (fn_labels q.bp_fn)` by metis_tac[] >>
  `raw_call_dalloca_window q.bp_fn i q.bp_state \/
   create_copy_dalloca_window q.bp_fn i q.bp_state` by metis_tac[] >>
  `w2n sz < 2 ** 64` by
    metis_tac[lower_budget_raw_call_current_size, lower_budget_create_copy_size,
              listTheory.CONS_11, optionTheory.SOME_11] >>
  decide_tac
QED
