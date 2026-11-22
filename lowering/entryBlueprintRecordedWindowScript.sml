Theory entryBlueprintRecordedWindow
Ancestors
  entryBlueprintBudgetSite loweringBudgetDallocaWindows dallocaCreateGeometry
  loweringCallBudgetHistory loweringBudgetStoreRecorder lowerDloadPtrRawReachable
  contextCodegenRel contextCodegenRelProps venomExecSemantics venomInst venomState venomExecProofs
  instIdxIndep fragExec exprLoweringProps context list rich_list arithmetic words

Theorem blueprint_reservation_insts[local]:
  compile_alloc_dynamic size_op sm = (alloc_ptr,sn) /\
  emitted_insts sm sn = [i] /\
  emit_void EXTCODECOPY [target;alloc_ptr;offset;code] sn = ((),se) /\
  (if args_len = Lit 0w then sc = se else
     ?dst x. emit_op ADD [alloc_ptr;code] se = (dst,x) /\
             compile_copy_memory_dynamic dst args_alloc_ptr args_len x = ((),sc)) ==>
  emitted_insts sm sc = i :: emitted_insts sn sc
Proof
  simp[compile_alloc_dynamic_def, compile_copy_memory_dynamic_def] >>
  strip_tac >> drule emit_op_extends >> strip_tac >>
  `sn.cs_current_insts = sm.cs_current_insts ++ [i]` by metis_tac[] >>
  `?tail. sc.cs_current_insts = sn.cs_current_insts ++ tail` by
    (Cases_on `args_len = Lit 0w` >> gvs[] >>
     metis_tac[emit_void_extends, emit_op_extends, APPEND_ASSOC]) >>
  qpat_assum `sc.cs_current_insts = _` (fn th =>
    pure_rewrite_tac[emitted_insts_def, th, DROP_LENGTH_APPEND]) >>
  qpat_assum `sn.cs_current_insts = _ ++ [i]`
    (fn th => pure_once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >> REFL_TAC
QED

Theorem blueprint_effect_args[local]:
  (case salt of NONE => effect.inst_opcode = CREATE /\
                       effect.inst_operands = [value;alloc_ptr;size_op]
     | SOME sop => effect.inst_opcode = CREATE2 /\
                   effect.inst_operands = [value;alloc_ptr;size_op;sop]) /\
  step_inst_base effect s = OK t /\
  eval_operand alloc_ptr s = SOME offset_word /\ eval_operand size_op s = SOME sz ==>
  ?ws. eval_operands effect.inst_operands s = SOME ws /\
       ?v w. (effect.inst_opcode = CREATE /\ ws = [v;offset_word;sz]) \/
             (effect.inst_opcode = CREATE2 /\ ws = [v;offset_word;sz;w])
Proof
  Cases_on `salt` >> simp[] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, eval_operands_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem blueprint_middle_at[local]:
  EVERY (\j. ~MEM j.inst_opcode [DALLOCA;CALL;STATICCALL;DELEGATECALL;
                                CREATE;CREATE2;INVOKE] /\
             ~is_terminator j.inst_opcode) middle /\
  0 < k /\ k < LENGTH (i :: middle) ==>
  ~MEM (EL k (i :: middle)).inst_opcode
      [DALLOCA;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2;INVOKE] /\
  ~is_terminator (EL k (i :: middle)).inst_opcode
Proof
  Cases_on `k` >> simp[EVERY_MEM] >> metis_tac[EL_MEM]
QED

(* The end of the reservation's straight-line prefix is the actual effect
   cursor. Nothing here infers that an unrecorded effect will succeed. *)
Theorem blueprint_effect_cursor[local]:
  q.bp_fn = p.bp_fn /\ q.bp_state.vs_current_bb = p.bp_state.vs_current_bb /\
  q.bp_state.vs_inst_idx = p.bp_state.vs_inst_idx + LENGTH steps /\
  lookup_block p.bp_state.vs_current_bb p.bp_fn.fn_blocks = SOME bb /\
  DROP p.bp_state.vs_inst_idx bb.bb_instructions = steps ++ effect :: rest ==>
  active_inst q.bp_fn effect q.bp_state
Proof
  strip_tac >>
  `DROP q.bp_state.vs_inst_idx bb.bb_instructions = effect :: rest` by
    (`q.bp_state.vs_inst_idx = LENGTH steps + p.bp_state.vs_inst_idx`
       by simp[ADD_COMM] >>
     pop_assum (fn th => pure_once_rewrite_tac[th]) >>
     pure_once_rewrite_tac[GSYM DROP_DROP_T] >>
     qpat_assum `DROP p.bp_state.vs_inst_idx _ = _`
       (fn th => pure_rewrite_tac[th, DROP_LENGTH_APPEND]) >> REFL_TAC) >>
  drule DROP_EQ_CONS >> strip_tac >>
  irule lookup_instruction_active >> qexists_tac `bb` >> simp[get_instruction_def]
QED

Theorem blueprint_recorded_effect[local]:
  lower_budget_path F (D,lo,explicit,ctx) root h marks last /\
  lower_budget_path F (D,lo,explicit,ctx) root (TAKE k h) m p /\
  k < LENGTH h /\ ALL_DISTINCT (fn_labels p.bp_fn) /\
  active_inst p.bp_fn effect p.bp_state /\
  (case salt of NONE => effect.inst_opcode = CREATE /\
                       effect.inst_operands = [value;alloc_ptr;size_op]
     | SOME sop => effect.inst_opcode = CREATE2 /\
                   effect.inst_operands = [value;alloc_ptr;size_op;sop]) /\
  eval_operand alloc_ptr p.bp_state = SOME offset_word /\
  eval_operand size_op p.bp_state = SOME sz ==>
  ?fuel t q ws. EL k h = BudgetStep k p effect fuel (OK t) q /\
    eval_operands effect.inst_operands p.bp_state = SOME ws /\
    ?v w. (effect.inst_opcode = CREATE /\ ws = [v;offset_word;sz]) \/
          (effect.inst_opcode = CREATE2 /\ ws = [v;offset_word;sz;w])
Proof
  strip_tac >>
  `~is_terminator effect.inst_opcode /\ effect.inst_opcode <> INVOKE` by
    (Cases_on `salt` >> fs[is_terminator_def]) >>
  drule_all lower_budget_window_index_next >> strip_tac >>
  drule_all blueprint_effect_args >> strip_tac >>
  qexistsl_tac [`fuel`,`t`,`q`,`ws`] >> simp[] >> metis_tac[]
QED

Theorem blueprint_interior_record[local]:
  EVERY (\j. ~MEM j.inst_opcode [DALLOCA;CALL;STATICCALL;DELEGATECALL;
                                CREATE;CREATE2;INVOKE] /\
             ~is_terminator j.inst_opcode) middle /\
  0 < k /\ k < LENGTH (i :: middle) /\
  EL j h = BudgetStep j jp (EL k (i :: middle)) jf (OK jt) jq ==>
  ?jp ji jf jt jq.
    EL j h = BudgetStep j jp ji jf (OK jt) jq /\
    ~lower_event_consumes (EL j h) /\ ~lower_event_allocates (EL j h) /\
    ~is_terminator ji.inst_opcode
Proof
  strip_tac >> drule_all blueprint_middle_at >> strip_tac >>
  qexistsl_tac [`jp`,`EL k (i :: middle)`,`jf`,`jt`,`jq`] >>
  asm_rewrite_tac[lower_event_consumes_def, lower_event_allocates_def] >> fs[MEM]
QED

Theorem blueprint_recorded_window:
  lower_budget_path F (D,lo,explicit,ctx) root h marks last /\
  n < LENGTH h /\ EL n h = BudgetStep n p i fuel (OK post) q /\
  ALL_DISTINCT (fn_labels p.bp_fn) /\
  entry_blueprint_window p.bp_fn i p.bp_state /\
  i.inst_operands = [op] /\ eval_operand op p.bp_state = SOME sz /\
  w2n sz <= 2 ** 255 + 2 ** 64 ==>
  lower_history_window h last n
Proof
  strip_tac >> drule_all lower_budget_path_at_base_step >> strip_tac >>
  qpat_x_assum `entry_blueprint_window _ _ _` (strip_assume_tac o
    REWRITE_RULE [entry_blueprint_window_def]) >>
  rename1 `compile_alloc_dynamic size_op sm = (alloc_ptr,sn)` >>
  rename1 `emit_void EXTCODECOPY _ sn = ((),se)` >>
  rename1 `DROP _ bb.bb_instructions = add_inst :: i ::
              (emitted_insts sn sc ++ effect :: rest)` >>
  `size_op = op` by metis_tac[CONS_11] >>
  qpat_x_assum `size_op = op` SUBST_ALL_TAC >>
  `lower_alloc_record h n p.bp_fn i p.bp_state op sz post` by
    (pure_rewrite_tac[lower_alloc_record_def] >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`p`,`fuel`,`q`] >> asm_rewrite_tac[]) >>
  qabbrev_tac `middle = emitted_insts sn sc` >>
  `DROP p.bp_state.vs_inst_idx bb.bb_instructions =
     (i :: middle) ++ effect :: rest` by
    (qpat_assum `p.bp_state.vs_inst_idx = _` (fn th => pure_rewrite_tac[th]) >>
     once_rewrite_tac[DECIDE ``SUC k = 1 + k``] >>
     pure_once_rewrite_tac[GSYM DROP_DROP_T] >> asm_rewrite_tac[DROP, APPEND] >> simp[]) >>
  `EVERY (\j. ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE)
      (i :: middle)` by fs[EVERY_MEM, is_terminator_def] >>
  pure_rewrite_tac[lower_history_window_def] >> BETA_TAC >>
  Cases_on `n + LENGTH (i :: middle) < LENGTH h`
  >- (`n + LENGTH (i :: middle) <= LENGTH h` by decide_tac >>
      `isPREFIX (i :: middle) (DROP p.bp_state.vs_inst_idx bb.bb_instructions)` by
        (qpat_assum `DROP p.bp_state.vs_inst_idx _ = _` (fn th =>
           pure_rewrite_tac[th]) >> metis_tac[IS_PREFIX_APPEND]) >>
      mp_tac (Q.SPECL [`i :: middle`,`n`,`m`,`p`] lower_budget_run_window) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (qx_choosel_then [`me`,`ep`,`ready`] strip_assume_tac) >>
      `active_inst ep.bp_fn effect ep.bp_state` by
        (irule blueprint_effect_cursor >>
         qexistsl_tac [`bb`,`p`,`rest`,`i :: middle`] >>
         asm_simp_tac (srw_ss()) [venom_state_accfupds]) >>
      `emitted_insts sm sc = i :: middle` by
        (drule_all blueprint_reservation_insts >> simp[Abbr `middle`]) >>
      `run_inst_seq (emitted_insts sm sc) p.bp_state = OK ready` by
        asm_rewrite_tac[] >>
      drule_all create_blueprint_allocation_geometry >> strip_tac >>
      `eval_operand alloc_ptr ep.bp_state = SOME p.bp_state.vs_fmp /\
       eval_operand op ep.bp_state = SOME sz` by
        (qpat_assum `ep.bp_state = _` (fn th => pure_once_rewrite_tac[th]) >>
         simp[eval_op_inst_idx] >> metis_tac[optionTheory.SOME_11]) >>
      `ALL_DISTINCT (fn_labels ep.bp_fn)` by metis_tac[] >>
      drule_all (Q.INST [`k` |-> `n + LENGTH (i :: middle)`, `p` |-> `ep`]
        blueprint_recorded_effect) >>
      disch_then (qx_choosel_then [`ef`,`et`,`eq`,`ws`]
        (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
      qexists_tac `n + LENGTH (i :: middle)` >> rpt conj_tac
      >- (simp[] >> decide_tac)
      >- decide_tac
      >- (strip_tac >> conj_tac
          >- (Cases_on `salt` >> fs[lower_event_consumes_def]) >>
          qexistsl_tac [`p.bp_fn`,`i`,`p.bp_state`,`op`,`sz`,`post`,
                        `p`,`fuel`,`q`,`ep`,`effect`,`ef`,`et`,`eq`,`ws`] >>
          asm_rewrite_tac[] >> metis_tac[])
      >- (strip_tac >> fs[] >> decide_tac)
      >- metis_tac[] >>
      rpt strip_tac >>
      `0 < j - n /\ j - n < LENGTH (i :: middle) /\ n + (j - n) = j` by
        (simp[] >> decide_tac) >>
      qpat_x_assum `!k. k < _ ==> _` (qspec_then `j - n` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      qpat_assum `n + (j - n) = j` (fn th => pure_rewrite_tac[th]) >>
      strip_tac >> drule_all blueprint_interior_record >> simp[]) >>
  qexists_tac `LENGTH h` >>
  `LENGTH h <= n + LENGTH (i :: middle)` by decide_tac >>
  mp_tac (Q.INST [`steps` |-> `i :: middle`,`effect` |-> `effect`,
                  `rest` |-> `rest`] lower_budget_pending_before_effect) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  simp[] >> conj_tac
  >- (gen_tac >> disch_tac >> qpat_x_assum `!i. active_inst _ i _ ==> _` drule >>
      disch_then SUBST1_TAC >>
      Cases_on `LENGTH h - n = LENGTH (i :: middle)`
      >- (Cases_on `salt` >> fs[EL_APPEND_EQN]) >>
      `0 < LENGTH h - n /\ LENGTH h - n < LENGTH (i :: middle)` by decide_tac >>
      `EL (LENGTH h - n) ((i :: middle) ++ [effect]) =
       EL (LENGTH h - n) (i :: middle)` by asm_simp_tac bool_ss [EL_APPEND_EQN] >>
      drule_all blueprint_middle_at >> fs[MEM]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `!j. n < j /\ j < LENGTH h ==> _` drule_all >> strip_tac >>
  `0 < j - n /\ j - n < LENGTH (i :: middle)` by decide_tac >>
  drule_all blueprint_interior_record >> simp[]
QED
