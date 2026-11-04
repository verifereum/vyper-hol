Theory dftOccurrenceTerminal
Ancestors
  dftOccurrenceReplay dftOccurrenceMachine dftOpenAdequacy dftOpenErase
  dftOpenMachine dftOpenFuel stateEquiv venomExecSemantics arithmetic list

Theorem dft_open_root_iterations:
  FUNPOW (dft_open_next a ctx) k (DftOpen (DftDone rr) [] n) =
    DftOpen (DftDone rr) [] n
Proof
  Induct_on `k` >> simp[FUNPOW_SUC, dft_open_next_def,
    dft_open_return_def] >> Cases_on `rr` >> simp[]
QED

Theorem dft_zero_entry_no_terminal:
  dft_zero_entry c /\ ((?s. rr = Halt s) \/ (?a s. rr = Abort a s)) ==>
  FUNPOW (dft_open_next a ctx) k c <> DftOpen (DftDone rr) [] n
Proof
  Cases_on `k` >> simp[FUNPOW, dft_zero_entry_def] >>
  rpt strip_tac >> gvs[dft_open_next_def, dft_open_root_iterations]
QED

Theorem dft_terminal_nonexhausting:
  FUNPOW (dft_open_next a ctx) j c = DftOpen (DftDone rr) [] n /\
  ((?s. rr = Halt s) \/ (?a s. rr = Abort a s)) ==>
  !h. h < j ==> ~dft_zero_entry (FUNPOW (dft_open_next a ctx) h c)
Proof
  rpt strip_tac >>
  `j = (j-h) + h` by decide_tac >>
  drule dft_zero_entry_no_terminal >>
  disch_then (qspecl_then [`rr`, `n`, `j-h`, `ctx`, `a`] mp_tac) >>
  gvs[GSYM FUNPOW_ADD]
QED

Theorem dft_open_root_first_hit:
  FUNPOW (dft_open_next a ctx) j c = DftOpen (DftDone rr) [] n ==>
  ?k. k <= j /\ dft_first_hit (dft_open_next a ctx)
    (dft_open_stack_exit []) c k (DftOpen (DftDone rr) [] n)
Proof
  completeInduct_on `j` >> rpt strip_tac >>
  Cases_on `?h. h < j /\ dft_open_stack_exit []
    (FUNPOW (dft_open_next a ctx) h c)`
  >- (gvs[dft_open_stack_exit_def] >>
      `j = (j-h) + h` by decide_tac >>
      `FUNPOW (dft_open_next a ctx) j c = DftOpen (DftDone r) [] n'` by
        metis_tac[FUNPOW_ADD, dft_open_root_iterations] >>
      gvs[] >> first_x_assum drule >> disch_then drule >>
      strip_tac >> qexists_tac `k` >> simp[] >> decide_tac) >>
  qexists_tac `j` >> gvs[dft_first_hit_def, dft_open_stack_exit_def] >>
  metis_tac[]
QED

Theorem dft_budget_terminal_native:
  dft_sparse_oracle a xs /\
  ((?s. rr = Halt s) \/ (?a s. rr = Abort a s)) /\
  FUNPOW (dft_open_next a ctx) j (DftOpen (DftEnter fn fuel s) [] 0) =
    DftOpen (DftDone rr) [] n ==>
  run_blocks fuel ctx fn (dft_open_materialize xs 0 s) =
    dft_open_materialize_result xs n rr
Proof
  strip_tac >> drule dft_open_root_first_hit >> strip_tac >>
  `0 < k` by
    (Cases_on `k` >> gvs[dft_first_hit_def, FUNPOW]) >>
  `dft_open_result_eq
     (run_blocks fuel ctx fn (dft_open_materialize xs 0 s))
     (dft_open_materialize_result xs n rr)` by
    (irule dft_open_run_segment_reflect >> simp[] >>
     qexistsl_tac [`a`, `[]`] >> simp[dft_open_run_segment_def] >>
     qexistsl_tac [`rr`, `n`, `k`, `DftOpen (DftDone rr) [] n`] >>
     simp[dft_open_classified_exit_def] >>
     gvs[dft_open_result_eq_def, lift_result_def]) >>
  gvs[dft_open_materialize_result_def]
QED

Theorem dft_occ_terminal_realize_blocks:
  dft_sparse_oracle a xs /\
  dft_occ_prefix_compatible w a ctx
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] 0)) j /\
  ((?t. rr = Halt t) \/ (?z t. rr = Abort z t)) /\
  (FUNPOW (dft_occ_oracle_next w ctx) j
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] 0))).dft_occ_core =
      DftOpen (DftDone rr) [] n ==>
  ?fuel. run_blocks fuel ctx fn (dft_open_materialize xs 0 s) =
    dft_open_materialize_result xs n rr
Proof
  strip_tac >> drule dft_occ_prefix_replay >> strip_tac >>
  `dft_erase (FUNPOW (dft_open_next a ctx) j
      (DftOpen (DftEnter fn j s) [] 0)) = DftOpen (DftDone rr) [] n` by
    (`dft_erase (FUNPOW (dft_open_next a ctx) j
        (dft_fill j (DftOpen (DftEnter fn 0 s) [] 0))) =
       FUNPOW (dft_next_inf a ctx) j
        (dft_erase (DftOpen (DftEnter fn 0 s) [] 0))` by
       (irule dft_fill_decorates >> simp[]) >>
     gvs[dft_occ_iter_projection, dft_occ_init_def,
         dft_erase_def, dft_fill_def, dft_fill_control_def]) >>
  `FUNPOW (dft_open_next a ctx) j (DftOpen (DftEnter fn j s) [] 0) =
     DftOpen (DftDone rr) [] n` by
    (Cases_on `FUNPOW (dft_open_next a ctx) j (DftOpen (DftEnter fn j s) [] 0)` >>
     qmatch_goalsub_rename_tac `DftOpen ctl0 stack0 n0 = _` >>
     Cases_on `ctl0` >> gvs[dft_erase_def, dft_fill_def, dft_fill_control_def]) >>
  qexists_tac `j` >> irule dft_budget_terminal_native >>
  simp[] >> qexistsl_tac [`a`, `j`] >> simp[]
QED

Theorem dft_occ_terminal_extract_blocks:
  dft_sparse_oracle a xs /\
  (!j. dft_occ_prefix_compatible w a ctx
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] 0)) j) /\
  run_blocks fuel ctx fn (dft_open_materialize xs 0 s) = r /\
  ((?t. r = Halt t) \/ (?z t. r = Abort z t)) ==>
  ?j n rr. ((?t. rr = Halt t) \/ (?z t. rr = Abort z t)) /\
    (FUNPOW (dft_occ_oracle_next w ctx) j
      (dft_occ_init (DftOpen (DftEnter fn 0 s) [] 0))).dft_occ_core =
        DftOpen (DftDone rr) [] n /\
    r = dft_open_materialize_result xs n rr
Proof
  strip_tac >> drule_all dft_open_run_forward_segment >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[dft_open_run_segment_def, dft_first_hit_def,
       dft_open_classified_exit_def] >> strip_tac >>
  `((?t. rr = Halt t) \/ (?z t. rr = Abort z t)) /\
   r = dft_open_materialize_result xs m rr` by
    (Cases_on `rr` >> gvs[dft_open_materialize_result_def]) >>
  qexistsl_tac [`k`, `m`, `rr`] >> simp[] >>
  `!h. h < k ==> ~dft_zero_entry
    (FUNPOW (dft_open_next a ctx) h (DftOpen (DftEnter fn fuel s) [] 0))` by
    (gvs[] >> metis_tac[dft_terminal_nonexhausting]) >>
  ` (FUNPOW (dft_occ_oracle_next w ctx) k
      (dft_occ_init (DftOpen (DftEnter fn 0 s) [] 0))).dft_occ_core =
      dft_erase (FUNPOW (dft_open_next a ctx) k
        (DftOpen (DftEnter fn fuel s) [] 0))` by
    (irule dft_occ_budget_prefix_replay >>
     simp[dft_occ_init_def, dft_erase_def, dft_fill_def, dft_fill_control_def]) >>
  gvs[dft_erase_def, dft_fill_def, dft_fill_control_def]
QED

Theorem dft_occ_terminal_realize:
  ctx.ctx_entry = SOME name /\ lookup_function name ctx.ctx_functions = SOME entry /\
  fn_entry_label entry = SOME lbl /\ dft_sparse_oracle a vs0.vs_gas_readings /\
  dft_occ_prefix_compatible w a ctx (dft_occ_start entry lbl vs0) j /\
  ((?t. rr = Halt t) \/ (?z t. rr = Abort z t)) /\
  (FUNPOW (dft_occ_oracle_next w ctx) j (dft_occ_start entry lbl vs0)).dft_occ_core =
    DftOpen (DftDone rr) [] n ==>
  ?fuel. run_context fuel ctx vs0 = dft_open_materialize_result vs0.vs_gas_readings n rr
Proof
  strip_tac >>
  `?fuel. run_blocks fuel ctx entry
     (dft_open_materialize vs0.vs_gas_readings 0
       (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) =
     dft_open_materialize_result vs0.vs_gas_readings n rr` by
    (irule dft_occ_terminal_realize_blocks >>
     simp[] >> qexistsl_tac [`a`, `j`, `w`] >> gvs[dft_occ_start_def]) >>
  qexists_tac `fuel` >>
  gvs[run_context_def, run_function_def, dft_open_materialize_def]
QED

Theorem dft_occ_terminal_extract:
  ctx.ctx_entry = SOME name /\ lookup_function name ctx.ctx_functions = SOME entry /\
  fn_entry_label entry = SOME lbl /\ dft_sparse_oracle a vs0.vs_gas_readings /\
  (!j. dft_occ_prefix_compatible w a ctx (dft_occ_start entry lbl vs0) j) /\
  run_context fuel ctx vs0 = r /\
  ((?t. r = Halt t) \/ (?z t. r = Abort z t)) ==>
  ?j n rr. ((?t. rr = Halt t) \/ (?z t. rr = Abort z t)) /\
    (FUNPOW (dft_occ_oracle_next w ctx) j (dft_occ_start entry lbl vs0)).dft_occ_core =
      DftOpen (DftDone rr) [] n /\
    r = dft_open_materialize_result vs0.vs_gas_readings n rr
Proof
  strip_tac >> simp[dft_occ_start_def] >>
  irule dft_occ_terminal_extract_blocks >>
  gvs[dft_occ_start_def, run_context_def, run_function_def, dft_open_materialize_def] >>
  metis_tac[]
QED
