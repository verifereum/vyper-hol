(*
 * The assembly run from a related state against the frame's run_call,
 * by induction on the assembly's step count.
 *
 * TOP-LEVEL:
 *   asm_frame_step - every instruction, from the two step classes
 *   asm_frame_run  - codegen_asm_run_call's clauses from asm_frame_rel
 *)

Theory asmFrameRun
Ancestors
  asmFrameRel asmFrameLocalStep asmFrameCallStep asmFrameCreateStep
  asmFrameDelegateStep asmFrameSelfdestructStep asmSem asmWf symbolResolve
  frameOutcome frameStep callTrace vfmExecution arithmetic relation vfmAccountFrame

(* Preserve the local-step interface while dispatching stateful frame steps. *)
Theorem asm_frame_local_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\ ~is_data_inst (EL as.as_pc prog) /\
  EL as.as_pc prog <> AsmOp "CALL" /\
  EL as.as_pc prog <> AsmOp "STATICCALL" ==>
  asm_frame_step_ok prog data es0 as es /\
  ((!e. asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       (EL as.as_pc prog) as <> AsmError e) ==>
   frame_last es \/ ?as1 es1.
     asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       (EL as.as_pc prog) as = AsmOK as1 /\
     frame_next es es1 /\ asm_frame_rel prog data es0 as1 es1)
Proof
  strip_tac >>
  Cases_on `EL as.as_pc prog = AsmOp "DELEGATECALL"`
  >- (simp[asm_frame_delegate_step]) >>
  Cases_on `EL as.as_pc prog = AsmOp "CREATE" \/
            EL as.as_pc prog = AsmOp "CREATE2"`
  >- (irule asm_frame_create_step >> simp[]) >>
  Cases_on `EL as.as_pc prog = AsmOp "SELFDESTRUCT"`
  >- (irule asm_frame_selfdestruct_step >> simp[]) >>
  drule asm_frame_noncall_step >> simp[] >> metis_tac[]
QED

Theorem asm_frame_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\ ~is_data_inst (EL as.as_pc prog) ==>
  asm_frame_step_ok prog data es0 as es /\
  ((!e. asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       (EL as.as_pc prog) as <> AsmError e) ==>
   frame_last es \/ ?as1 es1.
     asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       (EL as.as_pc prog) as = AsmOK as1 /\
     frame_next es es1 /\ asm_frame_rel prog data es0 as1 es1)
Proof
  strip_tac >>
  Cases_on `EL as.as_pc prog = AsmOp "CALL" \/
            EL as.as_pc prog = AsmOp "STATICCALL"`
  >- (drule_all asm_frame_call_step >> simp[]) >>
  irule asm_frame_local_step >> fs[]
QED

Theorem asm_frame_run:
  !n prog data es0 as es r es'.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
    run_call es = SOME (r, es') ==>
    frame_resource_starved es0 r es' \/
    ((!as'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
              prog n as = AsmHalt as' ==>
        frame_outcome es0 r es' NONE as'.as_returndata as'.as_logs /\
        es'.rollback.accounts = as'.as_accounts /\
        es'.rollback.toDelete = as'.as_pending_deletions /\
        es'.rollback.tStorage = as'.as_transient /\
        as'.as_requests = call_requests es0) /\
     (!as'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
              prog n as = AsmRevert as' ==>
        (?lgs. frame_outcome es0 r es' (SOME Reverted) as'.as_returndata lgs) /\
        frame_inst_raises es0 Reverted Revert) /\
     (!as'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
              prog n as = AsmFault as' ==>
        ?exc lgs. exc <> Reverted /\ frame_outcome es0 r es' (SOME exc) [] lgs))
Proof
  Induct >- simp[asm_steps_def] >>
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `as.as_pc < LENGTH prog`) >- simp[asm_steps_def] >>
  Cases_on `is_data_inst (EL as.as_pc prog)`
  >- (Cases_on `EL as.as_pc prog` >>
      gvs[is_data_inst_def, asm_step_def, asm_steps_def]) >>
  `asm_frame_step_ok prog data es0 as es` by (irule (cj 1 asm_frame_step) >> simp[]) >>
  pop_assum mp_tac >> simp[asm_frame_step_ok_def] >> strip_tac
  >- gvs[] >>
  simp[asm_steps_def] >>
  Cases_on `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
              (EL as.as_pc prog) as` >> gvs[]
  >~ [`AsmOK as1`]
  >- (first_x_assum (qspecl_then [`prog`, `data`, `es0`, `as1`, `es1`, `r`, `es'`]
        mp_tac) >> simp[]) >>
  DISJ2_TAC >> metis_tac[]
QED

Theorem asm_frame_terminal_gas_readings:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
  a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
  (asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL a.as_pc prog) a = AsmHalt b \/
   asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL a.as_pc prog) a = AsmRevert b \/
   asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL a.as_pc prog) a = AsmFault b) ==>
  b.as_gas_readings = []
Proof
  strip_tac >>
  `frame_last es` by (drule_all asm_frame_step >> simp[] >> metis_tac[]) >>
  `gas_readings es = []` by
    (Cases_on `step es` >> rename1 `step es = (result,succ)` >>
     Cases_on `result` >> gvs[frame_last_def] >>
     drule frameObsStepTheory.frame_obs_terminal >> simp[]) >>
  `b.as_gas_readings = a.as_gas_readings` by
    (irule asm_step_terminal_gas_readings >> metis_tac[]) >>
  gvs[asm_frame_rel_def]
QED

(* Carry the real frame simulation through an arbitrary unread suffix. *)
Theorem asm_frame_step_tail:
  asm_frame_prog_ok prog /\ asm_frame_rel_tail tail prog data es0 a es /\
  a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) ==>
  asm_frame_step_ok_tail tail prog data es0 a es
Proof
  strip_tac >>
  fs[asm_frame_rel_tail_def] >>
  qabbrev_tac `b = a with as_gas_readings := gas_readings es` >>
  `asm_frame_rel prog data es0 b es /\ b.as_pc = a.as_pc` by
    simp[Abbr `b`] >>
  Cases_on `?r es'. run_call es = SOME (r,es') /\
    frame_resource_starved es0 r es' /\ call_requests es = []`
  >- simp[asm_frame_step_ok_tail_def] >>
  `EL b.as_pc prog <> AsmOp "GAS" \/ b.as_gas_readings <> []` by
    (Cases_on `EL b.as_pc prog = AsmOp "GAS"` >> simp[] >>
     drule_at (Pat `asm_frame_rel _ _ _ _ _`) asm_frame_gas_readings_available >>
     simp[is_data_inst_def] >> simp[Abbr `b`]) >>
  `asm_frame_step_ok prog data es0 b es` by
    (irule (cj 1 asm_frame_step) >> simp[]) >>
  qpat_x_assum `asm_frame_step_ok _ _ _ _ _` mp_tac >>
  simp[asm_frame_step_ok_def] >> strip_tac >>
  `a = b with as_gas_readings := b.as_gas_readings ++ tail` by
    simp[Abbr `b`, asm_state_component_equality] >>
  `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL a.as_pc prog) a =
   case asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL b.as_pc prog) b of
     AsmOK c => AsmOK (c with as_gas_readings := c.as_gas_readings ++ tail)
   | AsmHalt c => AsmHalt (c with as_gas_readings := c.as_gas_readings ++ tail)
   | AsmRevert c => AsmRevert (c with as_gas_readings := c.as_gas_readings ++ tail)
   | AsmFault c => AsmFault (c with as_gas_readings := c.as_gas_readings ++ tail)
   | AsmError e => AsmError e` by
    metis_tac[asm_step_gas_readings_append] >>
  qpat_x_assum `a = b with as_gas_readings := _` kall_tac >>
  qpat_x_assum `Abbrev _` kall_tac >>
  Cases_on `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (EL b.as_pc prog) b` >>
  gvs[asm_frame_step_ok_tail_def]
  >>~- ([`asm_step _ _ _ b = AsmOK c`],
    rename1 `asm_frame_rel prog data es0 c next` >>
    disj2_tac >> qexists_tac `next` >>
    `c with as_gas_readings := gas_readings next = c` by
      (gvs[asm_frame_rel_def, asm_state_component_equality]) >>
    simp[asm_frame_rel_tail_def] >> gvs[asm_frame_rel_def]) >>
  metis_tac[asm_frame_terminal_gas_readings]
QED

Theorem asm_frame_run_tail:
  !n tail prog data es0 a es r es'.
    asm_frame_prog_ok prog /\ asm_frame_rel_tail tail prog data es0 a es /\
    run_call es = SOME (r, es') ==>
    frame_resource_starved es0 r es' \/
    ((!a'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
             prog n a = AsmHalt a' ==>
        frame_outcome es0 r es' NONE a'.as_returndata a'.as_logs /\
        es'.rollback.accounts = a'.as_accounts /\
        es'.rollback.toDelete = a'.as_pending_deletions /\
        es'.rollback.tStorage = a'.as_transient /\
        a'.as_requests = call_requests es0 /\ a'.as_gas_readings = tail) /\
     (!a'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
             prog n a = AsmRevert a' ==>
        (?lgs. frame_outcome es0 r es' (SOME Reverted) a'.as_returndata lgs) /\
        frame_inst_raises es0 Reverted Revert /\ a'.as_gas_readings = tail) /\
     (!a'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
             prog n a = AsmFault a' ==>
        (?exc lgs. exc <> Reverted /\
          frame_outcome es0 r es' (SOME exc) [] lgs) /\
        a'.as_gas_readings = tail))
Proof
  Induct >- simp[asm_steps_def] >>
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `a.as_pc < LENGTH prog`) >- simp[asm_steps_def] >>
  Cases_on `is_data_inst (EL a.as_pc prog)`
  >- (Cases_on `EL a.as_pc prog` >>
      gvs[is_data_inst_def, asm_step_def, asm_steps_def]) >>
  `asm_frame_step_ok_tail tail prog data es0 a es` by
    (irule asm_frame_step_tail >> simp[]) >>
  pop_assum mp_tac >> simp[asm_frame_step_ok_tail_def] >> strip_tac
  >- gvs[] >>
  simp[asm_steps_def] >>
  Cases_on `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
              (EL a.as_pc prog) a` >> gvs[]
  >~ [`AsmOK a1`]
  >- (first_x_assum (qspecl_then
        [`tail`, `prog`, `data`, `es0`, `a1`, `es1`, `r`, `es'`] mp_tac) >>
      simp[]) >>
  DISJ2_TAC >> metis_tac[]
QED

Theorem asm_frame_prefix_tail:
  !n tail prog data es0 a es a1 r final.
    asm_frame_prog_ok prog /\ asm_frame_rel_tail tail prog data es0 a es /\
    run_call es = SOME (r,final) /\ ~frame_resource_starved es0 r final /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n a = AsmOK a1 ==>
    ?es1. run_call es1 = SOME (r,final) /\
      asm_frame_rel_tail tail prog data es0 a1 es1
Proof
  Induct
  >- (rpt gen_tac >> simp[asm_steps_def] >> strip_tac >> gvs[] >>
      qexists_tac `es` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `a.as_pc < LENGTH prog` by
    (spose_not_then assume_tac >> fs[Once asm_steps_def]) >>
  `~is_data_inst (EL a.as_pc prog)` by
    (spose_not_then assume_tac >> Cases_on `EL a.as_pc prog` >>
     gvs[is_data_inst_def, Once asm_steps_def, asm_step_def]) >>
  drule_all asm_frame_step_tail >>
  simp[asm_frame_step_ok_tail_def] >> strip_tac >>
  Cases_on `asm_step (SND (compute_label_offsets prog))
    (build_offset_to_pc prog) (EL a.as_pc prog) a` >>
  gvs[Once asm_steps_def] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem asm_frame_prefix_gas_available_tail:
  !n tail prog data es0 a es a1 r final.
    asm_frame_prog_ok prog /\ asm_frame_rel_tail tail prog data es0 a es /\
    run_call es = SOME (r,final) /\ ~frame_resource_starved es0 r final /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n a = AsmOK a1 /\
    a1.as_pc < LENGTH prog /\ EL a1.as_pc prog = AsmOp "GAS" ==>
    LENGTH tail < LENGTH a1.as_gas_readings
Proof
  rpt gen_tac >> strip_tac >>
  drule_all asm_frame_prefix_tail >> strip_tac >>
  `~is_data_inst (EL a1.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_frame_gas_step_tail >> strip_tac >- gvs[] >>
  fs[asm_frame_rel_tail_def]
QED

Theorem asm_frame_prefix_gas_count_bound_tail:
  !n k tail prog data es0 a es a1 r final.
    asm_frame_prog_ok prog /\ asm_frame_rel_tail tail prog data es0 a es /\
    run_call es = SOME (r,final) /\ ~frame_resource_starved es0 r final /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n a = AsmOK a1 /\
    a1.as_pc < LENGTH prog /\ EL a1.as_pc prog = AsmOp "GAS" /\
    a1.as_gas_readings = DROP (k-1) a.as_gas_readings /\ 0<k ==>
    k <= LENGTH (gas_readings es)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all asm_frame_prefix_gas_available_tail >>
  fs[asm_frame_rel_tail_def, listTheory.LENGTH_DROP] >> decide_tac
QED

Theorem asm_frame_success_not_last:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
  a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
  run_call es = SOME (r,t) /\ ~frame_resource_starved es0 r t /\
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (EL a.as_pc prog) a = AsmOK a1 ==>
  ~frame_last es
Proof
  strip_tac >>
  Cases_on `EL a.as_pc prog = AsmOp "CALL" \/
            EL a.as_pc prog = AsmOp "STATICCALL"`
  >- (drule_all asm_frame_call_success_not_last >> simp[]) >>
  Cases_on `EL a.as_pc prog = AsmOp "DELEGATECALL"`
  >- (drule_all asm_frame_delegate_success_not_last >> simp[]) >>
  Cases_on `EL a.as_pc prog = AsmOp "CREATE" \/
            EL a.as_pc prog = AsmOp "CREATE2"`
  >- (drule_all asm_frame_create_success_not_last >> simp[]) >>
  Cases_on `EL a.as_pc prog = AsmOp "SELFDESTRUCT"`
  >- gvs[asm_step_def, asm_step_op_def, asm_step_arith_def,
         asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
         asm_step_control_def, asm_step_extcall_def, asm_selfdestruct_def,
         AllCaseEqs()] >>
  Cases_on `EL a.as_pc prog = AsmOp "GAS"`
  >- (`asm_frame_rel_tail [] prog data es0 a es` by simp[asm_frame_rel_tail_nil] >>
      drule_all asm_frame_gas_step_tail >> disch_then strip_assume_tac
      >- gvs[] >>
      `LENGTH es1.contexts = LENGTH es.contexts` by
        gvs[asm_frame_rel_tail_def, asm_frame_rel_def] >>
      fs[frame_last_def]) >>
  fs[] >> drule_all frame_plain_success_not_last >> simp[]
QED

Theorem asm_frame_step_progress_tail:
  asm_frame_prog_ok prog /\ asm_frame_rel_tail tail prog data es0 a es /\
  a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
  run_call es = SOME (r,t) /\ ~frame_resource_starved es0 r t /\
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (EL a.as_pc prog) a = AsmOK a1 ==>
  ?u es1. step es = (INL (),u) /\
    RTC (\x y. LENGTH x.contexts >= LENGTH es.contexts /\
               step x = (INL (),y)) u es1 /\
    run_call es1 = run_call es /\
    asm_frame_rel_tail tail prog data es0 a1 es1
Proof
  strip_tac >> fs[asm_frame_rel_tail_def] >>
  qabbrev_tac `b = a with as_gas_readings := gas_readings es` >>
  `asm_frame_rel prog data es0 b es /\ b.as_pc = a.as_pc` by simp[Abbr `b`] >>
  `EL b.as_pc prog <> AsmOp "GAS" \/ b.as_gas_readings <> []` by
    (Cases_on `EL b.as_pc prog = AsmOp "GAS"` >> simp[] >>
     drule_at (Pat `asm_frame_rel _ _ _ _ _`) asm_frame_gas_readings_available >>
     simp[is_data_inst_def] >> simp[Abbr `b`]) >>
  `a = b with as_gas_readings := b.as_gas_readings ++ tail` by
    simp[Abbr `b`, asm_state_component_equality] >>
  `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL a.as_pc prog) a =
   case asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL b.as_pc prog) b of
     AsmOK c => AsmOK (c with as_gas_readings := c.as_gas_readings ++ tail)
   | AsmHalt c => AsmHalt (c with as_gas_readings := c.as_gas_readings ++ tail)
   | AsmRevert c => AsmRevert (c with as_gas_readings := c.as_gas_readings ++ tail)
   | AsmFault c => AsmFault (c with as_gas_readings := c.as_gas_readings ++ tail)
   | AsmError e => AsmError e` by metis_tac[asm_step_gas_readings_append] >>
  qpat_x_assum `a = b with as_gas_readings := _` kall_tac >>
  qpat_x_assum `Abbrev _` kall_tac >>
  Cases_on `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (EL b.as_pc prog) b` >> gvs[] >>
  rename1 `asm_step _ _ _ b = AsmOK c` >>
  qpat_x_assum `b.as_pc = a.as_pc` (SUBST_ALL_TAC o SYM) >>
  `~frame_last es` by
    (drule_all asm_frame_success_not_last >> simp[]) >>
  `!e. asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (EL b.as_pc prog) b <> AsmError e` by simp[] >>
  drule_all (cj 2 asm_frame_step) >> simp[] >> disch_then strip_assume_tac >> gvs[] >>
  `run_call es1 = run_call es` by metis_tac[frame_next_run_call] >>
  `?u. step es = (INL (),u) /\
    RTC (\x y. LENGTH x.contexts >= LENGTH es.contexts /\
               step x = (INL (),y)) u es1` by
    (qpat_x_assum `frame_next es es1`
       (strip_assume_tac o REWRITE_RULE [frame_next_def]) >>
     qexists_tac `v` >> simp[RTC_REFL] >>
     drule frameObsStepTheory.run_call_inl_rtc >> disch_then strip_assume_tac >>
     irule RTC_MONOTONE >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`u`,`es1`] >> simp[] >>
  `c with as_gas_readings := gas_readings es1 = c` by
    gvs[asm_frame_rel_def, asm_state_component_equality] >>
  simp[asm_frame_rel_tail_def] >> gvs[asm_frame_rel_def]
QED

Theorem asm_frame_prefix_progress_tail:
  !n tail prog data es0 a es a1 r t.
    asm_frame_prog_ok prog /\ asm_frame_rel_tail tail prog data es0 a es /\
    run_call es = SOME (r,t) /\ ~frame_resource_starved es0 r t /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n a = AsmOK a1 ==>
    ?k es1. n <= k /\
      NRC (\x y. LENGTH x.contexts >= LENGTH es0.contexts /\
                 step x = (INL (),y)) k es es1 /\
      run_call es1 = SOME (r,t) /\
      asm_frame_rel_tail tail prog data es0 a1 es1
Proof
  Induct
  >- (rpt gen_tac >> simp[asm_steps_def] >> strip_tac >> gvs[] >>
      qexistsl_tac [`0`,`es`] >> simp[NRC]) >>
  rpt gen_tac >> strip_tac >>
  `a.as_pc < LENGTH prog` by
    (spose_not_then assume_tac >> fs[Once asm_steps_def]) >>
  `~is_data_inst (EL a.as_pc prog)` by
    (spose_not_then assume_tac >> Cases_on `EL a.as_pc prog` >>
     gvs[is_data_inst_def, Once asm_steps_def, asm_step_def]) >>
  Cases_on `asm_step (SND (compute_label_offsets prog))
    (build_offset_to_pc prog) (EL a.as_pc prog) a` >>
  gvs[Once asm_steps_def] >>
  rename1 `asm_steps _ _ prog n a2 = AsmOK a1` >>
  drule_all asm_frame_step_progress_tail >> strip_tac >>
  rename1 `asm_frame_rel_tail tail prog data es0 a2 es2` >>
  `LENGTH es.contexts = LENGTH es0.contexts` by
    gvs[asm_frame_rel_tail_def, asm_frame_rel_def] >>
  `?m. NRC (\x y. LENGTH x.contexts >= LENGTH es0.contexts /\
                     step x = (INL (),y)) m u es2` by
    (irule RTC_NRC >> fs[]) >>
  first_x_assum (qspecl_then
    [`tail`,`prog`,`data`,`es0`,`a2`,`es2`,`a1`,`r`,`t`] mp_tac) >>
  simp[] >> strip_tac >> rename1 `NRC _ remaining es2 es1` >>
  qexistsl_tac [`SUC m + remaining`,`es1`] >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (irule NRC_ADD_I >> qexists_tac `es2` >>
      conj_tac
      >- (simp[NRC] >> goal_assum (drule_at Any) >> simp[]) >>
      first_assum ACCEPT_TAC) >> simp[]
QED

Theorem frame_prefix_trace_index[local]:
  !k d es es1 n r t.
    NRC (\x y. LENGTH x.contexts >= d /\ step x = (INL (),y)) k es es1 /\
    d <= LENGTH es1.contexts /\
    FUNPOW (step o SND) n (INL (),es) = (r,t) /\
    ~(ISL r /\ d <= LENGTH t.contexts) ==>
    k < n /\ FUNPOW (step o SND) k (INL (),es) = (INL (),es1)
Proof
  Induct
  >- (rpt gen_tac >> rewrite_tac[NRC] >> strip_tac >> gvs[] >>
      Cases_on `n` >> gvs[FUNPOW]) >>
  rpt gen_tac >> rewrite_tac[NRC] >> strip_tac >>
  rename1 `NRC _ k mid es1` >>
  Cases_on `n` >- gvs[FUNPOW, GREATER_EQ] >>
  rename1 `FUNPOW _ (SUC remaining) _ = _` >>
  `k < remaining /\
   FUNPOW (step o SND) k (INL (),mid) = (INL (),es1)` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> gvs[FUNPOW]) >>
  gvs[FUNPOW]
QED

Theorem asm_frame_prefix_trace_tail:
  asm_frame_prog_ok prog /\ asm_frame_rel_tail tail prog data es0 a es /\
  run_call es = SOME (r,t) /\ ~frame_resource_starved es0 r t ==>
  ?total.
    FUNPOW (step o SND) total (INL (),es) = (r,t) /\
    ~(ISL r /\ LENGTH es.contexts <= LENGTH t.contexts) /\
    (!j. j < total ==>
      ISL (FST (FUNPOW (step o SND) j (INL (),es))) /\
      LENGTH es.contexts <=
        LENGTH (SND (FUNPOW (step o SND) j (INL (),es))).contexts) /\
    (!n a1.
      asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog n a = AsmOK a1 ==>
      ?k es1. n <= k /\ k < total /\
        FUNPOW (step o SND) k (INL (),es) = (INL (),es1) /\
        run_call es1 = SOME (r,t) /\
        asm_frame_rel_tail tail prog data es0 a1 es1)
Proof
  strip_tac >> drule run_call_finite_trace >> strip_tac >>
  rename1 `FUNPOW _ trace_length _ = (r,t)` >> qexists_tac `trace_length` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >>
  drule_all asm_frame_prefix_progress_tail >> strip_tac >>
  `LENGTH es.contexts = LENGTH es0.contexts /\
   LENGTH es1.contexts = LENGTH es0.contexts` by
    gvs[asm_frame_rel_tail_def, asm_frame_rel_def] >>
  qspecl_then [`k`,`LENGTH es0.contexts`,`es`,`es1`,`trace_length`,`r`,`t`]
    mp_tac frame_prefix_trace_index >>
  (impl_tac >- fs[]) >> strip_tac >>
  qexistsl_tac [`k`,`es1`] >> simp[]
QED
