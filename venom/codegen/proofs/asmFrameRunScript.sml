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
  frameOutcome callTrace vfmExecution arithmetic relation vfmAccountFrame

(* Preserve the local-step interface while dispatching stateful frame steps. *)
Theorem asm_frame_local_step:
  asm_frame_prog_ok prog /\ asm_frame_rel gas_tail prog data es0 as es /\
  as.as_pc < LENGTH prog /\ ~is_data_inst (EL as.as_pc prog) /\
  EL as.as_pc prog <> AsmOp "CALL" /\
  EL as.as_pc prog <> AsmOp "STATICCALL" ==>
  asm_frame_step_ok gas_tail prog data es0 as es
Proof
  strip_tac >>
  Cases_on `EL as.as_pc prog = AsmOp "DELEGATECALL"`
  >- (irule asm_frame_delegate_step >> simp[]) >>
  Cases_on `EL as.as_pc prog = AsmOp "CREATE" \/
            EL as.as_pc prog = AsmOp "CREATE2"`
  >- (irule asm_frame_create_step >> simp[]) >>
  Cases_on `EL as.as_pc prog = AsmOp "SELFDESTRUCT"`
  >- (irule asm_frame_selfdestruct_step >> simp[]) >>
  irule asm_frame_noncall_step >> simp[] >> metis_tac[]
QED

Theorem asm_frame_step:
  asm_frame_prog_ok prog /\ asm_frame_rel gas_tail prog data es0 as es /\
  as.as_pc < LENGTH prog /\ ~is_data_inst (EL as.as_pc prog) ==>
  asm_frame_step_ok gas_tail prog data es0 as es
Proof
  strip_tac >>
  Cases_on `EL as.as_pc prog = AsmOp "CALL" \/
            EL as.as_pc prog = AsmOp "STATICCALL"`
  >- (irule asm_frame_call_step >> simp[]) >>
  irule asm_frame_local_step >> fs[]
QED

(* Every successful assembly instruction advances the same actual run.
   Labels execute JUMPDEST and empty pushes execute PUSH0. Data-only
   constructors are errors; encoding well-formedness excludes empty opcodes. *)
Theorem asm_frame_step_progress:
  asm_frame_prog_ok prog /\ asm_frame_rel gas_tail prog data es0 a es /\
  a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
  run_call es = SOME (r,t) /\ ~frame_resource_starved es0 r t /\
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (EL a.as_pc prog) a = AsmOK a1 ==>
  ?u es1. step es = (INL (),u) /\
    RTC (\x y. LENGTH x.contexts >= LENGTH es.contexts /\
               step x = (INL (),y)) u es1 /\
    run_call es1 = run_call es /\
    asm_frame_rel gas_tail prog data es0 a1 es1
Proof
  strip_tac >>
  Cases_on `EL a.as_pc prog = AsmOp "CALL" \/
            EL a.as_pc prog = AsmOp "STATICCALL"`
  >- (drule_all asm_frame_call_step_progress >> strip_tac >> metis_tac[]) >>
  Cases_on `EL a.as_pc prog = AsmOp "DELEGATECALL"`
  >- (drule_all asm_frame_delegate_step_progress >> strip_tac >> metis_tac[]) >>
  Cases_on `EL a.as_pc prog = AsmOp "CREATE" \/
            EL a.as_pc prog = AsmOp "CREATE2"`
  >- (drule_all asm_frame_create_step_progress >> strip_tac >> metis_tac[]) >>
  Cases_on `EL a.as_pc prog = AsmOp "SELFDESTRUCT"`
  >- gvs[asm_step_def, asm_step_op_def, asm_step_arith_def,
         asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
         asm_step_control_def, asm_step_extcall_def, asm_selfdestruct_def,
         AllCaseEqs()] >>
  Cases_on `EL a.as_pc prog = AsmOp "GAS"`
  >- (drule_all asm_frame_gas_step >> strip_tac >- gvs[] >>
      gvs[] >> qexists_tac `es1` >> simp[relationTheory.RTC_REFL]) >>
  fs[] >> drule_all frame_plain_step_progress >> strip_tac >> metis_tac[]
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
  >- (rpt gen_tac >> rewrite_tac[NRC] >> strip_tac >>
      gvs[] >>
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

Theorem asm_frame_prefix_progress:
  !n gas_tail prog data es0 a es a1 r t.
    asm_frame_prog_ok prog /\ asm_frame_rel gas_tail prog data es0 a es /\
    run_call es = SOME (r,t) /\ ~frame_resource_starved es0 r t /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n a = AsmOK a1 ==>
    ?k es1. n <= k /\
      NRC (\x y. LENGTH x.contexts >= LENGTH es0.contexts /\
                 step x = (INL (),y)) k es es1 /\
      run_call es1 = SOME (r,t) /\
      asm_frame_rel gas_tail prog data es0 a1 es1
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
  drule_all asm_frame_step_progress >> strip_tac >>
  rename1 `asm_frame_rel gas_tail prog data es0 a2 es2` >>
  `LENGTH es.contexts = LENGTH es0.contexts` by
    (qpat_x_assum `asm_frame_rel _ _ _ _ a es`
       (strip_assume_tac o REWRITE_RULE [asm_frame_rel_def]) >> simp[]) >>
  `?m. NRC (\x y. LENGTH x.contexts >= LENGTH es0.contexts /\
                     step x = (INL (),y)) m u es2` by
    (irule RTC_NRC >> fs[]) >>
  first_x_assum (qspecl_then
    [`gas_tail`,`prog`,`data`,`es0`,`a2`,`es2`,`a1`,`r`,`t`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `NRC _ remaining es2 es1` >>
  qexistsl_tac [`SUC m + remaining`,`es1`] >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (irule NRC_ADD_I >> qexists_tac `es2` >>
      conj_tac
      >- (simp[NRC] >> goal_assum (drule_at Any) >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  simp[]
QED

(* The bound is chosen from the same actual run before the prefix. *)
Theorem asm_frame_prefix_trace:
  asm_frame_prog_ok prog /\ asm_frame_rel gas_tail prog data es0 a es /\
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
        asm_frame_rel gas_tail prog data es0 a1 es1)
Proof
  strip_tac >> drule run_call_finite_trace >> strip_tac >>
  rename1 `FUNPOW _ trace_length _ = (r,t)` >>
  qexists_tac `trace_length` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  drule_all asm_frame_prefix_progress >> strip_tac >>
  `LENGTH es.contexts = LENGTH es0.contexts /\
   LENGTH es1.contexts = LENGTH es0.contexts` by
    (conj_tac
     >- (qpat_x_assum `asm_frame_rel _ _ _ _ a es`
           (strip_assume_tac o REWRITE_RULE [asm_frame_rel_def]) >> simp[]) >>
     qpat_x_assum `asm_frame_rel _ _ _ _ a1 es1`
       (strip_assume_tac o REWRITE_RULE [asm_frame_rel_def]) >> simp[]) >>
  qspecl_then [`k`,`LENGTH es0.contexts`,`es`,`es1`,`trace_length`,`r`,`t`]
    mp_tac frame_prefix_trace_index >>
  (impl_tac >- fs[]) >>
  strip_tac >> qexistsl_tac [`k`,`es1`] >> simp[]
QED

(* Successful assembly prefixes stay inside the observed EVM run. *)
Theorem asm_frame_prefix:
  !n gas_tail prog data es0 as es a1 r es'.
    asm_frame_prog_ok prog /\ asm_frame_rel gas_tail prog data es0 as es /\
    run_call es = SOME (r, es') /\ ~frame_resource_starved es0 r es' /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n as = AsmOK a1 ==>
    ?es1. run_call es1 = SOME (r, es') /\
          asm_frame_rel gas_tail prog data es0 a1 es1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all asm_frame_prefix_progress >> strip_tac >> metis_tac[]
QED

(* A reached GAS must have a real reading, even with an unread padding tail. *)
Theorem asm_frame_prefix_gas_available:
  !n gas_tail prog data es0 as es a1 r es'.
    asm_frame_prog_ok prog /\ asm_frame_rel gas_tail prog data es0 as es /\
    run_call es = SOME (r, es') /\ ~frame_resource_starved es0 r es' /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n as = AsmOK a1 /\
    a1.as_pc < LENGTH prog /\ EL a1.as_pc prog = AsmOp "GAS" ==>
    LENGTH gas_tail < LENGTH a1.as_gas_readings
Proof
  rpt gen_tac >> strip_tac >>
  drule_all asm_frame_prefix >> strip_tac >>
  `~is_data_inst (EL a1.as_pc prog)` by simp[asmWfTheory.is_data_inst_def] >>
  drule_all asm_frame_gas_step >> strip_tac >- gvs[] >>
  fs[asm_frame_rel_def]
QED

Theorem asm_frame_prefix_gas_count_bound:
  !n k gas_tail prog data es0 as es a1 r es'.
    asm_frame_prog_ok prog /\ asm_frame_rel gas_tail prog data es0 as es /\
    run_call es = SOME (r, es') /\ ~frame_resource_starved es0 r es' /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n as = AsmOK a1 /\
    a1.as_pc < LENGTH prog /\ EL a1.as_pc prog = AsmOp "GAS" /\
    a1.as_gas_readings = DROP (k - 1) as.as_gas_readings /\ 0 < k ==>
    k <= LENGTH (gas_readings es)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all asm_frame_prefix_gas_available >>
  fs[asm_frame_rel_def, listTheory.LENGTH_DROP] >> decide_tac
QED

Theorem asm_frame_run:
  !n gas_tail prog data es0 as es r es'.
    asm_frame_prog_ok prog /\ asm_frame_rel gas_tail prog data es0 as es /\
    run_call es = SOME (r, es') ==>
    frame_resource_starved es0 r es' \/
    ((!as'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
              prog n as = AsmHalt as' ==>
        frame_outcome es0 r es' NONE as'.as_returndata as'.as_logs /\
        es'.rollback.accounts = as'.as_accounts /\
        es'.rollback.toDelete = as'.as_pending_deletions /\
        es'.rollback.tStorage = as'.as_transient /\
        as'.as_requests = call_requests es0 /\ as'.as_gas_readings = gas_tail) /\
     (!as'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
              prog n as = AsmRevert as' ==>
        as'.as_gas_readings = gas_tail /\
        ?lgs. frame_outcome es0 r es' (SOME Reverted) as'.as_returndata lgs) /\
     (!as'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
              prog n as = AsmFault as' ==>
        as'.as_gas_readings = gas_tail /\
        ?exc lgs. exc <> Reverted /\ frame_outcome es0 r es' (SOME exc) [] lgs))
Proof
  Induct >- simp[asm_steps_def] >>
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `as.as_pc < LENGTH prog`) >- simp[asm_steps_def] >>
  Cases_on `is_data_inst (EL as.as_pc prog)`
  >- (Cases_on `EL as.as_pc prog` >>
      gvs[is_data_inst_def, asm_step_def, asm_steps_def]) >>
  `asm_frame_step_ok gas_tail prog data es0 as es` by (irule asm_frame_step >> simp[]) >>
  pop_assum mp_tac >> simp[asm_frame_step_ok_def] >> strip_tac
  >- gvs[] >>
  simp[asm_steps_def] >>
  Cases_on `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
              (EL as.as_pc prog) as` >> gvs[]
  >~ [`AsmOK as1`]
  >- (first_x_assum (qspecl_then [`gas_tail`, `prog`, `data`, `es0`, `as1`, `es1`, `r`, `es'`]
        mp_tac) >> simp[]) >>
  DISJ2_TAC >> metis_tac[]
QED
