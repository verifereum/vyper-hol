Theory dftPacketSuccessfulTerminalRow
Ancestors
  dftPacketClosedRowNative dftPacketNativeSlice dftNativePlanPrefix
  dftGasFromListTraceDefs dftGasFromListReadings dftGasFromListRestore dftGasToListReplay
  dftRunRel dftIndexedExec gasOracleReplay gasEvents frameGasEvents
  stateEquiv passSimulationDefs
  venomExecSemantics venomInst venomState list rich_list arithmetic sorting

(* A terminal has no GAS/INVOKE effect, independently of call-outcome rules. *)
Theorem dft_packet_successful_terminal_step[local]:
  is_terminator c.inst_opcode /\ step_inst f C c s = r /\
  (r = OK out \/ ?ir. r = IntRet ir out) /\
  (r = OK out ==> ~out.vs_halted) ==>
  out.vs_gas_readings = s.vs_gas_readings /\
  !g D tail. dft_exec_cons g D c OK (s with vs_gas_readings := tail) =
    restore_result tail r
Proof
  strip_tac >>
  `c.inst_opcode <> GAS /\ c.inst_opcode <> INVOKE` by
    (Cases_on `c.inst_opcode` >> gvs[is_terminator_def]) >>
  `gas_replay_at 0 (step_inst_base c) s` by
    (irule gas_base_non_gas >> simp[]) >>
  gvs[gas_replay_at_def, step_inst_non_invoke] >>
  qpat_assum `!tail. _` (qspec_then `[]` mp_tac) >>
  Cases_on `step_inst_base c (s with vs_gas_readings := [])` >>
  simp[lift_result_def] >> strip_tac >> gvs[] >>
  map_every qx_gen_tac [`g`,`D`,`gs`] >>
  qpat_x_assum `!tail. _` (qspec_then `gs` mp_tac) >>
  Cases_on `step_inst_base c (s with vs_gas_readings := gs)` >>
  simp[lift_result_def, dft_exec_cons_def, step_inst_non_invoke,
       restore_result_def] >> strip_tac >> gvs[]
QED

(* Appending a silent terminal changes neither sites nor GAS keys, including
   branches which stop before reaching the appended instruction. *)
Theorem dft_packet_terminal_events[local]:
  !pre s bb cut.
    DROP s.vs_inst_idx bb.bb_instructions = pre ++ [c] /\
    DROP s.vs_inst_idx cut.bb_instructions = pre /\
    is_terminator c.inst_opcode ==>
    gas_events_block fuel C sf.fn_name bb s =
      gas_events_block fuel C sf.fn_name cut s /\
    trace_gas (trace_block a e fuel C sf bb s) =
      trace_gas (trace_block a e fuel C sf cut s)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (`c.inst_opcode <> GAS /\ c.inst_opcode <> INVOKE` by
        (Cases_on `c.inst_opcode` >> gvs[is_terminator_def]) >>
      `s.vs_inst_idx < LENGTH bb.bb_instructions /\
       LENGTH cut.bb_instructions <= s.vs_inst_idx` by
        (gvs[LIST_EQ_REWRITE, LENGTH_DROP, DROP_EQ_NIL]) >>
      `EL s.vs_inst_idx bb.bb_instructions = c` by
        (qpat_x_assum `DROP _ bb.bb_instructions = _` (mp_tac o AP_TERM ``HD:instruction list -> instruction``) >>
         simp[HD_DROP]) >>
      once_rewrite_tac[gas_events_block_def, trace_defs] >>
      simp[get_instruction_def, gas_events_step_plain, trace_step_noninvoke,
           trace_gas_cons, visit_gas_def] >>
      Cases_on `step_inst fuel C c s` >> simp[]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   s.vs_inst_idx < LENGTH cut.bb_instructions` by
    (gvs[LIST_EQ_REWRITE, LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   EL s.vs_inst_idx cut.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre ++ [c] /\
   DROP (SUC s.vs_inst_idx) cut.bb_instructions = pre` by
    gvs[DROP_CONS_EL] >>
  once_rewrite_tac[gas_events_block_def, trace_defs] >>
  simp[get_instruction_def, trace_gas_cons] >>
  Cases_on `step_inst fuel C h s` >> simp[] >>
  IF_CASES_TAC >> simp[] >> first_x_assum irule >> simp[]
QED

(* The caller supplies the preterminal certificates, not a closed-row
   constructor.  Fuel and contexts of the common silent terminal may differ. *)
Theorem dft_packet_successful_terminal_row:
  !N e C7 C8 sf bb ps xs ys xpre ypre c be s r8 out ms ess ks a.
    bb.bb_instructions = ps ++ xs /\ be.vs_inst_idx = LENGTH ps /\
    xs = xpre ++ [c] /\ ys = ypre ++ [c] /\
    LENGTH xpre = LENGTH ypre /\
    EVERY (\i. ~is_terminator i.inst_opcode) xpre /\
    EVERY (\i. ~is_terminator i.inst_opcode) ypre /\
    is_terminator c.inst_opcode /\
    step_inst (N-e) C8 c s = r8 /\
    (r8 = OK out \/ ?ir. r8 = IntRet ir out) /\
    (r8 = OK out ==> ~out.vs_halted) /\
    (!F. N <= F ==>
      FOLDR (dft_exec_cons (F-e) C8) OK ypre be = OK s) /\
    EVERY IS_SOME (FLAT ms) /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ s.vs_gas_readings)
      be.vs_gas_readings /\
    (!F gs tail.
      N <= F /\
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
      FOLDR (dft_exec_cons (F-e) C7) OK xpre
        (be with vs_gas_readings := gs ++ tail) =
          OK (s with vs_gas_readings := tail) /\
      gas_events_block (F-e) C7 sf.fn_name
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xpre|>
        (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
      trace_gas (trace_block a e (F-e) C7 sf
        (bb with bb_instructions := TAKE (LENGTH ps + LENGTH xpre) bb.bb_instructions)
        (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs)) ==>
    terminates r8 /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ out.vs_gas_readings)
      be.vs_gas_readings /\
    (!v. (r8 = OK v \/ ?ir. r8 = IntRet ir v) ==>
      EVERY IS_SOME (FLAT ms) /\ out.vs_gas_readings = v.vs_gas_readings) /\
    (!F. N <= F ==>
      FOLDR (dft_exec_cons (F-e) C8) OK ys be = r8 /\
      (!gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
        (?extra. FLAT ess =
          gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) ==>
          terminates (FOLDR (dft_exec_cons (F-e) C7) OK xs
            (be with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (FOLDR (dft_exec_cons (F-e) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)))
            (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
            residual_result tail r8
              (FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail)))) /\
        (!v. (FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = OK v \/
              ?ir. FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          trace_gas (trace_block a e (F-e) C7 sf
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs))))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `out.vs_gas_readings = s.vs_gas_readings /\
   !g D tail. dft_exec_cons g D c OK (s with vs_gas_readings := tail) =
     restore_result tail r8` by metis_tac[dft_packet_successful_terminal_step] >>
  `terminates r8 /\
   (!v. (r8 = OK v \/ ?ir. r8 = IntRet ir v) ==> out = v)` by
    (gvs[terminates_def] >> metis_tac[]) >>
  simp[] >> (conj_tac >- metis_tac[]) >>
  qx_gen_tac `budget` >> strip_tac >> conj_tac
  >- (`FOLDR (dft_exec_cons (budget-e) C8) OK ypre be = OK s` by metis_tac[] >>
      simp[FOLDR_APPEND, Once dft_exec_prefix_continue] >>
      `s with vs_gas_readings := s.vs_gas_readings = s` by
        simp[venom_state_component_equality] >>
      qpat_x_assum `!g D tail. _` (qspecl_then [`budget-e`,`C8`,`s.vs_gas_readings`] mp_tac) >>
      Cases_on `r8` >> gvs[restore_result_def, venom_state_component_equality]) >>
  map_every qx_gen_tac [`gs`,`tail`] >> strip_tac >>
  qpat_x_assum `!F gs tail. _` (qspecl_then [`budget`,`gs`,`tail`] mp_tac) >>
  simp[] >> strip_tac >>
  `FOLDR (dft_exec_cons (budget-e) C7) OK xs
      (be with vs_gas_readings := gs ++ tail) = restore_result tail r8` by
    (simp[FOLDR_APPEND, Once dft_exec_prefix_continue]) >>
  `gas_events_block (budget-e) C7 sf.fn_name
     <|bb_label := be.vs_current_bb; bb_instructions :=
       REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
     (be with vs_gas_readings := gs ++ tail) = FLAT ess` by
    (qpat_x_assum `gas_events_block _ _ _ _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
     irule (cj 1 dft_packet_terminal_events) >>
     qexistsl_tac [`c`,`xpre`] >> simp[DROP_APPEND, GSYM SUB_RIGHT_SUB]) >>
  `trace_gas (trace_block a e (budget-e) C7 sf
     <|bb_label := be.vs_current_bb; bb_instructions :=
       REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
     (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs)` by
    (qpat_x_assum `trace_gas _ = _` (fn th => rewrite_tac[GSYM th]) >>
     irule (cj 2 dft_packet_terminal_events) >>
     qexistsl_tac [`c`,`xpre`] >>
     simp[DROP_APPEND, TAKE_APPEND, TAKE_LENGTH_TOO_LONG,
          TAKE_LENGTH_ID_rwt, GSYM SUB_RIGHT_SUB]) >>
  fs[] >> Cases_on `r8` >>
  gvs[restore_result_def, terminates_def, residual_result_def, lift_result_def] >>
  qexists_tac `[]` >> simp[]
QED
