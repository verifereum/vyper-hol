Theory dftGasInvokeTransport
Ancestors
  dftGasFromListRestore dftGasToListReplay dftRunRel dftGasOracleDefs
  gasOracleReplay gasEvents venomExecSemantics venomInst venomState
  list rich_list sorting option

Theorem invoke_setup_common[local]:
  !y a b.
    y.inst_opcode = INVOKE /\
    (!op. MEM op y.inst_operands ==>
      eval_operand op a = eval_operand op b) /\
    (!callee args. setup_callee callee args a = setup_callee callee args b) ==>
    a.vs_fmp = b.vs_fmp /\
    (!callee_name arg_ops. decode_invoke y = SOME (callee_name,arg_ops) ==>
      eval_operands arg_ops a = eval_operands arg_ops b) /\
    (!callee args gs. setup_callee callee args
       (a with vs_gas_readings := gs) =
       setup_callee callee args (b with vs_gas_readings := gs))
Proof
  rpt gen_tac >> strip_tac >>
  `a.vs_fmp = b.vs_fmp` by
    (qpat_x_assum `!callee args. _`
       (qspecl_then [`mk_raw_function "" [ARB]`, `[]`] mp_tac) >>
     simp[setup_callee_def, venomInstTheory.mk_raw_function_def,
          venom_state_component_equality]) >>
  `!ops. EVERY (\op. MEM op y.inst_operands) ops ==>
    eval_operands ops a = eval_operands ops b` by
    (Induct >> simp[eval_operands_def] >> rpt strip_tac >> simp[]) >>
  `!callee_name arg_ops. decode_invoke y = SOME (callee_name,arg_ops) ==>
    eval_operands arg_ops a = eval_operands arg_ops b` by
    (rpt gen_tac >> strip_tac >>
     first_x_assum irule >> simp[EVERY_MEM] >>
     qpat_x_assum `decode_invoke _ = _` mp_tac >>
     simp[decode_invoke_def] >>
     Cases_on `y.inst_operands` >> simp[] >>
     Cases_on `h` >> simp[] >> rpt strip_tac >> gvs[]) >>
  `!callee args gs. setup_callee callee args
     (a with vs_gas_readings := gs) =
     setup_callee callee args (b with vs_gas_readings := gs)` by
    simp[gasOracleReplayTheory.gas_setup_callee] >>
  simp[]
QED

Theorem invoke_native_setup[local]:
  !y a b packet_finish invoke.
    y.inst_opcode = INVOKE /\
    (!op. MEM op y.inst_operands ==>
      eval_operand op a = eval_operand op b) /\
    (!callee args. setup_callee callee args a = setup_callee callee args b) /\
    packet_finish = (\s res.
    case res of
      IntRet ir u =>
        if LENGTH y.inst_outputs = LENGTH ir.iret_values then
          OK (THE (bind_outputs y.inst_outputs ir.iret_values
            (adopt_return_fmp ir (merge_callee_state s u))))
        else Error "invoke: return arity mismatch"
    | Halt u => Halt u | Abort e u => Abort e u | Error e => Error e
    | OK u => Error "invoke: callee did not return") /\
    invoke = (\F D gs.
    case decode_invoke y of
      NONE => Error "invoke: bad operand format"
    | SOME (name,ops) =>
      case lookup_function name D.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops a of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args (a with vs_gas_readings := gs) of
            NONE => Error "invoke: empty function"
          | SOME cs => run_blocks F D callee cs) ==>
    !F D gs.
      step_inst F D y (a with vs_gas_readings := gs) = packet_finish a (invoke F D gs) /\
      step_inst F D y (b with vs_gas_readings := gs) = packet_finish b (invoke F D gs)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all invoke_setup_common >> strip_tac >>
  rpt gen_tac >> simp[step_inst_def] >>
     Cases_on `decode_invoke y` >> simp[] >>
     PairCases_on `x` >> simp[] >>
     `eval_operands x1 a = eval_operands x1 b` by metis_tac[] >>
     simp[] >> BasicProvers.TOP_CASE_TAC >> simp[] >>
     BasicProvers.TOP_CASE_TAC >> simp[] >>
     BasicProvers.TOP_CASE_TAC >> simp[] >>
     BasicProvers.TOP_CASE_TAC >> simp[invoke_bind_case, merge_callee_state_def]
QED

Theorem invoke_finish_observations[local]:
  !outs a b r r' packet_finish.
  a.vs_fmp = b.vs_fmp /\
  packet_finish = (\s res.
    case res of
      IntRet ir u =>
        if LENGTH outs = LENGTH ir.iret_values then
          OK (THE (bind_outputs outs ir.iret_values
            (adopt_return_fmp ir (merge_callee_state s u))))
        else Error "invoke: return arity mismatch"
    | Halt u => Halt u | Abort e u => Abort e u | Error e => Error e
    | OK u => Error "invoke: callee did not return") ==>
    (terminates (packet_finish a r) <=> terminates (packet_finish b r)) /\
    (!P. (!u. (packet_finish a r = OK u \/ (?ir. packet_finish a r = IntRet ir u)) ==>
                 P u.vs_gas_readings) <=>
         (!u. (packet_finish b r = OK u \/ (?ir. packet_finish b r = IntRet ir u)) ==>
                 P u.vs_gas_readings)) /\
    (((?u. packet_finish a r = OK u) \/ (?ir u. packet_finish a r = IntRet ir u)) <=>
     ((?u. packet_finish b r = OK u) \/ (?ir u. packet_finish b r = IntRet ir u))) /\
    (dft_res_rel (restore_result [] (packet_finish a r))
                 (restore_result [] (packet_finish a r')) <=>
     dft_res_rel (restore_result [] (packet_finish b r))
                 (restore_result [] (packet_finish b r'))) /\
    (!tail. residual_result tail (packet_finish a r) (packet_finish a r') <=>
            residual_result tail (packet_finish b r) (packet_finish b r'))
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `r` >> Cases_on `r'` >>
  simp[passSimulationDefsTheory.terminates_def,
       restore_result_def, dftRunRelTheory.dft_res_rel_def,
       residual_result_def, stateEquivTheory.lift_result_def] >>
  rpt IF_CASES_TAC >>
  simp[passSimulationDefsTheory.terminates_def,
       restore_result_def, dftRunRelTheory.dft_res_rel_def,
       residual_result_def, stateEquivTheory.lift_result_def,
       invoke_return_readings, invoke_return_compare_gas] >>
  gen_tac >> pure_once_rewrite_tac[invoke_gas_equality] >>
  simp[invoke_return_readings] >> metis_tac[invoke_return_compare_gas]
QED

(* Lift an exact returning callee cut through the real caller frame. *)
Theorem invoke_return_residual:
  i.inst_opcode = INVOKE /\
  decode_invoke i = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME f /\
  eval_operands ops s = SOME args /\
  setup_callee f args s = SOME cs /\
  residual_result tail (IntRet ir u)
    (run_blocks fuel C f (cs with vs_gas_readings := gs)) /\
  bind_outputs i.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state s u)) = SOME t ==>
  step_inst fuel C i (s with vs_gas_readings := gs) =
    OK (t with vs_gas_readings := tail)
Proof
  strip_tac >>
  `setup_callee f args (s with vs_gas_readings := gs) =
     SOME (cs with vs_gas_readings := gs)` by
    (qpat_x_assum `setup_callee _ _ _ = SOME _` mp_tac >>
     simp[gasOracleReplayTheory.gas_setup_callee, optionTheory.OPTION_MAP_EQ_SOME] >>
     strip_tac >> gvs[] >>
     qpat_x_assum `cs = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  Cases_on `run_blocks fuel C f (cs with vs_gas_readings := gs)` >>
  gvs[residual_result_def, stateEquivTheory.lift_result_def] >>
  simp[Once step_inst_def, gasOracleReplayTheory.gas_eval_operands,
       gasOracleReplayTheory.gas_merge_callee,
       gasOracleReplayTheory.gas_adopt_return,
       gasOracleReplayTheory.gas_bind_outputs]
QED

(* Reuse a fixed returning child packet at its actual caller. *)
Theorem closed_child_invoke_fixed:
 !fuel C7 C8 i b0 nm ops args sf tf cs ir child_out caller_out m es unused.
  i.inst_opcode = INVOKE /\ decode_invoke i = SOME (nm,ops) /\
  lookup_function nm C7.ctx_functions = SOME sf /\
  lookup_function nm C8.ctx_functions = SOME tf /\
  eval_operands ops b0 = SOME args /\
  setup_callee sf args b0 = SOME cs /\
  setup_callee tf args b0 = SOME cs /\
  bind_outputs i.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_out /\
  run_blocks fuel C8 tf cs = IntRet ir child_out /\
  LENGTH m = LENGTH es /\ EVERY IS_SOME m /\
  unused = child_out.vs_gas_readings /\
  PERM (MAP THE (FILTER IS_SOME m) ++ unused) cs.vs_gas_readings /\
  (!gs tail.
   LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
   (?extra. es = gas_events_blocks fuel C7 sf
       (cs with vs_gas_readings := gs ++ tail) ++ extra) /\
   ((?f. terminates (run_blocks f C7 sf
       (cs with vs_gas_readings := gs ++ tail))) ==>
    terminates (run_blocks fuel C7 sf
       (cs with vs_gas_readings := gs ++ tail)) /\
    dft_res_rel
     (restore_result [] (run_blocks fuel C7 sf
       (cs with vs_gas_readings := gs ++ tail)))
     (restore_result [] (IntRet ir child_out)) /\
    gas_events_blocks fuel C7 sf
       (cs with vs_gas_readings := gs ++ tail) = es /\
    residual_result tail (IntRet ir child_out)
      (run_blocks fuel C7 sf (cs with vs_gas_readings := gs ++ tail))))
  ==>
  LENGTH m = LENGTH es /\ EVERY IS_SOME m /\
  unused = caller_out.vs_gas_readings /\
  PERM (MAP THE (FILTER IS_SOME m) ++ unused) b0.vs_gas_readings /\
  step_inst fuel C8 i b0 = OK caller_out /\
  !gs tail.
   LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
   (?extra. es = gas_events_step fuel C7 b0.vs_current_bb i
      (b0 with vs_gas_readings := gs ++ tail) ++ extra) /\
   ((?f. terminates (step_inst f C7 i
      (b0 with vs_gas_readings := gs ++ tail))) ==>
    terminates (step_inst fuel C7 i
      (b0 with vs_gas_readings := gs ++ tail)) /\
    dft_res_rel
     (restore_result [] (step_inst fuel C7 i
       (b0 with vs_gas_readings := gs ++ tail)))
     (restore_result [] (OK caller_out)) /\
    gas_events_step fuel C7 b0.vs_current_bb i
      (b0 with vs_gas_readings := gs ++ tail) = es /\
    residual_result tail (OK caller_out)
      (step_inst fuel C7 i (b0 with vs_gas_readings := gs ++ tail)))
Proof
  rpt gen_tac >> strip_tac >>
  `cs.vs_gas_readings = b0.vs_gas_readings` by
    metis_tac[gasOracleReplayTheory.gas_setup_callee_readings] >>
  `caller_out.vs_gas_readings = child_out.vs_gas_readings` by
    (drule gasOracleReplayTheory.gas_bind_outputs_readings >>
     simp[merge_callee_state_def, adopt_return_fmp_def]) >>
  `step_inst fuel C8 i b0 = OK caller_out` by
    simp[Once step_inst_def] >>
  `!rs. setup_callee sf args (b0 with vs_gas_readings := rs) =
     SOME (cs with vs_gas_readings := rs)` by
    (gen_tac >> qpat_x_assum `setup_callee sf args b0 = SOME cs` mp_tac >>
     simp[gasOracleReplayTheory.gas_setup_callee, optionTheory.OPTION_MAP_EQ_SOME] >>
     strip_tac >> gvs[] >>
     qpat_x_assum `cs = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!n rs. terminates (step_inst n C7 i (b0 with vs_gas_readings := rs)) ==>
     terminates (run_blocks n C7 sf (cs with vs_gas_readings := rs))` by
    (rpt gen_tac >>
     simp[Once step_inst_def, gasOracleReplayTheory.gas_eval_operands] >>
     Cases_on `run_blocks n C7 sf (cs with vs_gas_readings := rs)` >>
     simp[passSimulationDefsTheory.terminates_def]) >>
  `!n rs. gas_events_step n C7 b0.vs_current_bb i
     (b0 with vs_gas_readings := rs) =
     gas_events_blocks n C7 sf (cs with vs_gas_readings := rs)` by
    simp[gas_events_step_def, gasOracleReplayTheory.gas_eval_operands] >>
  `PERM (MAP THE (FILTER IS_SOME m) ++ unused) b0.vs_gas_readings` by
    (qpat_x_assum `PERM _ cs.vs_gas_readings` mp_tac >> simp[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs tail. LIST_REL _ _ _ ==> _`
    (qspecl_then [`gs`, `tail`] mp_tac) >>
  simp[] >> strip_tac >> strip_tac >>
  `?f. terminates (run_blocks f C7 sf
     (cs with vs_gas_readings := gs ++ tail))` by metis_tac[] >>
  qpat_x_assum `(?f. terminates (run_blocks _ _ _ _)) ==> _` mp_tac >>
  impl_tac >- metis_tac[] >> strip_tac >>
  `step_inst fuel C7 i (b0 with vs_gas_readings := gs ++ tail) =
     OK (caller_out with vs_gas_readings := tail)` by
    metis_tac[invoke_return_residual] >>
  qpat_assum `step_inst fuel C7 i _ = OK _` (fn step =>
  qpat_assum `gas_events_blocks fuel C7 sf _ = es` (fn events =>
    simp_tac (srw_ss()) [step, events,
      passSimulationDefsTheory.terminates_def, restore_result_def,
      dftRunRelTheory.dft_res_rel_def, residual_result_def,
      stateEquivTheory.lift_result_def]))
QED


(* Equal invocation operands and setup transport the same selected packet. *)
Theorem invoke_fixed_segment_setup:
  !m es unused fuel C C' y a b.
    y.inst_opcode = INVOKE /\
    a.vs_gas_readings = b.vs_gas_readings /\
    (!op. MEM op y.inst_operands ==>
      eval_operand op a = eval_operand op b) /\
    (!callee args. setup_callee callee args a = setup_callee callee args b) ==>
    ((
    PERM (MAP THE (FILTER IS_SOME m) ++ unused) a.vs_gas_readings /\
    (!u. (step_inst fuel C' y a = OK u \/
          (?ir. step_inst fuel C' y a = IntRet ir u)) ==>
      EVERY IS_SOME m /\ unused = u.vs_gas_readings) /\
    !gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
      (?extra. es = gas_events_step fuel C a.vs_current_bb y
         (a with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?j. terminates (step_inst j C y (a with vs_gas_readings := gs ++ tail))) ==>
        terminates (step_inst fuel C y (a with vs_gas_readings := gs ++ tail)) /\
        dft_res_rel
          (restore_result [] (step_inst fuel C y (a with vs_gas_readings := gs ++ tail)))
          (restore_result [] (step_inst fuel C' y a)) /\
        (((?v. step_inst fuel C' y a = OK v) \/
          (?ir v. step_inst fuel C' y a = IntRet ir v)) ==>
          gas_events_step fuel C a.vs_current_bb y
            (a with vs_gas_readings := gs ++ tail) = es /\
          residual_result tail (step_inst fuel C' y a)
            (step_inst fuel C y (a with vs_gas_readings := gs ++ tail))))
    ) <=> (
    PERM (MAP THE (FILTER IS_SOME m) ++ unused) b.vs_gas_readings /\
    (!u. (step_inst fuel C' y b = OK u \/
          (?ir. step_inst fuel C' y b = IntRet ir u)) ==>
      EVERY IS_SOME m /\ unused = u.vs_gas_readings) /\
    !gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
      (?extra. es = gas_events_step fuel C b.vs_current_bb y
         (b with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?j. terminates (step_inst j C y (b with vs_gas_readings := gs ++ tail))) ==>
        terminates (step_inst fuel C y (b with vs_gas_readings := gs ++ tail)) /\
        dft_res_rel
          (restore_result [] (step_inst fuel C y (b with vs_gas_readings := gs ++ tail)))
          (restore_result [] (step_inst fuel C' y b)) /\
        (((?v. step_inst fuel C' y b = OK v) \/
          (?ir v. step_inst fuel C' y b = IntRet ir v)) ==>
          gas_events_step fuel C b.vs_current_bb y
            (b with vs_gas_readings := gs ++ tail) = es /\
          residual_result tail (step_inst fuel C' y b)
            (step_inst fuel C y (b with vs_gas_readings := gs ++ tail))))
    ))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all invoke_setup_common >> strip_tac >>
  `!F D owner owner' gs.
    gas_events_step F D owner y (a with vs_gas_readings := gs) =
    gas_events_step F D owner' y (b with vs_gas_readings := gs)` by
    (rpt gen_tac >> simp[gas_events_step_def] >>
     BasicProvers.TOP_CASE_TAC >> simp[] >>
     rename1 `decode_invoke y = SOME decoded` >>
     PairCases_on `decoded` >> simp[] >>
     `eval_operands decoded1 a = eval_operands decoded1 b` by metis_tac[] >>
     simp[] >> BasicProvers.TOP_CASE_TAC >> simp[] >>
     BasicProvers.TOP_CASE_TAC >> simp[]) >>
  qabbrev_tac `packet_finish = (\s res.
    case res of
      IntRet ir u =>
        if LENGTH y.inst_outputs = LENGTH ir.iret_values then
          OK (THE (bind_outputs y.inst_outputs ir.iret_values
            (adopt_return_fmp ir (merge_callee_state s u))))
        else Error "invoke: return arity mismatch"
    | Halt u => Halt u | Abort e u => Abort e u | Error e => Error e
    | OK u => Error "invoke: callee did not return")` >>
  qabbrev_tac `invoke = (\F D gs.
    case decode_invoke y of
      NONE => Error "invoke: bad operand format"
    | SOME (name,ops) =>
      case lookup_function name D.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops a of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args (a with vs_gas_readings := gs) of
            NONE => Error "invoke: empty function"
          | SOME cs => run_blocks F D callee cs)` >>
  `!F D gs.
    step_inst F D y (a with vs_gas_readings := gs) = packet_finish a (invoke F D gs) /\
    step_inst F D y (b with vs_gas_readings := gs) = packet_finish b (invoke F D gs)` by
    (irule invoke_native_setup >> simp[Abbr `packet_finish`, Abbr `invoke`]) >>
  qspecl_then [`y.inst_outputs`, `a`, `b`] mp_tac
    invoke_finish_observations >>
  qpat_assum `Abbrev (packet_finish = _)`
    (fn th => rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  `step_inst fuel C' y a = packet_finish a (invoke fuel C' a.vs_gas_readings) /\
   step_inst fuel C' y b = packet_finish b (invoke fuel C' a.vs_gas_readings)` by
    (first_x_assum (qspecl_then [`fuel`, `C'`, `a.vs_gas_readings`] mp_tac) >>
     simp[]) >>
  `!gs. gas_events_step fuel C a.vs_current_bb y (a with vs_gas_readings := gs) =
        gas_events_step fuel C b.vs_current_bb y (b with vs_gas_readings := gs)` by
    metis_tac[] >>
  simp[]
QED

(* Replay of an actual invocation is portable across equal callee setup. *)
Theorem invoke_restore_setup:
  !nf ef C D y a b orc p d rs.
    y.inst_opcode = INVOKE /\
    a.vs_gas_readings = b.vs_gas_readings /\
    (!op. MEM op y.inst_operands ==>
      eval_operand op a = eval_operand op b) /\
    (!callee args. setup_callee callee args a = setup_callee callee args b) ==>
    (restore_rel rs (step_inst nf C y a)
       (ev_step orc p d ef D y (a with vs_gas_readings := rs)) <=>
     restore_rel rs (step_inst nf C y b)
       (ev_step orc p d ef D y (b with vs_gas_readings := rs)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all invoke_setup_common >> strip_tac >>
  qabbrev_tac `packet_finish = (\s res.
    case res of
      IntRet ir u =>
        if LENGTH y.inst_outputs = LENGTH ir.iret_values then
          OK (THE (bind_outputs y.inst_outputs ir.iret_values
            (adopt_return_fmp ir (merge_callee_state s u))))
        else Error "invoke: return arity mismatch"
    | Halt u => Halt u | Abort e u => Abort e u | Error e => Error e
    | OK u => Error "invoke: callee did not return")` >>
  qabbrev_tac `invoke = (\F D gs.
    case decode_invoke y of
      NONE => Error "invoke: bad operand format"
    | SOME (name,ops) =>
      case lookup_function name D.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops a of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args (a with vs_gas_readings := gs) of
            NONE => Error "invoke: empty function"
          | SOME cs => run_blocks F D callee cs)` >>
  `!F D gs.
    step_inst F D y (a with vs_gas_readings := gs) = packet_finish a (invoke F D gs) /\
    step_inst F D y (b with vs_gas_readings := gs) = packet_finish b (invoke F D gs)` by
    (irule invoke_native_setup >> simp[Abbr `packet_finish`, Abbr `invoke`]) >>
  qabbrev_tac `invoke_oracle = (\F D gs.
    case decode_invoke y of
      NONE => Error "invoke: bad operand format"
    | SOME (name,ops) =>
      case lookup_function name D.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops a of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args (a with vs_gas_readings := gs) of
            NONE => Error "invoke: empty function"
          | SOME cs => ev_blocks orc ((d,y.inst_id)::p) d F D callee cs)` >>
  `!F D gs.
    ev_step orc p d F D y (a with vs_gas_readings := gs) = packet_finish a (invoke_oracle F D gs) /\
    ev_step orc p d F D y (b with vs_gas_readings := gs) = packet_finish b (invoke_oracle F D gs)` by
    (rpt gen_tac >> simp[ev_step_def, Abbr `invoke_oracle`] >>
     Cases_on `decode_invoke y` >> simp[Abbr `packet_finish`] >>
     PairCases_on `x` >> simp[] >>
     `eval_operands x1 a = eval_operands x1 b` by metis_tac[] >>
     simp[] >> BasicProvers.TOP_CASE_TAC >> simp[] >>
     BasicProvers.TOP_CASE_TAC >> simp[] >>
     BasicProvers.TOP_CASE_TAC >> simp[] >>
     BasicProvers.TOP_CASE_TAC >> simp[invoke_bind_case, merge_callee_state_def]) >>

  `step_inst nf' C y a =
      packet_finish a (invoke nf' C a.vs_gas_readings) /\
   step_inst nf' C y b =
      packet_finish b (invoke nf' C a.vs_gas_readings)` by
    (qpat_x_assum `!F D gs. step_inst _ _ _ _ = _ /\ _`
      (qspecl_then [`nf'`, `C`, `a.vs_gas_readings`] mp_tac) >>
     simp[]) >>
  `!x x'. restore_rel rs x x' <=> residual_result rs x x'` by
    (Cases >> Cases >> simp[restore_rel_def, residual_result_def,
                           stateEquivTheory.lift_result_def] >> metis_tac[]) >>
  qspecl_then [`y.inst_outputs`, `a`, `b`,
    `invoke nf' C a.vs_gas_readings`, `invoke_oracle ef D rs`,
    `packet_finish`] mp_tac invoke_finish_observations >>
  (impl_tac >- simp[Abbr `packet_finish`]) >>
  strip_tac >> simp[] >>
  qpat_x_assum `!tail. residual_result _ _ _ <=> _`
    (qspec_then `rs` mp_tac) >> simp[]
QED
