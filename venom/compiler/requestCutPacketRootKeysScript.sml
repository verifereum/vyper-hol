Theory requestCutPacketRootKeys
Ancestors
  requestCutPacketRootResult requestCutStoppedPlan
  dftFinitePacket dftGasFromListTraceDefs dftIndexedExec
  venomExecSemantics venomState gasEvents list rich_list arithmetic finite_map

Theorem request_cut_packet_root_keys:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  LENGTH paths = LENGTH levels /\ HD paths = [] /\
  HD depths = 0 /\ FST (HD levels) = root_sf /\
  LENGTH keyss = LENGTH levels /\
  P 0 entry /\
  row_run = (\(bb,e,z) s. case eval_phis s bb.bb_instructions of
    OK sp => FOLDR (dft_exec_cons (fuel-e) C7) OK z
                (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
  | other => other) /\
  level_run = (\(sf,plan,call) ent.
    case FOLDL (\v row. case v of OK s => row_run row s | other => other) (OK ent) plan of
      OK caller => (case call of NONE => OK caller | SOME c =>
        (case decode_invoke c of
          NONE => Error "invoke: bad operand format"
        | SOME (nm,ops) =>
          (case lookup_function nm C7.ctx_functions of
            NONE => Error "invoke: function not found"
          | SOME callee =>
            (case eval_operands ops caller of
              NONE => Error "invoke: undefined argument"
            | SOME args =>
              (case setup_callee callee args caller of
                NONE => Error "invoke: empty function" | SOME cs => OK cs)))))
    | other => other) /\
  run_at = (\i s. if i < LENGTH levels then
    (run_blocks (fuel - EL i depths) C7 (FST (EL i levels)) s,
     MAP FST (trace_gas (trace_blocks (EL i paths) (EL i depths)
       (fuel - EL i depths) C7 (FST (EL i levels)) s)))
    else (OK s,[])) /\
  (!i s. i < LENGTH levels /\ P i s ==>
    case level_run (EL i levels) s of
      OK t => P (SUC i) t /\
        (~(?u. FST (run_at (SUC i) t) = OK u) /\
         ~(?ir u. FST (run_at (SUC i) t) = IntRet ir u) ==>
         FST (run_at i s) = FST (run_at (SUC i) t) /\
         SND (run_at i s) = EL i keyss ++ SND (run_at (SUC i) t))
    | stopped => ~(?ir u. stopped = IntRet ir u) /\
        FST (run_at i s) = stopped /\
        ?extra. EL i keyss = SND (run_at i s) ++ extra) /\
  SND (rooted_eval fuel C7 levels entry) = r /\ ~(?u. r = OK u) ==>
  ~(?ir u. r = IntRet ir u) /\ run_blocks fuel C7 root_sf entry = r /\
  ?extra. FLAT keyss = MAP FST (trace_gas (trace_blocks [] 0 fuel C7 root_sf entry)) ++ extra
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule request_cut_packet_root_result >>
  disch_then (qspecl_then [`fuel`,`C7`,`levels`,`entry`] assume_tac) >>
  `FOLDL (\r row. case r of OK s => row s | other => other)
      (OK entry) (MAP level_run levels) = r` by suspend "result" >>
  mp_tac (Q.SPECL [`MAP level_run (levels : (ir_function # (basic_block # num # instruction list) list # instruction option) list)`,`keyss`,`entry`,`P`,`run_at`]
    request_cut_nested_plan_keys) >>
  impl_tac >-
    (simp_tac bool_ss [LENGTH_MAP] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     `EL i (MAP level_run levels) = level_run (EL i levels)` by
       simp[EL_MAP] >>
     qpat_assum `EL i (MAP level_run levels) = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `!i s. i < LENGTH levels /\ P i s ==> _`
       (qspecl_then [`i`,`s`] mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     simp[NoAsms]) >>
  qpat_assum `FOLDL _ _ (MAP level_run levels) = r` (fn th => rewrite_tac[th]) >>
  Cases_on `levels` >- gvs[] >>
  Cases_on `r` >> gvs[EL,HD]
QED

Resume request_cut_packet_root_keys[result]:
  qpat_assum `SND (rooted_eval fuel C7 levels entry) = r` (SUBST1_TAC o SYM) >>
  simp[NoAsms,FOLDL_MAP] >>
  qpat_x_assum `SND (rooted_eval fuel C7 levels entry) = r` (K all_tac) >>
  qpat_assum `SND (rooted_eval fuel C7 levels entry) = FOLDL _ _ _`
    (fn th => rewrite_tac[th]) >>
  `(\v row. case v of OK s => row_run row s | other => other) =
    (\v (bb,e,z). case v of
      OK s => (case eval_phis s bb.bb_instructions of
        OK sp => FOLDR (dft_exec_cons (fuel-e) C7) OK z
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      | other => other)
    | other => other)` by
    (once_rewrite_tac[FUN_EQ_THM] >> qx_gen_tac `row_result` >>
     once_rewrite_tac[FUN_EQ_THM] >> qx_gen_tac `row` >> PairCases_on `row` >>
     qpat_assum `row_run = _` (fn th => rewrite_tac[th]) >>
     Cases_on `row_result` >> simp[NoAsms]) >>
  qpat_assum `level_run = _` (fn th => rewrite_tac[th]) >> BETA_TAC >>
  qpat_assum `(\v row. case v of OK s => row_run row s | _ => _) = _`
    (fn th => pure_rewrite_tac[th]) >>
  AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  once_rewrite_tac[FUN_EQ_THM] >> qx_gen_tac `level_result` >>
  once_rewrite_tac[FUN_EQ_THM] >> qx_gen_tac `level` >> PairCases_on `level` >>
  Cases_on `level_result` >> simp[NoAsms]
QED

Finalise request_cut_packet_root_keys
