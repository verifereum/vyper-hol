Theory requestCutClosedPlan
Ancestors
  dftGasOracleDefs venomExecSemantics venomState list arithmetic

Theorem request_cut_fold_stopped:
  !rows result. ~(?s. result = OK s) ==>
    FOLDL (\r row. case r of OK s => row s | other => other) result rows = result
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `result` >> simp[]
QED

(* A successful row records its full key list. A stopped row records a
   prefix and leaves all later rows unexecuted. *)
Theorem request_cut_plan_keys:
  !rows keyss entry P (run:num -> venom_state -> exec_result # gas_event list).
    LENGTH keyss = LENGTH rows /\ P 0 entry /\
    (!i s. i < LENGTH rows /\ P i s ==>
      case EL i rows s of
        OK t => P (SUC i) t /\ FST (run i s) = FST (run (SUC i) t) /\
          SND (run i s) = EL i keyss ++ SND (run (SUC i) t)
      | stopped => ~(?ir u. stopped = IntRet ir u) /\
          FST (run i s) = stopped /\
          ?extra. EL i keyss = SND (run i s) ++ extra) ==>
    case FOLDL (\result row. case result of OK s => row s | other => other)
      (OK entry) rows of
      OK u => P (LENGTH rows) u /\ FST (run 0 entry) = FST (run (LENGTH rows) u) /\
        SND (run 0 entry) = FLAT keyss ++ SND (run (LENGTH rows) u)
    | stopped => ~(?ir u. stopped = IntRet ir u) /\
        FST (run 0 entry) = stopped /\
        ?extra. FLAT keyss = SND (run 0 entry) ++ extra
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `LENGTH keyss = SUC (LENGTH rows)` >>
  namedCases_on `keyss` ["", "ks rest"] >> gvs[] >>
  `case h entry of
      OK t => P 1 t /\ FST (run' 0 entry) = FST (run' 1 t) /\
        SND (run' 0 entry) = ks ++ SND (run' 1 t)
    | stopped => ~(?ir u. stopped = IntRet ir u) /\
      FST (run' 0 entry) = stopped /\
        ?extra. ks = SND (run' 0 entry) ++ extra` by
    (qpat_assum `!i s. i < SUC (LENGTH rows) /\ P i s ==> _`
       (qspecl_then [`0`,`entry`] mp_tac) >>
     impl_tac >- simp[] >>
     `EL 0 (h::rows) = h /\ EL 0 (ks::rest) = ks /\ SUC 0 = 1` by simp[] >>
     simp[NoAsms,EL]) >>
  Cases_on `h entry` >> fs[]
  >- (qpat_assum `!ks init Q run. _`
        (qspecl_then [`rest`,`v`,`\i. P (SUC i)`,`\i. run' (SUC i)`] mp_tac) >>
      simp[] >> impl_tac
      >- (rpt gen_tac >> strip_tac >>
          qpat_assum `!i s. i < SUC (LENGTH rows) /\ P i s ==> _`
            (qspecl_then [`SUC i`,`s`] mp_tac) >>
          impl_tac >- gvs[] >>
          `EL (SUC i) (h::rows) = EL i rows /\ EL (SUC i) (ks::rest) = EL i rest` by
            simp[EL] >>
          simp[NoAsms,EL]) >>
      BasicProvers.TOP_CASE_TAC >> simp[APPEND_ASSOC] >>
      metis_tac[APPEND_ASSOC]) >>
  simp[request_cut_fold_stopped] >> metis_tac[APPEND_ASSOC]
QED
