Theory requestCutStoppedPlan
Ancestors
  requestCutClosedPlan dftGasOracleDefs venomExecSemantics venomState list arithmetic

(* Each active caller retains exactly the keys before its suspended call.
   If a nested activation stops, execution stays in that call chain. *)
Theorem request_cut_nested_plan_keys:
  !rows keyss entry P (run:num -> venom_state -> exec_result # gas_event list).
    LENGTH keyss = LENGTH rows /\ P 0 entry /\
    (!i s. i < LENGTH rows /\ P i s ==>
      case EL i rows s of
        OK t => P (SUC i) t /\
          (~(?u. FST (run (SUC i) t) = OK u) /\
           ~(?ir u. FST (run (SUC i) t) = IntRet ir u) ==>
           FST (run i s) = FST (run (SUC i) t) /\
           SND (run i s) = EL i keyss ++ SND (run (SUC i) t))
      | stopped => ~(?ir u. stopped = IntRet ir u) /\
          FST (run i s) = stopped /\
          ?extra. EL i keyss = SND (run i s) ++ extra) ==>
    case FOLDL (\r row. case r of OK s => row s | other => other) (OK entry) rows of
      OK u => T
    | stopped => ~(?ir u. stopped = IntRet ir u) /\
        FST (run 0 entry) = stopped /\ ?extra. FLAT keyss = SND (run 0 entry) ++ extra
Proof
  Induct >- simp_tac bool_ss [FOLDL,exec_result_case_def] >>
  simp_tac bool_ss [LENGTH,FOLDL,exec_result_case_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `LENGTH keyss = SUC (LENGTH rows)` >>
  namedCases_on `keyss` ["","ks rest"]
  >- (qpat_assum `LENGTH [] = SUC _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[LENGTH]) >>
  RULE_ASSUM_TAC (REWRITE_RULE [LENGTH, prim_recTheory.INV_SUC_EQ]) >>
  `case h entry of
      OK t => P 1 t /\
        (~(?u. FST (run' 1 t) = OK u) /\ ~(?ir u. FST (run' 1 t) = IntRet ir u) ==>
         FST (run' 0 entry) = FST (run' 1 t) /\
         SND (run' 0 entry) = ks ++ SND (run' 1 t))
    | stopped => ~(?ir u. stopped = IntRet ir u) /\
      FST (run' 0 entry) = stopped /\ ?extra. ks = SND (run' 0 entry) ++ extra` by
    (qpat_assum `!i s. i < SUC (LENGTH rows) /\ P i s ==> _`
      (qspecl_then [`0`,`entry`] mp_tac) >>
     impl_tac >- simp[] >>
     `EL 0 (h::rows) = h /\ EL 0 (ks::rest) = ks /\ SUC 0 = 1` by simp[] >>
     simp[NoAsms,EL]) >>
  Cases_on `h entry` >>
  RULE_ASSUM_TAC (REWRITE_RULE [exec_result_case_def,exec_result_distinct,exec_result_11])
  >- (qpat_x_assum `(\t. P 1 t /\ _) v` (strip_assume_tac o BETA_RULE) >>
      qpat_assum `!ks init Q run. _`
        (qspecl_then [`rest`,`v`,`\i. P (SUC i)`,`\i. run' (SUC i)`] mp_tac) >>
      BETA_TAC >> impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          TRY (simp[NoAsms, numeralTheory.numeral_suc] >>
            first_assum ACCEPT_TAC) >>
          rpt gen_tac >> strip_tac >>
          qpat_assum `!i s. i < SUC (LENGTH rows) /\ P i s ==> _`
            (qspecl_then [`SUC i`,`s`] mp_tac) >>
          impl_tac >- (simp_tac bool_ss [prim_recTheory.LESS_MONO_EQ] >> asm_rewrite_tac[]) >>
          `EL (SUC i) (h::rows) = EL i rows /\ EL (SUC i) (ks::rest) = EL i rest` by
            simp[EL] >>
          simp[NoAsms,EL]) >>
      BasicProvers.TOP_CASE_TAC >>
      simp_tac bool_ss [exec_result_case_def,exec_result_distinct,FLAT] >>
      `SUC 0 = 1` by simp[] >>
      qpat_assum `SUC 0 = 1` (fn th => simp_tac bool_ss [th]) >> rpt strip_tac >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`FST (run' 1 v) = _`,`FLAT rest = _`,
         `_ ==> FST (run' 0 entry) = _ /\ _`] >>
      POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[APPEND_ASSOC]) >>
  simp_tac (srw_ss()) [NoAsms,request_cut_fold_stopped] >>
  RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `_ /\ _` (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac `extra ++ FLAT rest` >> simp[APPEND_ASSOC]
QED
