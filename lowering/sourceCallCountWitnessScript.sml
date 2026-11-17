(* Finite causal witnesses for the shared source outcome horizon. *)
Theory sourceCallCountWitness
Ancestors sourceCallCount sourceCallCountEntryReplay
  vyperState[qualified,ignore_grammar] vyperStorageTrace vyperEvalOutcomeSuffix
  list option pair
Libs BasicProvers

val _ = Parse.hide "run";

Theorem entry_run_unused_append[local]:
  !run.
    (!xs r t.
       run xs = SOME (r,t) ==>
       ?used rest. xs = used ++ rest /\ t.outcomes = SOME rest) /\
    (!prefix next tail tail' r t.
       run (prefix ++ next::tail) = SOME (r,t) /\
       t.outcomes = SOME (next::tail) ==>
       run (prefix ++ tail') = SOME (r,t with outcomes := SOME tail')) ==>
    !os marker res st res_m st_m.
      run os = SOME (res,st) /\ st.outcomes = SOME [] /\
      run (os ++ [marker]) = SOME (res_m,st_m) /\
      st_m.outcomes <> SOME [] ==>
      res_m = res /\ st_m = st with outcomes := SOME [marker]
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!xs r t. _`
    (qspecl_then [`os ++ [marker]`,`res_m`,`st_m`] mp_tac) >>
  simp[] >> disch_then
    (qx_choose_then `used` (qx_choose_then `rest` strip_assume_tac)) >>
  `?pfx. os = used ++ pfx /\ rest = pfx ++ [marker]` by
    (qpat_x_assum `os ++ [marker] = used ++ rest`
       (strip_assume_tac o ONCE_REWRITE_RULE [APPEND_EQ_APPEND]) >>
     gvs[APPEND_EQ_SING] >> metis_tac[APPEND_NIL]) >>
  gvs[] >> Cases_on `pfx`
  >- (qpat_x_assum `!prefix next tail tail' r t. _`
        (qspecl_then [`used`,`marker`,`[]`,`[]`,`res_m`,`st_m`] mp_tac) >>
      gvs[vyperStateTheory.evaluation_state_component_equality]) >>
  qpat_x_assum `!prefix next tail tail' r t. _`
    (qspecl_then [`used`,`h`,`t ++ [marker]`,`h::t`,`res_m`,`st_m`] mp_tac) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  PURE_REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  simp[] >> rpt strip_tac >> gvs[]
QED
(* A terminal unused marker is replaced by empty_failed_outcome. Each
   consumed marker follows exactly the existing counter's selector, so
   projected replay transports one exhausted source run to the next.
   The final unused sentinel is excluded from the interior certificates. *)
Theorem entry_run_exhausted_witness[local]:
  !run.
    (!xs. IS_SOME (run xs)) /\
    (!xs r t.
       run xs = SOME (r,t) ==>
       ?used rest. xs = used ++ rest /\ t.outcomes = SOME rest) /\
    (!prefix next tail tail' r t.
       run (prefix ++ next::tail) = SOME (r,t) /\
       t.outcomes = SOME (next::tail) ==>
       run (prefix ++ tail') = SOME (r,t with outcomes := SOME tail')) /\
    (!os res_p st_p.
       run (os ++ [probe_failed_outcome]) = SOME (res_p,st_p) /\
       st_p.outcomes = SOME [] ==>
       OPTION_MAP (\(r,s). (r,erase_storage_trace s)) (run os) =
       OPTION_MAP (\(r,s). (r,erase_storage_trace s))
         (run (os ++ [case run (os ++ [empty_failed_outcome]) of
            SOME (res_e,_) =>
              if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
                 res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
                 ~NULL st_p.requests
              then failed_outcome (LAST st_p.requests)
              else empty_failed_outcome
          | NONE => empty_failed_outcome]))) ==>
    !k os res st.
      entry_calls_within_from k os run /\
      run os = SOME (res,st) /\ st.outcomes = SOME [] ==>
      ?extra st_out.
        extra <> [] /\ LENGTH extra <= k /\
        run (os ++ extra) = SOME (res,st_out) /\
        erase_storage_trace st_out =
          erase_storage_trace (st with outcomes := SOME [empty_failed_outcome]) /\
        st_out.outcomes = SOME [empty_failed_outcome] /\
        (!pfx o_next sfx.
           extra = pfx ++ o_next::sfx /\ sfx <> [] ==>
           ?res_p st_p st_prefix.
             run (os ++ pfx) = SOME (res,st_prefix) /\
             erase_storage_trace st_prefix = erase_storage_trace st /\
             (pfx = [] ==> st_prefix = st) /\
             run (os ++ pfx ++ [probe_failed_outcome]) = SOME (res_p,st_p) /\
             st_p.outcomes = SOME [] /\
             o_next =
               (case run (os ++ pfx ++ [empty_failed_outcome]) of
                  SOME (res_e,_) =>
                    if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
                       res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
                       ~NULL st_p.requests
                    then failed_outcome (LAST st_p.requests)
                    else empty_failed_outcome
                | NONE => empty_failed_outcome))

Proof
  gen_tac >> strip_tac >> Induct_on `k`
  >- simp[entry_calls_within_from_def] >>
  rpt gen_tac >> strip_tac >>
  `?res_p st_p. run (os ++ [probe_failed_outcome]) = SOME (res_p,st_p)` by
    (qpat_x_assum `!xs. IS_SOME (run xs)`
       (qspec_then `os ++ [probe_failed_outcome]` mp_tac) >>
     Cases_on `run (os ++ [probe_failed_outcome])` >> simp[] >>
     PairCases_on `x` >> simp[]) >>
  Cases_on `st_p.outcomes = SOME []`
  >- suspend "consumed" >>
  `res_p = res /\ st_p = st with outcomes := SOME [probe_failed_outcome]` by
    (irule entry_run_unused_append >> simp[] >>
     qexistsl [`os`,`run`] >> simp[]) >>
  gvs[] >>
  qpat_x_assum `!prefix next tail tail' r t. _`
    (qspecl_then [`os`,`probe_failed_outcome`,`[]`,
                  `[empty_failed_outcome]`,`res`,
                  `st with outcomes := SOME [probe_failed_outcome]`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`[empty_failed_outcome]`,
            `st with outcomes := SOME [empty_failed_outcome]`] >>
  simp[] >> rpt strip_tac >>
  Cases_on `pfx` >> gvs[] >> Cases_on `sfx` >> gvs[]
QED

Resume entry_run_exhausted_witness[consumed]:
  fs[entry_calls_within_from_def] >>
  qmatch_asmsub_abbrev_tac `entry_calls_within_from k (os ++ [selected]) run` >>
  `?r_n st_n. run (os ++ [selected]) = SOME (r_n,st_n)` by
    (qpat_x_assum `!xs. IS_SOME (run xs)`
       (qspec_then `os ++ [selected]` mp_tac) >>
     Cases_on `run (os ++ [selected])` >> simp[] >>
     PairCases_on `x` >> simp[]) >>
  qpat_x_assum `!os res_p st_p. _ ==> OPTION_MAP _ _ = _`
    (qspecl_then [`os`,`res_p`,`st_p`] mp_tac) >>
  simp[GSYM markerTheory.Abbrev_def] >>
  strip_tac >> gvs[] >>
  `st_n.outcomes = SOME []` by
    (qpat_x_assum `erase_storage_trace st = erase_storage_trace st_n` mp_tac >>
     simp[vyperStateTheory.erase_storage_trace_def,
          vyperStateTheory.evaluation_state_component_equality]) >>
  `erase_storage_trace (st_n with outcomes := SOME [empty_failed_outcome]) =
   erase_storage_trace (st with outcomes := SOME [empty_failed_outcome])` by
    (qpat_x_assum `erase_storage_trace st = erase_storage_trace st_n` mp_tac >>
     simp[vyperStateTheory.erase_storage_trace_def,
          vyperStateTheory.evaluation_state_component_equality]) >>
  qpat_x_assum `!os res st. entry_calls_within_from k os run /\ _ ==> _`
    (qspecl_then [`os ++ [selected]`,`r_n`,`st_n`] mp_tac) >>
  simp[] >> disch_then
    (qx_choose_then `extra_tail` (qx_choose_then `st_out` strip_assume_tac)) >>
  qexistsl [`selected::extra_tail`,`st_out`] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `pfx`
  >- (gvs[] >> qexistsl [`res_p`,`st_p`,`st`] >> simp[Abbr `selected`]) >>
  gvs[] >>
  qpat_x_assum `!pfx o_next sfx. _`
    (qspecl_then [`t`,`o_next`,`sfx`] mp_tac) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> simp[] >>
  disch_then (qx_choose_then `rp` (qx_choose_then `sp`
    (qx_choose_then `prefix_state` strip_assume_tac))) >>
  qexistsl [`rp`,`sp`,`prefix_state`] >> simp[]
QED

Finalise entry_run_exhausted_witness[local]

Theorem fn_entry_run_calls_within_witness:
  !n os gobs am cx nr mut mods args dflts vals fbody res st.
    entry_calls_within n os
      (\xs. fn_entry_run xs gobs am cx nr mut mods args dflts vals fbody) /\
    fn_entry_run os gobs am cx nr mut mods args dflts vals fbody =
      SOME (res,st) ==>
    ?os' extra rest st_out.
      os' = TAKE n os ++ extra /\ LENGTH os' <= n /\ rest <> [] /\
      fn_entry_run os' gobs am cx nr mut mods args dflts vals fbody =
        SOME (res,st_out) /\
      erase_storage_trace st_out =
        erase_storage_trace (st with outcomes := SOME rest) /\
      (extra = [] ==> st_out = st with outcomes := SOME rest) /\
      st.outcomes = SOME (DROP (LENGTH os' - LENGTH rest) os) /\
      (extra <> [] ==> st.outcomes = SOME [] /\ rest = [empty_failed_outcome]) /\
      (!pfx o_next sfx.
         extra = pfx ++ o_next :: sfx /\ sfx <> [] ==>
         ?res_p st_p st_prefix.
           fn_entry_run (TAKE n os ++ pfx) gobs am cx nr mut mods
             args dflts vals fbody = SOME (res,st_prefix) /\
           erase_storage_trace st_prefix = erase_storage_trace st /\
           (pfx = [] ==> st_prefix = st) /\
           fn_entry_run (TAKE n os ++ pfx ++ [probe_failed_outcome]) gobs am cx
             nr mut mods args dflts vals fbody = SOME (res_p,st_p) /\
           st_p.outcomes = SOME [] /\
           o_next =
             (case fn_entry_run (TAKE n os ++ pfx ++ [empty_failed_outcome])
                     gobs am cx nr mut mods args dflts vals fbody of
                SOME (res_e,_) =>
                  if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
                     res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
                     ~NULL st_p.requests
                  then failed_outcome (LAST st_p.requests)
                  else empty_failed_outcome
              | NONE => empty_failed_outcome))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `n <= LENGTH os`
  >- suspend "real_prefix" >>
  `TAKE n os = os` by (irule TAKE_LENGTH_TOO_LONG >> decide_tac) >>
  Cases_on `st.outcomes = SOME []`
  >- suspend "exhausted" >>
  drule_all fn_entry_run_outcomes_suffix >>
  simp[outcome_suffix_def] >>
  disch_then (qx_choose_then `used` (qx_choose_then `rest` strip_assume_tac)) >>
  `rest <> []` by metis_tac[] >>
  `st with outcomes := SOME rest = st` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `DROP (LENGTH os - LENGTH rest) os = rest` by
    (qpat_x_assum `os = used ++ rest` SUBST1_TAC >> simp[DROP_APPEND]) >>
  `LENGTH os <= n` by decide_tac >>
  qexists_tac `rest` >> simp[]
QED

Resume fn_entry_run_calls_within_witness[exhausted]:
  qspec_then `\xs. fn_entry_run xs gobs am cx nr mut mods args dflts vals fbody`
    mp_tac entry_run_exhausted_witness >> BETA_TAC >> impl_tac
  >- (conj_tac
      >- (gen_tac >>
          `IS_SOME (fn_entry_run xs gobs am cx nr mut mods args dflts vals fbody) =
           IS_SOME (fn_entry_run os gobs am cx nr mut mods args dflts vals fbody)` by
            MATCH_ACCEPT_TAC fn_entry_run_selection_invariant >> simp[]) >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          drule_all fn_entry_run_outcomes_suffix >> simp[outcome_suffix_def]) >>
      conj_tac
      >- MATCH_ACCEPT_TAC fn_entry_run_outcome_prefix >>
      MATCH_ACCEPT_TAC fn_entry_run_probe_replay) >>
  disch_then (qspecl_then [`n - LENGTH os`,`os`,`res`,`st`] mp_tac) >>
  impl_tac >- fs[entry_calls_within_def, TAKE_LENGTH_TOO_LONG] >>
  disch_then (qx_choose_then `extra` (qx_choose_then `st_out` strip_assume_tac)) >>
  `LENGTH os + LENGTH extra <= n` by decide_tac >>
  `LENGTH os <= LENGTH (os ++ extra) - 1` by
    (Cases_on `extra` >> gvs[]) >>
  qexistsl [`os ++ extra`,`extra`,`[empty_failed_outcome]`,`st_out`] >>
  simp[DROP_LENGTH_TOO_LONG] >> fs[LENGTH_APPEND] >> decide_tac
QED

Resume fn_entry_run_calls_within_witness[real_prefix]:
  drule_all fn_entry_run_truncate >>
  disch_then (qx_choose_then `rest` strip_assume_tac) >>
  `outcome_suffix (SOME (TAKE n os)) (SOME rest)` by
    (qpat_x_assum `fn_entry_run (TAKE n os) _ _ _ _ _ _ _ _ _ _ = _`
       (mp_tac o MATCH_MP fn_entry_run_outcomes_suffix) >> simp[]) >>
  fs[outcome_suffix_def] >>
  rename1 `TAKE n os = used ++ rest` >>
  `LENGTH used = n - LENGTH rest` by
    (qpat_x_assum `TAKE n os = used ++ rest` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> rw[] >> decide_tac) >>
  `os = used ++ (rest ++ DROP n os)` by metis_tac[TAKE_DROP, APPEND_ASSOC] >>
  `DROP (n - LENGTH rest) os = rest ++ DROP n os` by
    (qpat_x_assum `os = used ++ _`
       (mp_tac o Q.AP_TERM `DROP (LENGTH used)`) >> simp[DROP_APPEND] >>
     `n - LENGTH rest - (n - LENGTH rest + LENGTH rest) = 0` by decide_tac >>
     simp[]) >>
  qexists_tac `rest` >> fs[]
QED

Finalise fn_entry_run_calls_within_witness

Theorem source_calls_within_witness:
  !n am tx os gobs res st.
    source_calls_within n am tx os gobs /\
    call_entry_run os gobs am tx = SOME (res,st) ==>
    ?os' extra rest st_out.
      os' = TAKE n os ++ extra /\ LENGTH os' <= n /\ rest <> [] /\
      call_entry_run os' gobs am tx =
        SOME (res,st_out) /\
      erase_storage_trace st_out =
        erase_storage_trace (st with outcomes := SOME rest) /\
      (extra = [] ==> st_out = st with outcomes := SOME rest) /\
      st.outcomes = SOME (DROP (LENGTH os' - LENGTH rest) os) /\
      (extra <> [] ==> st.outcomes = SOME [] /\ rest = [empty_failed_outcome]) /\
      (!pfx o_next sfx.
         extra = pfx ++ o_next :: sfx /\ sfx <> [] ==>
         ?res_p st_p st_prefix.
           call_entry_run (TAKE n os ++ pfx) gobs am tx = SOME (res,st_prefix) /\
           erase_storage_trace st_prefix = erase_storage_trace st /\
           (pfx = [] ==> st_prefix = st) /\
           call_entry_run (TAKE n os ++ pfx ++ [probe_failed_outcome])
             gobs am tx = SOME (res_p,st_p) /\
           st_p.outcomes = SOME [] /\
           o_next =
             (case call_entry_run (TAKE n os ++ pfx ++ [empty_failed_outcome])
                     gobs am tx of
                SOME (res_e,_) =>
                  if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
                     res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
                     ~NULL st_p.requests
                  then failed_outcome (LAST st_p.requests)
                  else empty_failed_outcome
              | NONE => empty_failed_outcome))
Proof
  rpt gen_tac >>
  simp_tac bool_ss [source_calls_within_def, call_entry_run_def, LET_THM] >>
  rpt TOP_CASE_TAC >> simp[] >>
  strip_tac >> drule_all fn_entry_run_calls_within_witness >> simp[]
QED

Theorem deploy_source_calls_within_witness:
  !n tops am tx os gobs res st.
    deploy_source_calls_within n tops am tx os gobs /\
    deploy_entry_run os gobs tops am tx = SOME (res,st) ==>
    ?os' extra rest st_out.
      os' = TAKE n os ++ extra /\ LENGTH os' <= n /\ rest <> [] /\
      deploy_entry_run os' gobs tops am tx =
        SOME (res,st_out) /\
      erase_storage_trace st_out =
        erase_storage_trace (st with outcomes := SOME rest) /\
      (extra = [] ==> st_out = st with outcomes := SOME rest) /\
      st.outcomes = SOME (DROP (LENGTH os' - LENGTH rest) os) /\
      (extra <> [] ==> st.outcomes = SOME [] /\ rest = [empty_failed_outcome]) /\
      (!pfx o_next sfx.
         extra = pfx ++ o_next :: sfx /\ sfx <> [] ==>
         ?res_p st_p st_prefix.
           deploy_entry_run (TAKE n os ++ pfx) gobs tops am tx = SOME (res,st_prefix) /\
           erase_storage_trace st_prefix = erase_storage_trace st /\
           (pfx = [] ==> st_prefix = st) /\
           deploy_entry_run (TAKE n os ++ pfx ++ [probe_failed_outcome])
             gobs tops am tx = SOME (res_p,st_p) /\
           st_p.outcomes = SOME [] /\
           o_next =
             (case deploy_entry_run (TAKE n os ++ pfx ++ [empty_failed_outcome])
                     gobs tops am tx of
                SOME (res_e,_) =>
                  if res_p = INR (Error (RuntimeError "create outcome accounts")) /\
                     res_e <> INR (Error (RuntimeError "create outcome accounts")) /\
                     ~NULL st_p.requests
                  then failed_outcome (LAST st_p.requests)
                  else empty_failed_outcome
              | NONE => empty_failed_outcome))
Proof
  rpt gen_tac >>
  simp_tac bool_ss [deploy_source_calls_within_def, deploy_entry_run_def, LET_THM] >>
  rpt TOP_CASE_TAC >> simp[] >>
  strip_tac >> drule_all fn_entry_run_calls_within_witness >> simp[]
QED
