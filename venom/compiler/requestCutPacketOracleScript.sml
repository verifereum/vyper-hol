Theory requestCutPacketOracle
Ancestors
  requestCutKeyedPrefix requestCutDftPrefixReach
  dftFinitePacket dftGasFromListTraceDefs
  dftGasOracleDefs venomState list finite_map alist

(* A stopped C7 native trace and every retained C8 visit can use the
   same oracle from the full selected mask. *)
Theorem request_cut_packet_mask_observations:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  keys = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) ==>
  ALL_DISTINCT keys /\ ALL_DISTINCT (MAP FST obs) /\
  LENGTH keys = LENGTH raw_slots /\ raw_slots = MAP (ALOOKUP obs) keys
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o SIMP_RULE bool_ss [dft_focus_packet_rel_def,LET_THM]) >>
  qpat_x_assum `(j,obs) = _`
    (strip_assume_tac o SIMP_RULE bool_ss [pairTheory.PAIR_EQ]) >>
  qpat_assum `obs = trace_gas _` (fn obs_eq =>
    qpat_assum `keys = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e)))) _)` (fn keys_eq =>
      qpat_assum `raw_slots = FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab ([],e)))) _)` (fn slots_eq =>
        let
          val project = PURE_REWRITE_RULE [GSYM keys_eq, GSYM slots_eq, GSYM obs_eq]
        in
          qpat_assum `ALL_DISTINCT (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e)))) _))`
            (assume_tac o project) >>
          qpat_assum `ALL_DISTINCT (MAP FST (trace_gas _))`
            (assume_tac o project) >>
          qpat_assum `LENGTH (FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab ([],e)))) _)) =
            LENGTH (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e)))) _))`
            (assume_tac o SYM o project) >>
          qpat_assum `PERM (MAP _ (FILTER _ (ZIP (FLAT _, FLAT _)))) (trace_gas _)`
            (assume_tac o project)
        end))) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  drule_all request_cut_mask_matches_observations >>
  DISCH_THEN ACCEPT_TAC
QED

Theorem request_cut_packet_mask_prefix_agree:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  keys = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
  n <= LENGTH keys /\ trace_gas tr = ZIP (TAKE n keys,TAKE n raw) ==>
  trace_agrees (\key. case ALOOKUP (obs ++ ZIP (keys,raw)) key of
                          NONE => 0w | SOME w => w) tr
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all request_cut_packet_mask_observations >> strip_tac >>
  `LENGTH keys = LENGTH raw` by metis_tac[LIST_REL_LENGTH] >>
  mp_tac (Q.INST [`src` |-> `tr`, `tgt` |-> `[]`, `vals` |-> `raw`]
    request_cut_trace_selected_oracle) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     FIRST [qpat_assum `raw_slots = MAP _ keys` (fn th => rewrite_tac[GSYM th]) >>
            first_assum ACCEPT_TAC,
            simp[trace_gas_def]]) >>
  simp[]
QED

Theorem request_cut_packet_native_oracle:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  keys = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
  tr = trace_blocks [] 0 fuel C7 root_sf (root_entry with vs_gas_readings := raw ++ tail) /\
  keys = MAP FST (trace_gas tr) ++ extra ==>
  trace_agrees (\key. case ALOOKUP (obs ++ ZIP (keys,raw)) key of
                          NONE => 0w | SOME w => w) tr
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all request_cut_packet_mask_observations >> strip_tac >>
  `LENGTH raw = LENGTH keys` by metis_tac[LIST_REL_LENGTH] >>
  `?l. l <= LENGTH keys /\ trace_gas tr = ZIP (TAKE l keys,TAKE l raw)` by
    (mp_tac (Q.INST [`s` |-> `root_entry with vs_gas_readings := raw ++ tail`,
       `root` |-> `root_entry`,`gs` |-> `raw`,`hist` |-> `trace_gas tr`,
       `p` |-> `[]:(num # num) list`,`d` |-> `0`,`C` |-> `C7`,`fn` |-> `root_sf`,
       `rest` |-> `extra`] request_cut_native_keyed_prefix_zip) >>
     impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
        qpat_assum `tr = _` (fn th => simp[NoAsms,th])) >>
     DISCH_THEN ACCEPT_TAC) >>
  drule_all request_cut_packet_mask_prefix_agree >>
  disch_then ACCEPT_TAC
QED

Theorem request_cut_packet_observed_visit:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  C8.ctx_entry = SOME nm /\
  lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_tf = SOME lbl /\
  root_entry = (v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
  keys = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) /\
  tr = dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry /\
  h <= j /\ h < LENGTH tr /\ EL h tr = ((a,e,id),fn,inst,s) ==>
  ev_reachable (\key. case ALOOKUP (obs ++ ZIP (keys,raw)) key of
                          NONE => 0w | SOME w => w)
    v C8 a e fn inst (s with vs_gas_readings := v.vs_gas_readings)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all request_cut_packet_mask_observations >> strip_tac >>
  `tr = trace_context N C8 v` by simp[trace_context_def, trace_function_def] >>
  `obs = trace_gas (TAKE j tr)` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o SIMP_RULE bool_ss [dft_focus_packet_rel_def,LET_THM]) >>
     qpat_x_assum `(j,obs) = _`
       (strip_assume_tac o SIMP_RULE bool_ss [pairTheory.PAIR_EQ]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`j = _`, `obs = trace_gas _`, `tr = trace_blocks [] 0 N C8 root_tf root_entry`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  drule_all trace_context_observed_visit >>
  disch_then (qspec_then `ZIP (keys,raw)` ACCEPT_TAC)
QED
