Theory requestCutDftPacketVisit
Ancestors
  requestCutDftPrefixReach dftFinitePacket dftGasFromListTraceDefs
  jointRequestCut venomExecSemantics venomState list rich_list finite_map sorting alist
  requestCutPacketOracle

(* A successful rooted C7 cut and an indexed C8 visit from the stopped
   packet are both reachable on the same event oracle. *)
Theorem request_cut_packet_visit_pair:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  C7.ctx_entry = SOME nm /\ C8.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME root_sf /\
  lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl /\ fn_entry_label root_tf = SOME lbl /\
  root_entry = (v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
  FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) = Kcut ++ kr /\
  LENGTH Kcut = LENGTH gs /\ raw = gs ++ gr /\
  trace_blocks [] 0 fuel7 C7 root_sf (root_entry with vs_gas_readings := raw ++ [0w]) =
    pre7 ++ ((p7,d7,id7),fn7,i7,s7)::after7 /\
  trace_gas pre7 = ZIP (Kcut,gs) /\
  trace8 = trace_blocks [] 0 N C8 root_tf root_entry /\
  h <= j /\ h < LENGTH trace8 /\
  EL h trace8 = ((p8,d8,id8),fn8,i8,s8) ==>
  ev_reachable
    (\key. case ALOOKUP (obs ++ ZIP (Kcut ++ kr,raw)) key of NONE => 0w | SOME w => w) v C7 p7 d7 fn7 i7 (s7 with vs_gas_readings := v.vs_gas_readings) /\
  ev_reachable
    (\key. case ALOOKUP (obs ++ ZIP (Kcut ++ kr,raw)) key of NONE => 0w | SOME w => w) v C8 p8 d8 fn8 i8 (s8 with vs_gas_readings := v.vs_gas_readings)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `trace_context fuel7 C7 (v with vs_gas_readings := raw ++ [0w]) =
    trace_blocks [] 0 fuel7 C7 root_sf (root_entry with vs_gas_readings := raw ++ [0w])` by
    (qpat_x_assum `trace_blocks [] 0 fuel7 _ _ _ = _` kall_tac >>
     simp[trace_context_def, trace_function_def] >>
     AP_TERM_TAC >> simp[venom_state_component_equality]) >>
  `trace_context fuel7 C7 (v with vs_gas_readings := raw ++ [0w]) =
    pre7 ++ ((p7,d7,id7),fn7,i7,s7)::after7` by
    (qpat_assum `trace_context fuel7 _ _ = trace_blocks _ _ _ _ _ _` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `LENGTH Kcut <= LENGTH (Kcut ++ kr)` by (rewrite_tac[LENGTH_APPEND] >> decide_tac) >>
  `TAKE (LENGTH Kcut) raw = gs` by
    (qpat_assum `raw = gs ++ gr` SUBST1_TAC >>
     qpat_assum `LENGTH Kcut = LENGTH gs` SUBST1_TAC >>
     simp[TAKE_LENGTH_APPEND]) >>
  `trace_gas pre7 = ZIP (TAKE (LENGTH Kcut) (Kcut ++ kr),TAKE (LENGTH Kcut) raw)` by
    (qpat_assum `TAKE (LENGTH Kcut) raw = gs` SUBST1_TAC >>
     rewrite_tac[TAKE_LENGTH_APPEND] >> first_assum ACCEPT_TAC) >>
  `trace_agrees
    (\key. case ALOOKUP (obs ++ ZIP (Kcut ++ kr,raw)) key of NONE => 0w | SOME w => w)
    pre7` by
    (mp_tac (Q.INST [`keys` |-> `Kcut ++ kr`, `tr` |-> `pre7`,
       `n` |-> `LENGTH (Kcut : ((num # num) list # num # num) list)`]
       request_cut_packet_mask_prefix_agree) >>
     (impl_tac >- (rpt conj_tac >>
        (first_assum ACCEPT_TAC ORELSE (sym_tac >> first_assum ACCEPT_TAC)))) >>
     disch_then ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `trace_context fuel7 C7 _ = pre7 ++ _` (fn trace =>
        qpat_assum `trace_agrees _ pre7` (fn agree =>
          mp_tac (Q.SPEC `v.vs_gas_readings`
            (MATCH_MP (GEN_ALL trace_context_prefix_visit) (CONJ trace agree))))) >>
      simp[]) >>
  mp_tac (Q.INST [`keys` |-> `Kcut ++ kr`, `tr` |-> `trace8`,
    `a` |-> `p8`, `e` |-> `d8`, `id` |-> `id8`,
    `fn` |-> `fn8`, `inst` |-> `i8`, `s` |-> `s8`]
    request_cut_packet_observed_visit) >>
  impl_tac
  >- (rpt conj_tac >>
      (first_assum ACCEPT_TAC ORELSE (sym_tac >> first_assum ACCEPT_TAC))) >>
  disch_then ACCEPT_TAC
QED

(* Once the stopped walk crosses k, it contains every C8 native
   visit at the request cut. Their event oracle is fixed by the mask. *)
Theorem request_cut_observed_cover:
  EVERY wf_function C8.ctx_functions /\
  joint_trace v C8 q0 evs qs
    (JointConfig stk PG G tn f inst end8 oms om hs hist) /\
  k < LENGTH end8.vs_requests /\
  tr = trace_context N C8 v /\
  LENGTH evs < LENGTH tr /\
  obs = trace_gas (TAKE (LENGTH evs) tr) /\
  ALL_DISTINCT (MAP FST obs) /\
  (!h. h < LENGTH evs ==>
    ?p d f i t stk PG G tn oms om hs hist.
      EL h tr = ((p,d,i.inst_id),f,i,t) /\
      EL h (q0::qs) = JointConfig stk PG G tn f i t oms om hs hist) ==>
  !fn i s. raw_reachable v C8 fn i s /\ LENGTH s.vs_requests <= k ==>
    ?p d. ev_reachable
      (\key. case ALOOKUP (obs ++ filling) key of NONE => 0w | SOME w => w)
      v C8 p d fn i (s with vs_gas_readings := v.vs_gas_readings)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt strip_tac >>
  drule_all raw_reachable_request_cut_visit >> strip_tac >>
  qpat_x_assum `!h. h < LENGTH evs ==> _` drule >> strip_tac >>
  `n <= LENGTH evs /\ n < LENGTH tr` by decide_tac >>
  `?p d. EL n tr = ((p,d,i.inst_id),fn,i,s)` by
    metis_tac[frameJointTransitionTheory.joint_config_11] >>
  drule_all trace_context_observed_visit >> metis_tac[]
QED
