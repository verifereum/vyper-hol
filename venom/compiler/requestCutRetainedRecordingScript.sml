Theory requestCutRetainedRecording
Ancestors
  requestCutDftExternal requestCutNativeEventCover requestCutDftPacketVisit
  requestCutPacketOracle requestCutEventCoverUpto jointRequestCut
  dftGasFromListTraceDefs dftGasOracleDefs dftRunRel contextCodegenRel
  dftContractGas dftWf dftFinitePacket venomExecSemantics venomState venomInst
  unitShapeDefs list rich_list finite_map alist arithmetic

(* The rooted C7 cut provides the native state. The request field proof
   can use its event witness because both visits have the same key. *)
Theorem request_cut_dft_retained_recording_exact:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  C8.ctx_entry = C7.ctx_entry /\ o1_ctx_shape C7 /\
  ctx_labels_bound C7 initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn)) C7.ctx_functions /\
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  v7 = (initial with vs_gas_readings := filling) /\
  dftGasFromListTraceDefs$trace_context fuel7 C7 v7 = pre ++ ((p,d,inst.inst_id),fn7,inst,s)::post7 /\
  ev_reachable orc initial C7 p d fn7 inst (s with vs_gas_readings := initial.vs_gas_readings) /\
  ev_reachable orc initial C8 p d fn8 inst (t with vs_gas_readings := initial.vs_gas_readings) /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C8 inst t = OK post8 /\
  LENGTH t.vs_requests = k /\ k < LENGTH post8.vs_requests ==>
  raw_reachable v7 C7 fn7 inst s /\
  ?u. step_inst 0 C7 inst s = OK u /\
    s.vs_requests = t.vs_requests /\ s.vs_outcomes = t.vs_outcomes /\
    u.vs_requests = post8.vs_requests /\ u.vs_outcomes = post8.vs_outcomes
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY wf_function C7.ctx_functions /\
   EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
     f.fn_blocks) C7.ctx_functions` by
    (drule o1_ctx_shape_wf_functions >> simp[] >>
     rewrite_tac[EVERY_MEM] >> metis_tac[wf_fn_block_inst_ids_distinct]) >>
  conj_tac >- (irule request_cut_native_trace_reachable >> metis_tac[]) >>
  `LENGTH t.vs_requests < LENGTH post8.vs_requests` by decide_tac >>
  `inst.inst_opcode <> GAS` by
    (drule_all step_inst_request_outcomes >> Cases_on `inst.inst_opcode` >> simp[]) >>
  `step_inst fuel C8 inst (t with vs_gas_readings := initial.vs_gas_readings) =
     OK (post8 with vs_gas_readings := initial.vs_gas_readings)` by
    metis_tac[request_cut_recording_restore] >>
  `LENGTH (t with vs_gas_readings := initial.vs_gas_readings).vs_requests <
     LENGTH (post8 with vs_gas_readings := initial.vs_gas_readings).vs_requests` by simp[] >>
  drule_all request_cut_dft_recording >> simp[] >> strip_tac >>
  rename1 `ev_reachable orc initial C7 p d f inst x` >>
  `x = (s with vs_gas_readings := initial.vs_gas_readings)` by
    metis_tac[request_cut_event_visit_unique] >>
  qexists_tac `u with vs_gas_readings := s.vs_gas_readings` >>
  gvs[] >>
  mp_tac (Q.INST [`C` |-> `C7`, `C'` |-> `C7`, `fuel` |-> `0`, `fuel'` |-> `0`,
    `s` |-> `s with vs_gas_readings := initial.vs_gas_readings`,
    `gs` |-> `s.vs_gas_readings`] request_cut_recording_restore) >>
  simp[venom_state_component_equality]
QED

(* The historical row and crossing identify one common visit on the mask. *)
Theorem request_cut_packet_retained_recording:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (stopped,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  C7.ctx_entry = SOME nm /\ C8.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME root_sf /\
  lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl /\ fn_entry_label root_tf = SOME lbl /\
  root_entry = (initial with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
  FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) = Kcut ++ kr /\
  LENGTH Kcut = LENGTH gs /\ raw = gs ++ gr /\
  trace_blocks [] 0 fuel7 C7 root_sf (root_entry with vs_gas_readings := raw ++ [0w]) =
    pre ++ ((a,e,inst.inst_id),fn7,inst,s)::post7 /\
  trace_gas pre = ZIP (Kcut,gs) /\
  trace8 = trace_blocks [] 0 N C8 root_tf root_entry /\
  h < stopped /\ h < LENGTH trace8 /\
  EL h trace8 = ((a,e,inst.inst_id),fn8,inst,t) /\
  LIST_REL (\fn fn'. fn' = dft_fn fn) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\ o1_ctx_shape C7 /\
  ctx_labels_bound C7 initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn)) C7.ctx_functions /\
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  v7 = (initial with vs_gas_readings := raw ++ [0w]) /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C8 inst t = OK post8 /\
  LENGTH t.vs_requests = k /\ k < LENGTH post8.vs_requests ==>
  raw_reachable v7 C7 fn7 inst s /\
  (?u. step_inst 0 C7 inst s = OK u /\
    s.vs_requests = t.vs_requests /\ s.vs_outcomes = t.vs_outcomes /\
    u.vs_requests = post8.vs_requests /\ u.vs_outcomes = post8.vs_outcomes) /\
  (!p d fn i t. ev_reachable
     (\key. case ALOOKUP (obs ++ ZIP (Kcut ++ kr,raw)) key of NONE => 0w | SOME w => w)
     initial C7 p d fn i t /\ LENGTH t.vs_requests <= k ==>
    ?ws. raw_reachable v7 C7 fn i (t with vs_gas_readings := ws))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `h <= stopped` by decide_tac >>
  mp_tac (Q.INST [`j` |-> `stopped`, `v` |-> `initial`,
    `p7` |-> `a`, `d7` |-> `e`, `id7` |-> `inst.inst_id`, `i7` |-> `inst`,
    `s7` |-> `s`, `pre7` |-> `pre`, `after7` |-> `post7`,
    `p8` |-> `a`, `d8` |-> `e`, `id8` |-> `inst.inst_id`, `i8` |-> `inst`,
    `s8` |-> `t`] request_cut_packet_visit_pair) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `dftGasFromListTraceDefs$trace_context fuel7 C7 v7 =
    trace_blocks [] 0 fuel7 C7 root_sf (root_entry with vs_gas_readings := raw ++ [0w])` by
    (qpat_x_assum `trace_blocks [] 0 fuel7 _ _ _ = _` kall_tac >>
     simp[trace_context_def, trace_function_def] >>
     AP_TERM_TAC >> simp[venom_state_component_equality]) >>
  `dftGasFromListTraceDefs$trace_context fuel7 C7 v7 =
    pre ++ ((a,e,inst.inst_id),fn7,inst,s)::post7` by metis_tac[] >>
  mp_tac (Q.INST [`p` |-> `a`, `d` |-> `e`, `filling` |-> `raw ++ [0w]`,
    `orc` |-> `\key. case ALOOKUP (obs ++ ZIP (Kcut ++ kr,raw)) key of
      NONE => 0w | SOME w => w`]
    request_cut_dft_retained_recording_exact) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  strip_tac >> conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (qexists_tac `u` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH Kcut <= LENGTH (Kcut ++ kr)` by simp[] >>
  `TAKE (LENGTH Kcut) raw = gs` by
    (qpat_assum `LENGTH Kcut = LENGTH gs` SUBST1_TAC >> simp[TAKE_LENGTH_APPEND]) >>
  `trace_gas pre = ZIP (TAKE (LENGTH Kcut) (Kcut ++ kr), TAKE (LENGTH Kcut) raw)` by
    metis_tac[TAKE_LENGTH_APPEND] >>
  `trace_agrees (\key. case ALOOKUP (obs ++ ZIP (Kcut ++ kr,raw)) key of
      NONE => 0w | SOME w => w) pre` by
    (mp_tac (Q.INST [`j` |-> `stopped`, `keys` |-> `Kcut ++ kr`,
       `tr` |-> `pre`, `n` |-> `LENGTH (Kcut : ((num # num) list # num # num) list)`]
       request_cut_packet_mask_prefix_agree) >>
     (impl_tac >- (rpt conj_tac >>
        (first_assum ACCEPT_TAC ORELSE (sym_tac >> first_assum ACCEPT_TAC)))) >>
     disch_then ACCEPT_TAC) >>
  `EVERY wf_function C7.ctx_functions /\
   EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
     f.fn_blocks) C7.ctx_functions` by
    (drule o1_ctx_shape_wf_functions >> simp[] >>
     rewrite_tac[EVERY_MEM] >> metis_tac[wf_fn_block_inst_ids_distinct]) >>
  `k < LENGTH u.vs_requests /\ LENGTH s.vs_requests < LENGTH u.vs_requests` by
    metis_tac[] >>
  `inst.inst_opcode <> GAS` by
    (drule_all step_inst_request_outcomes >> Cases_on `inst.inst_opcode` >> simp[]) >>
  `dftGasFromListTraceDefs$trace_context fuel7 C7
     (initial with vs_gas_readings := raw ++ [0w]) =
     pre ++ ((a,e,inst.inst_id),fn7,inst,s)::post7` by metis_tac[] >>
  qx_genl_tac [`p7`, `d7`, `f7`, `i7`, `t7`] >> strip_tac >>
  mp_tac (Q.INST [`C` |-> `C7`, `fuel` |-> `fuel7`, `n` |-> `0`,
    `filling` |-> `raw ++ [0w]`, `p` |-> `a`, `d` |-> `e`, `i` |-> `inst`,
    `fn` |-> `fn7`, `after` |-> `post7`, `a` |-> `p7`, `e` |-> `d7`,
    `g` |-> `f7`, `inst` |-> `i7`, `t` |-> `t7`,
    `orc` |-> `\key. case ALOOKUP (obs ++ ZIP (Kcut ++ kr,raw)) key of
      NONE => 0w | SOME w => w`] request_cut_native_event_cover_upto) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  simp[]
QED
