Theory requestCutPacketNativeVisit
Ancestors
  requestCutDftPacketVisit requestCutNativeEventCover dftFinitePacket
  dftGasFromListTraceDefs dftGasOracleDefs o1PassContract contextCodegenRel
  venomWf venomInst venomState list finite_map alist

(* Keep the actual C7 residual tape alongside the restored event state. *)
Theorem request_cut_packet_native_visit:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  C7.ctx_entry = SOME nm /\ C8.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME root_sf /\
  lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl /\ fn_entry_label root_tf = SOME lbl /\
  root_entry = (v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
  keys = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) /\
  keys = Kcut ++ kr /\ LENGTH Kcut = LENGTH gs /\ raw = gs ++ gr /\
  trace_blocks [] 0 fuel7 C7 root_sf (root_entry with vs_gas_readings := raw ++ [0w]) =
    pre ++ ((a,e,inst.inst_id),fn7,inst,s)::after /\
  trace_gas pre = ZIP (Kcut,gs) /\
  trace8 = trace_blocks [] 0 N C8 root_tf root_entry /\
  h <= j /\ h < LENGTH trace8 /\ EL h trace8 = ((a,e,inst.inst_id),fn8,inst,t) /\
  EVERY wf_function C7.ctx_functions /\
  EVERY (\fn. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    fn.fn_blocks) C7.ctx_functions /\
  orc = (\key. case ALOOKUP (obs ++ ZIP (keys,raw)) key of NONE => 0w | SOME w => w) ==>
  raw_reachable (v with vs_gas_readings := raw ++ [0w]) C7 fn7 inst s /\
  ev_reachable orc v C7 a e fn7 inst (s with vs_gas_readings := v.vs_gas_readings) /\
  ev_reachable orc v C8 a e fn8 inst (t with vs_gas_readings := v.vs_gas_readings)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `trace_context fuel7 C7 (v with vs_gas_readings := raw ++ [0w]) =
    trace_blocks [] 0 fuel7 C7 root_sf (root_entry with vs_gas_readings := raw ++ [0w])` by
    (qpat_x_assum `trace_blocks [] 0 fuel7 _ _ _ = _` kall_tac >>
     simp[trace_context_def, trace_function_def] >>
     AP_TERM_TAC >> simp[venom_state_component_equality]) >>
  `trace_context fuel7 C7 (v with vs_gas_readings := raw ++ [0w]) =
    pre ++ ((a,e,inst.inst_id),fn7,inst,s)::after` by metis_tac[] >>
  conj_tac
  >- (irule request_cut_native_trace_reachable >> metis_tac[]) >>
  qpat_x_assum `keys = Kcut ++ kr` SUBST_ALL_TAC >>
  qpat_x_assum `orc = _` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`p7` |-> `a`, `d7` |-> `e`, `id7` |-> `inst.inst_id`,
    `i7` |-> `inst`, `s7` |-> `s`, `pre7` |-> `pre`, `after7` |-> `after`,
    `p8` |-> `a`, `d8` |-> `e`, `id8` |-> `inst.inst_id`, `i8` |-> `inst`,
    `s8` |-> `t`] request_cut_packet_visit_pair) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> sym_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
