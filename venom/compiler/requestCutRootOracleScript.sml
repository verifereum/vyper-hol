Theory requestCutRootOracle
Ancestors
  requestCutPacketOracle dftFinitePacket dftGasFromListTraceDefs
  dftGasOracleDefs venomExecSemantics venomState list finite_map alist

(* The stopped cut's key prefix and the retained visits use the full
   inventory's oracle, including when the native C7 cut is unsuccessful. *)
Theorem request_cut_packet_root_oracle:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  keys = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
  C7.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME root_sf /\
  fn_entry_label root_sf = SOME lbl /\
  root_entry = (v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
  (!fuel. N <= fuel ==> success \/
    ?extra. keys = MAP FST (trace_gas (trace_blocks [] 0 fuel C7 root_sf
      (root_entry with vs_gas_readings := raw ++ tail))) ++ extra) ==>
  !fuel. N <= fuel ==> success \/
    trace_agrees (\key. case ALOOKUP (obs ++ ZIP (keys,raw)) key of
      NONE => 0w | SOME w => w)
      (trace_context fuel C7 (v with vs_gas_readings := raw ++ tail))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >- simp[] >>
  disj2_tac >>
  `trace_context fuel C7 (v with vs_gas_readings := raw ++ tail) =
    trace_blocks [] 0 fuel C7 root_sf (root_entry with vs_gas_readings := raw ++ tail)` by
    (simp[trace_context_def, trace_function_def] >>
     AP_TERM_TAC >> simp[venom_state_component_equality]) >>
  qpat_assum `trace_context fuel _ _ = _` (fn th => PURE_REWRITE_TAC [th]) >>
  irule request_cut_packet_native_oracle >>
  metis_tac[]
QED
