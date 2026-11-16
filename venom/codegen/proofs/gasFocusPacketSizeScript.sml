Theory gasFocusPacketSize
Ancestors
  gasFocusPacketRows gasFocusPacketKeys gasFocusPacketCardinality
  dftFinitePacket fnSimSpec finite_map arithmetic

(* This bounds the complete retained mask, including NONE slots.  The
   occurrence index is packet-local; no uniform frontier bound is asserted. *)
Theorem dft_focus_packet_slots_bound:
  dft_focus_packet_rel (N:num) C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused ==>
  LENGTH raw_slots <= SUC (FST packet) * context_inst_count C7
Proof
  strip_tac >>
  `?order. FLOOKUP acts [] =
    SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)` by
    (qhdtm_assum `dft_focus_packet_rel` mp_tac >>
     rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
     goal_assum (drule_at Any)) >>
  `LENGTH raw_slots <= CARD (FDOM blocks) * context_inst_count C7` by
    (irule dft_focus_packet_slots_charge >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
     rpt strip_tac >> drule_all dft_focus_packet_root_key_origin >> simp[]) >>
  drule dft_focus_packet_rows_bound >> strip_tac >>
  irule LESS_EQ_TRANS >>
  qexists `CARD (FDOM blocks) * context_inst_count C7` >>
  simp[LESS_MONO_MULT]
QED
