Theory requestCutPacketFresh
Ancestors
  dftFinitePacket dftPacketFreshCut dftIndexedExec gasEvents
  venomExecSemantics venomInst venomState list finite_map arithmetic

(* The fresh endpoint is inside the pseudo prefix. It consumes no GAS key,
   and its row result is still OK on any native filling. *)
Theorem request_cut_packet_fresh_row:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn tf inst s oms om hs h raw_slots sites unused
    bb bt ps xs ys rho hin h0 z gs fuel.
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
      (JointConfig stk PG G tn tf inst s oms om hs h) raw_slots sites unused /\
    FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,NONE,0,OK s,F,NONE) /\
    z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s.vs_inst_idx ps) ==>
    FLOOKUP ms_tab (p,d) = SOME [] /\ FLOOKUP ks_tab (p,d) = SOME [] /\
    ?sp. eval_phis (hin with vs_gas_readings := gs) bb.bb_instructions = OK sp /\
      FOLDR (dft_exec_cons (fuel-d) C7) OK z
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      OK (s with vs_gas_readings := gs)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?sp8. FLOOKUP ms_tab (p,d) = SOME [] /\ FLOOKUP ks_tab (p,d) = SOME [] /\
    bb.bb_instructions = ps ++ xs /\ EVERY (\i. is_pseudo i.inst_opcode) ps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs /\ EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
    eval_phis hin (ps ++ ys) = OK sp8 /\
    phi_prefix_length (ps ++ ys) <= s.vs_inst_idx /\ s.vs_inst_idx < LENGTH ps /\
    FOLDR (dft_exec_cons (N-d) C8) OK
      (DROP (phi_prefix_length (ps ++ ys)) (TAKE s.vs_inst_idx ps))
      (sp8 with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK s` by
    suspend "record" >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST
    [`R` |-> `\entry'. case eval_phis entry' bb.bb_instructions of
        OK sp => (gas_events_block (fuel-d) C7 root_sf.fn_name
          (bb with bb_instructions :=
             TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
          FOLDR (dft_exec_cons (fuel-d) C7) OK z
            (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
        | other => ([],other)`,
     `entry` |-> `hin`,`sf` |-> `root_sf`,`f` |-> `fuel-d`,
     `g` |-> `N-d`,`k` |-> `s.vs_inst_idx`,`t` |-> `s`,`sp` |-> `sp8`]
    dft_packet_fresh_pseudo_cut) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> REFL_TAC) >>
  disch_then (qspec_then `gs` mp_tac) >>
  Cases_on `eval_phis (hin with vs_gas_readings := gs) bb.bb_instructions` >>
  qpat_assum `eval_phis (hin with vs_gas_readings := gs) bb.bb_instructions = _`
    (fn th => simp[NoAsms,th])
QED

Resume request_cut_packet_fresh_row[record]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (fn info => qpat_assum `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,_,hin,h0,NONE,0,OK s,F,NONE)`
      (strip_assume_tac o MATCH_MP info)) >>
  suspend "cursor"
QED

Resume request_cut_packet_fresh_row[cursor]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`JointConfig stk PG G tn tf inst s oms om hs h = _`,
     `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,_,hin,h0,NONE,0,OK s,F,NONE)`,
     `FLOOKUP blocks (p,d) = SOME _`,
     `case NONE of NONE => _ | SOME (be,hbe) => _`,
     `case body_entry of NONE => _ | SOME (be,hbe) => _`,
     `bt.bb_instructions = ps ++ ys`,
     `bb.bb_instructions = ps ++ xs`,`EVERY (\i. is_pseudo i.inst_opcode) ps`,
     `EVERY (\i. ~is_pseudo i.inst_opcode) xs`,`EVERY (\i. ~is_pseudo i.inst_opcode) ys`,
     `eval_phis hin bt.bb_instructions = OK _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]
QED

Finalise request_cut_packet_fresh_row

Theorem request_cut_packet_fresh_endpoint:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn tf inst s oms om hs h) raw_slots sites unused /\
  FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,row_order,hin,h0,NONE,row_count,front,closed,brest) /\
  z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s.vs_inst_idx ps) ==>
  !gs fuel. ?sp u.
    eval_phis (hin with vs_gas_readings := gs) bb.bb_instructions = OK sp /\
    FOLDR (dft_exec_cons (fuel-d) C7) OK z
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,row_order,hin,h0,NONE,0,OK s,F,NONE)` by
    (qhdtm_x_assum `dft_focus_packet_rel`
      (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_assum `JointConfig stk PG G tn tf inst s oms om hs h = _` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,row_order,hin,h0,NONE,row_count,front,closed,brest)`,
        `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,_,_,OK _,F,NONE)`,
        `case body_entry of NONE => _ | SOME (be,hbe) => _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >>
  drule_all request_cut_packet_fresh_row >>
  disch_then (qspecl_then [`gs`,`fuel`] strip_assume_tac) >>
  metis_tac[]
QED
