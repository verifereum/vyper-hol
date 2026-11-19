Theory requestCutHistoricalRecording
Ancestors
  requestCutRetainedRecording requestCutPacketVisitGeometry dftFinitePacket
  dftGasFromListTraceDefs dftGasOracleDefs dftRunRel dftDefs
  o1PassContract contextCodegenRel venomState venomExecSemantics
  venomInst venomWf list finite_map alist

(* Use the historical rooted cut at the request's actual C8 visit.
   The packet identifies its native instruction and splits the same tape. *)
Theorem request_cut_historical_recording:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (stopped,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  C7.ctx_entry = SOME nm /\ C8.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME root_sf /\
  lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl /\ fn_entry_label root_tf = SOME lbl /\
  root_entry = (initial with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,row_order,hin,h0,body_entry,nseen,front,closed,brest) /\
  q < LENGTH xs /\ EL q xs = inst /\
  z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
  raw_slots = Mcut ++ mr /\ LENGTH Mcut = LENGTH Kcut /\
  FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) = Kcut ++ kr /\
  (!F gs tail u. N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
     rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail) = (Ecut,OK u) ==>
     ?before after.
       trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
       before ++ [((a,e,(EL (LENGTH z)
           (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
         EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
       trace_gas before = ZIP (Kcut,gs)) /\
  trace8 = trace_blocks [] 0 N C8 root_tf root_entry /\
  h < stopped /\ h < LENGTH trace8 /\
  EL h trace8 = ((a,e,inst.inst_id),tf,inst,t) /\
  LIST_REL (\fn fn'. fn' = dft_fn fn) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\ o1_ctx_shape C7 /\
  ctx_labels_bound C7 initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn)) C7.ctx_functions /\
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  v7 = (initial with vs_gas_readings := raw ++ [0w]) /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C8 inst t = OK post8 /\
  LENGTH t.vs_requests = k /\ k < LENGTH post8.vs_requests /\
  N <= fuel7 /\
  rooted_eval fuel7 C7 levels (root_entry with vs_gas_readings := raw ++ [0w]) = (Ecut,OK s) ==>
  raw_reachable v7 C7 sf inst s /\
  (?u. step_inst 0 C7 inst s = OK u /\
    s.vs_requests = t.vs_requests /\ s.vs_outcomes = t.vs_outcomes /\
    u.vs_requests = post8.vs_requests /\ u.vs_outcomes = post8.vs_outcomes) /\
  (!p d fn i t. ev_reachable
     (\key. case ALOOKUP (obs ++ ZIP (Kcut ++ kr,raw)) key of NONE => 0w | SOME w => w)
     initial C7 p d fn i t /\ LENGTH t.vs_requests <= k ==>
    ?ws. raw_reachable v7 C7 fn i (t with vs_gas_readings := ws))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bb.bb_instructions = ps ++ xs /\ EVERY (\i. ~is_pseudo i.inst_opcode) xs` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o SIMP_RULE bool_ss [dft_focus_packet_rel_def, LET_THM]) >>
     qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> _`
       (fn rows => qpat_assum `FLOOKUP blocks (a,e) = SOME _` (mp_then Any mp_tac rows)) >>
     qpat_assum `FLOOKUP acts a = SOME _` (fn eq => simp_tac (srw_ss()) [eq]) >>
     strip_tac >> simp[]) >>
  `EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = inst`
    by metis_tac[dft_packet_cut_instruction] >>
  qpat_assum `LIST_REL _ raw_slots raw`
    (fn rel => qpat_assum `raw_slots = Mcut ++ mr`
       (fn eq => strip_assume_tac (REWRITE_RULE [eq, LIST_REL_SPLIT1] rel))) >>
  rename1 `raw = gs ++ gr` >>
  `LENGTH Kcut = LENGTH gs` by metis_tac[LIST_REL_LENGTH] >>
  `gs ++ (gr ++ [0w]) = raw ++ [0w]` by metis_tac[APPEND_ASSOC] >>
  `rooted_eval fuel7 C7 levels (root_entry with vs_gas_readings := gs ++ (gr ++ [0w])) =
    (Ecut,OK s)` by
    (qpat_assum `gs ++ (gr ++ [0w]) = raw ++ [0w]` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `!F gs tail u. N <= F /\ _ ==> _`
    (qspecl_then [`fuel7`,`gs`,`gr ++ [0w]`,`s`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `gs ++ (gr ++ [0w]) = raw ++ [0w]` (fn tape_eq =>
    qpat_assum `EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
      bb.bb_instructions) = inst` (fn inst_eq =>
      disch_then (strip_assume_tac o PURE_REWRITE_RULE [tape_eq, inst_eq, APPEND]))) >>
  mp_tac (Q.INST [`j` |-> `stopped`, `fn7` |-> `sf`, `fn8` |-> `tf`,
    `pre` |-> `before`, `post7` |-> `after`, `e` |-> `e`, `a` |-> `a`]
    request_cut_packet_retained_recording) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >>
  disch_then ACCEPT_TAC
QED
