Theory requestCutPacketVisitGeometry
Ancestors
  dftFinitePacket dftDefs dftRunRel dftGasInvMemoryObservation
  contextCodegenRel o1PassContract
  venomInst venomState venomWf venomWfProps simplifyCfgDefs
  finite_map list

(* The selected body row identifies both native active blocks. *)
Theorem request_cut_packet_visit_geometry:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,row_order,hin,h0,body_entry,nseen,front,closed,brest) /\
  q < LENGTH xs /\ EL q xs = inst /\
  z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
  active_inst sf inst u /\ active_inst tf inst t /\
  get_instruction bt t.vs_inst_idx = SOME inst ==>
  EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = inst /\
  tf = dft_fn sf /\ u.vs_current_bb = t.vs_current_bb
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o SIMP_RULE bool_ss [dft_focus_packet_rel_def, LET_THM]) >>
  `lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
   lookup_block bb.bb_label tf.fn_blocks = SOME bt /\ bt.bb_label = bb.bb_label /\
   bb.bb_instructions = ps ++ xs /\ EVERY (\i. ~is_pseudo i.inst_opcode) xs` by
    (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> _`
       (fn rows => qpat_assum `FLOOKUP blocks (a,e) = SOME _` (mp_then Any mp_tac rows)) >>
     qpat_assum `FLOOKUP acts a = SOME _` (fn eq => simp_tac (srw_ss()) [eq]) >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `MEM sf C7.ctx_functions /\ tf = dft_fn sf` by
    (qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
       (fn rows => qpat_assum `FLOOKUP acts a = SOME _` (mp_then Any mp_tac rows)) >>
     strip_tac >> simp[]) >>
  `MEM tf C8.ctx_functions` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions`,
        `MEM sf C7.ctx_functions`, `tf = dft_fn sf`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]) >>
  `wf_function sf /\ wf_function tf` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`o1_ctx_shape C7`,`o1_ctx_shape C8`,`MEM sf C7.ctx_functions`,`MEM tf C8.ctx_functions`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
     metis_tac[]) >>
  `MEM inst bb.bb_instructions /\ MEM inst bt.bb_instructions` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`bb.bb_instructions = ps ++ xs`,`q < LENGTH xs`,`EL q xs = inst`,
        `get_instruction bt t.vs_inst_idx = SOME inst`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[get_instruction_def, AllCaseEqs(), MEM_APPEND] >>
     metis_tac[EL_MEM]) >>
  conj_tac
  >- (mp_tac (Q.INST [`bb` |-> `bb`, `ps` |-> `ps`, `xs` |-> `xs`,
        `q` |-> `q`, `z` |-> `z`] dft_packet_cut_instruction) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      qpat_assum `EL q xs = inst` (fn eq => PURE_REWRITE_TAC [eq]) >> simp[]) >>
  simp[] >> map_every (fn pat => qpat_assum pat mp_tac)
    [`wf_function sf`,`wf_function tf`,`active_inst sf inst u`,`active_inst tf inst t`,
     `lookup_block bb.bb_label sf.fn_blocks = SOME bb`,
     `lookup_block bb.bb_label tf.fn_blocks = SOME bt`,
     `bt.bb_label = bb.bb_label`,`MEM inst bb.bb_instructions`,`MEM inst bt.bb_instructions`] >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[dft_packet_active_block]
QED


(* The pseudo-prefix alternative cannot host a memory observation. *)
Theorem request_cut_packet_observation_body:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,row_order,hin,h0,body_entry,nseen,front,closed,brest) /\
  get_instruction bt t.vs_inst_idx = SOME inst /\
  inv_memory_observation inst.inst_opcode /\
  ((q < LENGTH xs /\ EL q xs = inst /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
   t.vs_inst_idx < LENGTH ps) ==>
  q < LENGTH xs /\ EL q xs = inst /\
  z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
  EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o SIMP_RULE bool_ss [dft_focus_packet_rel_def, LET_THM]) >>
  `bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
   EVERY (\i. is_pseudo i.inst_opcode) ps /\
   EVERY (\i. ~is_pseudo i.inst_opcode) xs` by
    (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> _`
       (fn rows => qpat_assum `FLOOKUP blocks (a,e) = SOME _` (mp_then Any mp_tac rows)) >>
     qpat_assum `FLOOKUP acts a = SOME _` (fn eq => simp_tac (srw_ss()) [eq]) >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(q < LENGTH xs /\ _) \/ _`
    (DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS) assume_tac)
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      mp_tac (Q.INST [`bb` |-> `bb`, `ps` |-> `ps`, `xs` |-> `xs`,
        `q` |-> `q`, `z` |-> `z`] dft_packet_cut_instruction) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      qpat_assum `EL q xs = inst` (fn eq => PURE_REWRITE_TAC [eq]) >> simp[]) >>
  `inst = EL t.vs_inst_idx ps` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`get_instruction bt t.vs_inst_idx = SOME inst`, `bt.bb_instructions = ps ++ ys`,
       `t.vs_inst_idx < LENGTH ps`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[get_instruction_def, EL_APPEND_EQN]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`inst = EL t.vs_inst_idx ps`, `EVERY (\i. is_pseudo i.inst_opcode) ps`,
     `t.vs_inst_idx < LENGTH ps`, `inv_memory_observation inst.inst_opcode`] >>
  POP_ASSUM_LIST (K all_tac) >> simp[EVERY_EL] >>
  metis_tac[inv_memory_observation_nonpseudo]
QED
