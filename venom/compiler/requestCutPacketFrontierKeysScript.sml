Theory requestCutPacketFrontierKeys
Ancestors
  requestCutPacketSelectedKeys requestCutPacketFresh
  dftFinitePacket dftGasFromListTraceDefs dftIndexedExec
  venomExecSemantics venomState gasEvents list finite_map

(* The locked frontier gives the last row by lookup. The body guard is
   already on that row, and the fresh arm is still inside the pseudos. *)
Theorem request_cut_packet_frontier_keys:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,row_order,hin,h0,body_entry,row_count,front,closed,brest) /\
  ((IS_SOME body_entry /\ q < LENGTH xs /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
    (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
      MEM r (TAKE row_count row_order))) \/
   (a = p /\ e = d /\ body_entry = NONE /\ q = 0 /\
    ?stk PG G tn tf inst s oms om hs h.
      q8 = JointConfig stk PG G tn tf inst s oms om hs h /\
      z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s.vs_inst_idx ps))) /\
  paths = MAP (\(ai,ds,ei,qi,zi). ai) cuts /\
  paths = REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  LENGTH cuts = LENGTH levels /\
  (!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
       ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then
        ai = a /\ ei = e /\ qi = q /\ zi = z
      else
        ?cid h b0 done_at_call child_entry ret.
          EL (SUC i) paths = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\i. ~is_terminator i.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
      EL i levels =
        (sfi,MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++ [(bbi,ei,zi)],
         if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
  Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
  N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
  SND (rooted_eval fuel C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = r /\
  ~(?u. r = OK u) ==>
  ~(?ir u. r = IntRet ir u) /\
  run_blocks fuel C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = r /\
  ?extra. Kcut = MAP FST (trace_gas (trace_blocks [] 0 fuel C7 root_sf
    (root_entry with vs_gas_readings := gs ++ tail))) ++ extra
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac request_cut_packet_selected_keys >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> suspend "rows") >>
  DISCH_THEN ACCEPT_TAC
QED

Resume request_cut_packet_frontier_keys[rows]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!i ai ds ei qi zi. i < LENGTH cuts /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qexistsl_tac [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`bbi`,`bti`,
    `psi`,`xsi`,`ysi`,`rhoi`,`ini`,`hi`,`bei`,`counti`,`fronti`,`closedi`,`resti`,`later`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  Cases_on `SUC i = LENGTH cuts`
  >- (qpat_assum `SUC i = LENGTH cuts` (fn eq =>
       qpat_x_assum `if SUC i = LENGTH cuts then _ else _`
         (strip_assume_tac o REWRITE_RULE [eq,COND_CLAUSES]) >>
       simp_tac bool_ss [eq]) >>
      suspend "last_row") >>
  qpat_assum `SUC i <> LENGTH cuts` (fn neq =>
    qpat_assum `if SUC i = LENGTH cuts then _ else _`
      (fn th => simp_tac bool_ss [neq,REWRITE_RULE [neq,COND_CLAUSES] th]))
QED

Resume request_cut_packet_frontier_keys[last_row]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLOOKUP blocks (a,e) = SOME _`,`FLOOKUP blocks (ai,ei) = SOME _`,
     `ai = a`,`ei = e`,`qi = q`,`zi = z`] >>
  simp[NoAsms] >> strip_tac >>
  qpat_x_assum `(IS_SOME body_entry /\ _) \/ _`
    (DISJ_CASES_THEN strip_assume_tac) >>
  simp_tac bool_ss [arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  gvs[] >>
  drule request_cut_packet_fresh_endpoint >>
  disch_then drule >>
  disch_then (qspec_then
    `DROP (phi_prefix_length bb.bb_instructions) (TAKE s.vs_inst_idx ps)` mp_tac) >>
  simp_tac bool_ss [] >>
  disch_then (fn th => gen_tac >> MATCH_ACCEPT_TAC th)
QED

Finalise request_cut_packet_frontier_keys
