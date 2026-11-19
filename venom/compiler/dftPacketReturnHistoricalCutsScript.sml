Theory dftPacketReturnHistoricalCuts
Ancestors
  dftPacketReturnTables dftPacketSelectedCutTransport
  finite_map list rich_list

(* A return changes completion fields only.  Historical levels, including
   levels selected inside the completed child, retain their original meaning.
   No agreement with the NEW current cursor is asserted here. *)
Theorem dft_packet_return_historical_cut_frame:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls:(gas_event,
      num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ms_tab:(((num # num) list # num),bytes32 option list list) fmap)
    (es_tab:(((num # num) list # num),(string # num) list list) fmap)
    (ks_tab:(((num # num) list # num),gas_event list list) fmap).
  b = (ce,cid)::parent /\
  FLOOKUP acts b = SOME (csf,ctf,ce,child_entry,child_order,NONE,NONE) /\
  FLOOKUP blocks (b,cd) =
    SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE) /\
  FLOOKUP blocks (parent,ce) =
    SOME (pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),pn,OK b0,F,NONE) /\
  FLOOKUP calls (parent,ce,cid) = SOME (cq,call_h,b0,done,child_entry,NONE) /\
  acts' = acts |+ (b,(csf,ctf,ce,child_entry,child_order,
    SOME (IntRet ir child_out),SOME child_out.vs_gas_readings)) /\
  blocks' = blocks |+
    ((b,cd),(cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),
      LENGTH cys,IntRet ir child_out,T,SOME child_out.vs_gas_readings)) |+
    ((parent,ce),(pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),SUC pn,
      OK (caller_post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
  calls' = calls |+ ((parent,ce,cid),
    (cq,call_h,b0,done,child_entry,SOME (ir,child_out,caller_post))) /\
  ms_tab' = ms_tab /\ es_tab' = es_tab /\ ks_tab' = ks_tab /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts =
    REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
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
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
      EL i levels =
        (sfi, MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
          [(bbi,ei,zi)], if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
  Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
  Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
  FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) = Mcut ++ mr /\
  FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) = Ecut ++ er /\
  FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) = Kcut ++ kr /\
  LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
  (!F gs tail.
    N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
    levels_ok F C7 levels
      (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
      (MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts ai))))) cuts)
      root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
    (?extra. Ecut = FST (rooted_eval F C7 levels
      (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
      OK u =>
        FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
        u.vs_gas_readings = tail /\
        (?before after.
          dftGasFromListTraceDefs$trace_blocks [] 0 F C7 root_sf
            (root_entry with vs_gas_readings := gs ++ tail) =
            before ++ [((a,e,(EL (LENGTH z)
              (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
              EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
          dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
        (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
          (Ecut,OK (u with vs_gas_readings := tail')))
    | stopped =>
        run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
        gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
          FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)))) ==>
  MAP (\(ai,ds,ei,qi,zi). ai) cuts =
    REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  LENGTH cuts = LENGTH levels /\
  (!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks' (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then
        ai = a /\ ei = e /\ qi = q /\ zi = z
       else
        ?cid h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
          FLOOKUP calls' (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
      EL i levels =
        (sfi, MAP (\f. (FST (THE (FLOOKUP blocks' (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)) ds ++
          [(bbi,ei,zi)], if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab' (ai,ei))))) cuts) /\
  Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP es_tab' (ai,ei))))) cuts) /\
  Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ks_tab' (ai,ei))))) cuts) /\
  FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab' ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Mcut ++ mr /\
  FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab' ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Ecut ++ er /\
  FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab' ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Kcut ++ kr /\
  LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
  (!F gs tail.
    N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
    levels_ok F C7 levels
      (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
      (MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts' ai))))) cuts)
      root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
    (?extra. Ecut = FST (rooted_eval F C7 levels
      (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
      OK u =>
        FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
        u.vs_gas_readings = tail /\
        (?before after.
          dftGasFromListTraceDefs$trace_blocks [] 0 F C7 root_sf
            (root_entry with vs_gas_readings := gs ++ tail) =
            before ++ [((a,e,(EL (LENGTH z)
              (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
              EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
          dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
        (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
          (Ecut,OK (u with vs_gas_readings := tail')))
    | stopped =>
        run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
        gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
          FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `b <> parent` by (strip_tac >> gvs[]) >>
  `!x. FST (SND (SND (THE (FLOOKUP acts' x)))) =
        FST (SND (SND (THE (FLOOKUP acts x)))) /\
       FST (SND (SND (SND (SND (THE (FLOOKUP acts' x)))))) =
        FST (SND (SND (SND (SND (THE (FLOOKUP acts x))))))` by
    (gen_tac >> Cases_on `x = b` >> gvs[FLOOKUP_UPDATE]) >>
  `!x f. FST (THE (FLOOKUP blocks' (x,f))) =
         FST (THE (FLOOKUP blocks (x,f)))` by
    (rpt gen_tac >> Cases_on `x = parent`
     >- (Cases_on `f = ce` >> gvs[FLOOKUP_UPDATE]) >>
     Cases_on `x = b`
     >- (Cases_on `f = cd` >> gvs[FLOOKUP_UPDATE]) >>
     gvs[FLOOKUP_UPDATE]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "description" >>
  asm_simp_tac std_ss [] >>
  metis_tac[]
QED

Resume dft_packet_return_historical_cut_frame[description]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i ai ds ei qi zi. _` (drule_all_then strip_assume_tac) >>
  `?res' nrest'. FLOOKUP acts' ai =
      SOME (sfi,tfi,inci,enti,orderi,res',nrest')` by
    (Cases_on `ai = b` >> gvs[FLOOKUP_UPDATE]) >>
  `?count' front' closed' rest'. FLOOKUP blocks' (ai,ei) =
      SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,count',front',closed',rest')` by
    (Cases_on `ai = parent`
     >- (Cases_on `ei = ce` >> gvs[FLOOKUP_UPDATE]) >>
     Cases_on `ai = b`
     >- (Cases_on `ei = cd` >> gvs[FLOOKUP_UPDATE]) >>
     gvs[FLOOKUP_UPDATE]) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  asm_rewrite_tac[] >>
  Cases_on `SUC i = LENGTH cuts` >- gvs[] >>
  fs[] >>
  goal_assum (drule_at Any) >>
  Cases_on `(ai,ei,(EL qi xsi).inst_id) = (parent,ce,cid)`
  >- gvs[FLOOKUP_UPDATE] >>
  simp[FLOOKUP_UPDATE] >> metis_tac[]
QED
Finalise dft_packet_return_historical_cut_frame
