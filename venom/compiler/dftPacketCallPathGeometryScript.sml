Theory dftPacketCallPathGeometry
Ancestors
  dftPacketCallEdgeClauses dftPacketTableSplice list rich_list finite_map arithmetic

Theorem dft_packet_call_fresh_prefix_bound:
  !xs fresh_q qi done.
    fresh_q < LENGTH xs /\ (EL fresh_q xs).inst_opcode = INVOKE /\
    ~MEM fresh_q done /\
    (!r. r < qi /\ (EL r xs).inst_opcode = INVOKE ==> MEM r done) ==>
    qi <= fresh_q
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `qi <= fresh_q` >- simp[] >>
  `fresh_q < qi` by decide_tac >> metis_tac[]
QED

Theorem call_suffix_child[local]:
  !b:((num # num) list). !a e cid i.
    i <= LENGTH b /\ (e,cid)::a = DROP i b ==>
    i < LENGTH b /\ a = DROP (SUC i) b /\ (e,cid) = EL i b
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH ((e,cid)::a) = LENGTH (DROP i b)` by metis_tac[] >>
  `i < LENGTH b` by (gvs[] >> decide_tac) >>
  drule DROP_CONS_EL >> simp[] >> metis_tac[listTheory.CONS_11]
QED

Theorem call_completed_not_last[local]:
  !ds e later. ALL_DISTINCT (ds ++ e::later) ==>
    ~MEM (LAST (ds ++ e::later)) ds
Proof
  rpt gen_tac >> simp[ALL_DISTINCT_APPEND,LAST_APPEND] >>
  metis_tac[MEM_LAST,MEM]
QED

Theorem dft_packet_call_historical_pieces:
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
    (tab:(((num # num) list # num),'v list list) fmap)
    acts' blocks' calls' out new_act new_block new_call
    p d cid b L inds orders
    a ds e qi z sf tf inc entry order res rest later
    bb bt ps xs ys rho in_state h0 body_entry count front closed brest rows.
    b = (d,cid)::p /\ L = LENGTH b /\ LENGTH inds = L /\
    LENGTH orders = SUC L /\
    FLOOKUP acts b = NONE /\ FLOOKUP calls (p,d,cid) = NONE /\
    acts' = acts |+ (b,new_act) /\
    blocks' = blocks |+ ((b,SUC d),new_block) /\
    calls' = calls |+ ((p,d,cid),new_call) /\
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
    order = ds ++ e::later /\ ALL_DISTINCT order /\
    FLOOKUP tab (a,e) = SOME rows /\
    (IS_SOME body_entry ==> LENGTH rows = LENGTH xs) /\
    ALL_DISTINCT (MAP (\x. x.inst_id) xs) /\
    (body_entry = NONE ==> qi = 0) /\
    (IS_SOME body_entry ==>
      !r. r < qi /\ (EL r xs).inst_opcode = INVOKE ==>
        MEM r (TAKE count rho)) /\
    (!i. i < L ==>
      ?sfi tfi inci enti resi resti bbi bti psi xsi ysi rhoi ini hi bei hbei
        counti fronti closedi bresti rowi.
        FLOOKUP acts (DROP (SUC i) b) =
          SOME (sfi,tfi,inci,enti,EL (SUC i) orders,resi,resti) /\
        LAST (EL (SUC i) orders) = FST (EL i b) /\
        FLOOKUP blocks (DROP (SUC i) b,FST (EL i b)) =
          SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,SOME (bei,hbei),counti,fronti,closedi,bresti) /\
        FLOOKUP tab (DROP (SUC i) b,FST (EL i b)) = SOME rowi /\
        LENGTH rowi = LENGTH xsi /\ EL i inds < LENGTH xsi /\
        (EL (EL i inds) xsi).inst_opcode = INVOKE /\
        (EL (EL i inds) xsi).inst_id = SND (EL i b) /\
        (if i = 0 then ~MEM (EL i inds) (TAKE counti rhoi) else
          ?h b0 done_at_call child_entry.
            FLOOKUP calls (DROP (SUC i) b,FST (EL i b),SND (EL i b)) =
              SOME (EL i inds,h,b0,done_at_call,child_entry,NONE)) /\
        (!r. r < LENGTH xsi /\ MEM r (TAKE counti rhoi) /\
          (EL r xsi).inst_opcode = INVOKE ==>
          ?q h b0 done_at_call child_entry ir child_out caller_post.
            FLOOKUP calls (DROP (SUC i) b,FST (EL i b),(EL r xsi).inst_id) =
              SOME (q,h,b0,done_at_call,child_entry,
                SOME (ir,child_out,caller_post)))) /\
    (!i rowi. i < L /\
      FLOOKUP tab (DROP (SUC i) b,FST (EL i b)) = SOME rowi ==>
      FLOOKUP out (DROP (SUC i) b,FST (EL i b)) =
        SOME (LUPDATE
          (FLAT (MAP (\f. FLAT (THE (FLOOKUP out (DROP i b,f))))
            (EL i orders))) (EL i inds) rowi)) /\
    (!a e. (a,e) <> (b,SUC d) /\
      (!i. i < L ==> (a,e) <> (DROP (SUC i) b,FST (EL i b))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) ==>
    FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,rest) /\
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
    (!f. MEM f ds ==>
      FLOOKUP blocks' (a,f) = FLOOKUP blocks (a,f) /\
      FLOOKUP out (a,f) = FLOOKUP tab (a,f)) /\
    LENGTH (THE (FLOOKUP out (a,e))) = LENGTH rows /\
    TAKE qi (THE (FLOOKUP out (a,e))) = TAKE qi rows /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP out (a,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP out (a,e)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) ds) ++
      FLAT (TAKE qi rows) /\
    (!selected_cid call_h b0 done_at_call child_entry ret
        csf ctf cinc centry child_order cres crest.
      FLOOKUP calls (a,e,selected_cid) =
        SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
      qi < LENGTH xs /\ (EL qi xs).inst_opcode = INVOKE /\
      (EL qi xs).inst_id = selected_cid /\
      EL qi rows = FLAT (MAP (\f. FLAT
        (THE (FLOOKUP tab ((e,selected_cid)::a,f)))) child_order) /\
      FLOOKUP acts ((e,selected_cid)::a) =
        SOME (csf,ctf,cinc,centry,child_order,cres,crest) ==>
      FLOOKUP calls' (a,e,selected_cid) =
        SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
      FLOOKUP acts' ((e,selected_cid)::a) =
        SOME (csf,ctf,cinc,centry,child_order,cres,crest) /\
      EL qi (THE (FLOOKUP out (a,e))) = FLAT (MAP (\f. FLAT
        (THE (FLOOKUP out ((e,selected_cid)::a,f)))) child_order))
Proof
  rpt gen_tac >> strip_tac >>
  `a <> b` by metis_tac[optionTheory.NOT_NONE_SOME] >>
  `!i. i < L /\ a = DROP (SUC i) b ==>
    LAST order = FST (EL i b)` by
    (rpt strip_tac >>
     qpat_assum `!i. i < L ==> _`
       (qspec_then `i` (drule_then strip_assume_tac)) >>
     gvs[]) >>
  `!f. MEM f ds ==> FLOOKUP out (a,f) = FLOOKUP tab (a,f)` by
    (rpt strip_tac >> qpat_x_assum `!a e. _` irule >> simp[] >>
     rpt strip_tac >>
     `a = DROP (SUC i) b` by simp[] >>
     `i < L` by gvs[] >>
     `LAST order = FST (EL i b)` by metis_tac[] >>
     `~MEM (LAST order) ds` by metis_tac[call_completed_not_last] >>
     metis_tac[]) >>
  `!i. i < L /\ (a,e) = (DROP (SUC i) b,FST (EL i b)) ==>
    qi <= EL i inds` by
    (rpt strip_tac >>
     qpat_assum `!i. i < L ==> _`
       (qspec_then `i` (drule_then strip_assume_tac)) >>
     gvs[] >>
     Cases_on `i = 0`
     >- (gvs[] >> irule dft_packet_call_fresh_prefix_bound >>
         metis_tac[]) >>
     gvs[] >> Cases_on `qi <= EL i inds` >- simp[] >>
     `EL i inds < qi` by decide_tac >>
     qpat_x_assum `!r. r < LENGTH xs /\ _ ==> _`
       (qspec_then `EL i inds` mp_tac) >> simp[]) >>
  `!i. i < L ==> ?rowi.
    FLOOKUP tab (DROP (SUC i) b,FST (EL i b)) = SOME rowi /\
    EL i inds < LENGTH rowi` by
    (rpt strip_tac >>
     qpat_assum `!i. i < L ==> _`
       (qspec_then `i` (drule_then strip_assume_tac)) >> metis_tac[]) >>
  `LENGTH (THE (FLOOKUP out (a,e))) = LENGTH rows /\
   TAKE qi (THE (FLOOKUP out (a,e))) = TAKE qi rows` by
    (Cases_on `?i. i < L /\ (a,e) = (DROP (SUC i) b,FST (EL i b))`
     >- (pop_assum strip_assume_tac >>
         `qi <= EL i inds` by metis_tac[] >>
         `FLOOKUP tab (DROP (SUC i) b,FST (EL i b)) = SOME rows` by
           metis_tac[] >>
         qpat_assum `!i rowi. _`
           (qspecl_then [`i`,`rows`] (drule_then assume_tac)) >>
         gvs[dft_packet_row_prefix_splice]) >>
     `FLOOKUP out (a,e) = SOME rows` by
       (qpat_x_assum `!a e. _` (qspecl_then [`a`,`e`] mp_tac) >>
        simp[] >> metis_tac[]) >> simp[]) >>
  `MAP (\f. FLAT (THE (FLOOKUP out (a,f)))) ds =
   MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) ds` by
    (irule MAP_CONG >> simp[]) >>
  simp[FLOOKUP_UPDATE] >>
  rpt gen_tac >> strip_tac >>
  `(e,selected_cid)::a <> b` by metis_tac[optionTheory.NOT_NONE_SOME] >>
  `(a,e,selected_cid) <> (p,d,cid)` by
    (strip_tac >> gvs[]) >>
  simp[] >> FAIL_TAC "selected child cell"
QED
