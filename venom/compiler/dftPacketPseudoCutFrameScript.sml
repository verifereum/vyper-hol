Theory dftPacketPseudoCutFrame
Ancestors
  dftPacketPseudoHistory dftPacketSelectedCutTransport
  list rich_list finite_map arithmetic dftPacketPseudoCallCellFrame

Theorem pseudo_completed_key_frame[local]:
  !(acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    p d sf tf inc ent ord bbff res nrest ai ds ei later f.
  (!a sf tf inc ent ord res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,ent,ord,res,nrest) ==>
    ALL_DISTINCT ord) /\
  FLOOKUP acts p = SOME (sf,tf,inc,ent,ord,NONE,NONE) /\ LAST ord = d /\
  (!k. k < LENGTH p ==>
    ?sf tf inc ent ord.
      FLOOKUP acts (DROP (SUC k) p) = SOME (sf,tf,inc,ent,ord,NONE,NONE) /\
      LAST ord = FST (EL k p)) /\
  FLOOKUP acts ai = SOME bbff /\
  bbff = (sfi,tfi,inci,enti,ds ++ ei::later,res,nrest) /\ MEM f ds ==>
  (ai,f) <> (p,d) /\
  (!k. k < LENGTH p ==> (ai,f) <> (DROP (SUC k) p,FST (EL k p)))
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (ds ++ ei::later)` by metis_tac[] >>
  `~MEM (LAST (ds ++ ei::later)) ds` by
    (fs[ALL_DISTINCT_APPEND] >> metis_tac[rich_listTheory.MEM_LAST,MEM]) >>
  conj_tac
  >- (strip_tac >> gvs[] >>
      qpat_x_assum `MEM (LAST _) ds` mp_tac >>
      pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND,LAST_APPEND_CONS] >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!k. k < LENGTH _ ==> _` drule >> strip_tac >> gvs[] >>
  qpat_x_assum `LAST _ = FST _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND,LAST_APPEND_CONS] >>
  metis_tac[]
QED

(* This statement is polymorphic in the cell element.  It is instantiated
   separately for the slot, site and key tables.  Only selected prefixes of
   open ancestor rows are framed; their remaining cells may have changed. *)

Theorem dft_packet_pseudo_selected_root_prefix:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (tab:(((num # num) list # num),'v list list) fmap) out p d inds A A' cuts.
    cuts <> [] /\ FST (HD cuts) = [] /\
    A = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    A' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    (!cid. FLOOKUP calls (p,d,cid) = NONE) /\
    (!a e cid q h b done ent ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,ent,ret) ==>
      ?row. FLOOKUP tab (a,e) = SOME row /\ q < LENGTH row /\
        EL q row = A ((e,cid)::a) /\
        cid = (EL q (FST (SND (SND (SND (THE (FLOOKUP blocks (a,e)))))))).inst_id) /\
    (!i. i < LENGTH p ==>
      ?h b done ent. FLOOKUP calls
        (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
          SOME (EL i inds,h,b,done,ent,NONE)) /\
    (!a e. (a,e) <> (p,d) /\
      (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!i row. i < LENGTH p /\
      FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME row ==>
      FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
        SOME (LUPDATE (A' (DROP i p)) (EL i inds) row)) /\
    (!a. ~MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p))) ==> A' a = A a) /\
    (!i ai ds ei qi zi.
      i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      ?sf tf inc entry order res nrest later row.
        FLOOKUP acts ai = SOME (sf,tf,inc,entry,order,res,nrest) /\
        order = ds ++ ei::later /\ FLOOKUP tab (ai,ei) = SOME row /\
        qi <= LENGTH row /\ (ai,ei) <> (p,d) /\
        FLAT (MAP (\f. FLAT (THE (FLOOKUP out (ai,f)))) ds) =
          FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) /\
        TAKE qi (THE (FLOOKUP out (ai,ei))) = TAKE qi row /\
        (SUC i < LENGTH cuts ==>
          ?cid h b done ent ret.
            FST (EL (SUC i) cuts) = (ei,cid)::ai /\
            FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b,done,ent,ret))) ==>
    ?rest. A' [] = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP tab (ai,ei))))) cuts) ++ rest
Proof
  rpt gen_tac >> strip_tac >>
  `!a e cid q h b done ent ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,ent,ret) ==>
    ?row. FLOOKUP out (a,e) = SOME row /\ q < LENGTH row /\
      EL q row = A' ((e,cid)::a)` by
    (rpt gen_tac >> disch_tac >> irule dft_packet_pseudo_call_cell_frame >>
     rpt (first_assum (irule_at Any)) >>
     qexistsl_tac [`tab`,`p`,`inds`,`d`,`blocks`,`A`] >>
     asm_rewrite_tac[]) >>
  irule dft_packet_selected_cut_prefix >> simp[] >>
  qexistsl_tac [`acts`,`out`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i ai ds ei qi zi. _` drule_all >> strip_tac >>
  `?row'. FLOOKUP out (ai,ei) = SOME row' /\ LENGTH row' = LENGTH row` by
    (Cases_on `?k. k < LENGTH p /\ (ai,ei) = (DROP (SUC k) p,FST (EL k p))`
     >- (pop_assum strip_assume_tac >> gvs[] >> metis_tac[LENGTH_LUPDATE]) >>
     metis_tac[]) >>
  qexistsl_tac [`sf`,`tf`,`inc`,`entry`,`res`,`nrest`,`later`,`row'`] >>
  simp[] >> reverse conj_tac >- gvs[] >>
  strip_tac >>
  qpat_x_assum `SUC i < LENGTH cuts ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!a e cid q h b done ent ret. _` (drule_then strip_assume_tac) >>
  gvs[]
QED

Theorem dft_packet_pseudo_selected_cut_frame:
  !(acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks : (((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls : (gas_event, num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (tab : (((num # num) list # num), 'v list list) fmap)
    out acts' blocks' calls' p d sf tf inc entry order
    bb bt ps xs ys sched hin h0 s s1 new_body cuts a e q z.
  acts' = acts /\ calls' = calls /\
  FLOOKUP acts p = SOME (sf,tf,inc,entry,order,NONE,NONE) /\ LAST order = d /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,sched,hin,h0,NONE,0,OK s,F,NONE) /\
  blocks' = blocks |+ ((p,d),
    (bb,bt,ps,xs,ys,sched,hin,h0,new_body,0,OK s1,F,NONE)) /\
  (!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order)) /\
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order.
      FLOOKUP acts (DROP (SUC k) p) = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      LAST order = FST (EL k p)) /\
  (!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
    ?bb bt ps xs ys sched hin h0 be hbe pos front closed brest.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),pos,front,closed,brest)) /\
  (!a e. (a,e) <> (p,d) /\
    (!k. k < LENGTH p ==> (a,e) <> (DROP (SUC k) p,FST (EL k p))) ==>
    FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
  (!a e bb bt ps xs ys sched hin h0 be hbe pos front closed brest k.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),pos,front,closed,brest) /\
    k <= LENGTH xs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
    (!r. r < k /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE pos sched)) ==>
    TAKE k (THE (FLOOKUP out (a,e))) = TAKE k (THE (FLOOKUP tab (a,e)))) /\
  (!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
    TAKE q (THE (FLOOKUP out (a,e))) = TAKE q (THE (FLOOKUP tab (a,e)))) /\
  (!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei posi fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,posi,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then
        ai = a /\ ei = e /\ qi = q /\ zi = z /\ IS_SOME bei /\
        qi < LENGTH xsi /\ EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
        (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r (TAKE posi rhoi))
       else
        ?cid h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call))) ==>
  !i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    (!sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
        ini hi bei posi fronti closedi resti.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,posi,fronti,closedi,resti) ==>
      ?order' res' nrest' pos' front' closed' rest' later'.
        FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,order',res',nrest') /\
        FLOOKUP blocks' (ai,ei) =
          SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,pos',front',closed',rest') /\
        order' = ds ++ ei::later') /\
    (!f. MEM f ds ==>
      FST (THE (FLOOKUP blocks' (ai,f))) = FST (THE (FLOOKUP blocks (ai,f)))) /\
    (SUC i < LENGTH cuts ==>
      !cid. EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai ==>
        FLOOKUP calls' (ai,ei,cid) = FLOOKUP calls (ai,ei,cid)) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP out (ai,f)))) ds) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) /\
    TAKE qi (THE (FLOOKUP out (ai,ei))) = TAKE qi (THE (FLOOKUP tab (ai,ei))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP out (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP out (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP tab (ai,ei))))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i ai ds ei qi zi. _` drule_all >> strip_tac >>
  `!a sf tf inc ent ord res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,ent,ord,res,nrest) ==> ALL_DISTINCT ord` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     qpat_x_assum `ord = GENLIST _ _` (fn th => once_rewrite_tac[th]) >>
     simp[ALL_DISTINCT_GENLIST]) >>
  `!f. MEM f ds ==> (ai,f) <> (p,d) /\
      (!k. k < LENGTH p ==> (ai,f) <> (DROP (SUC k) p,FST (EL k p)))` by
    (gen_tac >> disch_tac >> irule pseudo_completed_key_frame >>
     rpt (first_assum (irule_at Any)) >> simp[] >> metis_tac[]) >>
  `(ai,ei) <> (p,d)` by
    (Cases_on `SUC i = LENGTH cuts` >> gvs[]
     >- (rpt strip_tac >> gvs[]) >>
     `?bb bt ps xs ys sched hin h0 be hbe pos front closed brest.
        FLOOKUP blocks (ai,ei) =
          SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),pos,front,closed,brest)` by
       metis_tac[] >> rpt strip_tac >> gvs[]) >>
  `TAKE qi (THE (FLOOKUP out (ai,ei))) = TAKE qi (THE (FLOOKUP tab (ai,ei)))` by
    (Cases_on `SUC i = LENGTH cuts` >> gvs[]
     >- (Cases_on `bei` >> gvs[] >> PairCases_on `x` >>
         qpat_x_assum `!a e bb bt ps xs ys sched hin h0 be hbe pos front closed brest k. _` irule >>
         rpt (first_assum (irule_at Any)) >> simp[]) >>
     metis_tac[]) >>
  `FLAT (MAP (\f. FLAT (THE (FLOOKUP out (ai,f)))) ds) =
   FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds)` by
    (AP_TERM_TAC >> irule MAP_CONG >> simp[] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      qexistsl [`posi`,`fronti`,`closedi`,`resti`] >>
      simp[FLOOKUP_UPDATE] >> IF_CASES_TAC >> gvs[]) >>
  rpt strip_tac >> simp[FLOOKUP_UPDATE] >> IF_CASES_TAC >> gvs[] >> metis_tac[]
QED
