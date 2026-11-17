Theory dftPacketPseudoHistoryCuts
Ancestors
  dftPacketPseudoHistoryFrame dftPacketPseudoCutFrame
  list rich_list finite_map arithmetic pred_set dftPacketSelectedCutTransport

Theorem dft_packet_pseudo_history_cut_frame:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    p d inds orders (tab:(((num # num) list # num),'v list list) fmap) out A A'
    bb0 bt0 ps0 xs0 ys0 rho0 in0 h0 s
    acts' blocks' calls' sf0 tf0 inc0 ent0 ord0 s1 new_body cuts a e q z.
    LENGTH inds = LENGTH p /\ LENGTH orders = SUC (LENGTH p) /\
    FLOOKUP blocks (p,d) =
      SOME (bb0,bt0,ps0,xs0,ys0,rho0,in0,h0,NONE,0,OK s,F,NONE) /\
    (!i. i <= LENGTH p ==>
      ?sf tf inc ent res nrest.
        FLOOKUP acts (DROP i p) = SOME (sf,tf,inc,ent,EL i orders,res,nrest)) /\
    (!i. i < LENGTH p ==>
      ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done_at_call child_entry call_h.
        FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,OK b0,F,NONE) /\
        FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
          SOME (EL i inds,call_h,b0,done_at_call,child_entry,NONE) /\
        dft_fn_rel sf tf /\
        lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
        lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
        bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
        EVERY (\x. is_pseudo x.inst_opcode) ps /\
        EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ LENGTH xs = LENGTH ys /\
        PERM rho (COUNT_LIST (LENGTH xs)) /\
        LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
          from_block [EL q xs] y) rho ys /\
        EL i inds < LENGTH xs /\ (EL (EL i inds) xs).inst_opcode = INVOKE /\
        b0.vs_inst_idx = LENGTH ps + pos /\
        get_instruction bt b0.vs_inst_idx = SOME (EL (EL i inds) xs)) /\
    (!a sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      (res = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p))))) /\
    (!a e cid q h b done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done_at_call,child_entry,ret) ==>
      ?bb bt ps xs ys rho hin h0 be hbe pos front closed brest.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),pos,front,closed,brest) /\
        q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
        (case ret of
          NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
        | SOME triple => MEM q (TAKE pos rho))) /\
    (!a e cid q h b done ent ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,ent,ret) ==>
      ?row. FLOOKUP tab (a,e) = SOME row /\ q < LENGTH row /\
        EL q row = A ((e,cid)::a) /\
        cid = (EL q (FST (SND (SND (SND (THE (FLOOKUP blocks (a,e)))))))).inst_id) /\
    A = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    A' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    (out = tab \/
      ((!a e. (a,e) <> (p,d) /\
        (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
        FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
       (!i row. i < LENGTH p /\
         FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME row ==>
         FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
           SOME (LUPDATE
             (FLAT (MAP (\e. FLAT (THE (FLOOKUP out (DROP i p,e))))
               (EL i orders))) (EL i inds) row)))) /\
    acts' = acts /\ calls' = calls /\
    blocks' = blocks |+ ((p,d),
      (bb0,bt0,ps0,xs0,ys0,rho0,in0,h0,new_body,0,OK s1,F,NONE)) /\
    FLOOKUP acts p = SOME (sf0,tf0,inc0,ent0,ord0,NONE,NONE) /\ LAST ord0 = d /\
    (!a sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order)) /\
    (!k. k < LENGTH p ==>
      ?sf tf inc ent ord.
        FLOOKUP acts (DROP (SUC k) p) = SOME (sf,tf,inc,ent,ord,NONE,NONE) /\
        LAST ord = FST (EL k p)) /\
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
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dft_packet_pseudo_history_frame >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  irule dft_packet_pseudo_selected_cut_frame >>
  rpt (first_assum (irule_at Any)) >>
  qexistsl [`z`,`q`,`e`,`a`] >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!a e bb bt ps xs ys rho hin h be hbe pos front closed brest k. _`
        (drule_all_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!a e cid q h b done_at_call child_entry ret.
        _ ==> ?bb bt ps xs ys rho hin h0 be hbe pos front closed brest. _`
        (drule_then strip_assume_tac) >>
      rpt (first_assum (irule_at Any))) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!a e cid q h b done_at_call child_entry ret.
    _ ==> TAKE _ _ = _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Theorem dft_packet_pseudo_history_root_prefix:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    p d inds orders (tab:(((num # num) list # num),'v list list) fmap) out A A'
    bb0 bt0 ps0 xs0 ys0 rho0 in0 h0 s
    acts' blocks' calls' sf0 tf0 inc0 ent0 ord0 s1 new_body cuts a e q z.
    LENGTH inds = LENGTH p /\ LENGTH orders = SUC (LENGTH p) /\
    FLOOKUP blocks (p,d) =
      SOME (bb0,bt0,ps0,xs0,ys0,rho0,in0,h0,NONE,0,OK s,F,NONE) /\
    (!i. i <= LENGTH p ==>
      ?sf tf inc ent res nrest.
        FLOOKUP acts (DROP i p) = SOME (sf,tf,inc,ent,EL i orders,res,nrest)) /\
    (!i. i < LENGTH p ==>
      ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done_at_call child_entry call_h.
        FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,OK b0,F,NONE) /\
        FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
          SOME (EL i inds,call_h,b0,done_at_call,child_entry,NONE) /\
        dft_fn_rel sf tf /\
        lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
        lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
        bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
        EVERY (\x. is_pseudo x.inst_opcode) ps /\
        EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ LENGTH xs = LENGTH ys /\
        PERM rho (COUNT_LIST (LENGTH xs)) /\
        LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
          from_block [EL q xs] y) rho ys /\
        EL i inds < LENGTH xs /\ (EL (EL i inds) xs).inst_opcode = INVOKE /\
        b0.vs_inst_idx = LENGTH ps + pos /\
        get_instruction bt b0.vs_inst_idx = SOME (EL (EL i inds) xs)) /\
    (!a sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      (res = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p))))) /\
    (!a e cid q h b done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done_at_call,child_entry,ret) ==>
      ?bb bt ps xs ys rho hin h0 be hbe pos front closed brest.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),pos,front,closed,brest) /\
        q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
        (case ret of
          NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
        | SOME triple => MEM q (TAKE pos rho))) /\
    (!a e cid q h b done ent ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,ent,ret) ==>
      ?row. FLOOKUP tab (a,e) = SOME row /\ q < LENGTH row /\
        EL q row = A ((e,cid)::a) /\
        cid = (EL q (FST (SND (SND (SND (THE (FLOOKUP blocks (a,e)))))))).inst_id) /\
    A = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    A' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    (out = tab \/
      ((!a e. (a,e) <> (p,d) /\
        (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
        FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
       (!i row. i < LENGTH p /\
         FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME row ==>
         FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
           SOME (LUPDATE
             (FLAT (MAP (\e. FLAT (THE (FLOOKUP out (DROP i p,e))))
               (EL i orders))) (EL i inds) row)))) /\
    acts' = acts /\ calls' = calls /\
    blocks' = blocks |+ ((p,d),
      (bb0,bt0,ps0,xs0,ys0,rho0,in0,h0,new_body,0,OK s1,F,NONE)) /\
    FLOOKUP acts p = SOME (sf0,tf0,inc0,ent0,ord0,NONE,NONE) /\ LAST ord0 = d /\
    (!a sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order)) /\
    (!k. k < LENGTH p ==>
      ?sf tf inc ent ord.
        FLOOKUP acts (DROP (SUC k) p) = SOME (sf,tf,inc,ent,ord,NONE,NONE) /\
        LAST ord = FST (EL k p)) /\
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
            (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call))) /\
    MAP (\(ai,ds,ei,qi,zi). ai) cuts =
      REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
    (!ai ei bb bt ps xs ys rho hin h be hbe pos front closed brest.
      FLOOKUP blocks (ai,ei) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,front,closed,brest) ==>
      ?row. FLOOKUP tab (ai,ei) = SOME row /\ LENGTH row = LENGTH xs) ==>
    ?rest. A' [] = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP tab (ai,ei))))) cuts) ++ rest
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dft_packet_pseudo_history_frame >> strip_tac >>
  `LENGTH cuts = SUC (LENGTH a)` by
    (qpat_assum `MAP _ cuts = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `cuts <> []` by (strip_tac >> fs[]) >>
  `GENLIST (\i. DROP i a) (SUC (LENGTH a)) <> []` by
    (strip_tac >> pop_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `FST (HD cuts) = []` by
    (qpat_x_assum `MAP _ cuts = _` (mp_tac o Q.AP_TERM `HD`) >>
     simp[HD_REVERSE, GENLIST_LAST, DROP_LENGTH_TOO_LONG] >>
     Cases_on `cuts` >> gvs[] >> rename1 `FST hd` >> PairCases_on `hd` >> simp[]) >>
  irule dft_packet_selected_cut_prefix >>
  rpt (first_assum (irule_at Any)) >>
  rpt gen_tac >> strip_tac >>
  drule_all dft_packet_pseudo_history_cut_frame >> strip_tac >>
  qpat_x_assum `!i ai ds ei qi zi. _` (drule_all_then strip_assume_tac) >>
  Cases_on `SUC i = LENGTH cuts`
  >- (qpat_x_assum `if _ then _ else _` mp_tac >> asm_rewrite_tac[] >> strip_tac >>
      Cases_on `bei` >- fs[] >> PairCases_on `x` >>
      qpat_x_assum `!ai ei bb bt ps xs ys rho hin h be hbe pos front closed brest.
        _ ==> ?row. _` (drule_then strip_assume_tac) >>
      `(a,e) <> (p,d)` by (strip_tac >> gvs[]) >>
      `?row'. FLOOKUP out (a,e) = SOME row' /\ LENGTH row' = LENGTH row` by
        (Cases_on `out = tab` >- metis_tac[] >>
         qpat_x_assum `out = tab \/ _` strip_assume_tac >>
         Cases_on `?k. k < LENGTH p /\ (a,e) = (DROP (SUC k) p,FST (EL k p))`
         >- (pop_assum strip_assume_tac >> gvs[] >> metis_tac[LENGTH_LUPDATE]) >>
         metis_tac[]) >>
      rpt (first_assum (irule_at Any)) >> simp[] >> gvs[]) >>
  fs[] >>
  qpat_x_assum `!a e cid q h b done ent ret.
    _ ==> ?row. FLOOKUP out _ = _ /\ _` (drule_then strip_assume_tac) >>
  rpt (first_assum (irule_at Any)) >> simp[] >>
  `FST (EL (SUC i) cuts) = (ei,(EL qi xsi).inst_id)::ai` by
    (qpat_x_assum `EL _ (MAP _ cuts) = _` mp_tac >>
     simp[EL_MAP] >>
     qmatch_goalsub_abbrev_tac `FST next` >> PairCases_on `next` >> simp[]) >>
  gvs[]
QED
