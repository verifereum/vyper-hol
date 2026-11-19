Theory dftPacketBlockReplayFrame
Ancestors
  dftPacketBlockReplayStructure dftPacketBlockReplayUQ dftPacketBlockReplayClosed
  dftPacketPseudoHistory dftGasFromListTraceDefs
  list rich_list finite_map arithmetic pred_set

(* A pending child has a nonempty live suffix as its address.  Reading the
   head and tail of that suffix recovers its one update coordinate. *)
Theorem block_replay_pending_index[local]:
  !(p:(num # num) list) a e cid.
    MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p))) ==>
    ?i. i < LENGTH p /\ a = DROP (SUC i) p /\ (e,cid) = EL i p /\
        (e,cid)::a = DROP i p
Proof
  simp[MEM_GENLIST] >> rpt strip_tac >> rename1 `_::_ = DROP k p` >>
  `k < LENGTH p` by
    (qpat_x_assum `_::_ = DROP _ _`
       (mp_tac o AP_TERM ``LENGTH:(num # num) list -> num``) >> simp[]) >>
  qexists `k` >> simp[] >>
  qpat_x_assum `_::_ = DROP _ _` mp_tac >>
  simp[Once DROP_CONS_EL]
QED

(* Each table's exact update determines which cells can change.  In the
   changed case, the call's immutable source index and unique instruction
   ID connect the update to the final child's aggregate. *)
Theorem block_replay_cell_frame[local]:
  !(calls:(gas_event,num # num # venom_state # num list # venom_state #
       (internal_return # venom_state # venom_state) option) fmap)
    p d inds (tab:(((num # num) list # num),'v list list) fmap) out A
    a e xs old_rows rows q.
    (a,e) <> (p,SUC d) /\
    FLOOKUP tab (a,e) = SOME old_rows /\ FLOOKUP out (a,e) = SOME rows /\
    LENGTH old_rows = LENGTH xs /\ q < LENGTH xs /\
    ALL_DISTINCT (MAP (\i:instruction. i.inst_id) xs) /\
    (!i. i < LENGTH p ==>
      ?h b done child.
        FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
          SOME (EL i inds,h,b,done,child,NONE)) /\
    (!cid r h b done child.
      FLOOKUP calls (a,e,cid) = SOME (r,h,b,done,child,NONE) ==>
      r < LENGTH xs /\ (EL r xs).inst_id = cid /\
      MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))) /\
    (!a e. (a,e) <> (p,SUC d) /\
      (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!i row. i < LENGTH p /\
      FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME row ==>
      FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
        SOME (LUPDATE (A (DROP i p)) (EL i inds) row)) ==>
    (if (?r h b done child. FLOOKUP calls (a,e,(EL q xs).inst_id) =
        SOME (r,h,b,done,child,NONE)) then
       EL q rows = A ((e,(EL q xs).inst_id)::a)
     else EL q rows = EL q old_rows)
Proof
  rpt gen_tac >> strip_tac >> IF_CASES_TAC
  >- (pop_assum strip_assume_tac >>
      qpat_assum `!cid r h b done child. _` (drule_then strip_assume_tac) >>
      `r = q` by metis_tac[ALL_DISTINCT_EL_IMP,EL_MAP,LENGTH_MAP] >>
      drule_then strip_assume_tac block_replay_pending_index >>
      qpat_assum `!i. i < LENGTH p ==> ?h b done child. _`
        (drule_then strip_assume_tac) >>
      `FST (EL i p) = e /\ SND (EL i p) = (EL q xs).inst_id` by metis_tac[pairTheory.FST,pairTheory.SND] >>
      `rows = LUPDATE (A (DROP i p)) (EL i inds) old_rows` by
        (qpat_x_assum `!i row. _` (qspecl_then [`i`,`old_rows`] mp_tac) >>
         (impl_tac >- gvs[]) >> disch_tac >> metis_tac[optionTheory.SOME_11]) >>
      gvs[EL_LUPDATE]) >>
  Cases_on `?i. i < LENGTH p /\ (a,e) = (DROP (SUC i) p,FST (EL i p))`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      qpat_assum `!i. i < LENGTH p ==> ?h b done child. _`
        (qspecl_then [`i`] mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
      `EL i inds <> q` by
        (strip_tac >>
         `FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
           SOME (q,h,b,done,child,NONE)` by simp[pairTheory.PAIR] >>
         qpat_assum `!cid r h b done child. _` (drule_then strip_assume_tac) >>
         metis_tac[]) >>
      `rows = LUPDATE (A (DROP i p)) (EL i inds) old_rows` by
        (qpat_x_assum `!i row. _` (qspecl_then [`i`,`old_rows`] mp_tac) >>
         (impl_tac >- gvs[]) >> disch_tac >> metis_tac[optionTheory.SOME_11]) >>
      gvs[EL_LUPDATE]) >>
  `FLOOKUP out (a,e) = FLOOKUP tab (a,e)` by metis_tac[] >> gvs[]
QED

(* The activation append changes only the order.  In particular a final
   completed activation is an old completed activation, not the append. *)
Theorem block_replay_acts_frame[local]:
  !acts acts' (p:(num # num) list) (sf0:ir_function) (tf0:ir_function)
    (inc0:num) (entry0:venom_state) (order0:num list) d.
  FLOOKUP acts p = SOME (sf0,tf0,inc0,entry0,order0,NONE:exec_result option,NONE:bytes32 list option) /\
  acts' = acts |+ (p,(sf0,tf0,inc0,entry0,order0 ++ [SUC d],NONE,NONE)) ==>
  (!a. a <> p ==> FLOOKUP acts' a = FLOOKUP acts a) /\
  (!a sf tf inc entry order res rest.
    FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,rest) ==>
    ?ord. FLOOKUP acts a = SOME (sf,tf,inc,entry,ord,res,rest)) /\
  (!a sf tf inc entry order r8 nrest.
    FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,SOME r8,nrest) ==>
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,nrest))
Proof
  rpt gen_tac >> strip_tac >> conj_tac >- simp[FLOOKUP_UPDATE] >>
  conj_tac >> rpt gen_tac >> Cases_on `a = p` >> gvs[FLOOKUP_UPDATE]
QED

(* The closing update preserves the part of the record read by Q.
   A fresh lookup cannot be selected by any old call record. *)
Theorem block_replay_blocks_frame[local]:
  !blocks blocks' (p:(num # num) list) d
    (bb0:basic_block) (bt0:basic_block) (ps0:instruction list)
    (xs0:instruction list) (ys0:instruction list) (rho0:num list)
    (hin0:venom_state) (h0:num) (be0:venom_state) (hb0:num) cnt0
    (s:venom_state) (post:venom_state)
    bb1 bt1 ps1 xs1 ys1 rho1 hin1 h1 body1 front1.
  FLOOKUP blocks (p,d) =
    SOME (bb0,bt0,ps0,xs0,ys0,rho0,hin0,h0,SOME (be0,hb0),cnt0,OK s,F,NONE:bytes32 list option) /\
  blocks' =
    (blocks |+ ((p,d),(bb0,bt0,ps0,xs0,ys0,rho0,hin0,h0,SOME (be0,hb0),
                         LENGTH ys0,OK post,T,SOME post.vs_gas_readings))) |+
      ((p,SUC d),(bb1,bt1,ps1,xs1,ys1,rho1,hin1,h1,body1,0,OK front1,F,NONE)) ==>
  (!a e. (a,e) <> (p,d) /\ (a,e) <> (p,SUC d) ==>
    FLOOKUP blocks' (a,e) = FLOOKUP blocks (a,e)) /\
  (!a e bb bt ps xs ys rho hin h be hb cnt front closed rest.
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,front,closed,rest) /\
    (a,e) <> (p,SUC d) ==>
    ?oc ofr ocl ors.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),oc,ofr,ocl,ors)) /\
  (!a e bb bt ps xs ys rho hin h body cnt front rest.
    FLOOKUP blocks' (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,body,cnt,front,T,rest) /\
    (a,e) <> (p,d) ==>
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,body,cnt,front,T,rest))
Proof
  rpt gen_tac >> strip_tac >> conj_asm1_tac
  >- (rpt gen_tac >> strip_tac >> simp[FLOOKUP_UPDATE,EQ_SYM_EQ]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `(a,e) = (p,d)`
      >- (fs[] >>
          qpat_x_assum `FLOOKUP blocks' (p,d) = _` mp_tac >>
          simp[FLOOKUP_UPDATE] >> strip_tac >>
          qexistsl_tac [`cnt0`,`OK s`,`F`,`NONE`] >> simp[]) >>
      `FLOOKUP blocks' (a,e) = FLOOKUP blocks (a,e)` by metis_tac[] >>
      qexistsl_tac [`cnt`,`front`,`closed`,`rest`] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `(a,e) = (p,SUC d)`
  >- (fs[] >> qpat_x_assum `FLOOKUP blocks' (p,SUC d) = _` mp_tac >>
      simp[FLOOKUP_UPDATE]) >>
  `FLOOKUP blocks' (a,e) = FLOOKUP blocks (a,e)` by metis_tac[] >> metis_tac[]
QED

(* Prefix exclusion and completed-record framing are independent of the
   cell type. The value written at each suspended row is the final child
   aggregate, not the child's value before appending the new visit. *)
Theorem block_replay_table_frame[local]:
  !(acts:((num # num) list, ir_function # ir_function # num # venom_state #
      num list # exec_result option # bytes32 list option) fmap) acts'
    (blocks:(((num # num) list # num), basic_block # basic_block #
      instruction list # instruction list # instruction list # num list #
      venom_state # num # (venom_state # num) option # num # exec_result #
      bool # bytes32 list option) fmap)
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
       (internal_return # venom_state # venom_state) option) fmap)
    p d inds (tab:(((num # num) list # num),'v list list) fmap) out A A'.
  (p,d) IN FDOM blocks /\ (p,SUC d) NOTIN FDOM blocks /\ FDOM tab = FDOM blocks /\
  (!i. i < LENGTH p ==>
    ?sf tf bb bt ps xs ys rho hin h be hb pos b0 done child ch.
      FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),pos,OK b0,F,NONE) /\
      FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
        SOME (EL i inds,ch,b0,done,child,NONE) /\
      dft_fn_rel sf tf /\ lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
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
  (!a e cid q h b done child ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
    ?bb bt ps xs ys rho hin h0 be hb pos front closed rest.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hb),pos,front,closed,rest) /\
      q < LENGTH xs /\ (EL q xs).inst_id = cid /\ (EL q xs).inst_opcode = INVOKE /\
      (case ret of NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
       | SOME triple => MEM q (TAKE pos rho))) /\
  (!a e bb bt ps xs ys rho hin h be hb pos front closed rest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),pos,front,closed,rest) ==>
    LENGTH (THE (FLOOKUP tab (a,e))) = LENGTH xs) /\
  (!a e bb bt ps xs ys rho hin h be hb pos front closed rest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),pos,front,closed,rest) ==>
    ALL_DISTINCT (MAP (\x. x.inst_id) xs)) /\
  (!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    (res = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p))))) /\
  (!a. a <> p ==> FLOOKUP acts' a = FLOOKUP acts a) /\
  (!a e. (a,e) <> (p,SUC d) /\
    (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
    FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
  (!i rows. i < LENGTH p /\
    FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME rows ==>
    FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
      SOME (LUPDATE (A' (DROP i p)) (EL i inds) rows)) /\
  A = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  A' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP out (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) ==>
  FLOOKUP out (p,d) = FLOOKUP tab (p,d) /\
  (!a e bb bt ps xs ys rho hin h be hb pos front closed rest k.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),pos,front,closed,rest) /\
    k <= LENGTH xs /\ EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k xs) /\
    (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE pos rho)) ==>
    TAKE k (THE (FLOOKUP out (a,e))) = TAKE k (THE (FLOOKUP tab (a,e)))) /\
  (!a e cid q h b done child ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
    TAKE q (THE (FLOOKUP out (a,e))) = TAKE q (THE (FLOOKUP tab (a,e)))) /\
  (!a e bb bt ps xs ys rho hin h body pos front rest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,body,pos,front,T,rest) ==>
    FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
  (!a sf tf inc entry order r8 nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,nrest) ==> A' a = A a) /\
  (!a e bb bt ps xs ys rho hin h be hb pos front closed rest old_rows rows q.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),pos,front,closed,rest) /\
    FLOOKUP tab (a,e) = SOME old_rows /\ FLOOKUP out (a,e) = SOME rows /\
    q < LENGTH xs ==>
    (if (?r ch b done child. FLOOKUP calls (a,e,(EL q xs).inst_id) =
        SOME (r,ch,b,done,child,NONE)) then EL q rows = A' ((e,(EL q xs).inst_id)::a)
     else EL q rows = EL q old_rows))
Proof
  rpt gen_tac >> strip_tac >>
  `!a e. (a,e) IN FDOM blocks ==> ?rows. FLOOKUP tab (a,e) = SOME rows` by
    (simp[flookup_thm]) >>
  `!i. i < LENGTH p ==>
    ?rows v. FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME rows /\
      FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
        SOME (LUPDATE v (EL i inds) rows)` by
    (rpt strip_tac >>
     qpat_assum `!i. i < LENGTH p ==> ?sf tf bb bt ps xs ys rho hin h be hb pos b0 done child ch. _`
       (drule_then strip_assume_tac) >>
     `(DROP (SUC i) p,FST (EL i p)) IN FDOM blocks` by
       metis_tac[FLOOKUP_DEF,optionTheory.NOT_SOME_NONE] >>
     qpat_assum `!a e. (a,e) IN FDOM blocks ==> _` (drule_then strip_assume_tac) >>
     qexistsl_tac [`rows`,`A' (DROP i p)`] >> simp[]) >>
  (* Obtain all three prefix conclusions in a single application. *)
  `FLOOKUP out (p,d) = FLOOKUP tab (p,d) /\
   (!a e bb bt ps xs ys rho hin h be hb pos front closed rest k.
     FLOOKUP blocks (a,e) =
       SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),pos,front,closed,rest) /\
     k <= LENGTH xs /\ EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k xs) /\
     (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE pos rho)) ==>
     TAKE k (THE (FLOOKUP out (a,e))) = TAKE k (THE (FLOOKUP tab (a,e)))) /\
   (!a e cid q h b done child ret.
     FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
     TAKE q (THE (FLOOKUP out (a,e))) = TAKE q (THE (FLOOKUP tab (a,e))))` by
    (match_mp_tac dft_packet_block_prefix_frame >>
     qexists_tac `inds` >>
     rpt (first_assum (irule_at Any)) >> simp[] >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!a e cid q h b done child ret. _`
       (drule_then strip_assume_tac) >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  `(!a e bb bt ps xs ys rho hin h body pos front rest.
     FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,body,pos,front,T,rest) ==>
     FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
   (!a sf tf inc entry order r8 nrest.
     FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,nrest) ==>
     FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,SOME r8,nrest) /\
     (!e. FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\ A' a = A a)` by
    (match_mp_tac dft_packet_block_closed_frame >>
     qexistsl_tac [`p`,`d`] >>
     rpt (first_assum (irule_at Any)) >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!i. i < LENGTH p ==> ?sf tf bb bt ps xs ys rho hin h be hb pos b0 done child ch. _`
       (drule_then strip_assume_tac) >>
     rpt (first_assum (irule_at Any))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  match_mp_tac block_replay_cell_frame >>
  qexistsl_tac [`p`,`d`,`inds`,`tab`,`out`] >>
  rpt (first_assum (irule_at Any)) >> conj_tac
  >- (strip_tac >> gvs[FLOOKUP_DEF]) >>
  qpat_assum `!a e bb bt ps xs ys rho hin h be hb pos front closed rest. _ ==> LENGTH _ = _`
    (drule_then (fn th =>
      qpat_assum `FLOOKUP tab (a,e) = SOME old_rows`
        (assume_tac o (fn eq => SIMP_RULE bool_ss [eq,optionTheory.THE_DEF] th)))) >>
  qpat_assum `!a e bb bt ps xs ys rho hin h be hb pos front closed rest. _ ==> ALL_DISTINCT _`
    (drule_then assume_tac) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!i. i < LENGTH p ==> ?sf tf bb bt ps xs ys rho hin h be hb pos b0 done child ch. _`
        (drule_then strip_assume_tac) >>
      qexistsl_tac [`ch`,`b0`,`done`,`child`] >>
      qpat_assum `FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) = SOME _`
        (ACCEPT_TAC o REWRITE_RULE [pairTheory.PAIR])) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!a e cid q h b done child ret. _ ==> ?bb bt ps xs ys rho hin h0 be hb pos front closed rest. _`
    (drule_then strip_assume_tac) >>
  gvs[]
QED

(* The five semantic transports all use this common structural projection.
   The old row is selected by the new record, except at the two local cases.
   Q is the only transport that also reads the closed replacement record. *)
Theorem block_replay_selected_rows[local]:
  !p d blocks blocks' calls
    (tab:(((num # num) list # num),'v list list) fmap) out A'.
  FDOM tab = FDOM blocks /\ (p,SUC d) NOTIN FDOM blocks /\
  (!a e. (a,e) <> (p,d) /\ (a,e) <> (p,SUC d) ==>
    FLOOKUP blocks' (a,e) = FLOOKUP blocks (a,e)) /\
  (!a e bb bt ps xs ys rho hin h be hb cnt front closed rest.
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,front,closed,rest) /\
    (a,e) <> (p,SUC d) ==>
    ?oc ofr ocl ors. FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),oc,ofr,ocl,ors)) /\
  (!a e bb bt ps xs ys rho hin h body cnt front rest.
    FLOOKUP blocks' (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,body,cnt,front,T,rest) /\
    (a,e) <> (p,d) ==>
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,body,cnt,front,T,rest)) /\
  (!a e cid q h b done child ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==> (a,e) IN FDOM blocks) /\
  (!a e bb bt ps xs ys rho hin h be hb pos front closed rest k.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),pos,front,closed,rest) /\
    k <= LENGTH xs /\ EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k xs) /\
    (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE pos rho)) ==>
    TAKE k (THE (FLOOKUP out (a,e))) = TAKE k (THE (FLOOKUP tab (a,e)))) /\
  (!a e cid q h b done child ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
    TAKE q (THE (FLOOKUP out (a,e))) = TAKE q (THE (FLOOKUP tab (a,e)))) /\
  (!a e bb bt ps xs ys rho hin h body pos front rest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,body,pos,front,T,rest) ==>
    FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
  (!a e bb bt ps xs ys rho hin h be hb pos front closed rest old_rows rows q.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),pos,front,closed,rest) /\
    FLOOKUP tab (a,e) = SOME old_rows /\ FLOOKUP out (a,e) = SOME rows /\
    q < LENGTH xs ==>
    (if (?r ch b done child. FLOOKUP calls (a,e,(EL q xs).inst_id) =
        SOME (r,ch,b,done,child,NONE)) then EL q rows = A' ((e,(EL q xs).inst_id)::a)
     else EL q rows = EL q old_rows)) ==>
  (!a e bb bt ps xs ys rho hin h be hb pos front closed rest.
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),pos,front,closed,rest) /\
    (a,e) <> (p,d) /\ (a,e) <> (p,SUC d) ==>
    ?old_rows. FLOOKUP tab (a,e) = SOME old_rows /\
      (!k. k <= LENGTH xs /\ EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k xs) /\
        (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE pos rho)) ==>
        TAKE k (THE (FLOOKUP out (a,e))) = TAKE k old_rows) /\
      (!rows q. FLOOKUP out (a,e) = SOME rows /\ q < LENGTH xs ==>
        (if (?r ch b done child. FLOOKUP calls (a,e,(EL q xs).inst_id) =
             SOME (r,ch,b,done,child,NONE)) then EL q rows = A' ((e,(EL q xs).inst_id)::a)
         else EL q rows = EL q old_rows))) /\
  (!a e cid q h b done child ret bb bt ps xs ys rho hin h0 be hb pos front closed rest rows.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) /\
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hb),pos,front,closed,rest) /\
    FLOOKUP out (a,e) = SOME rows ==>
    ?oc ofr ocl ors old_rows. FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hb),oc,ofr,ocl,ors) /\
      FLOOKUP tab (a,e) = SOME old_rows /\ TAKE q rows = TAKE q old_rows) /\
  (!a e bb bt ps xs ys rho hin h body pos front rest rows.
    FLOOKUP blocks' (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,body,pos,front,T,rest) /\
    FLOOKUP out (a,e) = SOME rows /\ (a,e) <> (p,d) ==>
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,body,pos,front,T,rest) /\
    FLOOKUP tab (a,e) = SOME rows)
Proof
  rpt gen_tac >> strip_tac >>
  `!a e. (a,e) IN FDOM blocks ==> ?rows. FLOOKUP tab (a,e) = SOME rows` by
    simp[flookup_thm] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!a e. _ /\ _ ==> FLOOKUP blocks' _ = _`
        (drule_all_then (fn eq =>
          qpat_assum `FLOOKUP blocks' (a,e) = SOME _`
            (assume_tac o REWRITE_RULE [eq]))) >>
      `(a,e) IN FDOM blocks` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_SOME_NONE] >>
      qpat_assum `!a e. _ IN FDOM blocks ==> ?rows. _` (drule_then strip_assume_tac) >>
      qexists `rows` >> conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          qpat_assum `!a e bb bt ps xs ys rho hin h be hb pos front closed rest k. _`
            (drule_all_then mp_tac) >> simp[]) >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!a e bb bt ps xs ys rho hin h be hb pos front closed rest old_rows rows q. _`
        (drule_all_then ACCEPT_TAC)) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!a e cid q h b done child ret. _ ==> _ IN FDOM blocks`
        (drule_then assume_tac) >>
      `(a,e) <> (p,SUC d)` by metis_tac[] >>
      qpat_assum `!a e bb bt ps xs ys rho hin h be hb cnt front closed rest. _`
        (drule_all_then strip_assume_tac) >>
      qpat_assum `!a e. _ IN FDOM blocks ==> ?rows. _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!a e cid q h b done child ret. _ ==> TAKE q _ = _`
        (drule_then mp_tac) >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!a e bb bt ps xs ys rho hin h body cnt front rest. FLOOKUP blocks' _ = _ /\ _ ==> _`
    (drule_all_then assume_tac) >>
  qpat_assum `!a e bb bt ps xs ys rho hin h body pos front rest. FLOOKUP blocks _ = _ ==> _`
    (drule_then assume_tac) >> gvs[]
QED

(* The three aggregate functions are obtained from the same final orders.
   Use the local lambdas only to share the literal replay formulas between
   the old, exceptional, and final clause instances. *)
Theorem dft_packet_block_replay_frame:
  !N N' C7 C8 p d inds
    (acts:((num # num) list,ir_function # ir_function # num # venom_state #
      num list # exec_result option # bytes32 list option) fmap) acts'
    (blocks:(((num # num) list # num),basic_block # basic_block #
      instruction list # instruction list # instruction list # num list #
      venom_state # num # (venom_state # num) option # num # exec_result #
      bool # bytes32 list option) fmap) blocks'
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    ms_tab es_tab ks_tab ms_out es_out ks_out AM AE AK AM' AE' AK'
    sf0 tf0 inc0 entry0 order0 bb0 bt0 ps0 xs0 ys0 rho0 hin0 h0 be0 hb0 cnt0 s post
    bb1 bt1 ps1 xs1 ys1 rho1 hin1 h1 body1 front1
    U Q R A inv_cells W all exceptions.
  U = (\H acts0 blocks0 m es ks at.
    !a e bb bt ps xs ys rho hin h be hb count front closed brest ms ess keys
        sf tf inc entry order res nrest.
      at a e /\ FLOOKUP blocks0 (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),count,front,closed,brest) /\
      FLOOKUP m (a,e) = SOME ms /\ FLOOKUP es (a,e) = SOME ess /\
      FLOOKUP ks (a,e) = SOME keys /\
      FLOOKUP acts0 a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      !F k kgss tail.
        H <= F /\ k <= LENGTH xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
        (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE count rho)) /\
        LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
        (?extra. FLAT (TAKE k ess) = gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
        (!u. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
          gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
          u.vs_gas_readings = tail /\
          dftGasFromListTraceDefs$trace_gas
            (dftGasFromListTraceDefs$trace_block a e (F-e) C7 sf
              (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
              (be with vs_gas_readings := FLAT kgss ++ tail)) =
            ZIP (FLAT (TAKE k keys),FLAT kgss) /\
          (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
              (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
              (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) ==>
  Q = (\H blocks0 m.
    !a e cid q h b0 done child ret bb bt ps xs ys rho hin hbe be hb count front closed brest ms.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child,ret) /\
      FLOOKUP blocks0 (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,hbe,SOME (be,hb),count,front,closed,brest) /\
      FLOOKUP m (a,e) = SOME ms ==>
      !F kgss tail u.
        H <= F /\ LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
        FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
        (!callee args. setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
          setup_callee callee args b0)) ==>
  R = (\H acts0 blocks0 m es ks at.
    !a e sf tf inc entry order res rest bb bt ps xs ys rho hin h be hb count r8 u0 ms ess keys.
      at a e /\ FLOOKUP acts0 a = SOME (sf,tf,inc,entry,order,res,rest) /\
      FLOOKUP blocks0 (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),count,r8,T,SOME u0) /\
      FLOOKUP m (a,e) = SOME ms /\ FLOOKUP es (a,e) = SOME ess /\ FLOOKUP ks (a,e) = SOME keys ==>
      terminates r8 /\
      PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ u0) be.vs_gas_readings /\
      (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==> EVERY IS_SOME (FLAT ms) /\ u0 = v.vs_gas_readings) /\
      (!F. H <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK ys be = r8 /\
        (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
          (?extra. FLAT ess = gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail) ++ extra) /\
          ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
              (be with vs_gas_readings := gs ++ tail))) ==>
            terminates (FOLDR (dft_exec_cons (F-e) C7) OK xs (be with vs_gas_readings := gs ++ tail)) /\
            dft_res_rel (restore_result [] (FOLDR (dft_exec_cons (F-e) C7) OK xs
              (be with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
            (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
              gas_events_block (F-e) C7 sf.fn_name
                <|bb_label := be.vs_current_bb; bb_instructions :=
                  REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
                (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
              residual_result tail r8 (FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail)))) /\
          (!v. (FOLDR (dft_exec_cons (F-e) C7) OK xs
                  (be with vs_gas_readings := gs ++ tail) = OK v \/
                ?ir. FOLDR (dft_exec_cons (F-e) C7) OK xs
                  (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
            dftGasFromListTraceDefs$trace_gas
              (dftGasFromListTraceDefs$trace_block a e (F-e) C7 sf
                <|bb_label := be.vs_current_bb; bb_instructions :=
                  REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
                (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT keys,gs))))) ==>
  A = (\H acts0 am ae ak.
    !a sf tf inc entry order r8 u0.
      FLOOKUP acts0 a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
      terminates r8 /\ LENGTH (am a) = LENGTH (ae a) /\ LENGTH (am a) = LENGTH (ak a) /\
      PERM (MAP THE (FILTER IS_SOME (am a)) ++ u0) entry.vs_gas_readings /\
      (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==> EVERY IS_SOME (am a) /\ u0 = v.vs_gas_readings) /\
      (!F. H <= F ==> run_blocks (F-inc) C8 tf entry = r8 /\
        (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (am a) gs ==>
          (?extra. ae a = gas_events_blocks (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
          ((?f. terminates (run_blocks f C7 sf (entry with vs_gas_readings := gs ++ tail))) ==>
            terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
            dft_res_rel (restore_result [] (run_blocks (F-inc) C7 sf
              (entry with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
            (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
              gas_events_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = ae a /\
              residual_result tail r8 (run_blocks (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail)))) /\
          (!v. (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = OK v \/
                ?ir. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
            dftGasFromListTraceDefs$trace_gas
              (dftGasFromListTraceDefs$trace_blocks a inc (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail)) = ZIP (ak a,gs))))) ==>
  inv_cells = (\blocks0 m es ks am ae ak at.
    !a e bb bt ps xs ys rho hin h be hb cnt front closed rest ms ess keys.
      at a e /\ FLOOKUP blocks0 (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,front,closed,rest) /\
      FLOOKUP m (a,e) = SOME ms /\ FLOOKUP es (a,e) = SOME ess /\ FLOOKUP ks (a,e) = SOME keys ==>
      !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
        case FLOOKUP calls (a,e,(EL q xs).inst_id) of
          NONE => EL q ms = [] /\ EL q ess = [] /\ EL q keys = []
        | SOME call => EL q ms = am ((e,(EL q xs).inst_id)::a) /\
            EL q ess = ae ((e,(EL q xs).inst_id)::a) /\ EL q keys = ak ((e,(EL q xs).inst_id)::a)) ==>
  W = (\blocks0 at.
    !a e bb bt ps xs ys rho hin h be hb cnt front closed rest.
      at a e /\ FLOOKUP blocks0 (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,front,closed,rest) ==>
      !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE cnt rho) ==>
        ?ch b done child ir child_out caller_post.
          FLOOKUP calls (a,e,(EL q xs).inst_id) =
            SOME (q,ch,b,done,child,SOME (ir,child_out,caller_post))) ==>
  all = (\a e. T) ==>
  exceptions = (\a e. (a,e) = (p,d) \/ (a,e) = (p,SUC d)) ==>
  N <= N' /\
  FLOOKUP acts p = SOME (sf0,tf0,inc0,entry0,order0,NONE,NONE) /\
  acts' = acts |+ (p,(sf0,tf0,inc0,entry0,order0 ++ [SUC d],NONE,NONE)) /\
  FLOOKUP blocks (p,d) = SOME (bb0,bt0,ps0,xs0,ys0,rho0,hin0,h0,SOME (be0,hb0),cnt0,OK s,F,NONE) /\
  blocks' = (blocks |+ ((p,d),(bb0,bt0,ps0,xs0,ys0,rho0,hin0,h0,SOME (be0,hb0),
      LENGTH ys0,OK post,T,SOME post.vs_gas_readings))) |+
    ((p,SUC d),(bb1,bt1,ps1,xs1,ys1,rho1,hin1,h1,body1,0,OK front1,F,NONE)) /\
  (p,SUC d) NOTIN FDOM blocks /\ FDOM ms_tab = FDOM blocks /\
  FDOM es_tab = FDOM blocks /\ FDOM ks_tab = FDOM blocks /\
  (!i. i < LENGTH p ==>
    ?sf tf bb bt ps xs ys rho hin h be hb pos b0 done child ch.
      FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),pos,OK b0,F,NONE) /\
      FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
        SOME (EL i inds,ch,b0,done,child,NONE) /\
      dft_fn_rel sf tf /\ lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
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
  (!a e cid q h b done child ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
    ?bb bt ps xs ys rho hin h0 be hb pos front closed rest.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hb),pos,front,closed,rest) /\
      q < LENGTH xs /\ (EL q xs).inst_id = cid /\ (EL q xs).inst_opcode = INVOKE /\
      (case ret of NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
       | SOME triple => MEM q (TAKE pos rho))) /\
  (!a e bb bt ps xs ys rho hin h be hb pos front closed rest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),pos,front,closed,rest) ==>
    ALL_DISTINCT (MAP (\x. x.inst_id) xs) /\
    LENGTH (THE (FLOOKUP ms_tab (a,e))) = LENGTH xs /\
    LENGTH (THE (FLOOKUP es_tab (a,e))) = LENGTH xs /\
    LENGTH (THE (FLOOKUP ks_tab (a,e))) = LENGTH xs) /\
  (!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    (res = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p))))) /\
  (!a e. (a,e) <> (p,SUC d) /\
    (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
    FLOOKUP ms_out (a,e) = FLOOKUP ms_tab (a,e) /\
    FLOOKUP es_out (a,e) = FLOOKUP es_tab (a,e) /\
    FLOOKUP ks_out (a,e) = FLOOKUP ks_tab (a,e)) /\
  (!i rows. i < LENGTH p /\ FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME rows ==>
    FLOOKUP ms_out (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AM' (DROP i p)) (EL i inds) rows)) /\
  (!i rows. i < LENGTH p /\ FLOOKUP es_tab (DROP (SUC i) p,FST (EL i p)) = SOME rows ==>
    FLOOKUP es_out (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AE' (DROP i p)) (EL i inds) rows)) /\
  (!i rows. i < LENGTH p /\ FLOOKUP ks_tab (DROP (SUC i) p,FST (EL i p)) = SOME rows ==>
    FLOOKUP ks_out (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AK' (DROP i p)) (EL i inds) rows)) /\
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AE = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AM' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_out (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
  AE' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es_out (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
  AK' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_out (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
  (!a e cid q h b done child ir child_out caller_post.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,SOME (ir,child_out,caller_post)) ==>
    ?csf ctf order rest. FLOOKUP acts ((e,cid)::a) =
      SOME (csf,ctf,e,child,order,SOME (IntRet ir child_out),rest)) /\
  U N acts blocks ms_tab es_tab ks_tab all /\ Q N blocks ms_tab /\
  R N acts blocks ms_tab es_tab ks_tab all /\ A N acts AM AE AK /\
  inv_cells blocks ms_tab es_tab ks_tab AM AE AK all /\ W blocks all /\
  U N' acts' blocks' ms_out es_out ks_out exceptions /\
  R N' acts' blocks' ms_out es_out ks_out (\a e. (a,e) = (p,d)) /\
  inv_cells blocks' ms_out es_out ks_out AM' AE' AK' exceptions /\ W blocks' exceptions ==>
  U N' acts' blocks' ms_out es_out ks_out all /\ Q N' blocks' ms_out /\
  R N' acts' blocks' ms_out es_out ks_out all /\ A N' acts' AM' AE' AK' /\
  inv_cells blocks' ms_out es_out ks_out AM' AE' AK' all /\ W blocks' all
Proof
  rpt gen_tac >> ntac 8 (disch_then SUBST_ALL_TAC) >> BETA_TAC >> strip_tac >>
  drule_all_then strip_assume_tac block_replay_acts_frame >>
  drule_all_then strip_assume_tac block_replay_blocks_frame >>
  `(p,d) IN FDOM blocks` by
    (qpat_assum `FLOOKUP blocks (p,d) = SOME _`
       (ACCEPT_TAC o CONJUNCT1 o PURE_REWRITE_RULE [flookup_thm])) >>
  qpat_x_assum `!a e bb bt ps xs ys rho hin h be hb pos front closed rest. _ ==> ALL_DISTINCT _ /\ _`
    (fn th => map_every (fn i => assume_tac (cj i th)) [1,2,3,4]) >>
  qpat_x_assum `!a e. _ ==> FLOOKUP ms_out _ = _ /\ _`
    (fn th => map_every (fn i => assume_tac (cj i th)) [1,2,3]) >>
  map_every (fn ty =>
    drule_all_then strip_assume_tac (INST_TYPE [``:'v`` |-> ty] block_replay_table_frame))
    [``:bytes32 option``,``:string # num``,``:gas_event``] >>
  `!a e cid q h b done child ret.
     FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
     (a,e) IN FDOM blocks` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!a e cid q h b done child ret. _ ==> ?bb bt ps xs ys rho hin h0 be hb pos front closed rest. _`
       (drule_then strip_assume_tac) >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME _`
       (ACCEPT_TAC o CONJUNCT1 o PURE_REWRITE_RULE [flookup_thm])) >>
  map_every (fn ty =>
    drule_all_then strip_assume_tac (INST_TYPE [``:'v`` |-> ty] block_replay_selected_rows))
    [``:bytes32 option``,``:string # num``,``:gas_event``] >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> rewrite_tac [] >>
  rule_assum_tac (REWRITE_RULE [] o CONV_RULE (REDEPTH_CONV BETA_CONV)) >>
  conj_tac >- suspend "open_row" >>
  conj_tac >- suspend "caller" >>
  conj_tac >- suspend "closed_row" >>
  conj_tac >- suspend "closed_activation" >>
  suspend "invoke_and_completion"
QED

Resume dft_packet_block_replay_frame[caller]:
  match_mp_tac dft_packet_block_Q_frame >>
  qexistsl_tac [`N`,`blocks`,`ms_tab`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_block_replay_frame[open_row]:
  match_mp_tac dft_packet_block_U_frame >>
  qexistsl_tac [`N`,`p`,`d`,`acts`,`blocks`,`ms_tab`,`es_tab`,`ks_tab`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!a e bb bt ps xs ys rho hin h be hb pos front closed rest.
      _ ==> ?old_rows. FLOOKUP ms_tab (a,e) = SOME old_rows /\ _`
    (drule_all_then (qx_choose_then `ms` strip_assume_tac)) >>
  qpat_assum `!a e bb bt ps xs ys rho hin h be hb pos front closed rest.
      _ ==> ?old_rows. FLOOKUP es_tab (a,e) = SOME old_rows /\ _`
    (drule_all_then (qx_choose_then `ess` strip_assume_tac)) >>
  qpat_assum `!a e bb bt ps xs ys rho hin h be hb pos front closed rest.
      _ ==> ?old_rows. FLOOKUP ks_tab (a,e) = SOME old_rows /\ _`
    (drule_all_then (qx_choose_then `ks` strip_assume_tac)) >>
  qpat_assum `!a e. _ ==> FLOOKUP blocks' (a,e) = FLOOKUP blocks (a,e)`
    (drule_all_then (fn eq =>
      qpat_assum `FLOOKUP blocks' (a,e) = SOME _`
        (assume_tac o ONCE_REWRITE_RULE [eq]))) >>
  qexistsl_tac [`front`,`closed`,`brest`,`ms`,`ess`,`ks`] >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  gen_tac >> strip_tac >> rpt conj_tac >>
  first_assum (drule_all_then ACCEPT_TAC)
QED

Resume dft_packet_block_replay_frame[closed_row]:
  Q_TAC (fn args => match_mp_tac
    (ISPECL (pairSyntax.strip_pair args) dft_packet_block_closed_replay_frame))
    `(N,N',C7,C8,p,d,acts)` >>
  qexistsl_tac [`blocks`,`ms_tab`,`es_tab`,`ks_tab`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- (conj_tac
      >- (rpt gen_tac >> disch_tac >>
          qpat_assum `!a sf tf inc entry order res rest. FLOOKUP acts' a = _ ==> ?ord. _`
            (drule_then strip_assume_tac) >>
          qexistsl_tac [`ord`,`res`,`rest`] >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `!a e sf tf inc entry order res rest bb bt ps xs ys rho hin h be hb count r8 u0 ms ess keys.
          (a,e) = (p,d) /\ _ ==> _`
        (qspecl_then [`p`,`d`] (ACCEPT_TAC o REWRITE_RULE []))) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!a e bb bt ps xs ys rho hin h body pos front rest rows.
    FLOOKUP blocks' _ = _ /\ FLOOKUP ms_out _ = _ /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!a e bb bt ps xs ys rho hin h body pos front rest rows.
    FLOOKUP blocks' _ = _ /\ FLOOKUP es_out _ = _ /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!a e bb bt ps xs ys rho hin h body pos front rest rows.
    FLOOKUP blocks' _ = _ /\ FLOOKUP ks_out _ = _ /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_block_replay_frame[closed_activation]:
  Q_TAC (fn args => match_mp_tac
    (ISPECL (pairSyntax.strip_pair args) dft_packet_block_closed_activation_frame))
    `(N,N',C7,C8,acts)` >>
  qexistsl_tac [`AM`,`AE`,`AK`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!a sf tf inc entry order r8 nrest. FLOOKUP acts' a = _ ==> FLOOKUP acts a = _`
    (drule_then assume_tac) >>
  simp[]
QED

Resume dft_packet_block_replay_frame[invoke_and_completion]:
  Q_TAC (fn args => match_mp_tac
    (ISPECL (pairSyntax.strip_pair args) dft_packet_block_invoke_frame))
    `(p,d,acts,blocks)` >>
  qexistsl_tac [`AM`,`AE`,`AK`,`ms_tab`,`es_tab`,`ks_tab`] >>
  conj_tac >- suspend "unchanged_cells" >>
  conj_tac >- suspend "unchanged_completion_row" >>
  conj_tac >- suspend "pending_cells" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt gen_tac >> disch_tac >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!a e bb bt ps xs ys rho hin h be hb cnt front closed rest ms ess keys.
        ((a,e) = (p,d) \/ (a,e) = (p,SUC d)) /\ _ ==> _`
        (qspecl_then [`p`,`e`] (mp_tac o REWRITE_RULE [pairTheory.PAIR_EQ])) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!a e bb bt ps xs ys rho hin h be hb cnt front closed rest.
    ((a,e) = (p,d) \/ (a,e) = (p,SUC d)) /\ _ ==> _`
    (qspecl_then [`p`,`e`] (mp_tac o REWRITE_RULE [pairTheory.PAIR_EQ])) >> simp[]
QED

Resume dft_packet_block_replay_frame[unchanged_cells]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!a e. _ ==> FLOOKUP blocks' (a,e) = FLOOKUP blocks (a,e)`
    (drule_all_then (fn eq =>
      qpat_assum `FLOOKUP blocks' (a,e) = SOME _`
        (assume_tac o ONCE_REWRITE_RULE [eq]))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  map_every (fn (table,old) => Q_TAC (fn tab =>
    qpat_assum `!a e bb bt ps xs ys rho hin h be hb pos front closed rest.
      _ ==> ?old_rows. FLOOKUP ^tab (a,e) = SOME old_rows /\ _`
      (drule_all_then (qx_choose_then old strip_assume_tac))) table)
    [(`ms_tab`,`old_ms`),(`es_tab`,`old_es`),(`ks_tab`,`old_ks`)] >>
  qexistsl_tac [`old_ms`,`old_es`,`old_ks`] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  rpt conj_tac >>
  first_assum (drule_all_then (fn th =>
    qpat_assum `~(?cq ch b done child. FLOOKUP calls (a,e,(EL q xs).inst_id) =
      SOME (cq,ch,b,done,child,NONE))`
      (ACCEPT_TAC o (fn guard => REWRITE_RULE [guard] th))))
QED

Resume dft_packet_block_replay_frame[unchanged_completion_row]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!a e. _ ==> FLOOKUP blocks' (a,e) = FLOOKUP blocks (a,e)`
    (drule_all_then (fn eq =>
      qpat_assum `FLOOKUP blocks' (a,e) = SOME _`
        (ACCEPT_TAC o ONCE_REWRITE_RULE [eq])))
QED

Resume dft_packet_block_replay_frame[pending_cells]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  (* A pending call belongs to a strict ancestor, not either local row. *)
  qpat_assum `!a e cid q h b done child ret. _ ==> ?bb bt ps xs ys rho hin h0 be hb pos front closed rest. _`
    (drule_then (strip_assume_tac o REWRITE_RULE [optionTheory.option_case_def])) >>
  drule_then strip_assume_tac block_replay_pending_index >>
  `LENGTH a < LENGTH p` by simp[LENGTH_DROP] >>
  `a <> p` by
    (strip_tac >> qpat_assum `a = p` (fn eq =>
      qpat_assum `LENGTH a < LENGTH p` (mp_tac o ONCE_REWRITE_RULE [eq])) >> simp[NoAsms]) >>
  `(a,e) <> (p,d) /\ (a,e) <> (p,SUC d)` by
    (qpat_assum `a <> p` (fn ne => simp[NoAsms,ne,pairTheory.PAIR_EQ])) >>
  Q_TAC (fn guard => SUBGOAL_THEN guard assume_tac)
    `?r ch b done child. FLOOKUP calls (a,e,(EL q xs).inst_id) =
       SOME (r,ch,b,done,child,NONE)`
  >- first_assum (irule_at Any) >>
  map_every (fn (table,old) => Q_TAC (fn tab =>
    qpat_assum `!a e bb bt ps xs ys rho hin h be hb pos front closed rest.
      _ ==> ?old_rows. FLOOKUP ^tab (a,e) = SOME old_rows /\ _`
      (drule_all_then (qx_choose_then old strip_assume_tac))) table)
    [(`ms_tab`,`old_ms`),(`es_tab`,`old_es`),(`ks_tab`,`old_ks`)] >>
  rpt conj_tac >>
  first_assum (drule_all_then (fn th =>
    qpat_assum `?cq ch b done child. FLOOKUP calls (a,e,(EL q xs).inst_id) =
      SOME (cq,ch,b,done,child,NONE)`
      (ACCEPT_TAC o (fn guard => REWRITE_RULE [guard] th))))
QED

Finalise dft_packet_block_replay_frame
