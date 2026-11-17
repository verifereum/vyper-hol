Theory dftPacketPseudoPrefixFrame
Ancestors
  dftPacketPseudoHistory dftPacketExistingPathRows dftPacketTableSplice list rich_list finite_map
  arithmetic pred_set

Theorem pseudo_eligible_bound[local]:
  !xs sched pos liveq k.
    ALL_DISTINCT sched /\ pos < LENGTH sched /\ liveq = EL pos sched /\
    (EL liveq xs).inst_opcode = INVOKE /\
    (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==>
      MEM q (TAKE pos sched)) ==>
    k <= liveq
Proof
  rpt strip_tac >>
  `~MEM liveq (TAKE pos sched)` by
    (strip_tac >>
     `?r. r < pos /\ EL r sched = liveq` by
       (gvs[MEM_EL,LENGTH_TAKE,EL_TAKE] >> metis_tac[]) >>
     `r < LENGTH sched` by decide_tac >>
     `r = pos` by metis_tac[EL_ALL_DISTINCT_EL_EQ] >> decide_tac) >>
  Cases_on `k <= liveq` >- simp[] >>
  `liveq < k` by decide_tac >> metis_tac[]
QED

(* The live-row premises are the structural projections of the old block,
   immutable-call and live-parent clauses.  In particular inds is fixed by
   the immutable calls, not chosen for the table update. *)
Theorem dft_packet_pseudo_prefix_frame:
  !(blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    p d inds (tab:(((num # num) list # num),'v list list) fmap) out
    bb0 bt0 ps0 xs0 ys0 rho0 in0 h0 s.
    LENGTH inds = LENGTH p /\
    FLOOKUP blocks (p,d) =
      SOME (bb0,bt0,ps0,xs0,ys0,rho0,in0,h0,NONE,0,OK s,F,NONE) /\
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
    (!a e cid q h b done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done_at_call,child_entry,ret) ==>
      ?bb bt ps xs ys rho hin h0 be hbe pos front closed brest.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),pos,front,closed,brest) /\
        q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
        (case ret of
          NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
        | SOME triple => MEM q (TAKE pos rho))) /\
    (!a e. (a,e) <> (p,d) /\
      (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!i. i < LENGTH p ==>
      ?rows v. FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME rows /\
        FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE v (EL i inds) rows)) ==>
    (!a e. (a,e) <> (p,d) /\
      (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!a e bb bt ps xs ys rho hin h be hbe pos front closed brest k.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,front,closed,brest) /\
      k <= LENGTH xs /\ EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k xs) /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE pos rho)) ==>
      TAKE k (THE (FLOOKUP out (a,e))) = TAKE k (THE (FLOOKUP tab (a,e))) /\
      (!i. i < LENGTH p /\ (a,e) = (DROP (SUC i) p,FST (EL i p)) ==>
        k <= EL i inds)) /\
    (!a e cid q h b done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done_at_call,child_entry,ret) ==>
      TAKE q (THE (FLOOKUP out (a,e))) = TAKE q (THE (FLOOKUP tab (a,e))) /\
      (!i. i < LENGTH p /\ (a,e) = (DROP (SUC i) p,FST (EL i p)) ==>
        q <= EL i inds))
Proof
  rpt gen_tac >> strip_tac >>
  `!i bb bt ps xs ys rho hin h be hbe pos front closed brest.
    i < LENGTH p /\
    FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,front,closed,brest) ==>
    (!k. (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==>
      MEM q (TAKE pos rho)) ==> k <= EL i inds) /\
    (!cid q ch b done_at_call child_entry ret.
      FLOOKUP calls (DROP (SUC i) p,FST (EL i p),cid) =
        SOME (q,ch,b,done_at_call,child_entry,ret) ==> q <= EL i inds)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH p ==> ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done_at_call child_entry call_h. _`
       (drule_then strip_assume_tac) >> gvs[] >>
     rename1 `PERM sched (COUNT_LIST _)` >>
     conj_tac
     >- (`ALL_DISTINCT (MAP (\x. x.inst_id) xs) /\ ALL_DISTINCT sched /\
           LENGTH sched = LENGTH ys /\ pos < LENGTH ys /\ EL i inds = EL pos sched` by
           (match_mp_tac dft_packet_history_suspended_schedule >>
            rpt (first_assum (irule_at Any)) >> simp[ADD_COMM] >> metis_tac[]) >>
         rpt strip_tac >> irule pseudo_eligible_bound >>
         rpt (first_assum (irule_at Any)) >> simp[] >> metis_tac[]) >>
     rpt gen_tac >> disch_tac >>
     irule (cj 1 dft_packet_history_recorded_call_bound) >>
     rpt (first_assum (irule_at Any)) >>
     qexistsl [`sched`,`call_h`,`child_entry`,`done_at_call`,`SND (EL i p)`,`pos`,`b0`] >>
     simp[ADD_COMM] >> rpt strip_tac >>
     qpat_x_assum `!a e cid q h b done_at_call child_entry ret. _`
       (drule_then strip_assume_tac) >> gvs[]) >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `(a,e) <> (p,d)` by (strip_tac >> gvs[]) >>
      Cases_on `?i. i < LENGTH p /\ (a,e) = (DROP (SUC i) p,FST (EL i p))`
      >- (pop_assum strip_assume_tac >> gvs[] >>
          `k <= EL i inds` by metis_tac[] >>
          conj_tac >- (qpat_x_assum `!i. i < LENGTH p ==> ?rows v. _`
              (drule_then strip_assume_tac) >>
            simp[dft_packet_row_prefix_splice]) >> metis_tac[]) >>
      simp[] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  `(a,e) <> (p,d)` by
    (strip_tac >> gvs[] >>
     qpat_x_assum `!a e cid q h b done_at_call child_entry ret. _`
       (drule_then strip_assume_tac) >> gvs[]) >>
  Cases_on `?i. i < LENGTH p /\ (a,e) = (DROP (SUC i) p,FST (EL i p))`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      `q <= EL i inds` by metis_tac[] >>
      conj_tac >- (qpat_x_assum `!i. i < LENGTH p ==> ?rows v. _`
              (drule_then strip_assume_tac) >>
        simp[dft_packet_row_prefix_splice]) >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

(* Completed records cannot be any of the open rows modified along the live
   suffix path.  This interface is polymorphic in the retained cell type. *)
Theorem dft_packet_pseudo_closed_table_frame:
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
    p d (tab:(((num # num) list # num),'v list list) fmap) out A A'
    bb0 bt0 ps0 xs0 ys0 rho0 in0 h0 s.
    FLOOKUP blocks (p,d) =
      SOME (bb0,bt0,ps0,xs0,ys0,rho0,in0,h0,NONE,0,OK s,F,NONE) /\
    (!i. i < LENGTH p ==>
      ?bb bt ps xs ys rho hin h be hbe pos b0.
        FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,OK b0,F,NONE)) /\
    (!a sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      (res = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p))))) /\
    (!a e cid q h b done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done_at_call,child_entry,ret) ==>
      ?bb bt ps xs ys rho hin h0 be hbe pos front closed brest.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),pos,front,closed,brest)) /\
    (!a e. (a,e) <> (p,d) /\
      (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    A = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    A' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) ==>
    (!a e bb bt ps xs ys rho hin h body pos front brest.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,body,pos,front,T,brest) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!a sf tf inc entry order r8 nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,nrest) ==>
      (!e. FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\ A' a = A a) /\
    (!cid. FLOOKUP calls (p,d,cid) = NONE)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_x_assum `!a e. _ ==> FLOOKUP out _ = _` irule >>
      rpt strip_tac >> gvs[] >>
      qpat_x_assum `!i. i < LENGTH p ==> ?bb bt ps xs ys rho hin h be hbe pos b0. _`
        (drule_then strip_assume_tac) >> gvs[]) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `~MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p)))` by
        (qpat_x_assum `!a sf tf inc entry order res nrest. _`
          (drule_then mp_tac) >> simp[]) >>
      `!i. i <= LENGTH p ==> a <> DROP i p` by
        (qpat_x_assum `~MEM a _` mp_tac >>
         simp[MEM_GENLIST,LESS_EQ_IFF_LESS_SUC] >> metis_tac[]) >>
      `!e. FLOOKUP out (a,e) = FLOOKUP tab (a,e)` by
        (gen_tac >> qpat_x_assum `!a e. _ ==> FLOOKUP out _ = _` match_mp_tac >>
         conj_tac
         >- (qpat_x_assum `!i. i <= LENGTH p ==> a <> DROP i p`
               (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
         rpt strip_tac >>
         qpat_x_assum `!i. i <= LENGTH p ==> a <> DROP i p`
           (qspec_then `SUC i` mp_tac) >> gvs[]) >>
      simp[]) >>
  irule dft_packet_pseudo_no_recorded_call >>
  rpt (first_assum (irule_at Any)) >> simp[] >> first_assum ACCEPT_TAC
QED
