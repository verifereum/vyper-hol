Theory dftPacketPseudoHistoryFrame
Ancestors
  dftPacketPseudoPrefixFrame dftPacketPseudoCutFrame dftPacketPseudoReplayFrame
  dftPacketExistingPathRows dftPacketPseudoCallCellFrame
  list rich_list finite_map arithmetic pred_set

Theorem dft_packet_pseudo_actual_order_payload:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (out:(((num # num) list # num),'v list list) fmap)
    a sf tf inc entry order res nrest A'.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    A' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) ==>
    FLAT (MAP (\e. FLAT (THE (FLOOKUP out (a,e)))) order) = A' a
Proof
  rpt strip_tac >> simp[]
QED

(* Only structural projections of old records occur here.  In particular the
   indices and orders in the final-map equations are certified by lookups. *)
Theorem dft_packet_pseudo_history_frame:
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
    bb0 bt0 ps0 xs0 ys0 rho0 in0 h0 s.
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
               (EL i orders))) (EL i inds) row)))) ==>
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
        q <= EL i inds)) /\
    (!a e bb bt ps xs ys rho hin h body pos front brest.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,body,pos,front,T,brest) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!a sf tf inc entry order r8 nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,nrest) ==>
      (!e. FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\ A' a = A a) /\
    (!a. ~MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p))) ==> A' a = A a) /\
    (!cid. FLOOKUP calls (p,d,cid) = NONE) /\
    (!a e cid q h b done ent ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,ent,ret) ==>
      ?row. FLOOKUP out (a,e) = SOME row /\ q < LENGTH row /\
        EL q row = A' ((e,cid)::a))
Proof
  rpt gen_tac >> strip_tac >>
  `!a e. (a,e) <> (p,d) /\
    (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
    FLOOKUP out (a,e) = FLOOKUP tab (a,e)` by metis_tac[] >>
  `!i. i < LENGTH p ==>
    ?rows v. FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME rows /\
      FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
        SOME (LUPDATE v (EL i inds) rows)` by
    (rpt strip_tac >>
     qpat_assum `!i. i < LENGTH p ==> ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done_at_call child_entry call_h. _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!a e cid q h b done ent ret. _ ==> ?row. FLOOKUP _ _ = SOME row /\ _`
       (drule_then strip_assume_tac) >>
     Cases_on `out = tab`
     >- (gvs[] >> qexists `EL (EL i inds) row` >>
         simp[LUPDATE_SAME]) >>
     qexistsl [`row`,`FLAT (MAP (\e. FLAT (THE (FLOOKUP out (DROP i p,e)))) (EL i orders))`] >>
     metis_tac[]) >>
  `!a. ~MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p))) ==> A' a = A a` by
    (rpt strip_tac >>
     `!i. i <= LENGTH p ==> a <> DROP i p` by
       (gvs[MEM_GENLIST,LESS_EQ_IFF_LESS_SUC] >> metis_tac[]) >>
     `a <> p` by
       (qpat_assum `!i. i <= LENGTH p ==> a <> DROP i p`
          (qspec_then `0` mp_tac) >> pure_rewrite_tac[DROP_0] >> metis_tac[ZERO_LESS_EQ]) >>
     `!i. i < LENGTH p ==> a <> DROP (SUC i) p` by
       (rpt strip_tac >>
        qpat_assum `!i. i <= LENGTH p ==> a <> DROP i p`
          (qspec_then `SUC i` mp_tac) >> metis_tac[LESS_EQ_IFF_LESS_SUC,LESS_MONO_EQ]) >>
     `!e. FLOOKUP out (a,e) = FLOOKUP tab (a,e)` by
       (gen_tac >> qpat_x_assum `!a e. _ ==> FLOOKUP out _ = _` irule >>
        metis_tac[pairTheory.PAIR_EQ]) >>
     simp[]) >>
  `!i row. i < LENGTH p /\
    FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME row ==>
    FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
      SOME (LUPDATE (A' (DROP i p)) (EL i inds) row)` by
    (rpt strip_tac >>
     qpat_assum `!i. i < LENGTH p ==> ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done_at_call child_entry call_h. _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!a e cid q h b done ent ret. _ ==> ?row. FLOOKUP _ _ = SOME row /\ _`
       (drule_then strip_assume_tac) >>
     Cases_on `out = tab`
     >- (gvs[] >>
         `EL i p::DROP (SUC i) p = DROP i p` by simp[DROP_CONS_EL] >>
         metis_tac[LUPDATE_SAME]) >>
     qpat_assum `!i. i <= LENGTH p ==> _` (qspec_then `i` strip_assume_tac) >>
     gvs[] >> metis_tac[]) >>
  drule_all dft_packet_pseudo_prefix_frame >> strip_tac >>
  `(!a e bb bt ps xs ys rho hin h body pos front brest.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,body,pos,front,T,brest) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!a sf tf inc entry order r8 nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,nrest) ==>
      (!e. FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\ A' a = A a) /\
    (!cid. FLOOKUP calls (p,d,cid) = NONE)` by
    (irule dft_packet_pseudo_closed_table_frame >>
     rpt (first_assum (irule_at Any)) >> simp[] >> metis_tac[]) >>
  `!a e cid q h b done ent ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,ent,ret) ==>
    ?row. FLOOKUP out (a,e) = SOME row /\ q < LENGTH row /\
      EL q row = A' ((e,cid)::a)` by
    (irule dft_packet_pseudo_call_cell_frame >>
     rpt (first_assum (irule_at Any)) >> simp[] >> metis_tac[]) >>
  simp[]
QED
