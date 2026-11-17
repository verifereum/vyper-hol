Theory dftPacketBlockReplayStructure
Ancestors
  dftPacketCallOldReplay dftPacketTableSplice
  list rich_list finite_map arithmetic pred_set

(* Polymorphic in mask/site/key cells.  Only strict ancestors change old
   rows; the appended row is fresh in the old block domain. *)
Theorem dft_packet_block_prefix_frame:
  !(blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    p d inds (tab:(((num # num) list # num),'v list list) fmap) out.
    (p,d) IN FDOM blocks /\ (p,SUC d) NOTIN FDOM blocks /\
    (!i. i < LENGTH p ==>
      ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done child ch.
        FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,OK b0,F,NONE) /\
        FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
          SOME (EL i inds,ch,b0,done,child,NONE) /\
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
    (!a e cid q h b done child ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
      ?bb bt ps xs ys rho hin h0 be hbe pos front closed brest.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),pos,front,closed,brest) /\
        q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
        (case ret of
          NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
        | SOME triple => MEM q (TAKE pos rho))) /\
    (!a e. (a,e) <> (p,SUC d) /\
      (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!i. i < LENGTH p ==>
      ?rows v. FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME rows /\
        FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE v (EL i inds) rows)) ==>
    FLOOKUP out (p,d) = FLOOKUP tab (p,d) /\
    (!a e bb bt ps xs ys rho hin h be hbe pos front closed brest k.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,front,closed,brest) /\
      k <= LENGTH xs /\ EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k xs) /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE pos rho)) ==>
      TAKE k (THE (FLOOKUP out (a,e))) = TAKE k (THE (FLOOKUP tab (a,e)))) /\
    (!a e cid q h b done child ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
      TAKE q (THE (FLOOKUP out (a,e))) = TAKE q (THE (FLOOKUP tab (a,e))))
Proof
  rpt gen_tac >> strip_tac >>
  `!i. i < LENGTH p ==> DROP (SUC i) p <> p` by
    (rpt strip_tac >>
     pop_assum (mp_tac o AP_TERM ``LENGTH:(num # num) list -> num``) >> simp[]) >>
  `!i bb bt ps xs ys rho hin h be hbe pos front closed brest.
    i < LENGTH p /\
    FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,front,closed,brest) ==>
    (!k. k <= LENGTH xs /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==>
        MEM q (TAKE pos rho)) ==> k <= EL i inds) /\
    (!cid q ch b done child ret.
      FLOOKUP calls (DROP (SUC i) p,FST (EL i p),cid) =
        SOME (q,ch,b,done,child,ret) ==> q <= EL i inds)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH p ==> ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done child ch. _`
       (drule_then strip_assume_tac) >> gvs[] >>
     qpat_assum `LENGTH xs = LENGTH ys` (fn th => rewrite_tac[GSYM th]) >>
     match_mp_tac dft_packet_call_old_row_bounds >>
     rpt (first_assum (irule_at Any)) >> simp[] >>
     qexistsl_tac [`p`,`SND (EL i p)`,`b0`] >> simp[] >> conj_tac
     >- (qexists_tac `i` >> simp[]) >>
     rpt gen_tac >> disch_tac >>
     qpat_x_assum `!a e cid q h b done child ret. _`
       (drule_then strip_assume_tac) >> gvs[]) >>
  conj_tac
  >- (qpat_x_assum `!a e. _` irule >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `(a,e) IN FDOM blocks` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_SOME_NONE] >>
      `(a,e) <> (p,SUC d)` by metis_tac[] >>
      Cases_on `?i. i < LENGTH p /\ (a,e) = (DROP (SUC i) p,FST (EL i p))`
      >- (pop_assum strip_assume_tac >> gvs[] >>
          `k <= EL i inds` by metis_tac[] >>
          qpat_x_assum `!i. i < LENGTH p ==> ?rows v. _`
            (drule_then strip_assume_tac) >> simp[dft_packet_row_prefix_splice]) >>
      `FLOOKUP out (a,e) = FLOOKUP tab (a,e)` by metis_tac[] >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  `?bb bt ps xs ys rho hin h0 be hbe pos front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),pos,front,closed,brest)` by metis_tac[] >>
  `(a,e) IN FDOM blocks` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_SOME_NONE] >>
  `(a,e) <> (p,SUC d)` by metis_tac[] >>
  Cases_on `?i. i < LENGTH p /\ (a,e) = (DROP (SUC i) p,FST (EL i p))`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      `q <= EL i inds` by metis_tac[] >>
      qpat_x_assum `!i. i < LENGTH p ==> ?rows v. _`
        (drule_then strip_assume_tac) >> simp[dft_packet_row_prefix_splice]) >>
  `FLOOKUP out (a,e) = FLOOKUP tab (a,e)` by metis_tac[] >> simp[]
QED

Theorem dft_packet_block_closed_frame:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap) acts'
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    p d (tab:(((num # num) list # num),'v list list) fmap) out A A'.
    (p,SUC d) NOTIN FDOM blocks /\
    (!i. i < LENGTH p ==>
      ?bb bt ps xs ys rho hin h be hbe pos b0.
        FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,OK b0,F,NONE)) /\
    (!a sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      (res = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p))))) /\
    (!a. a <> p ==> FLOOKUP acts' a = FLOOKUP acts a) /\
    (!a e. (a,e) <> (p,SUC d) /\
      (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    A = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    A' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) ==>
    (!a e bb bt ps xs ys rho hin h body pos front brest.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,body,pos,front,T,brest) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!a sf tf inc entry order r8 nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,nrest) ==>
      FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,SOME r8,nrest) /\
      (!e. FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\ A' a = A a)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `(a,e) IN FDOM blocks` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_SOME_NONE] >>
      qpat_x_assum `!a e. _ ==> FLOOKUP out _ = _` irule >>
      rpt strip_tac >> gvs[] >>
      qpat_x_assum `!i. i < LENGTH p ==> ?bb bt ps xs ys rho hin h be hbe pos b0. _`
        (drule_then strip_assume_tac) >> gvs[]) >>
  rpt gen_tac >> disch_tac >>
  `~MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p)))` by
    (qpat_x_assum `!a sf tf inc entry order res nrest. _`
      (drule_then mp_tac) >> simp[]) >>
  `!i. i <= LENGTH p ==> a <> DROP i p` by
    (qpat_x_assum `~MEM a _` mp_tac >>
     simp[MEM_GENLIST,LESS_EQ_IFF_LESS_SUC] >> metis_tac[]) >>
  `a <> p` by
    (qpat_assum `!i. i <= LENGTH p ==> a <> DROP i p`
      (qspec_then `0` mp_tac) >> pure_rewrite_tac[DROP_0] >> metis_tac[ZERO_LESS_EQ]) >>
  `FLOOKUP acts' a = FLOOKUP acts a` by metis_tac[] >>
  `!e. FLOOKUP out (a,e) = FLOOKUP tab (a,e)` by
    (gen_tac >> qpat_x_assum `!a e. _ ==> FLOOKUP out _ = _` irule >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `!i. i <= LENGTH p ==> a <> DROP i p`
       (qspec_then `SUC i` mp_tac) >> gvs[]) >>
  simp[]
QED
