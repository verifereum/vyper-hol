Theory dftPacketBlockHistoryRootPrefix
Ancestors
  dftPacketPseudoCallCellFrame dftPacketSelectedCutTransport
  list rich_list finite_map arithmetic pred_set

(* Appending the bottom order changes its aggregate, but not aggregates of
   retained children outside the live suffix chain. *)
Theorem dft_packet_block_history_call_cells:
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
    (tab:(((num # num) list # num),'v list list) fmap) out
    p d inds sf0 tf0 inc0 ent0 ord0 acts' A A'.
    FLOOKUP acts p = SOME (sf0,tf0,inc0,ent0,ord0,NONE,NONE) /\
    acts' = acts |+ (p,(sf0,tf0,inc0,ent0,ord0 ++ [SUC d],NONE,NONE)) /\
    FLOOKUP tab (p,SUC d) = NONE /\
    (!a e cid q h b done ent ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,ent,ret) ==>
      ?row. FLOOKUP tab (a,e) = SOME row /\ q < LENGTH row /\
        EL q row = A ((e,cid)::a) /\
        cid = (EL q (FST (SND (SND (SND (THE (FLOOKUP blocks (a,e)))))))).inst_id) /\
    (!i. i < LENGTH p ==>
      ?h b done ent. FLOOKUP calls
        (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
          SOME (EL i inds,h,b,done,ent,NONE)) /\
    A = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    A' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
    (!a e. (a,e) <> (p,SUC d) /\
      (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!i row. i < LENGTH p /\
      FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME row ==>
      FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
        SOME (LUPDATE (A' (DROP i p)) (EL i inds) row)) ==>
    !a e cid q h b done ent ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,ent,ret) ==>
      ?row. FLOOKUP out (a,e) = SOME row /\ q < LENGTH row /\
        EL q row = A' ((e,cid)::a)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!cid. FLOOKUP calls (p,SUC d,cid) = NONE` by
    (gen_tac >> Cases_on `FLOOKUP calls (p,SUC d,cid)` >- simp[] >>
     PairCases_on `x` >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
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
     simp[FLOOKUP_UPDATE]) >>
  rpt gen_tac >> disch_tac >>
  irule dft_packet_pseudo_call_cell_frame >>
  rpt (first_assum (irule_at Any)) >>
  qexistsl [`tab`,`p`,`inds`,`SUC d`,`blocks`,`A`] >> asm_rewrite_tac[]
QED

(* The selected pieces are unchanged; only their remainders in the new root
   may differ.  The nonterminal nesting cells are derived, not postulated. *)
Theorem dft_packet_block_history_root_prefix:
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
    (tab:(((num # num) list # num),'v list list) fmap) out
    p d inds sf0 tf0 inc0 ent0 ord0 acts' A A' cuts endpoint.
    FLOOKUP acts p = SOME (sf0,tf0,inc0,ent0,ord0,NONE,NONE) /\
    acts' = acts |+ (p,(sf0,tf0,inc0,ent0,ord0 ++ [SUC d],NONE,NONE)) /\
    FLOOKUP tab (p,SUC d) = NONE /\
    (!a e cid q h b done ent ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,ent,ret) ==>
      ?row. FLOOKUP tab (a,e) = SOME row /\ q < LENGTH row /\
        EL q row = A ((e,cid)::a) /\
        cid = (EL q (FST (SND (SND (SND (THE (FLOOKUP blocks (a,e)))))))).inst_id) /\
    (!i. i < LENGTH p ==>
      ?h b done ent. FLOOKUP calls
        (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
          SOME (EL i inds,h,b,done,ent,NONE)) /\
    A = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    A' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
    (!a e. (a,e) <> (p,SUC d) /\
      (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!i row. i < LENGTH p /\
      FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME row ==>
      FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
        SOME (LUPDATE (A' (DROP i p)) (EL i inds) row)) /\
    MAP (\(ai,ds,ei,qi,zi). ai) cuts =
      REVERSE (GENLIST (\i. DROP i endpoint) (SUC (LENGTH endpoint))) /\
    (!i ai ds ei qi zi.
      i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      ?sf tf inc entry order res nrest later row.
        FLOOKUP acts ai = SOME (sf,tf,inc,entry,order,res,nrest) /\
        order = ds ++ ei::later /\ FLOOKUP tab (ai,ei) = SOME row /\
        qi <= LENGTH row /\
        (SUC i < LENGTH cuts ==>
          ?cid h b done ent ret.
            FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b,done,ent,ret) /\
            FST (EL (SUC i) cuts) = (ei,cid)::ai)) /\
    (!i ai ds ei qi zi.
      i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      FLAT (MAP (\f. FLAT (THE (FLOOKUP out (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP out (ai,ei)))) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP tab (ai,ei)))) ) ==>
    ?rest. A' [] = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP tab (ai,ei))))) cuts) ++ rest
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!a e cid q h b done ent ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,ent,ret) ==>
    ?row. FLOOKUP out (a,e) = SOME row /\ q < LENGTH row /\
      EL q row = A' ((e,cid)::a)` by
    (rpt gen_tac >> disch_tac >>
     irule dft_packet_block_history_call_cells >>
     qrefinel [`A`,`acts`,`acts'`,`_`,`blocks`,`_`,`_`,`_`,`_`,`_`,`_`,
       `_`,`inds`,`_`,`_`,`_`,`_`,`tab`] >>
     rpt (first_assum (irule_at Any)) >> asm_rewrite_tac[]) >>
  `!a e row. FLOOKUP tab (a,e) = SOME row ==>
    ?row'. FLOOKUP out (a,e) = SOME row' /\ LENGTH row' = LENGTH row` by
    (rpt gen_tac >> disch_tac >>
     `(a,e) <> (p,SUC d)` by (strip_tac >> gvs[]) >>
     Cases_on `?i. i < LENGTH p /\ (a,e) = (DROP (SUC i) p,FST (EL i p))`
     >- (pop_assum strip_assume_tac >> gvs[] >> metis_tac[LENGTH_LUPDATE]) >>
     metis_tac[]) >>
  `LENGTH cuts = SUC (LENGTH endpoint)` by
    (qpat_assum `MAP _ cuts = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `cuts <> []` by (strip_tac >> fs[]) >>
  `GENLIST (\i. DROP i endpoint) (SUC (LENGTH endpoint)) <> []` by
    (strip_tac >> pop_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `FST (HD cuts) = []` by
    (qpat_x_assum `MAP _ cuts = _` (mp_tac o Q.AP_TERM `HD`) >>
     simp[HD_REVERSE, GENLIST_LAST, DROP_LENGTH_TOO_LONG] >>
     Cases_on `cuts` >> gvs[] >> rename1 `FST hd` >> PairCases_on `hd` >> simp[]) >>
  irule dft_packet_selected_cut_prefix >>
  rpt (first_assum (irule_at Any)) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i ai ds ei qi zi. _ ==> ?sf tf inc entry order res nrest later row. _`
    (drule_all_then strip_assume_tac) >>
  `?row'. FLOOKUP out (ai,ei) = SOME row' /\ LENGTH row' = LENGTH row` by
    metis_tac[] >>
  `FLOOKUP acts' ai = SOME (sf,tf,inc,entry,
      (if ai = p then order ++ [SUC d] else order),res,nrest)` by
    (Cases_on `ai = p` >> gvs[FLOOKUP_UPDATE]) >>
  qexistsl [`sf`,`tf`,`inc`,`entry`,
    `if ai = p then order ++ [SUC d] else order`,`res`,`nrest`,
    `if ai = p then later ++ [SUC d] else later`,`row'`] >>
  simp[APPEND_ASSOC] >> conj_tac
  >- (Cases_on `ai = p` >> simp[]) >>
  conj_tac
  >- (strip_tac >>
      qpat_x_assum `SUC i < LENGTH cuts ==> _` mp_tac >> simp[] >> strip_tac >>
      qpat_x_assum `!a e cid q h b done ent ret.
        _ ==> ?row. FLOOKUP out _ = _ /\ _` (drule_then strip_assume_tac) >>
      gvs[]) >>
  qpat_x_assum `!i ai ds ei qi zi. _ ==> FLAT _ ++ _ = _` drule_all >>
  simp[]
QED
