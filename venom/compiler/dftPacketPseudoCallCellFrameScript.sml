Theory dftPacketPseudoCallCellFrame
Ancestors
  dftPacketPseudoHistory list rich_list finite_map arithmetic

(* Recorded call cells use final child aggregates, including returned children.
   Only the single suspended cell changes in each live ancestor row. *)
Theorem dft_packet_pseudo_call_cell_frame:
  !(calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (tab:(((num # num) list # num),'v list list) fmap) out p d inds A A'.
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
    (!a. ~MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p))) ==> A' a = A a) ==>
    !a e cid q h b done ent ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,ent,ret) ==>
      ?row. FLOOKUP out (a,e) = SOME row /\ q < LENGTH row /\
        EL q row = A' ((e,cid)::a)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  `?row. FLOOKUP tab (a,e) = SOME row /\ q < LENGTH row /\
    EL q row = A ((e,cid)::a) /\
    cid = (EL q (FST (SND (SND (SND (THE (FLOOKUP blocks (a,e)))))))).inst_id` by
    metis_tac[] >>
  `(a,e) <> (p,d)` by (strip_tac >> gvs[]) >>
  Cases_on `?i. i < LENGTH p /\ (a,e) = (DROP (SUC i) p,FST (EL i p))`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      `?h b done ent. FLOOKUP calls
        (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
          SOME (EL i inds,h,b,done,ent,NONE)` by
        (qpat_x_assum `!i. i < LENGTH p ==> ?h b done ent. _`
          (qspec_then `i` mp_tac) >> simp[pairTheory.PAIR]) >>
      `EL i inds < LENGTH row /\
        SND (EL i p) = (EL (EL i inds)
          (FST (SND (SND (SND (THE (FLOOKUP blocks
            (DROP (SUC i) p,FST (EL i p))))))))).inst_id` by
        (qpat_x_assum `!a e cid q h b done ent ret. _`
          (drule_then strip_assume_tac) >> gvs[]) >>
      `FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
        SOME (LUPDATE (A' (DROP i p)) (EL i inds) row)` by metis_tac[] >>
      qexists_tac `LUPDATE (A' (DROP i p)) (EL i inds) row` >>
      simp[EL_LUPDATE] >> Cases_on `q = EL i inds` >> gvs[]
      >- (qpat_x_assum `SND _ = _` (fn th => rewrite_tac[GSYM th]) >>
          simp[GSYM DROP_CONS_EL,pairTheory.PAIR]) >>
      qmatch_goalsub_abbrev_tac `A' ((FST (EL i p),cid)::DROP (SUC i) p)` >>
      `~MEM ((FST (EL i p),cid)::DROP (SUC i) p)
        (GENLIST (\k. DROP k p) (SUC (LENGTH p)))` by
        (strip_tac >>
         `cid = SND (EL i p)` by
           (irule dft_packet_history_live_child_unique >>
            qexistsl_tac [`DROP (SUC i) p`,`FST (EL i p)`,`i`,`p`] >> simp[pairTheory.PAIR]) >>
         qpat_x_assum `cid = SND _` SUBST_ALL_TAC >>
         qpat_x_assum `SND _ = _`
           (fn th => rule_assum_tac (REWRITE_RULE [GSYM th])) >>
         fs[pairTheory.PAIR]) >> metis_tac[]) >>
  `~MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))` by
    (strip_tac >> fs[MEM_GENLIST] >> rename1 `_::a = DROP k p` >>
     `k < LENGTH p` by
       (Cases_on `k < LENGTH p` >> simp[] >>
        `DROP k p = []` by simp[DROP_LENGTH_TOO_LONG] >> gvs[]) >>
     qpat_x_assum `_::a = DROP k p` mp_tac >> simp[DROP_CONS_EL] >>
     strip_tac >> metis_tac[pairTheory.FST]) >>
  qexists_tac `row` >> metis_tac[]
QED
