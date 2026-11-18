Theory dftPacketBlockHistorySelectedFrame
Ancestors
  dftPacketBlockHistoryFrame dftPacketBlockTableSplice dftPacketTableSplice
  list rich_list finite_map arithmetic pred_set

(* Apply at each selected index.  The source structural projections come
   from the local block splice; the numerical bound comes from the eligible
   prefix or immutable recorded-call projection of the prefix frame. *)
Theorem dft_packet_block_history_selected_frame:
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
    acts1 blocks1 calls1 p d inds
    (tab:(((num # num) list # num),'v list list) fmap) out
    ai ds ei qi zi sfi tfi inci enti orderi resi nresti
    bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later
    orderi1 resi1 nresti1 counti1 fronti1 closedi1 resti1 later1
    (call:instruction option).
    FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
    FLOOKUP blocks (ai,ei) =
      SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
    orderi = ds ++ ei::later /\ ALL_DISTINCT orderi /\
    (ai,ei) IN FDOM blocks /\
    (!f. MEM f ds ==> (ai,f) IN FDOM blocks) /\
    FLOOKUP acts1 ai = SOME (sfi,tfi,inci,enti,orderi1,resi1,nresti1) /\
    orderi1 = ds ++ ei::later1 /\
    FLOOKUP blocks1 (ai,ei) =
      SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti1,fronti1,closedi1,resti1) /\
    (!f. MEM f ds ==>
      FST (THE (FLOOKUP blocks1 (ai,f))) = FST (THE (FLOOKUP blocks (ai,f)))) /\
    (p,SUC d) NOTIN FDOM blocks /\ LENGTH inds = LENGTH p /\
    (!a e. (a,e) <> (p,SUC d) /\
      (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!i. i < LENGTH p ==>
      ?rows v. FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME rows /\
        FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE v (EL i inds) rows)) /\
    (!i. i < LENGTH p /\ (ai,ei) = (DROP (SUC i) p,FST (EL i p)) ==>
      qi <= EL i inds) /\
    (!i. i < LENGTH p /\ DROP (SUC i) p = ai ==>
      FST (EL i p) = LAST orderi) /\
    calls1 = calls ==>
    (?order' res' nrest' count' front' closed' rest' later'.
      FLOOKUP acts1 ai = SOME (sfi,tfi,inci,enti,order',res',nrest') /\
      FLOOKUP blocks1 (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,count',front',closed',rest') /\
      order' = ds ++ ei::later') /\
    (!f. MEM f ds ==>
      FST (THE (FLOOKUP blocks1 (ai,f))) = FST (THE (FLOOKUP blocks (ai,f)))) /\
    (sfi,
      MAP (\f. (FST (THE (FLOOKUP blocks1 (ai,f))),f,
        DROP (phi_prefix_length (FST (THE (FLOOKUP blocks1 (ai,f)))).bb_instructions)
          (FST (THE (FLOOKUP blocks1 (ai,f)))).bb_instructions)) ds ++ [(bbi,ei,zi)],call) =
    (sfi,
      MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
        DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
          (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++ [(bbi,ei,zi)],call) /\
    FST (SND (SND (THE (FLOOKUP acts1 ai)))) = inci /\
    (!f. MEM f ds ==> FLOOKUP out (ai,f) = FLOOKUP tab (ai,f)) /\
    TAKE qi (THE (FLOOKUP out (ai,ei))) = TAKE qi (THE (FLOOKUP tab (ai,ei))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP out (ai,f)))) ds) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP out (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP out (ai,ei)))) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP tab (ai,ei)))) /\
    (!cid. FLOOKUP calls1 (ai,ei,cid) = FLOOKUP calls (ai,ei,cid))
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM (LAST orderi) ds` by
    (qpat_x_assum `ALL_DISTINCT orderi` mp_tac >>
     simp[ALL_DISTINCT_APPEND,LAST_APPEND] >> metis_tac[MEM_LAST,MEM]) >>
  `!f. MEM f ds ==> FLOOKUP out (ai,f) = FLOOKUP tab (ai,f)` by
    (rpt strip_tac >>
     `(ai,f) <> (p,SUC d)` by metis_tac[] >>
     `!i. i < LENGTH p ==>
       (ai,f) <> (DROP (SUC i) p,FST (EL i p))` by
       metis_tac[pairTheory.PAIR_EQ] >>
     metis_tac[]) >>
  `TAKE qi (THE (FLOOKUP out (ai,ei))) = TAKE qi (THE (FLOOKUP tab (ai,ei)))` by
    (Cases_on `?i. i < LENGTH p /\ (ai,ei) = (DROP (SUC i) p,FST (EL i p))`
     >- (pop_assum strip_assume_tac >>
         `qi <= EL i inds` by metis_tac[] >>
         qpat_x_assum `!i. i < LENGTH p ==> ?rows v. _`
           (drule_then strip_assume_tac) >> simp[dft_packet_row_prefix_splice]) >>
     `(ai,ei) <> (p,SUC d)` by metis_tac[] >>
     `FLOOKUP out (ai,ei) = FLOOKUP tab (ai,ei)` by metis_tac[] >> simp[]) >>
  `FLAT (MAP (\f. FLAT (THE (FLOOKUP out (ai,f)))) ds) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds)` by
    (AP_TERM_TAC >> irule MAP_CONG >> simp[] >> metis_tac[]) >>
  simp[] >> irule MAP_CONG >> simp[] >> metis_tac[]
QED
