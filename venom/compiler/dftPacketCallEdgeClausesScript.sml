Theory dftPacketCallEdgeClauses
Ancestors
  dftPacketTableSplice dftPacketCallUpdate dftPacketCutExtension dftPacketFreshRow
  dftPacketFreshCut dftPacketCalleeAlignment dftPacketCallNative
  list rich_list finite_map arithmetic

(* The aggregate stored in a parent is the final child aggregate, not the
   intermediate aggregate from the bottom-up construction. *)
Theorem dft_packet_call_path_coherence:
  !b:((num # num) list). !L inds orders
    (tab:(((num # num) list # num),'v list list) fmap) out.
    L = LENGTH b /\ LENGTH inds = L /\
    (!i. i < L ==> ?rows.
      FLOOKUP tab (DROP (SUC i) b,FST (EL i b)) = SOME rows /\
      EL i inds < LENGTH rows) /\
    (!i rows. i < L /\
      FLOOKUP tab (DROP (SUC i) b,FST (EL i b)) = SOME rows ==>
      FLOOKUP out (DROP (SUC i) b,FST (EL i b)) =
        SOME (LUPDATE
          (FLAT (MAP (\f. FLAT (THE (FLOOKUP out (DROP i b,f))))
            (EL i orders))) (EL i inds) rows)) ==>
    !i. i < L ==>
      EL (EL i inds)
        (THE (FLOOKUP out (DROP (SUC i) b,FST (EL i b)))) =
        FLAT (MAP (\f. FLAT (THE (FLOOKUP out (DROP i b,f))))
          (EL i orders)) /\
      (!k. k <= EL i inds ==>
        TAKE k (THE (FLOOKUP out (DROP (SUC i) b,FST (EL i b)))) =
        TAKE k (THE (FLOOKUP tab (DROP (SUC i) b,FST (EL i b))))) /\
      (!r. r < LENGTH (THE (FLOOKUP tab (DROP (SUC i) b,FST (EL i b)))) /\
        r <> EL i inds ==>
        EL r (THE (FLOOKUP out (DROP (SUC i) b,FST (EL i b)))) =
        EL r (THE (FLOOKUP tab (DROP (SUC i) b,FST (EL i b))))) /\
      LENGTH (THE (FLOOKUP out (DROP (SUC i) b,FST (EL i b)))) =
        LENGTH (THE (FLOOKUP tab (DROP (SUC i) b,FST (EL i b))))
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  `?rows. FLOOKUP tab (DROP (SUC i) b,FST (EL i b)) = SOME rows /\
    EL i inds < LENGTH rows` by metis_tac[] >>
  `FLOOKUP out (DROP (SUC i) b,FST (EL i b)) =
    SOME (LUPDATE
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP out (DROP i b,f))))
        (EL i orders))) (EL i inds) rows)` by metis_tac[] >>
  simp[EL_LUPDATE,dft_packet_row_prefix_splice]
QED

(* Away from every activation on the newly live path, all rows and hence
   whole activation aggregates are unchanged. *)
Theorem dft_packet_call_offpath_frame:
  !b:((num # num) list). !child_depth
    (tab:(((num # num) list # num),'v list list) fmap) out a.
    (!i. i <= LENGTH b ==> a <> DROP i b) /\
    (!a e. (a,e) <> (b,child_depth) /\
      (!r. r < LENGTH b ==>
        (a,e) <> (DROP (SUC r) b,FST (EL r b))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) ==>
    (!e. FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!order. FLAT (MAP (\e. FLAT (THE (FLOOKUP out (a,e)))) order) =
      FLAT (MAP (\e. FLAT (THE (FLOOKUP tab (a,e)))) order))
Proof
  rpt gen_tac >> strip_tac >>
  `a <> b` by
    (metis_tac[DROP_0,arithmeticTheory.ZERO_LESS_EQ]) >>
  `!r. r < LENGTH b ==> a <> DROP (SUC r) b` by
    (metis_tac[arithmeticTheory.LESS_EQ]) >>
  `!e. FLOOKUP out (a,e) = FLOOKUP tab (a,e)` by
    (gen_tac >> qpat_x_assum `!a e. _`
       (qspecl_then [`a`,`e`] mp_tac) >> simp[] >>
     metis_tac[pairTheory.PAIR_EQ]) >>
  simp[]
QED

(* A historical cut cannot include a still suspended call.  This gives the
   TAKE bound at the one ancestor cell that the insertion changes. *)
Theorem dft_packet_call_cut_bound:
  !(calls:(gas_event,
    num # num # venom_state # num list # venom_state #
    (internal_return # venom_state # venom_state) option) fmap)
    a e xs call_q qi h b0 done_at_call child_entry.
    call_q < LENGTH xs /\
    (EL call_q xs).inst_opcode = INVOKE /\
    FLOOKUP calls (a,e,(EL call_q xs).inst_id) =
      SOME (call_q,h,b0,done_at_call,child_entry,NONE) /\
    (!r. r < qi /\ (EL r xs).inst_opcode = INVOKE ==>
      ?q h b0 done_at_call child_entry ir child_out caller_post.
        FLOOKUP calls (a,e,(EL r xs).inst_id) =
          SOME (q,h,b0,done_at_call,child_entry,
            SOME (ir,child_out,caller_post))) ==>
    qi <= call_q
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `qi <= call_q` >- simp[] >>
  `call_q < qi` by decide_tac >>
  qpat_x_assum `!r. _` (qspec_then `call_q` mp_tac) >> simp[]
QED
