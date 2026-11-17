Theory dftPacketCallReplayPreservation
Ancestors
  dftPacketTableSplice dftPacketCallEdgeClauses dftPacketPseudoHistory dftPacketFreshRow
  dftGasInvCallerExtract list rich_list finite_map arithmetic

(* A returned record's immutable completed prefix is contained in the
   current completed prefix.  No comparison of source instruction indices
   is used for this chronology fact. *)
Theorem dft_packet_call_done_prefix:
  !sched prior cnt q.
    ~MEM q (TAKE prior sched) /\ MEM q (TAKE cnt sched) ==>
    prior < cnt /\
    (!r. MEM r (TAKE prior sched) ==> MEM r (TAKE cnt sched))
Proof
  rpt gen_tac >> strip_tac >>
  `prior < cnt` by
    (spose_not_then assume_tac >>
     `TAKE cnt (TAKE prior sched) = TAKE cnt sched` by
       (irule TAKE_TAKE_T >> decide_tac) >>
     metis_tac[MEM_TAKE]) >>
  simp[] >> rpt strip_tac >>
  `TAKE prior (TAKE cnt sched) = TAKE prior sched` by
    (irule TAKE_TAKE_T >> decide_tac) >>
  metis_tac[MEM_TAKE]
QED

(* This checks precisely the two prefix kinds used by old U and historical
   Q.  rows may be a mask, site or key row; v is the FINAL child aggregate.
   The record bound already accnts for retained returned children. *)
Theorem dft_packet_call_replay_prefixes:
  !(calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    p i a e livecid liveq liveh b0 livedone liveentry sf tf bb bt ps xs ys sched cnt.
    i < LENGTH p /\ a = DROP (SUC i) p /\ (e,livecid) = EL i p /\
    FLOOKUP calls (a,e,livecid) = SOME (liveq,liveh,b0,livedone,liveentry,NONE) /\
    dft_fn_rel sf tf /\
    lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
    lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
    bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
    EVERY (\x. is_pseudo x.inst_opcode) ps /\
    EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ LENGTH xs = LENGTH ys /\
    PERM sched (COUNT_LIST (LENGTH xs)) /\
    LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
      from_block [EL q xs] y) sched ys /\
    liveq < LENGTH xs /\ (EL liveq xs).inst_opcode = INVOKE /\
    (EL liveq xs).inst_id = livecid /\
    b0.vs_inst_idx = LENGTH ps + cnt /\
    get_instruction bt b0.vs_inst_idx = SOME (EL liveq xs) /\
    (!cid q h b done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done_at_call,child_entry,ret) ==>
      q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
      (case ret of
        NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
      | SOME triple => MEM q (TAKE cnt sched))) /\
    (!r. r < LENGTH xs /\ (EL r xs).inst_opcode = INVOKE /\
      MEM r (TAKE cnt sched) ==>
      ?h b done child ir out post.
        FLOOKUP calls (a,e,(EL r xs).inst_id) =
          SOME (r,h,b,done,child,SOME (ir,out,post))) ==>
    (!k. k <= LENGTH xs /\
      (!r. r < k /\ (EL r xs).inst_opcode = INVOKE ==>
        MEM r (TAKE cnt sched)) ==>
      k <= liveq /\ !rows v. TAKE k (LUPDATE v liveq rows) = TAKE k rows) /\
    (!cid q h b done child ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
      q <= liveq /\ !rows v. TAKE q (LUPDATE v liveq rows) = TAKE q rows)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `k <= liveq` by
        (irule dft_packet_call_cut_bound >>
         goal_assum (drule_at (Pat `call_q < LENGTH xs`)) >>
         simp[] >>
         goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
         simp[] >> rpt strip_tac >>
         qpat_x_assum `!r. r < LENGTH xs /\ _ ==> _` (qspec_then `r` mp_tac) >>
         simp[] >> metis_tac[]) >>
      simp[dft_packet_row_prefix_splice]) >>
  rpt gen_tac >> disch_tac >>
  irule dft_packet_history_recorded_call_bound >>
  rpt (first_assum (irule_at Any)) >> simp[] >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!cid q h b done_at_call child_entry ret. _` mp_tac >>
  qpat_x_assum `FLOOKUP calls (DROP _ _,e,_) = _` mp_tac >>
  qpat_x_assum `LENGTH xs = LENGTH ys` mp_tac >>
  qpat_x_assum `a = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
