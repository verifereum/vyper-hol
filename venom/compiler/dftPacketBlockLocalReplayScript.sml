Theory dftPacketBlockLocalReplay
Ancestors
  dftPacketBlockReplayFrame finite_map list rich_list arithmetic

(* Table edits at strict ancestors leave the closing row alone. *)
Theorem block_closing_row_lookup:
  (!a e. (a,e) <> (p,SUC d) /\
    (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
    FLOOKUP out (a,e) = FLOOKUP tab (a,e)) ==>
  FLOOKUP out (p,d) = FLOOKUP tab (p,d)
Proof
  disch_then irule >> simp[] >> rpt strip_tac >>
  qpat_assum `p = DROP (SUC i) p` (mp_tac o (Q.AP_TERM `LENGTH`)) >>
  simp[LENGTH_DROP] >> decide_tac
QED

(* The fresh visit has no old call records.  Only the domain projection
   of the immutable call-to-block linkage is needed here. *)
Theorem block_fresh_visit_no_call:
  (p,SUC d) NOTIN FDOM blocks /\
  (!a e cid. IS_SOME (FLOOKUP calls (a,e,cid)) ==> (a,e) IN FDOM blocks) ==>
  !cid. FLOOKUP calls (p,SUC d,cid) = NONE
Proof
  strip_tac >> gen_tac >>
  Cases_on `FLOOKUP calls (p,SUC d,cid)` >> simp[] >>
  first_x_assum (qspecl_then [`p`,`SUC d`,`cid`] mp_tac) >> simp[]
QED

(* At the terminal cursor all source INVOKEs were already executed.
   Closing the row cannot add a pending INVOKE to any source TAKE. *)
Theorem block_closing_invoke_prefix:
  (!q. q < LENGTH (xs:instruction list) /\ (EL q xs).inst_opcode = INVOKE ==>
    MEM q (TAKE cnt ord)) ==>
  (!k. k <= LENGTH xs ==>
    !q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE cnt ord))
Proof
  strip_tac >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

(* A closing INVOKE cell points to a completed child.  Its old payload
   already agrees with the final aggregate of that child. *)
Theorem block_closing_invoke_payload:
  (!q. q < LENGTH (xs:instruction list) /\ (EL q xs).inst_opcode = INVOKE ==>
    ?h b done child ir out post.
      FLOOKUP calls (p,d,(EL q xs).inst_id) =
      SOME (q,h,b,done,child,SOME (ir,out,post))) /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
    case FLOOKUP calls (p,d,(EL q xs).inst_id) of
      NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
    | SOME call => EL q ms = AM ((d,(EL q xs).inst_id)::p) /\
        EL q ess = AE ((d,(EL q xs).inst_id)::p) /\
        EL q ks = AK ((d,(EL q xs).inst_id)::p)) /\
  (!cid q h b done child ir out post.
    FLOOKUP calls (p,d,cid) = SOME (q,h,b,done,child,SOME (ir,out,post)) ==>
    AM' ((d,cid)::p) = AM ((d,cid)::p) /\
    AE' ((d,cid)::p) = AE ((d,cid)::p) /\
    AK' ((d,cid)::p) = AK ((d,cid)::p)) ==>
  !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
    case FLOOKUP calls (p,d,(EL q xs).inst_id) of
      NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
    | SOME call => EL q ms = AM' ((d,(EL q xs).inst_id)::p) /\
        EL q ess = AE' ((d,(EL q xs).inst_id)::p) /\
        EL q ks = AK' ((d,(EL q xs).inst_id)::p)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >> strip_tac >>
  qpat_assum `!q. _ ==> ?h b done child ir out post. _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!cid q h b done child ir out post. _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!q. _ ==> case FLOOKUP calls _ of NONE => _ | SOME call => _`
    (drule_all_then assume_tac) >>
  qpat_assum `FLOOKUP calls (p,d,_) = SOME _` (fn th =>
    qpat_x_assum `case FLOOKUP calls _ of NONE => _ | SOME call => _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [th])) >> simp[]
QED
