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

(* ReplayFrame's completion exception: every source INVOKE in the closing
   row already has a returned record; the fresh row has an empty prefix. *)
Theorem block_exceptional_completion:
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,rho_y,ord,hin,h0,SOME (be,hb),cnt,OK s,F,NONE) /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
    MEM q (TAKE cnt ord)) /\
  (!a e bb bt ps xs ys ord hin h be hb cnt front closed rest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,ord,hin,h,SOME (be,hb),cnt,front,closed,rest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE cnt ord) ==>
      ?ch b done child ir child_out caller_post.
        FLOOKUP calls (a,e,(EL q xs).inst_id) =
          SOME (q,ch,b,done,child,SOME (ir,child_out,caller_post))) /\
  blocks' = (blocks |+ ((p,d),(bb,bt,ps,xs,rho_y,ord,hin,h0,SOME (be,hb),
      LENGTH rho_y,OK post,T,SOME post.vs_gas_readings))) |+
    ((p,SUC d),(bb1,bt1,ps1,xs1,ys1,ord1,post,h1,body1,0,OK s1,F,NONE)) ==>
  !a e bb bt ps xs ys ord hin h be hb cnt front closed rest.
    ((a,e) = (p,d) \/ (a,e) = (p,SUC d)) /\
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,ord,hin,h,SOME (be,hb),cnt,front,closed,rest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE cnt ord) ==>
      ?ch b done child ir child_out caller_post.
        FLOOKUP calls (a,e,(EL q xs).inst_id) =
          SOME (q,ch,b,done,child,SOME (ir,child_out,caller_post))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac
  >- (gvs[FLOOKUP_UPDATE] >> gen_tac >> strip_tac >>
      qpat_assum `!a e bb bt ps xs ys ord hin h be hb cnt front closed rest. _`
        (drule_then irule) >> simp[]) >>
  gvs[FLOOKUP_UPDATE]
QED

(* A single lookup of a live row supplies the other two lookups because
   the old tables have the same domain. *)
Theorem ancestor_lupdates_separate:
  !m es ks m' es' ks' live key am ae ak pos.
  FDOM m = FDOM es /\ FDOM m = FDOM ks /\
  (!i x y z. live i /\
    FLOOKUP m (key i) = SOME x /\ FLOOKUP es (key i) = SOME y /\
    FLOOKUP ks (key i) = SOME z ==>
    FLOOKUP m' (key i) = SOME (LUPDATE (am i) (pos i) x) /\
    FLOOKUP es' (key i) = SOME (LUPDATE (ae i) (pos i) y) /\
    FLOOKUP ks' (key i) = SOME (LUPDATE (ak i) (pos i) z)) ==>
  (!i x. live i /\ FLOOKUP m (key i) = SOME x ==>
    FLOOKUP m' (key i) = SOME (LUPDATE (am i) (pos i) x)) /\
  (!i y. live i /\ FLOOKUP es (key i) = SOME y ==>
    FLOOKUP es' (key i) = SOME (LUPDATE (ae i) (pos i) y)) /\
  (!i z. live i /\ FLOOKUP ks (key i) = SOME z ==>
    FLOOKUP ks' (key i) = SOME (LUPDATE (ak i) (pos i) z))
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  `key i IN FDOM m /\ key i IN FDOM es /\ key i IN FDOM ks` by
    metis_tac[finite_mapTheory.flookup_thm] >>
  metis_tac[venomExecProofsTheory.FDOM_FLOOKUP]
QED
