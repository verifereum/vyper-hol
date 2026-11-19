Theory staticAbortOptConditionalJumpsKeptReceipt
Ancestors
  staticAbortOptConditionalJumpsRetained pred_set

Theorem conditional_jump_kept_receipt:
  !p q b x V (rank:(num#num)->num) (pc:(num#num)->num) height
    (tag:(num#num)->num->(string#num)option) boolean old cc z0 z1.
  !r. r = splice_pc b 4 3 ==>
  !C. C = (\p l d. ?off. FLOOKUP (SND(compute_label_offsets p)) l=SOME off /\
                       off<dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off=SOME d) ==>
  !Flow. Flow = (\p pc height tag boolean (u:num#num) (v:num#num).
    !hi hj ins. hi = height u /\ hj = height v /\ ins = EL (pc u) p ==>
    !inherit. inherit = (\(src:num->num option) (fresh:num->(string#num)option) bnew.
      (!k l i. tag v k=SOME(l,i) ==> k<hj /\
        (fresh k=SOME(l,i) \/ ?a. src k=SOME a /\ a<hi /\ tag u a=SOME(l,i))) /\
      (!k. boolean v k ==> k<hj /\ (bnew k \/ ?a. src k=SOME a /\ a<hi /\ boolean u a))) ==>
    case ins of
      AsmLabel l => hj=hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj=hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t s. asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                     (AsmPush bs) t=AsmOK s ==> EL 0 s.as_stack=0w \/ EL 0 s.as_stack=1w)
    | AsmPushLabel l => hj=hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,pc u) else NONE) (\k. F)
    | AsmPushOfst l d => hj=hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,pc u) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => n<hi /\ hj=hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0<n /\ n<hi /\ hj=hi /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k)) (\k. NONE) (\k. F)
           | NONE =>
               !a. a = asm_op_arity name ==>
               !m. m = hj+a-hi ==>
               a<=hi /\ hj=m+(hi-a) /\ ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !t s. LENGTH t.as_stack=hi /\
                     asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p) ins t=AsmOK s ==>
                       EL 0 s.as_stack=0w \/ EL 0 s.as_stack=1w))
    | _ => F) ==>
  !Target. Target = (\p tg d. ?l i. tg 0=SOME(l,i) /\ C p l d) ==>
  !Legal. Legal = (\p i tg j.
    if EL i p=AsmOp "JUMP" then Target p tg j else
    if EL i p=AsmOp "JUMPI" then j=i+1 \/ Target p tg j else j=i+1) ==>
  !Row. Row = (\p i h tg (edge:(num#num)->bool) pc height.
    !arm. arm = (\P n. ?v. edge v /\ P (pc v) /\ height v=n) ==>
    !legal. legal = (\P n. !v. edge v ==> P (pc v) /\ height v=n) ==>
    !fall. fall = (\d. d=i+1) ==>
    !taken. taken = Target p tg ==>
    !next. next = (\n. arm fall n /\ legal fall n) ==>
    !untagged. untagged = (\a. !k. k<a ==> tg k=NONE) ==>
    !stop. stop = (\a. a<=h /\ untagged a /\ !v. ~edge v) ==>
    case EL i p of
      AsmLabel l => next h
    | AsmPush bs => next (h+1)
    | AsmPushLabel l => IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) /\ next (h+1)
    | AsmPushOfst l d => IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) /\ next (h+1)
    | AsmOp name =>
        if name="INVALID" then stop 0 else if name="REVERT" then stop 2 else
        if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"] then
          cc.cc_static /\ stop (asm_op_arity name) else
        (case ALOOKUP dup_table name of
           SOME n => n<h /\ next (h+1)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0<n /\ n<h /\ next h
           | NONE => if name="JUMP" then 1<=h /\ arm taken (h-1) /\ legal taken (h-1) else
                     if name="JUMPI" then 2<=h /\ tg 1=NONE /\ arm fall (h-2) /\
                       arm taken (h-2) /\ legal (\d. fall d \/ taken d) (h-2) else
                     ?m. static_abort_straight name m /\ asm_op_arity name<=h /\
                       untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
    | _ => F) ==>
  !keep. keep = {u | u IN V /\ (pc u<b \/ b+4<=pc u)} ==>
  !D. D = {u | u IN V /\ pc u=b} ==>
  !U. U = (\u k. case tag (z0 u) k of NONE => tag (z1 u) k | SOME t => SOME t) ==>
  !UB. UB = (\u k. boolean (z0 u) k \/ boolean (z1 u) k) ==>
  !vraw. vraw = (\u (i:num) k.
    if i<2 then (if k=0 then NONE else U u (k-1)) else
    if i=2 then (if k=0 then SOME(x,b+2) else if k=1 then NONE else U u (k-2))
    else if i=4 then tag (z0 u) k else tag (z1 u) k) ==>
  !vb. vb = (\u (i:num) k.
    if i=0 then k<>0 /\ UB u (k-1) else if i=1 then k=0 \/ UB u (k-1) else
    if i=2 then k=1 \/ (2<=k /\ UB u (k-2)) else
    if i=4 then boolean (z0 u) k else boolean (z1 u) k) ==>
  !rt. rt = (\u. if u IN keep then tag u else vraw u 0) ==>
  !rb. rb = (\u. if u IN keep then boolean u else vb u 0) ==>
  !Tr. Tr = (\rho tg k. OPTION_MAP (\(l,i). (l,rho l i)) (tg k)) ==>
  (!i. i<LENGTH p /\ (i<b \/ b+4<=i) ==>
       r i<LENGTH q /\ EL (r i) q=EL i p) /\
  (!l j. C p l j ==> (j<b \/ b+4<=j) /\ C q l (r j)) /\
  (!l. IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) ==>
       IS_SOME (FLOOKUP (SND (compute_label_offsets q)) l)) /\
  (!u. u IN V ==> pc u<LENGTH p) /\
  (!u. u IN keep ==>
       Row p (pc u) (height u) (tag u) (old u) pc height /\
       !v. old u v ==> v IN V /\ rank v<rank u /\
         Flow p pc height tag boolean u v /\ Legal p (pc u) (tag u) (pc v)) /\
  (!v. v IN D ==>
       (!k t. (tag (z0 v) k=SOME t \/ tag (z1 v) k=SOME t) ==> tag v (k+1)=SOME t) /\
       (!k. UB v k ==> boolean v (k+1))) ==>
  (!u v. u IN keep /\ old u v ==> (v IN keep \/ v IN D) /\ rank v<rank u) /\
  (!u v k l. u IN keep /\ old u v /\ tag v k=SOME(l,b) ==> ?j. tag u j=SOME(l,b)) /\
  (!u rho. u IN keep /\
     (!l. EL (pc u) p=AsmPushLabel l \/ EL (pc u) p=AsmPushOfst l 0 ==> rho l (pc u)=r(pc u)) ==>
     r(pc u)<LENGTH q /\ Row q (r(pc u)) (height u) (Tr rho (tag u)) (old u) (r o pc) height /\
     (!v. old u v ==> Legal q (r(pc u)) (Tr rho (tag u)) (r(pc v)) /\
        Flow q (r o pc) height (\v. if v=u then Tr rho (tag u) else Tr rho (rt v))
          (\v. if v=u then boolean u else rb v) u v))
Proof
  ntac 14 gen_tac >>
  map_every (fn v => qx_gen_tac v >>
    CONV_TAC (LAND_CONV (RAND_CONV (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)))) >>
    disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]))
    [`r`,`C`,`Flow`,`Target`,`Legal`,`Row`,`keep`,`D`,`U`,`UB`,`vraw`,`vb`,`rt`,`rb`,`Tr`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!u. u IN keep ==>
     (!v. old u v ==> (v IN keep \/ v IN D) /\ rank v<rank u) /\
     (!v k l. old u v /\ tag v k=SOME(l,b) ==> ?j. tag u j=SOME(l,b)) /\
     (!rho. (!l. EL (pc u) p=AsmPushLabel l \/ EL (pc u) p=AsmPushOfst l 0 ==>
              rho l (pc u)=r(pc u)) ==>
       r(pc u)<LENGTH q /\ Row q (r(pc u)) (height u) (Tr rho (tag u)) (old u) (r o pc) height /\
       (!v. old u v ==> Legal q (r(pc u)) (Tr rho (tag u)) (r(pc v)) /\
          Flow q (r o pc) height (\v. if v=u then Tr rho (tag u) else Tr rho (rt v))
            (\v. if v=u then boolean u else rb v) u v))`
    suffices_by (POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qx_gen_tac `u` >> disch_tac >>
  Q.SUBGOAL_THEN `u IN V /\ (pc u<b \/ b+4<=pc u)`
    (CONJUNCTS_THEN2 assume_tac assume_tac) >- fs[Abbr `keep`] >>
  `pc u<LENGTH p` by metis_tac[] >>
  qpat_assum `!a. a IN keep ==> Row _ _ _ _ _ _ _ /\ _`
    (drule_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qspecl_then [`p`,`q`,`b`,`pc u`,`cc`,`height u`,`tag u`,`boolean u`,
               `old u`,`pc`,`height`,`tag`,`boolean`]
    (mp_tac o SIMP_RULE bool_ss [combinTheory.o_THM] o
      CONV_RULE (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)))
    conditional_jump_retained_row >>
  impl_tac >-
    (qpat_assum `!i. i < LENGTH p /\ _ ==> r i < LENGTH q /\ _`
       (qspec_then `pc u` mp_tac) >> simp[] >> strip_tac >>
     qpat_assum `!l j. C p l j ==> _` mp_tac >>
     qpat_assum `Row p _ _ _ _ _ _` mp_tac >>
     qpat_assum `!v. old u v ==> v IN V /\ _` mp_tac >>
     simp_tac bool_ss [Abbr `r`, Abbr `C`, Abbr `Row`, Abbr `Flow`,
                       Abbr `Legal`, Abbr `Target`, LET_THM] >>
     disch_then (mk_asm "edges") >> disch_then (mk_asm "source_row") >> disch_tac >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (ntac 2 gen_tac >> disch_tac >>
         qpat_assum `!l j. _ ==> (_ \/ _) /\ _`
           (drule_then (ACCEPT_TAC o CONJUNCT1)))
     >- (asm "source_row" mp_tac >> simp[NoAsms]) >>
     gen_tac >> disch_tac >>
     asm "edges" (drule_then (mp_tac o CONJUNCT2 o CONJUNCT2)) >>
     simp[NoAsms]) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "successor_pc") (mk_asm "relocate")) >>
  conj_asm1_tac >-
    (qx_gen_tac `v` >> disch_tac >>
     asm "successor_pc" (drule_then assume_tac) >>
     qpat_assum `!v. old u v ==> v IN V /\ _` (drule_then strip_assume_tac) >>
     simp[Abbr `keep`, Abbr `D`] >> decide_tac) >>
  conj_tac >-
    (qx_gen_tac `v` >> qx_gen_tac `k` >> qx_gen_tac `l` >> strip_tac >>
     asm "relocate" (qspecl_then [`\l j. r j`, `tag`, `boolean`] mp_tac) >>
     simp_tac bool_ss [Abbr `r`] >>
     disch_then (fn th => drule_then (mp_tac o cj 5) (CONJUNCT2 th)) >>
     simp[] >> metis_tac[]) >>
  `!v k l j. old u v /\ rt v k = SOME(l,j) ==> tag v k = SOME(l,j)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!v. old u v ==> (v IN keep \/ v IN D) /\ _`
       (drule_then strip_assume_tac)
     >- fs[Abbr `rt`] >>
     Cases_on `v IN keep` >- fs[Abbr `rt`] >>
     Cases_on `k` >> fs[Abbr `rt`, Abbr `vraw`, Abbr `U`, arithmeticTheory.ADD1] >>
     qpat_assum `!v. v IN D ==> _` (drule_then (mp_tac o CONJUNCT1)) >>
     Cases_on `tag (z0 v) n` >> fs[] >> metis_tac[]) >>
  `!v k. old u v /\ rb v k ==> boolean v k` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!v. old u v ==> (v IN keep \/ v IN D) /\ _`
       (drule_then strip_assume_tac)
     >- fs[Abbr `rb`] >>
     Cases_on `v IN keep` >- fs[Abbr `rb`] >>
     Cases_on `k` >> fs[Abbr `rb`, Abbr `vb`, arithmeticTheory.ADD1] >>
     qpat_assum `!v. v IN D ==> _` (drule_then (mp_tac o CONJUNCT2)) >> simp[]) >>
  qx_gen_tac `rho'` >> disch_tac >>
  asm "relocate" (qspecl_then [`rho'`,`rt`,`rb`] mp_tac) >>
  impl_tac >-
    (conj_tac >-
       (qpat_assum `!l. _ ==> rho' l (pc u) = r (pc u)` mp_tac >>
        simp_tac bool_ss [Abbr `r`]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "moved_row") (mk_asm "moved_edges")) >>
  `r (pc u) < LENGTH q /\ EL (r (pc u)) q = EL (pc u) p` by
    (qpat_assum `!i. i < LENGTH p /\ _ ==> r i < LENGTH q /\ _`
       (qspec_then `pc u` mp_tac) >> simp[]) >>
  simp_tac bool_ss [Abbr `r`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (asm "moved_row" mp_tac >>
     simp[Abbr `Row`, Abbr `Target`, Abbr `C`, Abbr `Tr`, combinTheory.o_THM, LET_THM]) >>
  qx_gen_tac `v` >> disch_tac >>
  `v <> u` by
    (qpat_assum `!v. old u v ==> (v IN keep \/ v IN D) /\ _`
       (qspec_then `v` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (assume_tac o CONJUNCT2) >>
     disch_then SUBST_ALL_TAC >> fs[]) >>
  asm "moved_edges" (drule_then (fn th =>
    MAP_EVERY mp_tac [List.nth (CONJUNCTS th,2), List.nth (CONJUNCTS th,3)])) >>
  simp[Abbr `Legal`, Abbr `Target`, Abbr `C`, Abbr `Flow`, Abbr `Tr`,
       combinTheory.o_THM, LET_THM]
QED
