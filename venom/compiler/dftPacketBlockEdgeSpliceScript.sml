Theory dftPacketBlockEdgeSplice
Ancestors
  dftPacketBlockPathUpdate finite_map list rich_list pred_set

(* Reindex the live parents without changing their suspended call records. *)
Theorem dft_block_splice_parent_indices:
  !(p:(num # num) list) acts calls.
    (!i. i < LENGTH p ==>
      ?a e cid sf tf inc ent ord q h b done child.
        a = DROP (SUC i) p /\ (e,cid) = EL i p /\
        FLOOKUP acts a = SOME (sf,tf,inc,ent,ord,NONE:exec_result option,NONE:bytes32 list option) /\
        LAST ord = e /\ FLOOKUP calls (a,e,cid) =
          SOME (q,h,b,done,child,NONE:(internal_return # venom_state # venom_state) option)) ==>
    !i. i < LENGTH p ==>
      ?sf tf inc ent ord q h b done child.
        FLOOKUP acts (DROP (SUC i) p) = SOME (sf,tf,inc,ent,ord,NONE,NONE) /\
        LAST ord = FST (EL i p) /\
        FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
          SOME (q,h,b,done,child,NONE)
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >> first_x_assum drule >>
  disch_then strip_assume_tac >>
  qexistsl [`sf`,`tf`,`inc`,`ent`,`ord`,`q`,`h`,`b`,`done`,`child`] >>
  qpat_assum `(e,cid) = EL i p` (fn th => rewrite_tac[SYM th,pairTheory.FST,pairTheory.SND]) >>
  qpat_assum `a = DROP (SUC i) p` (fn th => rewrite_tac[SYM th]) >> simp[]
QED

(* The entry initializer's two cases have precisely the cells accepted by
   the path updater; none of its semantic replay conjuncts need unfolding. *)
Theorem dft_block_splice_fresh_cells:
  (if (s1:venom_state).vs_inst_idx < LENGTH ps1 then
     cm = [] /\ ce = [] /\ ck = [] /\ pseudo_case
   else
     cm = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [NONE:bytes32 option] else []) (LENGTH xs1) /\
     ce = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(sf.fn_name,(EL q xs1).inst_id)] else []) (LENGTH xs1) /\
     ck = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(p,SUC d,(EL q xs1).inst_id)] else []) (LENGTH xs1) /\ body_case) ==>
  ((cm = [] /\ ce = [] /\ ck = []) \/
   (cm = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [NONE] else []) (LENGTH xs1) /\
    ce = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(sf.fn_name,(EL q xs1).inst_id)] else []) (LENGTH xs1) /\
    ck = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(p,SUC d,(EL q xs1).inst_id)] else []) (LENGTH xs1)))
Proof
  Cases_on `s1.vs_inst_idx < LENGTH ps1` >> simp[]
QED

(* Use the actual initialized block as the newest visit, and no new call
   record.  The row tables returned here use the final child aggregates. *)
Theorem dft_block_splice_initialized_path:
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
    (m:(((num # num) list # num),bytes32 option list list) fmap)
    (es:(((num # num) list # num),(string # num) list list) fmap)
    (ks:(((num # num) list # num),gas_event list list) fmap)
    p d sf tf inc entry order bb bt ps xs ys rho hin h0 be hbe count
    s post j bb1 bt1 ps1 xs1 ys1 rho1 body1 s1 cm ce ck AM AE AK.
    FDOM blocks = FDOM m /\ FDOM blocks = FDOM es /\ FDOM blocks = FDOM ks /\
    FLOOKUP acts p = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
    FLOOKUP blocks (p,d) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,OK s,F,NONE) /\
    LAST order = d /\
    (?rsf rtf rinc rentry rorder rres rrest.
      FLOOKUP acts [] = SOME (rsf,rtf,rinc,rentry,rorder,rres,rrest)) /\
    (!a f g ai ent ord r u.
      FLOOKUP acts a = SOME (f,g,ai,ent,ord,r,u) ==>
      ord <> [] /\ ord = GENLIST (\i. ai + SUC i) (LENGTH ord) /\
      (!e. MEM e ord <=> (a,e) IN FDOM blocks)) /\
    (!i. i < LENGTH p ==>
      ?a e cid f g ai ent ord q h b done child.
        a = DROP (SUC i) p /\ (e,cid) = EL i p /\
        FLOOKUP acts a = SOME (f,g,ai,ent,ord,NONE,NONE) /\ LAST ord = e /\
        FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,NONE)) /\
    (!a e cid q h b done child ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
      ?bb bt ps xs ys rho hin h0 be hbe count front closed brest
        cf cg cord cr cu.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
        q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ (EL q xs).inst_id = cid /\
        FLOOKUP acts ((e,cid)::a) = SOME (cf,cg,e,child,cord,cr,cu)) /\
    (!a e bb bt ps xs ys rho hin h0 body count front closed brest.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) ==>
      body = NONE ==>
        FLOOKUP m (a,e) = SOME [] /\ FLOOKUP es (a,e) = SOME [] /\
        FLOOKUP ks (a,e) = SOME []) /\
    (!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest mr er kr.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      FLOOKUP m (a,e) = SOME mr /\ FLOOKUP es (a,e) = SOME er /\
      FLOOKUP ks (a,e) = SOME kr ==>
      LENGTH mr = LENGTH xs /\ LENGTH er = LENGTH mr /\ LENGTH kr = LENGTH mr /\
      LIST_REL (\x y. LENGTH x = LENGTH y) mr er /\
      LIST_REL (\x y. LENGTH x = LENGTH y) mr kr /\
      (!q. q < LENGTH xs ==>
        ((EL q xs).inst_opcode = GAS ==> EL q kr = [(a,e,(EL q xs).inst_id)]) /\
        ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
          EL q kr = []) /\
        ((EL q xs).inst_opcode = INVOKE ==>
          (case FLOOKUP calls (a,e,(EL q xs).inst_id) of
             NONE => EL q kr = []
           | SOME call =>
               EL q mr = AM ((e,(EL q xs).inst_id)::a) /\
               EL q er = AE ((e,(EL q xs).inst_id)::a) /\
               EL q kr = AK ((e,(EL q xs).inst_id)::a))))) /\
    AM = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP m (a,f))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    AE = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP es (a,f))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    AK = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks (a,f))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    ALL_DISTINCT (AK []) /\ ALL_DISTINCT (MAP (\i. i.inst_id) xs1) /\
    (if s1.vs_inst_idx < LENGTH ps1 then
       cm = [] /\ ce = [] /\ ck = []
     else
       cm = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [NONE] else []) (LENGTH xs1) /\
       ce = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(sf.fn_name,(EL q xs1).inst_id)] else []) (LENGTH xs1) /\
       ck = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(p,SUC d,(EL q xs1).inst_id)] else []) (LENGTH xs1)) ==>
    ?acts' blocks' calls' inds m' es' ks' AM' AE' AK'.
      acts' = acts |+ (p,(sf,tf,inc,entry,order ++ [SUC d],NONE,NONE)) /\
      blocks' = (blocks |+ ((p,d),
        (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),LENGTH ys,OK post,T,
          SOME post.vs_gas_readings))) |+ ((p,SUC d),
        (bb1,bt1,ps1,xs1,ys1,rho1,post,SUC j,body1,0,OK s1,F,NONE)) /\
      calls' = calls /\
      inds = GENLIST (\i. FST (THE (FLOOKUP calls
        (DROP (SUC i) p,FST (EL i p),SND (EL i p))))) (LENGTH p) /\
      AM' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (a,f))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
      AE' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (a,f))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
      AK' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (a,f))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
      (p,SUC d) NOTIN FDOM blocks /\ FDOM acts' = FDOM acts /\
      order ++ [SUC d] = GENLIST (\i. inc + SUC i) (LENGTH (order ++ [SUC d])) /\
      (!e. MEM e (order ++ [SUC d]) <=> (p,e) IN FDOM blocks') /\
      FDOM blocks' = (p,SUC d) INSERT FDOM blocks /\
      FDOM blocks' = FDOM m' /\ FDOM blocks' = FDOM es' /\ FDOM blocks' = FDOM ks' /\
      FLOOKUP m' (p,SUC d) = SOME cm /\ FLOOKUP es' (p,SUC d) = SOME ce /\
      FLOOKUP ks' (p,SUC d) = SOME ck /\
      (!i. i < LENGTH p ==>
        ?h b done child.
          FLOOKUP calls' (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
            SOME (EL i inds,h,b,done,child,NONE)) /\
      (!i mr er kr. i < LENGTH p /\
        FLOOKUP m (DROP (SUC i) p,FST (EL i p)) = SOME mr /\
        FLOOKUP es (DROP (SUC i) p,FST (EL i p)) = SOME er /\
        FLOOKUP ks (DROP (SUC i) p,FST (EL i p)) = SOME kr ==>
        FLOOKUP m' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AM' (DROP i p)) (EL i inds) mr) /\
        FLOOKUP es' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AE' (DROP i p)) (EL i inds) er) /\
        FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AK' (DROP i p)) (EL i inds) kr)) /\
      (!a e. (a,e) <> (p,SUC d) /\
        (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
        FLOOKUP m' (a,e) = FLOOKUP m (a,e) /\
        FLOOKUP es' (a,e) = FLOOKUP es (a,e) /\
        FLOOKUP ks' (a,e) = FLOOKUP ks (a,e)) /\
      LENGTH (AM' []) = LENGTH (AE' []) /\ LENGTH (AM' []) = LENGTH (AK' []) /\
      MAP THE (FILTER IS_SOME (AM' [])) = MAP THE (FILTER IS_SOME (AM [])) /\
      MAP (\(key,slot). (key,THE slot))
        (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK' [],AM' []))) =
      MAP (\(key,slot). (key,THE slot))
        (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],AM []))) /\
      ALL_DISTINCT (AK' [])
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac dft_block_splice_parent_indices >>
  Q_TAC (fn t => SUBGOAL_THEN t assume_tac)
    `((cm = [] /\ ce = [] /\ ck = []) \/
       (cm = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [NONE:bytes32 option] else []) (LENGTH xs1) /\
        ce = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(sf.fn_name,(EL q xs1).inst_id)] else []) (LENGTH xs1) /\
        ck = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(p,SUC d,(EL q xs1).inst_id)] else []) (LENGTH xs1)))` >-
    (qpat_x_assum `(if s1.vs_inst_idx < LENGTH ps1 then _ else _)` mp_tac >>
     Cases_on `s1.vs_inst_idx < LENGTH ps1` >> simp[]) >>
  rename1 `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,rho0,hin,h0,SOME (be,hbe),cnt0,OK s,F,NONE)` >>
  qabbrev_tac `newrow = (bb1,bt1,ps1,xs1,ys1,rho1,post,SUC j,body1,(0:num),OK s1,F,NONE:bytes32 list option)` >>
  qabbrev_tac `acts' = acts |+ (p,(sf,tf,inc,entry,order ++ [SUC d],NONE,NONE))` >>
  qabbrev_tac `blocks' = (blocks |+ ((p,d),
    (bb,bt,ps,xs,ys,rho0,hin,h0,SOME (be,hbe),LENGTH ys,OK post,T,
      SOME post.vs_gas_readings))) |+ ((p,SUC d),newrow)` >>
  `acts' = acts |+ (p,(sf,tf,inc,entry,order ++ [SUC d],NONE,NONE)) /\
   blocks' = (blocks |+ ((p,d),
     (bb,bt,ps,xs,ys,rho0,hin,h0,SOME (be,hbe),LENGTH ys,OK post,T,
       SOME post.vs_gas_readings))) |+ ((p,SUC d),newrow)` by
    simp[Abbr `acts'`,Abbr `blocks'`] >>
  assume_tac (REFL ``calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap``) >>
  drule_all dft_packet_block_path_update >>
  disch_then (qx_choose_then `inds` (qx_choose_then `orders` (qx_choose_then `m'`
    (qx_choose_then `es'` (qx_choose_then `ks'` (qx_choose_then `AM'`
      (qx_choose_then `AE'` (qx_choose_then `AK'` (map_every assume_tac o CONJUNCTS))))))))) >>
  qexistsl [`acts'`,`blocks'`,`calls`,`inds`,`m'`,`es'`,`ks'`,`AM'`,`AE'`,`AK'`] >>
  conj_tac >- REFL_TAC >>
  conj_tac >- REFL_TAC >>
  conj_tac >- REFL_TAC >>
  `!i mr er kr. i < LENGTH p /\
    FLOOKUP m (DROP (SUC i) p,FST (EL i p)) = SOME mr /\
    FLOOKUP es (DROP (SUC i) p,FST (EL i p)) = SOME er /\
    FLOOKUP ks (DROP (SUC i) p,FST (EL i p)) = SOME kr ==>
    FLOOKUP m' (DROP (SUC i) p,FST (EL i p)) =
      SOME (LUPDATE (AM' (DROP i p)) (EL i inds) mr) /\
    FLOOKUP es' (DROP (SUC i) p,FST (EL i p)) =
      SOME (LUPDATE (AE' (DROP i p)) (EL i inds) er) /\
    FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)) =
      SOME (LUPDATE (AK' (DROP i p)) (EL i inds) kr)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i mr er kr. _ ==> FLOOKUP m' _ = SOME (LUPDATE _ _ _) /\ _`
       (qspecl_then [`i`,`mr`,`er`,`kr`]
         (drule_all_then (fn th =>
           let val cs = CONJUNCTS th in
             conj_tac >- ACCEPT_TAC (List.nth(cs,0)) >>
             conj_tac >- ACCEPT_TAC (List.nth(cs,1)) >>
             ACCEPT_TAC (List.nth(cs,2))
           end)))) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
