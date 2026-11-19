Theory dftPacketBlockPathUpdate
Ancestors option[qualified,ignore_grammar]
  dftPacketBlockTableSplice dftPacketBlockPathRows
  dftPacketBlockPathInsertion dftPacketBlockPathConservation
  list rich_list finite_map arithmetic pred_set

(* The indices and orders below come from immutable call records and the
   actual appended activation map. Only the three row tables are constructed. *)
Theorem dft_packet_block_path_update:
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
    p d sf tf inc entry order bb bt ps xs ys rho in_state h0 be hbe count
    s post newrow acts' blocks' calls' fresh_xs cm ce ck AM AE AK.
    FDOM blocks = FDOM m /\ FDOM blocks = FDOM es /\ FDOM blocks = FDOM ks /\
    FLOOKUP acts p = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
    FLOOKUP blocks (p,d) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) /\
    LAST order = d /\
    (?rsf rtf rinc rentry rorder rres rrest.
      FLOOKUP acts [] = SOME (rsf,rtf,rinc,rentry,rorder,rres,rrest)) /\
    (!a f g ai ent ord r u.
      FLOOKUP acts a = SOME (f,g,ai,ent,ord,r,u) ==>
      ord <> [] /\ ord = GENLIST (\i. ai + SUC i) (LENGTH ord) /\
      (!e. MEM e ord <=> (a,e) IN FDOM blocks)) /\
    (!i. i < LENGTH p ==>
      ?f g ai ent ord q h b done child.
        FLOOKUP acts (DROP (SUC i) p) = SOME (f,g,ai,ent,ord,NONE,NONE) /\
        LAST ord = FST (EL i p) /\
        FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
          SOME (q,h,b,done,child,NONE)) /\
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
    ALL_DISTINCT (AK []) /\
    acts' = acts |+ (p,(sf,tf,inc,entry,order ++ [SUC d],NONE,NONE)) /\
    blocks' = (blocks |+ ((p,d),
      (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),LENGTH ys,OK post,T,
       SOME post.vs_gas_readings))) |+ ((p,SUC d),newrow) /\
    calls' = calls /\
    ALL_DISTINCT (MAP (\i. i.inst_id) fresh_xs) /\
    ((cm = [] /\ ce = [] /\ ck = []) \/
     (cm = GENLIST (\q. if (EL q fresh_xs).inst_opcode = GAS then [NONE] else [])
        (LENGTH fresh_xs) /\
      ce = GENLIST (\q. if (EL q fresh_xs).inst_opcode = GAS
        then [(sf.fn_name,(EL q fresh_xs).inst_id)] else []) (LENGTH fresh_xs) /\
      ck = GENLIST (\q. if (EL q fresh_xs).inst_opcode = GAS
        then [(p,SUC d,(EL q fresh_xs).inst_id)] else []) (LENGTH fresh_xs))) ==>
    ?inds orders m' es' ks' AM' AE' AK'.
      inds = GENLIST (\i. FST (THE (FLOOKUP calls
        (DROP (SUC i) p,FST (EL i p),SND (EL i p))))) (LENGTH p) /\
      orders = GENLIST (\i. FST (SND (SND (SND (SND
        (THE (FLOOKUP acts' (DROP i p)))))))) (SUC (LENGTH p)) /\
      AM' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (a,f))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
      AE' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (a,f))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
      AK' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (a,f))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
      (p,SUC d) NOTIN FDOM blocks /\
      FLOOKUP acts' p = SOME (sf,tf,inc,entry,order ++ [SUC d],NONE,NONE) /\
      (!a. a <> p ==> FLOOKUP acts' a = FLOOKUP acts a) /\
      FDOM acts' = FDOM acts /\
      order ++ [SUC d] = GENLIST (\i. inc + SUC i) (LENGTH (order ++ [SUC d])) /\
      (!e. MEM e (order ++ [SUC d]) <=> (p,e) IN FDOM blocks') /\
      FLOOKUP blocks' (p,d) = SOME
        (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),LENGTH ys,OK post,T,
         SOME post.vs_gas_readings) /\
      FLOOKUP blocks' (p,SUC d) = SOME newrow /\
      (!key. key <> (p,d) /\ key <> (p,SUC d) ==>
        FLOOKUP blocks' key = FLOOKUP blocks key) /\
      FDOM blocks' = (p,SUC d) INSERT FDOM blocks /\ calls' = calls /\
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
          SOME (LUPDATE (AK' (DROP i p)) (EL i inds) kr) /\
        (!k. k <= EL i inds ==>
          TAKE k (THE (FLOOKUP m' (DROP (SUC i) p,FST (EL i p)))) = TAKE k mr /\
          TAKE k (THE (FLOOKUP es' (DROP (SUC i) p,FST (EL i p)))) = TAKE k er /\
          TAKE k (THE (FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)))) = TAKE k kr) /\
        (!r. r < LENGTH mr /\ r <> EL i inds ==>
          EL r (THE (FLOOKUP m' (DROP (SUC i) p,FST (EL i p)))) = EL r mr /\
          EL r (THE (FLOOKUP es' (DROP (SUC i) p,FST (EL i p)))) = EL r er /\
          EL r (THE (FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)))) = EL r kr) /\
        LENGTH (THE (FLOOKUP m' (DROP (SUC i) p,FST (EL i p)))) = LENGTH mr /\
        LENGTH (THE (FLOOKUP es' (DROP (SUC i) p,FST (EL i p)))) = LENGTH er /\
        LENGTH (THE (FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)))) = LENGTH kr) /\
      (!a e. (a,e) <> (p,SUC d) /\
        (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
        FLOOKUP m' (a,e) = FLOOKUP m (a,e) /\
        FLOOKUP es' (a,e) = FLOOKUP es (a,e) /\
        FLOOKUP ks' (a,e) = FLOOKUP ks (a,e)) /\
      (!key mr er kr. FLOOKUP m' key = SOME mr /\ FLOOKUP es' key = SOME er /\
        FLOOKUP ks' key = SOME kr ==>
        LENGTH mr = LENGTH er /\ LENGTH mr = LENGTH kr /\
        LIST_REL (\x y. LENGTH x = LENGTH y) mr er /\
        LIST_REL (\x y. LENGTH x = LENGTH y) mr kr) /\
      (?lm rm le re lk rk.
        AM [] = lm ++ rm /\ AM' [] = lm ++ FLAT cm ++ rm /\
        AE [] = le ++ re /\ AE' [] = le ++ FLAT ce ++ re /\
        AK [] = lk ++ rk /\ AK' [] = lk ++ FLAT ck ++ rk /\
        LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
        LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk) /\
      LENGTH (AM' []) = LENGTH (AE' []) /\ LENGTH (AM' []) = LENGTH (AK' []) /\
      MAP THE (FILTER IS_SOME (AM' [])) = MAP THE (FILTER IS_SOME (AM [])) /\
      MAP (\(key,slot). (key,THE slot))
        (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK' [],AM' []))) =
      MAP (\(key,slot). (key,THE slot))
        (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],AM []))) /\
      ALL_DISTINCT (AK' [])
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?rsf rtf rinc rentry rorder rres rrest. _` strip_assume_tac >>
  qpat_assum `!a f g ai ent ord r u.
    FLOOKUP acts a = SOME (f,g,ai,ent,ord,r,u) ==> _`
    (fn th => qpat_assum `FLOOKUP acts p = SOME (_,_,_,_,_,NONE,NONE)`
      (mp_then Any (map_every assume_tac o CONJUNCTS) th)) >>
  `?mb eb kb.
    mb = m |+ ((p,SUC d),cm) /\ eb = es |+ ((p,SUC d),ce) /\
    kb = ks |+ ((p,SUC d),ck)` by metis_tac[] >>
  drule_all_then (map_every assume_tac o CONJUNCTS) dft_packet_block_table_splice >>
  qpat_x_assum `acts' = _` kall_tac >> qpat_x_assum `blocks' = _` kall_tac >>
  qabbrev_tac `inds = GENLIST (\i. FST (THE (FLOOKUP calls
      (DROP (SUC i) p,FST (EL i p),SND (EL i p))))) (LENGTH p)` >>
  qabbrev_tac `orders = GENLIST (\i. FST (SND (SND (SND (SND
      (THE (FLOOKUP acts' (DROP i p)))))))) (SUC (LENGTH p))` >>
  `LENGTH inds = LENGTH p /\ LENGTH orders = SUC (LENGTH p) /\
   EL 0 orders = order ++ [SUC d]` by simp[Abbr `inds`,Abbr `orders`,EL_GENLIST] >>
  `!i. i < LENGTH p ==> DROP (SUC i) p <> p` by
    (rpt strip_tac >>
     pop_assum (mp_tac o AP_TERM ``LENGTH:(num # num) list -> num``) >> simp[]) >>
  `!i. i < LENGTH p ==>
    ?f g ai ent ord h b done child.
      FLOOKUP acts (DROP (SUC i) p) = SOME (f,g,ai,ent,ord,NONE,NONE) /\
      FLOOKUP acts' (DROP (SUC i) p) = SOME (f,g,ai,ent,ord,NONE,NONE) /\
      EL (SUC i) orders = ord /\ MEM (FST (EL i p)) ord /\
      FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
        SOME (EL i inds,h,b,done,child,NONE)` by suspend "indexed_parents" >>
  `!i. i <= LENGTH p ==>
    ALL_DISTINCT (EL i orders) /\
    (!f. MEM f (EL i orders) ==> (DROP i p,f) IN FDOM blocks')` by
      suspend "indexed_orders" >>
  `!key mr er kr. FLOOKUP m key = SOME mr /\ FLOOKUP es key = SOME er /\
    FLOOKUP ks key = SOME kr ==>
    LENGTH mr = LENGTH er /\ LENGTH mr = LENGTH kr /\
    LIST_REL (\x y. LENGTH x = LENGTH y) mr er /\
    LIST_REL (\x y. LENGTH x = LENGTH y) mr kr` by suspend "old_alignment" >>
  `!i. i < LENGTH p ==>
    MEM (FST (EL i p)) (EL (SUC i) orders) /\
    ?mr er kr.
      FLOOKUP m (DROP (SUC i) p,FST (EL i p)) = SOME mr /\
      FLOOKUP es (DROP (SUC i) p,FST (EL i p)) = SOME er /\
      FLOOKUP ks (DROP (SUC i) p,FST (EL i p)) = SOME kr /\
      EL i inds < LENGTH mr /\ EL i inds < LENGTH er /\ EL i inds < LENGTH kr /\
      EL (EL i inds) mr = AM (DROP i p) /\ EL (EL i inds) er = AE (DROP i p) /\
      EL (EL i inds) kr = AK (DROP i p)` by suspend "parent_cells" >>
  suspend "construct"
QED

Resume dft_packet_block_path_update[indexed_parents]:
  gen_tac >> disch_tac >>
  qpat_assum `!i. i < LENGTH p ==> ?f g ai ent ord q h b done child. _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!a f g ai ent ord r u.
    FLOOKUP acts a = SOME (f,g,ai,ent,ord,r,u) ==> _`
    (fn th => qpat_assum `FLOOKUP acts (DROP (SUC i) p) = SOME _`
      (mp_then Any (map_every assume_tac o CONJUNCTS) th)) >>
  `MEM (FST (EL i p)) ord` by
    (qpat_assum `LAST ord = _` (SUBST1_TAC o SYM) >>
     simp[MEM_LAST_NOT_NIL, IgnAsm `!e. MEM e ord <=> _`]) >>
  `FLOOKUP acts' (DROP (SUC i) p) = FLOOKUP acts (DROP (SUC i) p)` by simp[] >>
  qexistsl [`f`,`g`,`ai`,`ent`,`ord`,`h`,`b`,`done`,`child`] >>
  simp[Abbr `inds`,Abbr `orders`,EL_GENLIST]
QED

Resume dft_packet_block_path_update[indexed_orders]:
  gen_tac >> disch_tac >> Cases_on `i`
  >- (conj_tac
      >- (qpat_assum `EL 0 orders = _` SUBST1_TAC >>
          qpat_assum `order ++ [SUC d] = GENLIST _ _` SUBST1_TAC >>
          simp[ALL_DISTINCT_GENLIST]) >>
      simp[IgnAsm `order ++ [SUC d] = GENLIST _ _`] >> metis_tac[]) >>
  rename1 `SUC j <= LENGTH p` >>
  `j < LENGTH p` by decide_tac >>
  qpat_assum `!i. i < LENGTH p ==> ?f g ai ent ord h b done child. _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!a f g ai ent ord r u.
    FLOOKUP acts a = SOME (f,g,ai,ent,ord,r,u) ==> _`
    (fn th => qpat_assum `FLOOKUP acts (DROP (SUC j) p) = SOME _`
      (mp_then Any (map_every assume_tac o CONJUNCTS) th)) >>
  qpat_assum `EL (SUC j) orders = ord` SUBST1_TAC >> conj_tac
  >- (qpat_assum `ord = GENLIST _ _` SUBST1_TAC >>
      simp[ALL_DISTINCT_GENLIST]) >>
  simp[]
QED

Resume dft_packet_block_path_update[old_alignment]:
  rpt gen_tac >> strip_tac >> PairCases_on `key` >>
  `?bv. FLOOKUP blocks (key0,key1) = SOME bv` by gvs[flookup_thm] >>
  PairCases_on `bv` >> Cases_on `bv8`
  >- (qpat_assum `!a e bb bt ps xs ys rho hin h0 body count front closed brest.
        FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,body,_,_,_,_) ==> body = NONE ==> _`
        (fn th => qpat_assum `FLOOKUP blocks (key0,key1) = SOME _`
          (mp_then Any mp_tac th)) >> simp[]) >>
  PairCases_on `x` >>
  qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest mr er kr. _`
    (drule_all_then strip_assume_tac) >> simp[]
QED

Resume dft_packet_block_path_update[parent_cells]:
  gen_tac >> disch_tac >>
  qpat_assum `!i. i < LENGTH p ==> ?f g ai ent ord h b done child. _`
    (drule_then strip_assume_tac) >>
  conj_tac >- simp[] >>
  qpat_assum `!a e cid q h b done child ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==> _`
    (fn th => qpat_assum `FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) = SOME _`
      (mp_then Any strip_assume_tac th)) >>
  `?mr er kr. FLOOKUP m (DROP (SUC i) p,FST (EL i p)) = SOME mr /\
       FLOOKUP es (DROP (SUC i) p,FST (EL i p)) = SOME er /\
       FLOOKUP ks (DROP (SUC i) p,FST (EL i p)) = SOME kr` by gvs[flookup_thm] >>
  qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest mr er kr. _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!q. q < LENGTH _ ==> _` (drule_then strip_assume_tac) >>
  qexistsl [`mr`,`er`,`kr`] >> gvs[] >>
  `DROP i p = (FST (EL i p),SND (EL i p))::DROP (SUC i) p` by
    simp[Once DROP_CONS_EL] >>
  pop_assum (fn th => pure_once_rewrite_tac[th]) >> simp[]
QED

Resume dft_packet_block_path_update[construct]:
  qspecl_then [`p`,`inds`,`orders`,`d`,`cm`,`ce`,`ck`,`m`,`es`,`ks`] mp_tac
    dft_packet_block_path_rows >>
  (impl_tac >- (simp[] >> rpt conj_tac >> gen_tac >> disch_tac >>
     qpat_assum `!i. i < LENGTH p ==> MEM _ _ /\ ?mr er kr. _`
       (drule_then strip_assume_tac) >> goal_assum drule >> simp[])) >>
  disch_then (qx_choose_then `mts` (qx_choose_then `ets` (qx_choose_then `kts`
    (qx_choose_then `m'` (qx_choose_then `es'` (qx_choose_then `ks'`
      (map_every assume_tac o CONJUNCTS))))))) >>
  qabbrev_tac `AM' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (a,f))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a)))))))))` >>
  qabbrev_tac `AE' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (a,f))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a)))))))))` >>
  qabbrev_tac `AK' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (a,f))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a)))))))))` >>
  `LENGTH cm = LENGTH ce /\ LENGTH cm = LENGTH ck /\
    LIST_REL (\x y. LENGTH x = LENGTH y) cm ce /\
    LIST_REL (\x y. LENGTH x = LENGTH y) cm ck` by suspend "seed_alignment" >>
  `!i. i <= LENGTH p ==>
    FST (SND (SND (SND (SND (THE (FLOOKUP acts (DROP i p))))))) =
      (if i = 0 then order else EL i orders) /\
    FST (SND (SND (SND (SND (THE (FLOOKUP acts' (DROP i p))))))) = EL i orders`
    by suspend "order_projections" >>
  suspend "insert"
QED

Resume dft_packet_block_path_update[seed_alignment]:
  qpat_x_assum `(cm = [] /\ ce = [] /\ ck = []) \/ _` strip_assume_tac >>
  simp[LIST_REL_EL_EQN,EL_GENLIST] >>
  conj_tac >> gen_tac >> disch_tac >> Cases_on `(EL n fresh_xs).inst_opcode = GAS` >> simp[]
QED

Resume dft_packet_block_path_update[order_projections]:
  gen_tac >> disch_tac >> Cases_on `i`
  >- simp[IgnAsm `order ++ [SUC d] = GENLIST _ _`] >>
  rename1 `SUC j <= LENGTH p` >> `j < LENGTH p` by decide_tac >>
  qpat_assum `!i. i < LENGTH p ==> ?f g ai ent ord h b done child. _`
    (drule_then strip_assume_tac) >> simp[]
QED

Resume dft_packet_block_path_update[insert]:
  `!i mr er kr. i < LENGTH p /\
    FLOOKUP m (DROP (SUC i) p,FST (EL i p)) = SOME mr /\
    FLOOKUP es (DROP (SUC i) p,FST (EL i p)) = SOME er /\
    FLOOKUP ks (DROP (SUC i) p,FST (EL i p)) = SOME kr ==>
    FLOOKUP m' (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AM' (DROP i p)) (EL i inds) mr) /\
    FLOOKUP es' (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AE' (DROP i p)) (EL i inds) er) /\
    FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AK' (DROP i p)) (EL i inds) kr) /\
    (!k. k <= EL i inds ==>
      TAKE k (THE (FLOOKUP m' (DROP (SUC i) p,FST (EL i p)))) = TAKE k mr /\
      TAKE k (THE (FLOOKUP es' (DROP (SUC i) p,FST (EL i p)))) = TAKE k er /\
      TAKE k (THE (FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)))) = TAKE k kr) /\
    (!r. r < LENGTH mr /\ r <> EL i inds ==>
      EL r (THE (FLOOKUP m' (DROP (SUC i) p,FST (EL i p)))) = EL r mr /\
      EL r (THE (FLOOKUP es' (DROP (SUC i) p,FST (EL i p)))) = EL r er /\
      EL r (THE (FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)))) = EL r kr) /\
    LENGTH (THE (FLOOKUP m' (DROP (SUC i) p,FST (EL i p)))) = LENGTH mr /\
    LENGTH (THE (FLOOKUP es' (DROP (SUC i) p,FST (EL i p)))) = LENGTH er /\
    LENGTH (THE (FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)))) = LENGTH kr`
    by suspend "updated_cells" >>
  `!a e. (a,e) <> (p,SUC d) /\
    (!r. r < LENGTH p ==> (a,e) <> (DROP (SUC r) p,FST (EL r p))) ==>
    FLOOKUP m' (a,e) = FLOOKUP m (a,e) /\
    FLOOKUP es' (a,e) = FLOOKUP es (a,e) /\
    FLOOKUP ks' (a,e) = FLOOKUP ks (a,e)` by suspend "row_frame" >>
  `FDOM m = FDOM es /\ FDOM m = FDOM ks` by
    (qpat_assum `FDOM blocks = FDOM m` (SUBST1_TAC o SYM) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!i. i <= LENGTH p ==> ALL_DISTINCT (EL i orders)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!i. i <= LENGTH p ==> ALL_DISTINCT _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `FDOM blocks' = FDOM m UNION {(p,SUC d)}` by
    (qpat_assum `FDOM blocks' = (p,SUC d) INSERT FDOM blocks` SUBST1_TAC >>
     qpat_assum `FDOM blocks = FDOM m` SUBST1_TAC >>
     CONV_TAC (LHS_CONV (REWR_CONV INSERT_SING_UNION)) >>
     MATCH_ACCEPT_TAC UNION_COMM) >>
  `!i f. i <= LENGTH p /\ MEM f (EL i orders) ==>
     (DROP i p,f) IN FDOM m UNION {(p,SUC d)}` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `FDOM blocks' = FDOM m UNION _` (SUBST1_TAC o SYM) >>
     qpat_assum `!i. i <= LENGTH p ==> ALL_DISTINCT _ /\ _`
       (drule_then (drule_then ACCEPT_TAC o CONJUNCT2))) >>
  qabbrev_tac `oldord = \i. if i = 0 then order else EL i orders` >>
  qabbrev_tac `M = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP i p,f)))) (oldord i))` >>
  qabbrev_tac `E = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP es (DROP i p,f)))) (oldord i))` >>
  qabbrev_tac `BK = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks (DROP i p,f)))) (oldord i))` >>
  qabbrev_tac `M' = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (DROP i p,f)))) (EL i orders))` >>
  qabbrev_tac `E' = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (DROP i p,f)))) (EL i orders))` >>
  qabbrev_tac `BK' = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (DROP i p,f)))) (EL i orders))` >>
  `!i. i <= LENGTH p ==>
    M i = AM (DROP i p) /\ E i = AE (DROP i p) /\ BK i = AK (DROP i p) /\
    M' i = AM' (DROP i p) /\ E' i = AE' (DROP i p) /\ BK' i = AK' (DROP i p)`
    by suspend "aggregate_projections" >>
  suspend "insertion_inputs"
QED

Resume dft_packet_block_path_update[updated_cells]:
  rpt gen_tac >> strip_tac >> `i <= LENGTH p` by decide_tac >>
  qpat_assum `!i. i <= LENGTH p ==> FST (SND (SND (SND (SND (THE (FLOOKUP acts (DROP i p))))))) = _ /\ _`
    (drule_at_then Any (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!i rows. i < LENGTH p /\ FLOOKUP m _ = SOME rows ==> _`
    (qspecl_then [`i`,`mr`] (drule_all_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!i rows. i < LENGTH p /\ FLOOKUP es _ = SOME rows ==> _`
    (qspecl_then [`i`,`er`] (drule_all_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!i rows. i < LENGTH p /\ FLOOKUP ks _ = SOME rows ==> _`
    (qspecl_then [`i`,`kr`] (drule_all_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!key mr er kr. FLOOKUP m key = SOME mr /\ FLOOKUP es key = SOME er /\
    FLOOKUP ks key = SOME kr ==> _`
    (qspecl_then [`(DROP (SUC i) p,FST (EL i p))`,`mr`,`er`,`kr`]
      (drule_all_then (map_every assume_tac o CONJUNCTS))) >>
  simp[Abbr `AM'`,Abbr `AE'`,Abbr `AK'`,
    IgnAsm `m' = EL (LENGTH p) mts`,IgnAsm `es' = EL (LENGTH p) ets`,
    IgnAsm `ks' = EL (LENGTH p) kts`]
QED

Resume dft_packet_block_path_update[row_frame]:
  rpt gen_tac >> strip_tac >>
  map_every (fn q => qpat_assum q (qspecl_then [`LENGTH p`,`a`,`e`] mp_tac))
    [`!i a e. _ ==> FLOOKUP (EL i mts) (a,e) = _`,
     `!i a e. _ ==> FLOOKUP (EL i ets) (a,e) = _`,
     `!i a e. _ ==> FLOOKUP (EL i kts) (a,e) = _`] >> simp[]
QED

Resume dft_packet_block_path_update[aggregate_projections]:
  gen_tac >> disch_tac >>
  qpat_assum `!i. i <= LENGTH p ==> FST (SND (SND (SND (SND (THE (FLOOKUP acts (DROP i p))))))) = _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  simp[Abbr `oldord`,Abbr `M`,Abbr `E`,Abbr `BK`,Abbr `M'`,Abbr `E'`,Abbr `BK'`,
       Abbr `AM'`,Abbr `AE'`,Abbr `AK'`]
QED

Resume dft_packet_block_path_update[insertion_inputs]:
  qspecl_then [`p`,`inds`,`orders`,`order`,`d`,`cm`,`ce`,`ck`,`m`,`es`,`ks`,
    `mts`,`ets`,`kts`,`m'`,`es'`,`ks'`,`M`,`M'`,`E`,`E'`,`BK`,`BK'`] mp_tac
    dft_packet_block_path_insertion >>
  (impl_tac >- suspend "insertion_premises") >>
  qpat_assum `!i. i <= LENGTH p ==> M i = _ /\ _`
    (qspec_then `LENGTH p` (rewrite_tac o single o
      REWRITE_RULE[LESS_EQ_REFL,DROP_LENGTH_NIL])) >>
  strip_tac >> suspend "conservation"
QED

Resume dft_packet_block_path_update[insertion_premises]:
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `FDOM blocks = FDOM m` (SUBST1_TAC o SYM) >>
    first_assum ACCEPT_TAC) >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qx_gen_tac `i` >> disch_tac >> `i <= LENGTH p` by decide_tac >>
     qpat_assum `!i. i <= LENGTH p ==> M i = _ /\ _`
       (drule_then (rewrite_tac o single)) >>
     first_assum (drule_then ACCEPT_TAC)) >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- simp[Abbr `M`,Abbr `oldord`,NoAsms] >>
  conj_tac >- simp[Abbr `E`,Abbr `oldord`,NoAsms] >>
  conj_tac >- simp[Abbr `BK`,Abbr `oldord`,NoAsms] >>
  conj_tac >- simp[Abbr `M'`,NoAsms] >>
  conj_tac >- simp[Abbr `E'`,NoAsms] >>
  conj_tac >- simp[Abbr `BK'`,NoAsms] >>
  ntac 13 (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> `i <= LENGTH p` by decide_tac >>
  qpat_assum `!i. i <= LENGTH p ==> M i = _ /\ _`
    (drule_then (rewrite_tac o single)) >>
  qpat_assum `!i mr er kr. _ ==> FLOOKUP m' _ = SOME _ /\ _`
    (drule_all_then (fn th =>
      case CONJUNCTS th of mth::eth::kth::_ =>
        ACCEPT_TAC (LIST_CONJ [mth,eth,kth])
      | _ => FAIL_TAC "updated parent lookups"))
QED

Resume dft_packet_block_path_update[conservation]:
  qspecl_then [`acts`,`blocks`,`calls`,`ks`,`AK`,`AM`,`AE`,
    `p`,`d`,`fresh_xs`,`sf`,`rsf`,`rtf`,`rinc`,`rentry`,`rorder`,`rres`,`rrest`,
    `cm`,`ce`,`ck`,`lm`,`rm`,`le`,`re`,`lk`,`rk`,`AM' []`,`AE' []`,`AK' []`] mp_tac
    dft_packet_block_path_conservation >>
  (impl_tac >- suspend "conservation_premises") >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "package"
QED

Resume dft_packet_block_path_update[conservation_premises]:
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!a f g ai ent ord r u.
       FLOOKUP acts a = SOME (f,g,ai,ent,ord,r,u) ==> _`
       (drule_then (fn th => mp_tac (cj 3 th))) >>
     disch_then (drule_then ACCEPT_TAC o iffLR)) >>
  conj_tac >- suspend "provenance" >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_block_path_update[provenance]:
  rpt gen_tac >> disch_tac >>
  rename1 `FLOOKUP blocks (a,f) = SOME (_,_,_,src,_,_,_,_,row_entry,_,_,_,_)` >>
  namedCases_on `row_entry` ["", "be_pair"]
  >- (qpat_assum `!a e bb bt ps xs ys rho hin h0 body count front closed brest.
        FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,body,_,_,_,_) ==> body = NONE ==> _`
        (qspecl_then [`a`,`f`] (drule_then (fn th => simp[NoAsms,th])))) >>
  PairCases_on `be_pair` >>
  `(a,f) IN FDOM blocks` by
    (qpat_assum `FLOOKUP blocks (a,f) = SOME _`
      (mp_tac o REWRITE_RULE [flookup_thm]) >> simp[NoAsms]) >>
  `?mr er kr. FLOOKUP m (a,f) = SOME mr /\ FLOOKUP es (a,f) = SOME er /\
       FLOOKUP ks (a,f) = SOME kr` by
    (qexistsl [`m ' (a,f)`,`es ' (a,f)`,`ks ' (a,f)`] >>
     simp[NoAsms,flookup_thm] >>
     map_every (fn pat => qpat_assum pat (SUBST1_TAC o SYM))
       [`FDOM blocks = FDOM m`,`FDOM blocks = FDOM es`,`FDOM blocks = FDOM ks`] >>
     qpat_assum `(a,f) IN FDOM blocks` (fn th => simp[NoAsms,th])) >>
  qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest mr er kr. _`
    (drule_all_then (map_every assume_tac o CONJUNCTS)) >>
  simp[Once optionTheory.option_case_def, IgnAsm `AK = _`] >>
  gen_tac >> disch_tac >>
  qpat_assum `!q. q < LENGTH _ ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  disch_tac >>
  qpat_assum `(EL q src).inst_opcode = INVOKE ==> _`
    (drule_then (fn th =>
      Cases_on `FLOOKUP calls (a,f,(EL q src).inst_id)` >>
      simp[NoAsms] >>
      pop_assum (fn lookup =>
        assume_tac lookup >>
        map_every assume_tac (CONJUNCTS (SIMP_RULE (srw_ss()) [lookup] th)))))
  >- first_assum ACCEPT_TAC >>
  rename1 `FLOOKUP calls (a,f,(EL q src).inst_id) = SOME call_record` >>
  PairCases_on `call_record` >>
  qpat_assum `!a e cid q h b done child ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `FLOOKUP acts ((f,(EL q src).inst_id)::a) = SOME _`
    (fn child => simp[NoAsms,child] >>
      qpat_assum `EL q kr = AK ((f,(EL q src).inst_id)::a)`
        (fn cell => qpat_assum `AK = _`
          (fn agg => ACCEPT_TAC (SIMP_RULE (srw_ss()) [agg,child] cell))))
QED

Resume dft_packet_block_path_update[package]:
  qexistsl [`inds`,`orders`,`m'`,`es'`,`ks'`,`AM'`,`AE'`,`AK'`] >>
  conj_tac >- simp[Abbr `inds`,NoAsms] >>
  conj_tac >- simp[Abbr `orders`,NoAsms] >>
  conj_tac >- simp[Abbr `AM'`,NoAsms] >>
  conj_tac >- simp[Abbr `AE'`,NoAsms] >>
  conj_tac >- simp[Abbr `AK'`,NoAsms] >>
  ntac 11 (conj_tac >- first_assum ACCEPT_TAC) >>
  `FDOM blocks' = FDOM m'` by
    (qpat_assum `FDOM blocks' = FDOM m UNION _` SUBST1_TAC >>
     sym_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_assum `FDOM m' = FDOM es'` (SUBST1_TAC o SYM) >>
    first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `FDOM m' = FDOM ks'` (SUBST1_TAC o SYM) >>
    first_assum ACCEPT_TAC) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qx_gen_tac `i` >> disch_tac >>
     qpat_assum `!i. i < LENGTH p ==> ?f g ai ent ord h b done child. _`
       (drule_then strip_assume_tac) >>
     qpat_assum `calls' = calls` SUBST1_TAC >>
     qpat_assum `FLOOKUP calls (DROP (SUC i) p,_,_) = SOME (EL i inds,_,_,_,_,NONE)`
       (assume_tac o REWRITE_RULE [pairTheory.PAIR]) >>
     goal_assum drule) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "package_frame" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexistsl [`lm`,`rm`,`le`,`re`,`lk`,`rk`] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_block_path_update[package_frame]:
  qx_gen_tac `a` >> qx_gen_tac `e` >>
  disch_then (fn frame =>
    map_every (fn (pat, eq) =>
      qpat_assum pat (qspecl_then [`LENGTH p`,`a`,`e`] (fn th =>
        qpat_assum eq (fn fin =>
          assume_tac (SIMP_RULE (srw_ss()) [frame,SYM fin] th)))))
      [(`!i a e. _ ==> FLOOKUP (EL i mts) (a,e) = FLOOKUP m (a,e)`,
        `m' = EL (LENGTH p) mts`),
       (`!i a e. _ ==> FLOOKUP (EL i ets) (a,e) = FLOOKUP es (a,e)`,
        `es' = EL (LENGTH p) ets`),
       (`!i a e. _ ==> FLOOKUP (EL i kts) (a,e) = FLOOKUP ks (a,e)`,
        `ks' = EL (LENGTH p) kts`)]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise dft_packet_block_path_update
