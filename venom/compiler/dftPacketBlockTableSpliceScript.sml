Theory dftPacketBlockTableSplice
Ancestors
  dftGasFromListTraceDefs venomExecSemantics venomState venomInst
  finite_map list pred_set

Theorem dft_packet_block_order_append[local]:
  !order inc d.
    order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
    order <> [] /\ LAST order = d ==>
    ~MEM (SUC d) order /\
    order ++ [SUC d] =
      GENLIST (\i. inc + SUC i) (LENGTH (order ++ [SUC d]))
Proof
  rpt gen_tac >> strip_tac >>
  `?n. LENGTH order = SUC n` by
    (Cases_on `LENGTH order` >> gvs[]) >>
  `d = inc + SUC n` by
    (qpat_x_assum `LAST order = d` (fn th => rewrite_tac[GSYM th]) >>
     qpat_assum `order = _` (fn th => once_rewrite_tac[th]) >>
     simp[GENLIST_LAST]) >>
  conj_tac
  >- (qpat_x_assum `order = _` (fn th => once_rewrite_tac[th]) >>
      simp[MEM_GENLIST] >> decide_tac) >>
  qpat_x_assum `order = _` (fn th => once_rewrite_tac[th]) >>
  asm_simp_tac bool_ss [LENGTH_APPEND,LENGTH_GENLIST,LENGTH] >>
  `SUC n + SUC 0 = SUC (SUC n)` by decide_tac >>
  pop_assum (fn th => rewrite_tac[th]) >>
  pure_once_rewrite_tac[GENLIST] >>
  simp[SNOC_APPEND] >> simp[rich_listTheory.GENLIST]
QED

Theorem dft_packet_block_aggregate_append:
  !order d p (tab:('a # num,'b list list) fmap) rows.
    ~MEM (SUC d) order ==>
    FLAT (MAP (\e. FLAT (THE (FLOOKUP (tab |+ ((p,SUC d),rows)) (p,e))))
      (order ++ [SUC d])) =
    FLAT (MAP (\e. FLAT (THE (FLOOKUP tab (p,e)))) order) ++ FLAT rows
Proof
  rpt strip_tac >>
  `MAP (\e. FLAT (THE (FLOOKUP (tab |+ ((p,SUC d),rows)) (p,e)))) order =
   MAP (\e. FLAT (THE (FLOOKUP tab (p,e)))) order` by
    (irule MAP_CONG >> simp[FLOOKUP_UPDATE] >> metis_tac[]) >>
  simp[MAP_APPEND,FLAT_APPEND,FLOOKUP_UPDATE]
QED

Theorem dft_packet_block_table_splice:
  !acts blocks ms es ks (p:(num # num) list) (sf:ir_function) (tf:ir_function) inc
    (entry:venom_state) order d (bb:basic_block) (bt:basic_block)
    (ps:instruction list) (xs:instruction list) (ys:instruction list) (rho:num list) (in_state:venom_state) (h0:num)
    (be:venom_state) (hbe:num) count (s:venom_state) (post:venom_state)
    newrow (newms:bytes32 option list list) (newes:(string # num) list list)
    (newks:gas_event list list) acts1 blocks1 ms1 es1 ks1.
    FLOOKUP acts p = SOME (sf,tf,inc,entry,order,NONE:exec_result option,NONE:bytes32 list option) /\
    order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
    order <> [] /\ LAST order = d /\
    (!e. MEM e order <=> (p,e) IN FDOM blocks) /\
    FLOOKUP blocks (p,d) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME(be,hbe),count,OK s,F,NONE:bytes32 list option) /\
    FDOM blocks = FDOM ms /\ FDOM blocks = FDOM es /\ FDOM blocks = FDOM ks /\
    acts1 = acts |+ (p,(sf,tf,inc,entry,order ++ [SUC d],NONE,NONE)) /\
    blocks1 = (blocks |+ ((p,d),
      (bb,bt,ps,xs,ys,rho,in_state,h0,SOME(be,hbe),LENGTH ys,OK post,T,SOME post.vs_gas_readings)))
       |+ ((p,SUC d),newrow) /\
    ms1 = ms |+ ((p,SUC d),newms) /\
    es1 = es |+ ((p,SUC d),newes) /\
    ks1 = ks |+ ((p,SUC d),newks) ==>
    (p,SUC d) NOTIN FDOM blocks /\
    (p,SUC d) NOTIN FDOM ms /\
    (p,SUC d) NOTIN FDOM es /\
    (p,SUC d) NOTIN FDOM ks /\
    FLOOKUP acts1 p = SOME (sf,tf,inc,entry,order ++ [SUC d],NONE,NONE) /\
    (!a. a <> p ==> FLOOKUP acts1 a = FLOOKUP acts a) /\
    FLOOKUP blocks1 (p,d) = SOME
      (bb,bt,ps,xs,ys,rho,in_state,h0,SOME(be,hbe),LENGTH ys,OK post,T,SOME post.vs_gas_readings) /\
    FLOOKUP blocks1 (p,SUC d) = SOME newrow /\
    (!key. key <> (p,d) /\ key <> (p,SUC d) ==>
      FLOOKUP blocks1 key = FLOOKUP blocks key) /\
    FLOOKUP ms1 (p,SUC d) = SOME newms /\
    FLOOKUP es1 (p,SUC d) = SOME newes /\
    FLOOKUP ks1 (p,SUC d) = SOME newks /\
    (!key. key <> (p,SUC d) ==>
      FLOOKUP ms1 key = FLOOKUP ms key /\
      FLOOKUP es1 key = FLOOKUP es key /\
      FLOOKUP ks1 key = FLOOKUP ks key) /\
    FDOM acts1 = FDOM acts /\
    FDOM blocks1 = (p,SUC d) INSERT FDOM blocks /\
    FDOM blocks1 = FDOM ms1 /\ FDOM blocks1 = FDOM es1 /\ FDOM blocks1 = FDOM ks1 /\
    order ++ [SUC d] = GENLIST (\i. inc + SUC i) (LENGTH (order ++ [SUC d])) /\
    (!e. MEM e (order ++ [SUC d]) <=> (p,e) IN FDOM blocks1) /\
    FLAT (MAP (\e. FLAT (THE (FLOOKUP ms1 (p,e)))) (order ++ [SUC d])) =
      FLAT (MAP (\e. FLAT (THE (FLOOKUP ms (p,e)))) order) ++ FLAT newms /\
    FLAT (MAP (\e. FLAT (THE (FLOOKUP es1 (p,e)))) (order ++ [SUC d])) =
      FLAT (MAP (\e. FLAT (THE (FLOOKUP es (p,e)))) order) ++ FLAT newes /\
    FLAT (MAP (\e. FLAT (THE (FLOOKUP ks1 (p,e)))) (order ++ [SUC d])) =
      FLAT (MAP (\e. FLAT (THE (FLOOKUP ks (p,e)))) order) ++ FLAT newks
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM (SUC d) order /\
   order ++ [SUC d] = GENLIST (\i. inc + SUC i) (LENGTH (order ++ [SUC d]))` by
    (irule dft_packet_block_order_append >> metis_tac[]) >>
  `(p,d) IN FDOM blocks` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_SOME_NONE] >>
  `p IN FDOM acts` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_SOME_NONE] >>
  `(p,SUC d) NOTIN FDOM blocks` by metis_tac[] >>
  `(p,d) INSERT FDOM blocks = FDOM blocks /\
   p INSERT FDOM acts = FDOM acts` by metis_tac[ABSORPTION_RWT] >>
  map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
    [`acts1 = _`,`blocks1 = _`,`ms1 = _`,`es1 = _`,`ks1 = _`] >>
  asm_simp_tac bool_ss [dft_packet_block_aggregate_append] >>
  simp[FLOOKUP_UPDATE,FDOM_FUPDATE] >> metis_tac[]
QED

Theorem dft_packet_block_selected_frame:
  !acts blocks ms es ks (p:(num # num) list) d (sf:ir_function) (tf:ir_function) inc
    (entry:venom_state) order (bb:basic_block) (bt:basic_block)
    (ps:instruction list) (xs:instruction list) (ys:instruction list) (rho:num list) (in_state:venom_state) (h0:num)
    (be:venom_state) (hbe:num) count (s:venom_state) (post:venom_state)
    newrow (newms:bytes32 option list list) (newes:(string # num) list list)
    (newks:gas_event list list) acts1 blocks1 ms1 es1 ks1
    ai ei (sfi:ir_function) tfi inci enti orderi resi nresti
    bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti
    ds later orderi1 later1 qi zi (call:instruction option).
    FLOOKUP acts p = SOME (sf,tf,inc,entry,order,NONE:exec_result option,NONE:bytes32 list option) /\
    FLOOKUP blocks (p,d) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME(be,hbe),count,OK s,F,NONE:bytes32 list option) /\
    (p,SUC d) NOTIN FDOM blocks /\
    acts1 = acts |+ (p,(sf,tf,inc,entry,order ++ [SUC d],NONE,NONE)) /\
    blocks1 = (blocks |+ ((p,d),
      (bb,bt,ps,xs,ys,rho,in_state,h0,SOME(be,hbe),LENGTH ys,OK post,T,SOME post.vs_gas_readings)))
       |+ ((p,SUC d),newrow) /\
    ms1 = ms |+ ((p,SUC d),newms) /\
    es1 = es |+ ((p,SUC d),newes) /\
    ks1 = ks |+ ((p,SUC d),newks) /\
    FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
    FLOOKUP blocks (ai,ei) =
      SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
    orderi = ds ++ ei::later /\
    (!f. MEM f ds ==> (ai,f) IN FDOM blocks) /\
    orderi1 = (if ai = p then orderi ++ [SUC d] else orderi) /\
    later1 = (if ai = p then later ++ [SUC d] else later) ==>
    FLOOKUP acts1 ai = SOME (sfi,tfi,inci,enti,orderi1,resi,nresti) /\
    orderi1 = ds ++ ei::later1 /\
    (?count1 front1 closed1 rest1.
      FLOOKUP blocks1 (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,count1,front1,closed1,rest1)) /\
    (sfi,
     MAP (\f. (FST (THE (FLOOKUP blocks1 (ai,f))),f,
       DROP (phi_prefix_length (FST (THE (FLOOKUP blocks1 (ai,f)))).bb_instructions)
         (FST (THE (FLOOKUP blocks1 (ai,f)))).bb_instructions)) ds ++ [(bbi,ei,zi)],call) =
    (sfi,
     MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
       DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
         (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++ [(bbi,ei,zi)],call) /\
    FST (SND (SND (THE (FLOOKUP acts1 ai)))) = inci /\
    TAKE qi (THE (FLOOKUP ms1 (ai,ei))) = TAKE qi (THE (FLOOKUP ms (ai,ei))) /\
    TAKE qi (THE (FLOOKUP es1 (ai,ei))) = TAKE qi (THE (FLOOKUP es (ai,ei))) /\
    TAKE qi (THE (FLOOKUP ks1 (ai,ei))) = TAKE qi (THE (FLOOKUP ks (ai,ei))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms1 (ai,f)))) ds) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms (ai,f)))) ds) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es1 (ai,f)))) ds) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es (ai,f)))) ds) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks1 (ai,f)))) ds) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks (ai,f)))) ds)
Proof
  rpt gen_tac >> strip_tac >>
  `(ai,ei) IN FDOM blocks` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_SOME_NONE] >>
  `FLOOKUP acts1 ai = SOME (sfi,tfi,inci,enti,orderi1,resi,nresti)` by
    (Cases_on `ai = p` >> gvs[FLOOKUP_UPDATE]) >>
  `orderi1 = ds ++ ei::later1` by
    (Cases_on `ai = p` >> gvs[APPEND_ASSOC]) >>
  `?count1 front1 closed1 rest1.
      FLOOKUP blocks1 (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,count1,front1,closed1,rest1)` by
    (Cases_on `(ai,ei) = (p,d)`
     >- (gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
     `(ai,ei) <> (p,SUC d)` by metis_tac[] >>
     simp[FLOOKUP_UPDATE] >> metis_tac[]) >>
  `!key. key IN FDOM blocks ==>
     FLOOKUP ms1 key = FLOOKUP ms key /\
     FLOOKUP es1 key = FLOOKUP es key /\
     FLOOKUP ks1 key = FLOOKUP ks key` by
    (rpt strip_tac >> `key <> (p,SUC d)` by metis_tac[] >>
     simp[FLOOKUP_UPDATE] >> metis_tac[]) >>
  `!f. MEM f ds ==>
      FST (THE (FLOOKUP blocks1 (ai,f))) = FST (THE (FLOOKUP blocks (ai,f)))` by
    (rpt strip_tac >>
     `(ai,f) <> (p,SUC d)` by metis_tac[] >>
     Cases_on `ai = p` >- (gvs[FLOOKUP_UPDATE] >>
       Cases_on `f = d` >> gvs[]) >>
     gvs[FLOOKUP_UPDATE,EQ_SYM_EQ]) >>
  simp[] >>
  conj_tac
  >- (irule MAP_CONG >> simp[] >> metis_tac[]) >>
  rpt conj_tac >> AP_TERM_TAC >> irule MAP_CONG >> simp[] >> metis_tac[]
QED
