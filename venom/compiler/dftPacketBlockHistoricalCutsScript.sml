Theory dftPacketBlockHistoricalCuts
Ancestors
  dftPacketBlockHistorySelectedFrame dftPacketBlockTerminatorCoverage
  dftPacketBlockHistoryRootPrefix dftPacketSelectedCutTransport
  dftPacketTableSplice dftPacketBlockHistoryFrame dftPacketBlockTableSplice
  dftGasFromListTraceDefs dftGasInvCrossingProbe dftRunRel
  dftDefs dftStructural venomExecSemantics venomInst venomState sorting
  finite_map list rich_list arithmetic pred_set

(* The two pieces of each selected row avoid all overwritten cells. *)
Theorem historical_table_piece[local]:
  !(tab:(((num # num) list # num),'v list list) fmap) out p d inds
    ai ei ds qi rows.
    FLOOKUP tab (ai,ei) = SOME rows /\ (ai,ei) <> (p,SUC d) /\
    (!f. MEM f ds ==> (ai,f) <> (p,SUC d) /\
      (!k. k < LENGTH p ==> (ai,f) <> (DROP (SUC k) p,FST (EL k p)))) /\
    (!k. k < LENGTH p /\ (ai,ei) = (DROP (SUC k) p,FST (EL k p)) ==>
      qi <= EL k inds) /\
    (!a e. (a,e) <> (p,SUC d) /\
      (!k. k < LENGTH p ==> (a,e) <> (DROP (SUC k) p,FST (EL k p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!k rows. k < LENGTH p /\
      FLOOKUP tab (DROP (SUC k) p,FST (EL k p)) = SOME rows ==>
      ?v. FLOOKUP out (DROP (SUC k) p,FST (EL k p)) =
        SOME (LUPDATE v (EL k inds) rows)) ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP out (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP out (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP tab (ai,ei))))
Proof
  rpt gen_tac >> strip_tac >>
  `MAP (\f. FLAT (THE (FLOOKUP out (ai,f)))) ds =
   MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds` by
    (irule MAP_CONG >> simp[] >> metis_tac[]) >>
  `TAKE qi (THE (FLOOKUP out (ai,ei))) = TAKE qi rows` by
    (Cases_on `?k. k < LENGTH p /\ (ai,ei) = (DROP (SUC k) p,FST (EL k p))`
     >- (pop_assum strip_assume_tac >>
         `qi <= EL k inds` by metis_tac[] >>
         qpat_x_assum `!k rows. _ ==> ?v. _` (qspecl_then [`k`,`rows`] mp_tac) >>
         fs[] >> strip_tac >> gvs[dft_packet_row_prefix_splice]) >>
     `FLOOKUP out (ai,ei) = FLOOKUP tab (ai,ei)` by metis_tac[] >> simp[]) >>
  simp[]
QED

(* The old activation and source row are retained even when the block cursor
   is overwritten by its completed form. *)
Theorem historical_structure_frame[local]:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (rho:num list) (count:num).
  FLOOKUP acts p = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) /\
  (p,SUC d) NOTIN FDOM blocks /\
  acts' = acts |+ (p,(sf,tf,inc,entry,order ++ [SUC d],NONE,NONE)) /\
  blocks' = blocks |+ ((p,d),
    (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),LENGTH ys,OK post,T,SOME post.vs_gas_readings))
    |+ ((p,SUC d),newrow) /\
  FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
  FLOOKUP blocks (ai,ei) =
    SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
  orderi = ds ++ ei::later ==>
  ?order' res' nrest' count' front' closed' rest' later'.
    FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,order',res',nrest') /\
    FLOOKUP blocks' (ai,ei) =
      SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,count',front',closed',rest') /\
    order' = ds ++ ei::later'
Proof
  rpt gen_tac >> strip_tac >>
  `(ai,ei) <> (p,SUC d)` by metis_tac[FLOOKUP_DEF,optionTheory.NOT_SOME_NONE] >>
  qexistsl [`if ai = p then orderi ++ [SUC d] else orderi`,`resi`,`nresti`,
    `if (ai,ei) = (p,d) then LENGTH ys else counti`,
    `if (ai,ei) = (p,d) then OK post else fronti`,
    `(ai,ei) = (p,d) \/ closedi`,
    `if (ai,ei) = (p,d) then SOME post.vs_gas_readings else resti`,
    `if ai = p then later ++ [SUC d] else later`] >>
  Cases_on `ai = p` >> Cases_on `ei = d` >> gvs[FLOOKUP_UPDATE,APPEND_ASSOC]
QED

(* The closing row can gain no INVOKE in its completed prefix. *)
Theorem historical_endpoint[local]:
  !(blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    blocks' p d bb bt ps xs ys rho in_state h0 be hbe count s post newrow.
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) /\
  blocks' = blocks |+ ((p,d),
    (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),LENGTH ys,OK post,T,SOME post.vs_gas_readings))
    |+ ((p,SUC d),newrow) /\
  (!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
    body_entry = NONE ==> (a,e) = (p,d)) /\
  (!r. r < LENGTH xs /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) ==>
  !a e bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti q.
    (a,e) <> (p,SUC d) /\
    FLOOKUP blocks' (a,e) =
      SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
    q < LENGTH xsi /\
    (!r. r < q /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r (TAKE counti rhoi)) ==>
    ?be' hbe' count' front' closed' rest'.
      bei = SOME (be',hbe') /\
      FLOOKUP blocks (a,e) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,count',front',closed',rest') /\
      (!r. r < q /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r (TAKE count' rhoi))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `(a,e) = (p,d)`
  >- (qpat_x_assum `FLOOKUP blocks' _ = _` mp_tac >>
      simp[FLOOKUP_UPDATE] >> strip_tac >>
      qexistsl [`be`,`hbe`] >> simp[] >> rpt strip_tac >>
      qpat_x_assum `!r. r < LENGTH xs /\ _ ==> _` (qspec_then `r` mp_tac) >>
      fs[] >> decide_tac) >>
  `FLOOKUP blocks (a,e) =
    SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti)` by
    (qpat_x_assum `FLOOKUP blocks' _ = _` mp_tac >> simp[FLOOKUP_UPDATE]) >>
  Cases_on `bei`
  >- (qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest. _`
       (drule_then mp_tac o REWRITE_RULE[AND_IMP_INTRO]) >> simp[]) >>
  PairCases_on `x` >> qexistsl [`x0`,`x1`,`counti`,`fronti`,`closedi`,`resti`] >> simp[]
QED

Theorem historical_next_key_absent[local]:
  !order inc d (blocks:('a # num,'b) fmap) p.
    order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
    LAST order = d /\ (!e. MEM e order <=> (p,e) IN FDOM blocks) ==>
    (p,SUC d) NOTIN FDOM blocks
Proof
  rpt gen_tac >> strip_tac >>
  `?n. LENGTH order = SUC n` by (Cases_on `LENGTH order` >> fs[]) >>
  `order = GENLIST (\i. inc + SUC i) (SUC n)` by metis_tac[] >>
  `d = inc + SUC n` by
    (qpat_assum `LAST order = d` mp_tac >>
     qpat_assum `order = GENLIST _ (SUC n)` (rewrite_tac o single) >> simp[GENLIST_LAST]) >>
  qpat_x_assum `!e. MEM e order <=> _` (qspec_then `SUC d` (rewrite_tac o single o GSYM)) >>
  qpat_assum `order = GENLIST _ (SUC n)` (rewrite_tac o single) >>
  simp[MEM_GENLIST] >> decide_tac
QED
Theorem dft_packet_block_historical_cuts:
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
    (ms_tab:(((num # num) list # num),bytes32 option list list) fmap)
    (es_tab:(((num # num) list # num),(string # num) list list) fmap)
    (ks_tab:(((num # num) list # num),gas_event list list) fmap)
    acts' blocks' ms_tab' es_tab' ks_tab' p d inds sf0 tf0 inc0 ent0 ord0
    bb0 bt0 ps0 xs0 ys0 rho0 in0 h00 be0 hbe0 pos0 s post newrow inst inst' st'
    AM AE AK AM' AE' AK' N N' C7 root_sf root_entry rooted_eval levels_ok.
    N <= N' /\
    FLOOKUP acts p = SOME (sf0,tf0,inc0,ent0,ord0,NONE,NONE) /\ LAST ord0 = d /\
    FLOOKUP blocks (p,d) =
      SOME (bb0,bt0,ps0,xs0,ys0,rho0,in0,h00,SOME (be0,hbe0),pos0,OK s,F,NONE) /\
    pos0 < LENGTH ys0 /\ inst = EL pos0 ys0 /\ is_terminator inst.inst_opcode /\
    ~post.vs_halted /\
    acts' = acts |+ (p,(sf0,tf0,inc0,ent0,ord0 ++ [SUC d],NONE,NONE)) /\
    blocks' = blocks |+ ((p,d),
      (bb0,bt0,ps0,xs0,ys0,rho0,in0,h00,SOME (be0,hbe0),LENGTH ys0,OK post,T,SOME post.vs_gas_readings))
      |+ ((p,SUC d),newrow) /\
    FDOM blocks = FDOM ms_tab /\ FDOM blocks = FDOM es_tab /\ FDOM blocks = FDOM ks_tab /\
    FDOM blocks' = FDOM ms_tab' /\ FDOM blocks' = FDOM es_tab' /\ FDOM blocks' = FDOM ks_tab' /\
    AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    AE = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    AM' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab' (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
    AE' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab' (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
    AK' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab' (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
    LENGTH inds = LENGTH p /\
    (!a e. (a,e) <> (p,SUC d) /\
      (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
      FLOOKUP ms_tab' (a,e) = FLOOKUP ms_tab (a,e) /\
      FLOOKUP es_tab' (a,e) = FLOOKUP es_tab (a,e) /\
      FLOOKUP ks_tab' (a,e) = FLOOKUP ks_tab (a,e)) /\
    (!i rows. i < LENGTH p /\ FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME rows ==>
      FLOOKUP ms_tab' (DROP (SUC i) p,FST (EL i p)) =
        SOME (LUPDATE (AM' (DROP i p)) (EL i inds) rows)) /\
    (!i rows. i < LENGTH p /\ FLOOKUP es_tab (DROP (SUC i) p,FST (EL i p)) = SOME rows ==>
      FLOOKUP es_tab' (DROP (SUC i) p,FST (EL i p)) =
        SOME (LUPDATE (AE' (DROP i p)) (EL i inds) rows)) /\
    (!i rows. i < LENGTH p /\ FLOOKUP ks_tab (DROP (SUC i) p,FST (EL i p)) = SOME rows ==>
      FLOOKUP ks_tab' (DROP (SUC i) p,FST (EL i p)) =
        SOME (LUPDATE (AK' (DROP i p)) (EL i inds) rows)) /\
    (!a sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      tf = dft_fn sf /\ dft_fn_rel sf tf /\
      order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
      (!e. MEM e order <=> (a,e) IN FDOM blocks)) /\
    (!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest.
      FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) ==>
      (?sf tf inc entry order res nrest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
        lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
        lookup_block bb.bb_label tf.fn_blocks = SOME bt) /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\x. is_pseudo x.inst_opcode) ps /\
      EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
      EVERY (\x. ~is_pseudo x.inst_opcode) ys /\ LENGTH xs = LENGTH ys /\
      PERM rho (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
        from_block [EL q xs] y) rho ys /\
      (body_entry = NONE ==> (a,e) = (p,d))) /\
    (!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
      FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
      FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP es_tab (a,e) = SOME ess /\ FLOOKUP ks_tab (a,e) = SOME ks ==>
      LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
      (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
        case FLOOKUP calls (a,e,(EL q xs).inst_id) of
          NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
        | SOME call => EL q ms = AM ((e,(EL q xs).inst_id)::a) /\
            EL q ess = AE ((e,(EL q xs).inst_id)::a) /\ EL q ks = AK ((e,(EL q xs).inst_id)::a))) /\
    (!a e cid q h b done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done_at_call,child_entry,ret) ==>
      ?bb bt ps xs ys rho hin h0 be hbe pos front closed brest.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),pos,front,closed,brest) /\
        q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ (EL q xs).inst_id = cid /\
        (case ret of
          NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
        | SOME triple => MEM q (TAKE pos rho))) /\
    (!k. k < LENGTH p ==>
      ?sf tf inc entry order bb bt ps xs ys rho in_state h0 be hbe count
       h b0 done_at_call child_entry.
        FLOOKUP acts (DROP (SUC k) p) = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
        LAST order = FST (EL k p) /\
        FLOOKUP blocks (DROP (SUC k) p,FST (EL k p)) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
        FLOOKUP calls (DROP (SUC k) p,FST (EL k p),SND (EL k p)) =
          SOME (EL k inds,h,b0,done_at_call,child_entry,NONE) /\
        done_at_call = TAKE count rho /\ b0.vs_inst_idx = LENGTH ps + count /\
        get_instruction bt b0.vs_inst_idx = SOME (EL (EL k inds) xs)) /\
    (!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
          body_entry count front closed brest q z.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      ((IS_SOME body_entry /\ q < LENGTH xs /\
        z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
        (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho))) \/
       (body_entry = NONE /\ a = p /\ e = d /\ q = 0 /\
        z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s.vs_inst_idx ps))) ==>
      ?cuts levels Mcut Ecut Kcut mr er kr.
        MAP (\(ai,ds,ei,qi,zi). ai) cuts = REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then ai = a /\ ei = e /\ qi = q /\ zi = z else
              ?cid h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
            EL i levels = (sfi,
              MAP (\f. case THE (FLOOKUP blocks (ai,f)) of
                (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) =>
                  (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds ++ [(bbi,ei,zi)],
              if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
        Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
        AM [] = Mcut ++ mr /\ AE [] = Ecut ++ er /\ AK [] = Kcut ++ kr /\
        LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
        (!F gs tail.
          N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
          levels_ok F C7 levels (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
            (MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts ai) of
                (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts)
            root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
          (?extra. Ecut = FST (rooted_eval F C7 levels
            (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
          (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
            OK u =>
              FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
              u.vs_gas_readings = tail /\
              (?before after.
                dftGasFromListTraceDefs$trace_blocks [] 0 F C7 root_sf
                  (root_entry with vs_gas_readings := gs ++ tail) =
                  before ++ [((a,e,(EL (LENGTH z)
                    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
                    EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
                dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
              (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
                (Ecut,OK (u with vs_gas_readings := tail'))) /\
              (body_entry = NONE ==> u with vs_gas_readings := s.vs_gas_readings = s) /\
              (a = p /\ e = d /\ IS_SOME body_entry /\
               inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
                (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op s) /\
                u.vs_initial_fmp = s.vs_initial_fmp)
          | stopped =>
              run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
              gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
                FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))) ==>
    !a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
        body_entry count front closed brest q z.
      (a,e) <> (p,SUC d) /\
      FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      FLOOKUP blocks' (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      ((IS_SOME body_entry /\ q < LENGTH xs /\
        z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
        (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho))) \/
       (body_entry = NONE /\ a = p /\ e = SUC d /\ q = 0 /\
        z = DROP (phi_prefix_length bb.bb_instructions) (TAKE st'.vs_inst_idx ps))) ==>
      ?cuts levels Mcut Ecut Kcut mr er kr.
        MAP (\(ai,ds,ei,qi,zi). ai) cuts = REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks' (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then ai = a /\ ei = e /\ qi = q /\ zi = z else
              ?cid h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
            EL i levels = (sfi,
              MAP (\f. case THE (FLOOKUP blocks' (ai,f)) of
                (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) =>
                  (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds ++ [(bbi,ei,zi)],
              if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ms_tab' (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es_tab' (ai,ei))))) cuts) /\
        Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ks_tab' (ai,ei))))) cuts) /\
        AM' [] = Mcut ++ mr /\ AE' [] = Ecut ++ er /\ AK' [] = Kcut ++ kr /\
        LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
        (!F gs tail.
          N' <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
          levels_ok F C7 levels (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
            (MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts' ai) of
                (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts)
            root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
          (?extra. Ecut = FST (rooted_eval F C7 levels
            (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
          (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
            OK u =>
              FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
              u.vs_gas_readings = tail /\
              (?before after.
                dftGasFromListTraceDefs$trace_blocks [] 0 F C7 root_sf
                  (root_entry with vs_gas_readings := gs ++ tail) =
                  before ++ [((a,e,(EL (LENGTH z)
                    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
                    EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
                dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
              (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
                (Ecut,OK (u with vs_gas_readings := tail'))) /\
              (body_entry = NONE ==> u with vs_gas_readings := st'.vs_gas_readings = st') /\
              (a = p /\ e = SUC d /\ IS_SOME body_entry /\
               inv_memory_observation inst'.inst_opcode /\ EL q xs = inst' ==>
                (!op. MEM op inst'.inst_operands ==> eval_operand op u = eval_operand op st') /\
                u.vs_initial_fmp = st'.vs_initial_fmp)
          | stopped =>
              run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
              gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
                FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  map_every qx_gen_tac [`a`,`e`,`sf`,`tf`,`inc`,`entry`,`order`,`res`,`nrest`,
    `bb`,`bt`,`ps`,`xs`,`ys`,`rho1`,`in_state`,`h0`,`body_entry`,`count1`,
    `front`,`closed`,`brest`,`q`,`z`] >> reverse strip_tac
  >- (qpat_x_assum `(a,e) <> (p,SUC d)` mp_tac >> simp[]) >>
  `(p,SUC d) NOTIN FDOM blocks` by
    (qpat_assum `!a sf tf inc entry order res nrest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
        tf = dft_fn sf /\ _`
       (qspecl_then [`p`] (drule_then strip_assume_tac)) >>
     irule historical_next_key_absent >> qexistsl [`inc0`,`ord0`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!r. r < LENGTH xs0 /\ (EL r xs0).inst_opcode = INVOKE ==>
       MEM r (TAKE pos0 rho0)` by
    (qpat_assum `!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest.
        FLOOKUP blocks (a,e) = SOME _ ==> (?sf tf inc entry order res nrest. _) /\ _`
       (qspecl_then [`p`,`d`] (drule_then mp_tac)) >>
     simp[] >> strip_tac >>
     qpat_assum `!a sf tf inc entry order res nrest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
        tf = dft_fn sf /\ _`
       (qspecl_then [`p`] (drule_then strip_assume_tac)) >>
     drule_all_then strip_assume_tac dft_packet_block_terminator_invoke_coverage >>
     qpat_assum `!r. r < LENGTH xs0 /\ _ ==> _` mp_tac >> simp[]) >>
  `!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
    body_entry = NONE ==> (a,e) = (p,d)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest.
        FLOOKUP blocks (a,e) = SOME _ ==> (?sf tf inc entry order res nrest. _) /\ _`
       (drule_then mp_tac) >> simp[]) >>
  drule_all_then strip_assume_tac historical_endpoint >>
  `?order0. FLOOKUP acts a = SOME (sf,tf,inc,entry,order0,res,nrest)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP acts' a = _`,`acts' = acts |+ _`,`FLOOKUP acts p = _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> Cases_on `a = p`
     >- (qexists `ord0` >> gvs[FLOOKUP_UPDATE]) >>
     qexists `order` >> gvs[FLOOKUP_UPDATE]) >>
  qpat_x_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
       body_entry count front closed brest q z. _ ==> ?cuts levels Mcut Ecut Kcut mr er kr. _`
    (qspecl_then [`a`,`e`] (drule_then (drule_then (qspecl_then [`q`,`z`] mp_tac)))) >>
  (impl_tac >- (disj1_tac >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `!i. i < LENGTH p ==>
    ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done_at_call child_entry call_h.
      FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,OK b0,F,NONE) /\
      FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
        SOME (EL i inds,call_h,b0,done_at_call,child_entry,NONE) /\
      dft_fn_rel sf tf /\
      lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
      lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\x. is_pseudo x.inst_opcode) ps /\
      EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ LENGTH xs = LENGTH ys /\
      PERM rho (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
        from_block [EL q xs] y) rho ys /\
      EL i inds < LENGTH xs /\ (EL (EL i inds) xs).inst_opcode = INVOKE /\
      b0.vs_inst_idx = LENGTH ps + pos /\
      get_instruction bt b0.vs_inst_idx = SOME (EL (EL i inds) xs)` by suspend "live_schedule" >>
  suspend "selected"
QED

Resume dft_packet_block_historical_cuts[live_schedule]:
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!k. k < LENGTH p ==> ?sf tf inc entry order bb bt ps xs ys rho in_state h0 be hbe count h b0 done_at_call child_entry. _`
    (qspec_then `i` (drule_then strip_assume_tac)) >>
  qpat_assum `!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest.
      FLOOKUP blocks (a,e) = SOME _ ==> (?sf tf inc entry order res nrest. _) /\ _`
    (qspecl_then [`DROP (SUC i) p`,`FST (EL i p)`] (drule_then strip_assume_tac)) >>
  qpat_assum `!a sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> tf = dft_fn sf /\ _`
    (qspec_then `DROP (SUC i) p` (drule_then strip_assume_tac)) >>
  qpat_assum `FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) = _`
    (fn row =>
      qpat_assum `!a e cid q h b done_at_call child_entry ret. FLOOKUP calls (a,e,cid) = _ ==> _`
        (qspecl_then [`DROP (SUC i) p`,`FST (EL i p)`,`SND (EL i p)`]
          (drule_then (strip_assume_tac o SRULE [row])))) >>
  qpat_assum `FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) = _` (irule_at Any) >>
  qpat_assum `FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) = _` (irule_at Any) >>
  qpat_assum `dft_fn_rel _ _` (irule_at Any) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_block_historical_cuts[selected]:
  `!i. i < LENGTH p ==>
     ?rows. FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME rows` by
    (qx_gen_tac `i` >> disch_tac >>
     qpat_assum `!i. i < LENGTH p ==> ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done_at_call child_entry call_h. _`
       (qspec_then `i` (drule_then strip_assume_tac)) >>
     qpat_assum `FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) = _` mp_tac >>
     qpat_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF] >> metis_tac[]) >>
  Q.ISPECL_THEN [`blocks`,`calls`,`p`,`d`,`inds`,`ms_tab`,`ms_tab'`]
    mp_tac dft_packet_block_history_prefix_frame >>
  (impl_tac >- suspend "mask_schedule_inputs") >>
  strip_tac >> suspend "selected_rows"
QED

Resume dft_packet_block_historical_cuts[mask_schedule_inputs]:
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!a e cid q h b done_at_call child_entry ret. FLOOKUP calls _ = _ ==> _`
        (drule_then strip_assume_tac) >>
      goal_assum (drule_at Any) >> simp[])
  >- (qx_gen_tac `a1` >> qx_gen_tac `e1` >> disch_tac >>
      qpat_assum `!a e. _ ==> FLOOKUP ms_tab' _ = _ /\ _`
        (qspecl_then [`a1`,`e1`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH p ==> ?rows. FLOOKUP ms_tab _ = _`
    (drule_then strip_assume_tac) >>
  qexistsl [`rows`,`AM' (DROP i p)`] >> simp[]
QED

Resume dft_packet_block_historical_cuts[selected_rows]:
  `!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      (!k. k < LENGTH p /\ (ai,ei) = (DROP (SUC k) p,FST (EL k p)) ==>
        qi <= EL k inds)` by suspend "selected_bound" >>
  suspend "selected_pieces"
QED

Resume dft_packet_block_historical_cuts[selected_bound]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`
    (drule_all_then strip_assume_tac) >>
  Cases_on `SUC i = LENGTH cuts`
  >- (qpat_assum `SUC i = LENGTH cuts` (fn guard =>
        qpat_assum `if SUC i = LENGTH cuts then _ else _`
          (strip_assume_tac o REWRITE_RULE [guard])) >>
      `FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho1,in_state,h0,SOME (be',hbe'),count',front',closed',rest')`
        by simp[] >>
      qpat_assum `!a e bb bt ps xs ys rho hin h be hbe pos front closed brest k.
          _ ==> TAKE k (THE (FLOOKUP ms_tab' _)) = _ /\ _`
        (qspecl_then [`a`,`e`] (drule_then (qspec_then `q` mp_tac))) >>
      simp[LESS_IMP_LESS_OR_EQ] >>
      map_every (fn pat => qpat_assum pat SUBST1_TAC)
        [`ai = a`,`ei = e`,`qi = q`] >> simp[]) >>
  qpat_assum `~(SUC i = LENGTH cuts)` (fn guard =>
    qpat_assum `if SUC i = LENGTH cuts then _ else _`
      (strip_assume_tac o REWRITE_RULE [guard])) >>
  qpat_assum `!a e cid q h b done_at_call child_entry ret.
      _ ==> TAKE q (THE (FLOOKUP ms_tab' _)) = _ /\ _`
    (qspecl_then [`ai`,`ei`,`cid`] (drule_then (mp_tac o CONJUNCT2))) >>
  simp[]
QED

Resume dft_packet_block_historical_cuts[selected_pieces]:
  `!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      (ai,ei) IN FDOM blocks /\
      (!f. MEM f ds ==> (ai,f) IN FDOM blocks /\
        (!k. k < LENGTH p ==> (ai,f) <> (DROP (SUC k) p,FST (EL k p))))` by
    suspend "selected_domains" >>
  `!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP ms_tab' (ai,ei)))) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei)))) /\
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP es_tab' (ai,ei)))) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei)))) /\
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP ks_tab' (ai,ei)))) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))` by
    suspend "piece_algebra" >>
  suspend "root_prefix"
QED

Resume dft_packet_block_historical_cuts[selected_domains]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> tf = dft_fn sf /\ _`
    (qspec_then `ai` (drule_then strip_assume_tac)) >>
  conj_tac
  >- (qpat_assum `!e. MEM e orderi <=> _` (qspec_then `ei` (mp_tac o iffLR)) >>
      qpat_assum `orderi = ds ++ ei::later` SUBST1_TAC >> simp[MEM_APPEND]) >>
  qx_gen_tac `f` >> disch_tac >> conj_tac
  >- (qpat_assum `!e. MEM e orderi <=> _` (qspec_then `f` (mp_tac o iffLR)) >>
      qpat_assum `orderi = ds ++ ei::later` SUBST1_TAC >> simp[MEM_APPEND]) >>
  `ALL_DISTINCT orderi` by
    (qpat_assum `orderi = GENLIST _ _` SUBST1_TAC >> simp[ALL_DISTINCT_GENLIST]) >>
  `~MEM (LAST orderi) ds` by
    (qpat_assum `ALL_DISTINCT orderi` mp_tac >>
     qpat_assum `orderi = ds ++ ei::later` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ALL_DISTINCT_APPEND,LAST_APPEND] >> metis_tac[MEM_LAST,MEM]) >>
  qx_gen_tac `k` >> disch_tac >> strip_tac >>
  qpat_assum `!k. k < LENGTH p ==> ?sf tf inc entry order bb bt ps xs ys rho in_state h0 be hbe count h b0 done_at_call child_entry. _`
    (qspec_then `k` (drule_then strip_assume_tac)) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`(ai,f) = _`,`~MEM (LAST orderi) ds`,`MEM f ds`,
     `LAST _ = FST (EL k p)`,`FLOOKUP acts ai = _`,`FLOOKUP acts (DROP (SUC k) p) = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]
QED

Resume dft_packet_block_historical_cuts[piece_algebra]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!i ai ds ei qi zi. _ ==> (ai,ei) IN FDOM blocks /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!j aj djs ej qj zj. _ ==> !k.
      k < LENGTH p /\ (aj,ej) = (DROP (SUC k) p,FST (EL k p)) ==> qj <= EL k inds`
    (qspecl_then [`i`,`ai`,`ds`,`ei`,`qi`,`zi`]
      (fn th => mp_tac th >> (impl_tac >- simp[]) >> disch_tac)) >>
  `(ai,ei) <> (p,SUC d) /\
    (!f. MEM f ds ==> (ai,f) <> (p,SUC d) /\
      (!k. k < LENGTH p ==> (ai,f) <> (DROP (SUC k) p,FST (EL k p))))` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`(ai,ei) IN FDOM blocks`,`(p,SUC d) NOTIN FDOM blocks`,
        `!f. MEM f ds ==> (ai,f) IN FDOM blocks /\ _`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  rpt conj_tac >> irule historical_table_piece >>
  (reverse conj_tac >-
    (qpat_assum `(ai,ei) IN FDOM blocks` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FDOM blocks = FDOM ms_tab`,`FDOM blocks = FDOM es_tab`,`FDOM blocks = FDOM ks_tab`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF])) >>
  qexistsl [`d`,`inds`,`p`] >> simp[] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  metis_tac[]
QED

Resume dft_packet_block_historical_cuts[root_prefix]:
  `!a e bb bt ps xs ys rho hin h be hbe pos front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,front,closed,brest) ==>
    ?ms ess ks. FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP es_tab (a,e) = SOME ess /\
      FLOOKUP ks_tab (a,e) = SOME ks /\ LENGTH ms = LENGTH xs /\
      LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
      (!r. r < LENGTH xs /\ (EL r xs).inst_opcode = INVOKE ==>
        case FLOOKUP calls (a,e,(EL r xs).inst_id) of
          NONE => EL r ms = [] /\ EL r ess = [] /\ EL r ks = []
        | SOME call => EL r ms = AM ((e,(EL r xs).inst_id)::a) /\
          EL r ess = AE ((e,(EL r xs).inst_id)::a) /\
          EL r ks = AK ((e,(EL r xs).inst_id)::a))` by suspend "body_rows" >>
  `!a e cid q h b done ent ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,ent,ret) ==>
    ?ms ess ks. FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP es_tab (a,e) = SOME ess /\
      FLOOKUP ks_tab (a,e) = SOME ks /\ q < LENGTH ms /\ q < LENGTH ess /\ q < LENGTH ks /\
      EL q ms = AM ((e,cid)::a) /\ EL q ess = AE ((e,cid)::a) /\ EL q ks = AK ((e,cid)::a) /\
      cid = (EL q (FST (SND (SND (SND (THE (FLOOKUP blocks (a,e)))))))).inst_id` by
    suspend "old_cells" >>
  suspend "root_remainders"
QED

Resume dft_packet_block_historical_cuts[body_rows]:
  map_every qx_gen_tac [`ab`,`eb`] >> rpt gen_tac >> disch_tac >>
  `?ms ess ks. FLOOKUP ms_tab (ab,eb) = SOME ms /\
     FLOOKUP es_tab (ab,eb) = SOME ess /\ FLOOKUP ks_tab (ab,eb) = SOME ks` by
    (qpat_assum `FLOOKUP blocks (ab,eb) = _` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FDOM blocks = FDOM ms_tab`,`FDOM blocks = FDOM es_tab`,`FDOM blocks = FDOM ks_tab`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF] >> metis_tac[]) >>
  qexistsl [`ms`,`ess`,`ks`] >>
  qpat_assum `!a1 e1 bb1 bt1 ps1 xs1 ys1 rho1 hin1 h1 be1 hbe1 pos1 fr1 cl1 br1 m1 e2 k1.
    FLOOKUP blocks (a1,e1) = SOME (bb1,bt1,ps1,xs1,ys1,rho1,hin1,h1,SOME (be1,hbe1),pos1,fr1,cl1,br1) /\
    FLOOKUP ms_tab (a1,e1) = SOME m1 /\ FLOOKUP es_tab (a1,e1) = SOME e2 /\
    FLOOKUP ks_tab (a1,e1) = SOME k1 ==> _`
    (qspecl_then [`ab`,`eb`] (drule_all_then mp_tac)) >> simp[]
QED

Resume dft_packet_block_historical_cuts[old_cells]:
  map_every qx_gen_tac [`ac`,`ec`,`cidc`,`qc`] >> rpt gen_tac >>
  disch_then (mk_asm "cell_lookup") >>
  qpat_assum `!aa ee ci q h b done ent ret. FLOOKUP calls (aa,ee,ci) = _ ==>
    ?bb bt ps xs ys rho hin h0 be hbe pos closed_front closed rest. _`
    (fn rule => asm "cell_lookup" (mp_then Any strip_assume_tac rule)) >>
  qpat_assum `!aa ee bb bt ps xs ys rho hin h be hbe pos front closed brest.
    FLOOKUP blocks (aa,ee) = _ ==> ?ms ess ks. _`
    (fn rule => qpat_assum `FLOOKUP blocks (ac,ec) = _`
      (mp_then Any strip_assume_tac rule)) >>
  asm_x "cell_lookup" assume_tac >>
  qpat_x_assum `(EL qc _).inst_id = cidc` (SUBST_ALL_TAC o SYM) >>
  qexistsl [`ms`,`ess`,`ks`] >>
  qpat_x_assum `!r. r < LENGTH _ /\ (EL r _).inst_opcode = INVOKE ==> _`
    (qspec_then `qc` mp_tac) >>
  impl_tac >- simp[] >>
  asm_rewrite_tac[optionTheory.option_case_def] >> strip_tac >> simp[]
QED

Resume dft_packet_block_historical_cuts[root_remainders]:
  `!i. i < LENGTH p ==> ?h b done ent.
     FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
       SOME (EL i inds,h,b,done,ent,NONE)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!k. k < LENGTH p ==> ?sf tf inc entry order bb bt ps xs ys rho in_state h0 be hbe count h b0 done_at_call child_entry. _`
       (qspec_then `i` (drule_then strip_assume_tac)) >>
     rpt (first_assum (irule_at Any))) >>
  `!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
     ?sfi tfi inci enti orderi resi nresti later ms ess ks.
       FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
       orderi = ds ++ ei::later /\ FLOOKUP ms_tab (ai,ei) = SOME ms /\
       FLOOKUP es_tab (ai,ei) = SOME ess /\ FLOOKUP ks_tab (ai,ei) = SOME ks /\
       qi <= LENGTH ms /\ qi <= LENGTH ess /\ qi <= LENGTH ks /\
       (SUC i < LENGTH cuts ==>
         ?cid h b done ent ret. FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b,done,ent,ret) /\
           FST (EL (SUC i) cuts) = (ei,cid)::ai)` by suspend "root_rows" >>
  suspend "apply_root_prefix"
QED

Resume dft_packet_block_historical_cuts[root_rows]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`
    (drule_all_then strip_assume_tac) >>
  `?be hbe. bei = SOME (be,hbe)` by
    (Cases_on `bei`
     >- (qpat_assum `!aa ee bb bt ps xs ys rho hin h body count front closed rest.
           FLOOKUP blocks (aa,ee) = _ /\ body = NONE ==> (aa,ee) = (p,d)`
           (fn rule => qpat_assum `FLOOKUP blocks (ai,ei) = SOME (_,_,_,_,_,_,_,_,NONE,_,_,_,_)`
             (mp_then Any mp_tac rule)) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`FLOOKUP blocks (ai,ei) = SOME (_,_,_,_,_,_,_,_,NONE,_,_,_,_)`,
            `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[pairTheory.PAIR_EQ] >>
         rpt disch_tac >> gvs[]) >>
     Cases_on `x` >> simp[]) >>
  qpat_assum `bei = SOME _` SUBST_ALL_TAC >>
  qpat_assum `!aa ee bb bt ps xs ys rho hin h be hbe pos front closed brest.
    FLOOKUP blocks (aa,ee) = _ ==> ?ms ess ks. _`
    (fn rule => qpat_assum `FLOOKUP blocks (ai,ei) = _`
      (mp_then Any strip_assume_tac rule)) >>
  qexistsl [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`later`,`ms`,`ess`,`ks`] >>
  Cases_on `SUC i = LENGTH cuts`
  >- (qpat_x_assum `if SUC i = LENGTH cuts then _ else _` mp_tac >> simp[] >> strip_tac >>
      `LENGTH xsi = LENGTH xs` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`FLOOKUP blocks (ai,ei) = _`,`FLOOKUP blocks (a,e) = _`,`ai = a`,`ei = e`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >> simp[]) >>
  `SUC i < LENGTH cuts` by decide_tac >>
  qpat_assum `~(SUC i = LENGTH cuts)` (fn guard =>
    qpat_x_assum `if SUC i = LENGTH cuts then _ else _`
      (strip_assume_tac o REWRITE_RULE [guard])) >>
  simp[] >>
  qexistsl [`cid`,`h`,`b0`,`done_at_call`,`child_entry`,`ret`] >>
  qpat_x_assum `MAP _ cuts = _` kall_tac >>
  qpat_x_assum `EL (SUC i) (MAP _ cuts) = _` mp_tac >>
  simp[EL_MAP] >>
  Cases_on `EL (SUC i) cuts` >> rename1 `_ = (path,payload)` >>
  PairCases_on `payload` >> simp[]
QED

Resume dft_packet_block_historical_cuts[apply_root_prefix]:
  `?mr'. AM' [] = Mcut ++ mr'` by suspend "mask_remainder" >>
  `?er'. AE' [] = Ecut ++ er'` by suspend "site_remainder" >>
  `?kr'. AK' [] = Kcut ++ kr'` by suspend "key_remainder" >>
  suspend "transport"
QED

Resume dft_packet_block_historical_cuts[mask_remainder]:
  qpat_assum `Mcut = FLAT _` SUBST1_TAC >> irule dft_packet_block_history_root_prefix >>
  (conj_tac >- (qexists `a` >> first_assum ACCEPT_TAC)) >>
  qexistsl [`AM`,`acts`,`acts'`,`blocks`,`calls`,`d`,`ent0`,`inc0`,`inds`,
    `ord0`,`ms_tab'`,`p`,`sf0`,`tf0`] >>
  rpt (first_assum (irule_at Any)) >>
  conj_tac
  >- (map_every qx_gen_tac [`ap`,`ep`,`cidp`,`qp`,`hp`,`bp`,`dp`,`enp`,`rp`] >> disch_tac >>
      qpat_assum `!a e cid q h b done ent ret. FLOOKUP calls (a,e,cid) = _ ==>
        ?ms ess ks. _`
        (qspecl_then [`ap`,`ep`,`cidp`] (drule_then strip_assume_tac)) >>
      qexists `ms` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (map_every qx_gen_tac [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
      qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti later ms ess ks. _`
        (qspecl_then [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then strip_assume_tac)) >>
      qexistsl [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`later`,`ms`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> disch_tac >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (map_every qx_gen_tac [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
      qpat_assum `!i ai ds ei qi zi. _ ==> FLAT _ ++ _ = _ /\ _`
        (qspecl_then [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then (ACCEPT_TAC o CONJUNCT1)))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
  qpat_assum `(p,SUC d) NOTIN FDOM blocks` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF] >> metis_tac[]
QED

Resume dft_packet_block_historical_cuts[site_remainder]:
  qpat_assum `Ecut = FLAT _` SUBST1_TAC >> irule dft_packet_block_history_root_prefix >>
  (conj_tac >- (qexists `a` >> first_assum ACCEPT_TAC)) >>
  qexistsl [`AE`,`acts`,`acts'`,`blocks`,`calls`,`d`,`ent0`,`inc0`,`inds`,
    `ord0`,`es_tab'`,`p`,`sf0`,`tf0`] >>
  rpt (first_assum (irule_at Any)) >>
  conj_tac
  >- (map_every qx_gen_tac [`ap`,`ep`,`cidp`,`qp`,`hp`,`bp`,`dp`,`enp`,`rp`] >> disch_tac >>
      qpat_assum `!a e cid q h b done ent ret. FLOOKUP calls (a,e,cid) = _ ==>
        ?ms ess ks. _`
        (qspecl_then [`ap`,`ep`,`cidp`] (drule_then strip_assume_tac)) >>
      qexists `ess` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (map_every qx_gen_tac [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
      qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti later ms ess ks. _`
        (qspecl_then [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then strip_assume_tac)) >>
      qexistsl [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`later`,`ess`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> disch_tac >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (map_every qx_gen_tac [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
      qpat_assum `!i ai ds ei qi zi. _ ==> FLAT _ ++ _ = _ /\ _`
        (qspecl_then [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`]
          (drule_all_then (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2)))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
  qpat_assum `(p,SUC d) NOTIN FDOM blocks` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF] >> metis_tac[]
QED

Resume dft_packet_block_historical_cuts[key_remainder]:
  qpat_assum `Kcut = FLAT _` SUBST1_TAC >> irule dft_packet_block_history_root_prefix >>
  (conj_tac >- (qexists `a` >> first_assum ACCEPT_TAC)) >>
  qexistsl [`AK`,`acts`,`acts'`,`blocks`,`calls`,`d`,`ent0`,`inc0`,`inds`,
    `ord0`,`ks_tab'`,`p`,`sf0`,`tf0`] >>
  rpt (first_assum (irule_at Any)) >>
  conj_tac
  >- (map_every qx_gen_tac [`ap`,`ep`,`cidp`,`qp`,`hp`,`bp`,`dp`,`enp`,`rp`] >> disch_tac >>
      qpat_assum `!a e cid q h b done ent ret. FLOOKUP calls (a,e,cid) = _ ==>
        ?ms ess ks. _`
        (qspecl_then [`ap`,`ep`,`cidp`] (drule_then strip_assume_tac)) >>
      qexists `ks` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (map_every qx_gen_tac [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
      qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti later ms ess ks. _`
        (qspecl_then [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then strip_assume_tac)) >>
      qexistsl [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`later`,`ks`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> disch_tac >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (map_every qx_gen_tac [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
      qpat_assum `!i ai ds ei qi zi. _ ==> FLAT _ ++ _ = _ /\ _`
        (qspecl_then [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`]
          (drule_all_then (ACCEPT_TAC o CONJUNCT2 o CONJUNCT2)))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
  qpat_assum `(p,SUC d) NOTIN FDOM blocks` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF] >> metis_tac[]
QED

Resume dft_packet_block_historical_cuts[transport]:
  Q.ISPECL_THEN [`acts`,`blocks`,`calls`]
    (fn th => Q.ISPECL_THEN
      [`acts'`,`blocks'`,`calls`,`ms_tab`,`ms_tab'`,`es_tab`,`es_tab'`,`ks_tab`,`ks_tab'`,
       `levels_ok`,`rooted_eval`,`Ecut`,`body_entry`,`s`] mp_tac
      (Q.GENL [`acts'`,`blocks'`,`calls'`,`ms_tab`,`ms_tab'`,`es_tab`,`es_tab'`,`ks_tab`,`ks_tab'`,
        `levels_ok`,`rooted_eval`,`Ecut`,`body_entry`,`st`] th))
    (dft_packet_selected_cut_transport |> Q.GEN `gas_events_blocks` |>
      Q.ISPEC `gasEvents$gas_events_blocks`) >>
  (impl_tac >- suspend "transport_inputs") >>
  disch_then (qx_choose_then `new_mr` (qx_choose_then `new_er`
    (qx_choose_then `new_kr` (map_every assume_tac o CONJUNCTS)))) >>
  suspend "transport_finish"
QED

Resume dft_packet_block_historical_cuts[transport_inputs]:
  conj_tac >- suspend "transport_frame" >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "transport_inputs_rest"
QED

Resume dft_packet_block_historical_cuts[transport_frame]:
  map_every qx_gen_tac [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> irule historical_structure_frame >>
      rpt (first_assum (irule_at Any)) >>
      qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
          bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later.
          FLOOKUP acts ai = _ /\ FLOOKUP blocks (ai,ei) = _ /\ _`
        (qspecl_then [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then strip_assume_tac)) >>
      qpat_x_assum `FLOOKUP acts ai = _` (fn th =>
        qpat_x_assum `FLOOKUP acts ai = _` (mp_tac o REWRITE_RULE [th])) >>
      qpat_assum `_ = ds ++ ei::_` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (qpat_assum `!i ai ds ei qi zi. _ ==> (ai,ei) IN FDOM blocks /\ _`
        (drule_all_then (assume_tac o CONJUNCT2)) >>
      qx_gen_tac `f` >> disch_tac >>
      qpat_x_assum `!f. MEM f ds ==> _` (drule_then (assume_tac o CONJUNCT1)) >>
      `(ai,f) <> (p,SUC d)` by
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`(ai,f) IN FDOM blocks`,`(p,SUC d) NOTIN FDOM blocks`] >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
      Cases_on `(ai,f) = (p,d)` >> simp[FLOOKUP_UPDATE]) >>
  conj_tac >- simp[] >>
  qpat_assum `!i ai ds ei qi zi. _ ==> FLAT _ ++ _ = _ /\ _`
    (qspecl_then [`ix`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then ACCEPT_TAC))
QED

Resume dft_packet_block_historical_cuts[transport_inputs_rest]:
  map_every (fn (defpat,rempat) => conj_tac >-
    (qpat_assum defpat (fn def =>
       qpat_assum rempat (mp_tac o REWRITE_RULE [def])) >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]))
    [(`AM' = _`,`AM' [] = Mcut ++ _`),
     (`AE' = _`,`AE' [] = Ecut ++ _`),
     (`AK' = _`,`AK' [] = Kcut ++ _`)] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "transport_old_levels" >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "transport_old_semantics"
QED

Resume dft_packet_block_historical_cuts[transport_old_levels]:
  qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
      bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = _ /\ FLOOKUP blocks (ai,ei) = _ /\ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  rewrite_tac [pairTheory.pair_CASE_def] >> BETA_TAC >>
  disch_then ACCEPT_TAC
QED

Resume dft_packet_block_historical_cuts[transport_old_semantics]:
  map_every qx_gen_tac [`fuel`,`gs`,`tail`] >> disch_tac >>
  qpat_assum `!F gs tail. N <= F /\ _ ==> levels_ok F C7 levels _ _ root_sf _ [] 0 /\ _`
    (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  POP_ASSUM_LIST (K all_tac) >>
  rewrite_tac [pairTheory.pair_CASE_def] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Resume dft_packet_block_historical_cuts[transport_finish]:
  qexistsl [`cuts`,`levels`,`Mcut`,`Ecut`,`Kcut`,`new_mr`,`new_er`,`new_kr`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "transport_levels" >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "transport_finish_rest"
QED

Resume dft_packet_block_historical_cuts[transport_levels]:
  qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
      bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later.
      FLOOKUP acts' ai = _ /\ FLOOKUP blocks' (ai,ei) = _ /\ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  rewrite_tac [pairTheory.pair_CASE_def] >> BETA_TAC >>
  disch_then ACCEPT_TAC
QED

Resume dft_packet_block_historical_cuts[transport_finish_rest]:
  map_every (fn defpat => conj_tac >-
    (qpat_assum defpat (rewrite_tac o single) >> BETA_TAC >>
     first_assum ACCEPT_TAC))
    [`AM' = _`,`AE' = _`,`AK' = _`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "transport_successor_semantics"
QED

Resume dft_packet_block_historical_cuts[transport_successor_semantics]:
  map_every qx_gen_tac [`fuel`,`gs`,`tail`] >> strip_tac >>
  `N <= fuel` by
    (qpat_assum `N <= N'` mp_tac >> qpat_assum `N' <= fuel` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qpat_assum `!F gs tail. N <= F /\ _ ==>
    levels_ok F C7 levels _
      (MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts' ai))))) cuts)
      root_sf _ [] 0 /\ _` (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `body_entry = SOME _` mp_tac >>
  qpat_assum `(a,e) <> (p,SUC d)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  strip_tac >> strip_tac >>
  rewrite_tac [pairTheory.pair_CASE_def] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qhdtm_x_assum `exec_result_CASE` mp_tac >>
  Cases_on `SND (rooted_eval fuel C7 levels
    (root_entry with vs_gas_readings := gs ++ tail))` >> simp[] >>
  strip_tac >> strip_tac >> fs[]
QED

Finalise dft_packet_block_historical_cuts
