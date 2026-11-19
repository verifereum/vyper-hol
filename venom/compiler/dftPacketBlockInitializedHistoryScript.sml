Theory dftPacketBlockInitializedHistory
Ancestors
  dftPacketBlockHistoricalCuts dftPacketBlockLocalReplay gasEvents
  dftGasFromListTraceDefs dftGasInvCrossingProbe dftRunRel dftDefs dftStructural
  venomExecSemantics venomInst venomState sorting finite_map list rich_list arithmetic pred_set

(* The block initializer gives a single three-table update at each live
   caller. Historical transport only needs the three individual projections. *)
Theorem block_initialized_historical_cuts:
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
    acts' blocks' calls' ms_tab' es_tab' ks_tab' p d inds sf0 tf0 inc0 ent0 ord0
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
    calls' = calls /\
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
    inds = GENLIST (\i. FST (THE (FLOOKUP calls
      (DROP (SUC i) p,FST (EL i p),SND (EL i p))))) (LENGTH p) /\
    (!a e. (a,e) <> (p,SUC d) /\
      (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
      FLOOKUP ms_tab' (a,e) = FLOOKUP ms_tab (a,e) /\
      FLOOKUP es_tab' (a,e) = FLOOKUP es_tab (a,e) /\
      FLOOKUP ks_tab' (a,e) = FLOOKUP ks_tab (a,e)) /\
    (!i ms ess ks. i < LENGTH p /\
      FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME ms /\
      FLOOKUP es_tab (DROP (SUC i) p,FST (EL i p)) = SOME ess /\
      FLOOKUP ks_tab (DROP (SUC i) p,FST (EL i p)) = SOME ks ==>
      FLOOKUP ms_tab' (DROP (SUC i) p,FST (EL i p)) =
        SOME (LUPDATE (AM' (DROP i p)) (EL i inds) ms) /\
      FLOOKUP es_tab' (DROP (SUC i) p,FST (EL i p)) =
        SOME (LUPDATE (AE' (DROP i p)) (EL i inds) ess) /\
      FLOOKUP ks_tab' (DROP (SUC i) p,FST (EL i p)) =
        SOME (LUPDATE (AK' (DROP i p)) (EL i inds) ks)) /\
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
       q h b0 done_at_call child_entry cid e a.
        a = DROP (SUC k) p /\ (e,cid) = EL k p /\
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\ LAST order = e /\
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
        FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,NONE) /\
        done_at_call = TAKE count rho /\ b0.vs_inst_idx = LENGTH ps + count /\
        get_instruction bt b0.vs_inst_idx = SOME (EL q xs)) /\
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
              gasEvents$gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
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
                FLOOKUP calls' (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
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
              gasEvents$gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
                FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `calls' = calls` SUBST_ALL_TAC >>
  `LENGTH inds = LENGTH p` by simp[] >>
  `FDOM ms_tab = FDOM es_tab /\ FDOM ms_tab = FDOM ks_tab` by
    (map_every (fn pat => qpat_assum pat (rewrite_tac o single o SYM))
       [`FDOM blocks = FDOM ms_tab`, `FDOM blocks = FDOM es_tab`,
        `FDOM blocks = FDOM ks_tab`]) >>
  Q.ISPECL_THEN
    [`ms_tab`,`es_tab`,`ks_tab`,`ms_tab'`,`es_tab'`,`ks_tab'`,
     `\i. i < LENGTH p`,`\i. (DROP (SUC i) p,FST (EL i p))`,
     `\i. AM' (DROP i p)`,`\i. AE' (DROP i p)`,`\i. AK' (DROP i p)`,
     `\i. EL i inds`]
    (drule_all_then (map_every assume_tac o CONJUNCTS) o BETA_RULE)
    ancestor_lupdates_separate >>
  MATCH_MP_TAC dft_packet_block_historical_cuts >>
  qexistsl [`acts`,`blocks`,`ms_tab`,`es_tab`,`ks_tab`,`inds`,
    `sf0`,`tf0`,`inc0`,`ent0`,`ord0`,`bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,
    `in0`,`h00`,`be0`,`hbe0`,`pos0`,`s`,`post`,`newrow`,`inst`,`AM`,`AE`,`AK`,`N`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!k. k < LENGTH p ==> _` (qspec_then `k` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then strip_assume_tac >>
  qpat_x_assum `a = DROP (SUC k) p` SUBST_ALL_TAC >>
  qpat_x_assum `(e,cid) = EL k p` (assume_tac o SYM) >>
  rename1 `FLOOKUP blocks (DROP (SUC k) p,e) =
    SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,SOME (be,hbe),completed,OK b0,F,NONE)` >>
  `EL k inds = q` by simp[EL_GENLIST] >>
  qexistsl [`sf`,`tf`,`inc`,`entry`,`order`,`bb`,`bt`,`ps`,`xs`,`ys`,
    `row_order`,`in_state`,`h0`,`be`,`hbe`,`completed`,`h`,`b0`,`done_at_call`,`child_entry`] >>
  simp[]
QED
