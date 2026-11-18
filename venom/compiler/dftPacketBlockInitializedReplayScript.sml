Theory dftPacketBlockInitializedReplay
Ancestors
  dftPacketBlockReplayFrame dftPacketBlockLocalReplay dftPacketBlockReplayStructure
  dftGasFromListTraceDefs dftRunRel dftIndexedExec stateEquiv
  venomExecProofs venomInst venomState list rich_list finite_map arithmetic

(* Replay on the tables already chosen by the initialized splice. *)
Theorem block_initialized_replay:
  !N N' C7 C8 p d inds
    (acts:((num # num) list,ir_function # ir_function # num # venom_state #
      num list # exec_result option # bytes32 list option) fmap) acts'
    (blocks:(((num # num) list # num),basic_block # basic_block #
      instruction list # instruction list # instruction list # num list #
      venom_state # num # (venom_state # num) option # num # exec_result #
      bool # bytes32 list option) fmap) blocks'
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    m es ks m' es' ks'
    AM AE AK AM' AE' AK' sf tf inc entry ord bb bt ps xs ys rho0 hin h0 be hb
    cnt0 s post bb1 bt1 ps1 xs1 ys1 rho1 j body1 s1 cm ce ck ms ess keys.
  let U = (\H acts0 blocks0 m es ks at.
    !a e bb bt ps xs ys rho hin h be hb cnt front closed brest ms ess keys
        sf tf inc entry order res nrest.
      at a e /\ FLOOKUP blocks0 (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,front,closed,brest) /\
      FLOOKUP m (a,e) = SOME ms /\ FLOOKUP es (a,e) = SOME ess /\
      FLOOKUP ks (a,e) = SOME keys /\
      FLOOKUP acts0 a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      !F k kgss tail.
        H <= F /\ k <= LENGTH xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
        (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE cnt rho)) /\
        LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
        (?extra. FLAT (TAKE k ess) = gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
        (!u. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
          gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
          u.vs_gas_readings = tail /\
          trace_gas (trace_block a e (F-e) C7 sf
            (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
            (be with vs_gas_readings := FLAT kgss ++ tail)) =
            ZIP (FLAT (TAKE k keys),FLAT kgss) /\
          (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
              (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
              (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) in
  let Q = (\H blocks0 m.
    !a e cid q h b0 done child ret bb bt ps xs ys rho hin hbe be hb cnt front closed brest ms.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child,ret) /\
      FLOOKUP blocks0 (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,hbe,SOME (be,hb),cnt,front,closed,brest) /\
      FLOOKUP m (a,e) = SOME ms ==>
      !F kgss tail u.
        H <= F /\ LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
        FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
        (!callee args. setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
          setup_callee callee args b0)) in
  let R = (\H acts0 blocks0 m es ks at.
    !a e sf tf inc entry order res rest bb bt ps xs ys rho hin h be hb cnt r8 u0 ms ess keys.
      at a e /\ FLOOKUP acts0 a = SOME (sf,tf,inc,entry,order,res,rest) /\
      FLOOKUP blocks0 (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,r8,T,SOME u0) /\
      FLOOKUP m (a,e) = SOME ms /\ FLOOKUP es (a,e) = SOME ess /\ FLOOKUP ks (a,e) = SOME keys ==>
      terminates r8 /\
      PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ u0) be.vs_gas_readings /\
      (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==> EVERY IS_SOME (FLAT ms) /\ u0 = v.vs_gas_readings) /\
      (!F. H <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK ys be = r8 /\
        (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
          (?extra. FLAT ess = gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail) ++ extra) /\
          ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
              (be with vs_gas_readings := gs ++ tail))) ==>
            terminates (FOLDR (dft_exec_cons (F-e) C7) OK xs (be with vs_gas_readings := gs ++ tail)) /\
            dft_res_rel (restore_result [] (FOLDR (dft_exec_cons (F-e) C7) OK xs
              (be with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
            (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
              gas_events_block (F-e) C7 sf.fn_name
                <|bb_label := be.vs_current_bb; bb_instructions :=
                  REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
                (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
              residual_result tail r8 (FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail)))) /\
          (!v. (FOLDR (dft_exec_cons (F-e) C7) OK xs
                  (be with vs_gas_readings := gs ++ tail) = OK v \/
                ?ir. FOLDR (dft_exec_cons (F-e) C7) OK xs
                  (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
            trace_gas (trace_block a e (F-e) C7 sf
                <|bb_label := be.vs_current_bb; bb_instructions :=
                  REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
                (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT keys,gs))))) in
  let A = (\H acts0 am ae ak.
    !a sf tf inc entry order r8 u0.
      FLOOKUP acts0 a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
      terminates r8 /\ LENGTH (am a) = LENGTH (ae a) /\ LENGTH (am a) = LENGTH (ak a) /\
      PERM (MAP THE (FILTER IS_SOME (am a)) ++ u0) entry.vs_gas_readings /\
      (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==> EVERY IS_SOME (am a) /\ u0 = v.vs_gas_readings) /\
      (!F. H <= F ==> run_blocks (F-inc) C8 tf entry = r8 /\
        (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (am a) gs ==>
          (?extra. ae a = gas_events_blocks (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
          ((?f. terminates (run_blocks f C7 sf (entry with vs_gas_readings := gs ++ tail))) ==>
            terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
            dft_res_rel (restore_result [] (run_blocks (F-inc) C7 sf
              (entry with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
            (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
              gas_events_blocks (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail) = ae a /\
              residual_result tail r8 (run_blocks (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail)))) /\
          (!v. (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = OK v \/
                ?ir. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
            trace_gas (trace_blocks a inc (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail)) = ZIP (ak a,gs))))) in
  let inv_cells = (\blocks0 m es ks am ae ak at.
    !a e bb bt ps xs ys rho hin h be hb cnt front closed rest ms ess keys.
      at a e /\ FLOOKUP blocks0 (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,front,closed,rest) /\
      FLOOKUP m (a,e) = SOME ms /\ FLOOKUP es (a,e) = SOME ess /\ FLOOKUP ks (a,e) = SOME keys ==>
      !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
        case FLOOKUP calls (a,e,(EL q xs).inst_id) of
          NONE => EL q ms = [] /\ EL q ess = [] /\ EL q keys = []
        | SOME call => EL q ms = am ((e,(EL q xs).inst_id)::a) /\
            EL q ess = ae ((e,(EL q xs).inst_id)::a) /\ EL q keys = ak ((e,(EL q xs).inst_id)::a)) in
  let W = (\blocks0 at.
    !a e bb bt ps xs ys rho hin h be hb cnt front closed rest.
      at a e /\ FLOOKUP blocks0 (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,front,closed,rest) ==>
      !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE cnt rho) ==>
        ?ch b done child ir child_out caller_post.
          FLOOKUP calls (a,e,(EL q xs).inst_id) =
            SOME (q,ch,b,done,child,SOME (ir,child_out,caller_post))) in
  let all = (\a e. T) in
  N <= N' /\
  FLOOKUP acts p = SOME (sf,tf,inc,entry,ord,NONE,NONE) /\
  acts' = acts |+ (p,(sf,tf,inc,entry,ord ++ [SUC d],NONE,NONE)) /\
  FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,rho0,hin,h0,SOME (be,hb),cnt0,OK s,F,NONE) /\
  blocks' = (blocks |+ ((p,d),(bb,bt,ps,xs,ys,rho0,hin,h0,SOME (be,hb),
      LENGTH ys,OK post,T,SOME post.vs_gas_readings))) |+
    ((p,SUC d),(bb1,bt1,ps1,xs1,ys1,rho1,post,SUC j,body1,0,OK s1,F,NONE)) /\
  (p,SUC d) NOTIN FDOM blocks /\ FDOM m = FDOM blocks /\
  FDOM es = FDOM blocks /\ FDOM ks = FDOM blocks /\
  (!i. i < LENGTH p ==>
    ?sf tf bb bt ps xs ys rho hin h be hb pos b0 done child ch.
      FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),pos,OK b0,F,NONE) /\
      FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
        SOME (EL i inds,ch,b0,done,child,NONE) /\
      dft_fn_rel sf tf /\ lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
      lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\x. is_pseudo x.inst_opcode) ps /\
      EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ LENGTH xs = LENGTH ys /\
      PERM rho (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
        from_block [EL q xs] y) rho ys /\
      EL i inds < LENGTH xs /\ (EL (EL i inds) xs).inst_opcode = INVOKE /\
      b0.vs_inst_idx = LENGTH ps + pos /\
      get_instruction bt b0.vs_inst_idx = SOME (EL (EL i inds) xs)) /\
  (!a e cid q h b done child ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
    ?bb bt ps xs ys rho hin h0 be hb pos front closed rest.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hb),pos,front,closed,rest) /\
      q < LENGTH xs /\ (EL q xs).inst_id = cid /\ (EL q xs).inst_opcode = INVOKE /\
      (case ret of NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
       | SOME triple => MEM q (TAKE pos rho))) /\
  (!a e bb bt ps xs ys rho hin h be hb pos front closed rest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),pos,front,closed,rest) ==>
    ALL_DISTINCT (MAP (\x. x.inst_id) xs) /\
    LENGTH (THE (FLOOKUP m (a,e))) = LENGTH xs /\
    LENGTH (THE (FLOOKUP es (a,e))) = LENGTH xs /\
    LENGTH (THE (FLOOKUP ks (a,e))) = LENGTH xs) /\
  (!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    (res = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p))))) /\
  (!a e. (a,e) <> (p,SUC d) /\
    (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
    FLOOKUP m' (a,e) = FLOOKUP m (a,e) /\
    FLOOKUP es' (a,e) = FLOOKUP es (a,e) /\
    FLOOKUP ks' (a,e) = FLOOKUP ks (a,e)) /\
  (!i mr er kr. i < LENGTH p /\
    FLOOKUP m (DROP (SUC i) p,FST (EL i p)) = SOME mr /\
    FLOOKUP es (DROP (SUC i) p,FST (EL i p)) = SOME er /\
    FLOOKUP ks (DROP (SUC i) p,FST (EL i p)) = SOME kr ==>
    FLOOKUP m' (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AM' (DROP i p)) (EL i inds) mr) /\
    FLOOKUP es' (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AE' (DROP i p)) (EL i inds) er) /\
    FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AK' (DROP i p)) (EL i inds) kr)) /\
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP m (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AE = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AM' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP m' (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
  AE' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es' (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
  AK' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks' (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
  (!a e cid q h b done child ir child_out caller_post.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,SOME (ir,child_out,caller_post)) ==>
    ?csf ctf order rest. FLOOKUP acts ((e,cid)::a) =
      SOME (csf,ctf,e,child,order,SOME (IntRet ir child_out),rest)) /\
  U N acts blocks m es ks all /\ Q N blocks m /\ R N acts blocks m es ks all /\
  A N acts AM AE AK /\ inv_cells blocks m es ks AM AE AK all /\ W blocks all /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE cnt0 rho0)) /\
  FLOOKUP m (p,d) = SOME ms /\ FLOOKUP es (p,d) = SOME ess /\ FLOOKUP ks (p,d) = SOME keys /\
  FLOOKUP m' (p,SUC d) = SOME cm /\ FLOOKUP es' (p,SUC d) = SOME ce /\ FLOOKUP ks' (p,SUC d) = SOME ck /\
  (body1 <> NONE ==> body1 = SOME (s1,SUC j) /\
    (!q. q < LENGTH xs1 /\ (EL q xs1).inst_opcode <> GAS ==>
       EL q cm = [] /\ EL q ce = [] /\ EL q ck = []) /\
    (!F k kgss tail.
       N' <= F /\ k <= LENGTH xs1 /\
       EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs1) /\
       (!q. q < k /\ (EL q xs1).inst_opcode = INVOKE ==> MEM q (TAKE 0 rho1)) /\
       LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k cm) kgss ==>
       (?extra. FLAT (TAKE k ce) = gas_events_block (F-SUC d) C7 sf.fn_name
         <|bb_label := s1.vs_current_bb; bb_instructions :=
           REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs1|>
         (s1 with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
       (!u. FOLDR (dft_exec_cons (F-SUC d) C7) OK (TAKE k xs1)
         (s1 with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
         gas_events_block (F-SUC d) C7 sf.fn_name
           <|bb_label := s1.vs_current_bb; bb_instructions :=
             REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs1|>
           (s1 with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ce) /\
         u.vs_gas_readings = tail /\
         trace_gas (trace_block p (SUC d) (F-SUC d) C7 sf
           (bb1 with bb_instructions := TAKE (LENGTH ps1 + k) bb1.bb_instructions)
           (s1 with vs_gas_readings := FLAT kgss ++ tail)) =
           ZIP (FLAT (TAKE k ck),FLAT kgss) /\
         (!tail'. FOLDR (dft_exec_cons (F-SUC d) C7) OK (TAKE k xs1)
             (s1 with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
           gas_events_block (F-SUC d) C7 sf.fn_name
             <|bb_label := s1.vs_current_bb; bb_instructions :=
               REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs1|>
             (s1 with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ce))))) /\
  (terminates (OK post) /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ post.vs_gas_readings) be.vs_gas_readings /\
    (!v. (OK post = OK v \/ (?ir. OK post = IntRet ir v)) ==>
      EVERY IS_SOME (FLAT ms) /\ post.vs_gas_readings = v.vs_gas_readings) /\
    (!F. N <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK ys be = OK post /\
      (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
        (?extra. FLAT ess = gas_events_block (F-d) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) ==>
          terminates (FOLDR (dft_exec_cons (F-d) C7) OK xs (be with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel (restore_result [] (FOLDR (dft_exec_cons (F-d) C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) (restore_result [] (OK post)) /\
          (((?v. OK post = OK v) \/ (?ir v. OK post = IntRet ir v)) ==>
            gas_events_block (F-d) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
            residual_result tail (OK post) (FOLDR (dft_exec_cons (F-d) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)))) /\
        (!v. (FOLDR (dft_exec_cons (F-d) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = OK v \/
              ?ir. FOLDR (dft_exec_cons (F-d) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          trace_gas (trace_block p d (F-d) C7 sf
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT keys,gs))))) ==>
  U N' acts' blocks' m' es' ks' all /\ Q N' blocks' m' /\
  R N' acts' blocks' m' es' ks' all /\ A N' acts' AM' AE' AK' /\
  inv_cells blocks' m' es' ks' AM' AE' AK' all /\ W blocks' all
Proof
  rpt gen_tac >> pure_rewrite_tac [LET_THM] >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> rewrite_tac [] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  MATCH_MP_TAC (REWRITE_RULE [] (CONV_RULE (REDEPTH_CONV BETA_CONV)
    (PURE_REWRITE_RULE [LET_THM] dft_packet_block_replay_frame))) >>
  qexistsl_tac [`N`,`p`,`d`,`inds`,`acts`,`blocks`,`m`,`es`,`ks`,`AM`,`AE`,`AK`,
    `sf`,`tf`,`inc`,`entry`,`ord`,`bb`,`bt`,`ps`,`xs`,`ys`,`rho0`,`hin`,`h0`,
    `be`,`hb`,`cnt0`,`s`,`post`,`bb1`,`bt1`,`ps1`,`xs1`,`ys1`,`rho1`,`post`,`SUC j`,`body1`,`s1`] >>
  ntac 14 (conj_tac >- first_assum ACCEPT_TAC) >>
  Q_TAC (fn args => mp_tac (CONV_RULE (REDEPTH_CONV BETA_CONV)
    (ISPECL (pairSyntax.strip_pair args) ancestor_lupdates_separate)))
    `(m,es,ks,m',es',ks',(\i. i < LENGTH p),(\i. (DROP (SUC i) p,FST (EL i p))),
      (\i. AM' (DROP i p)),(\i. AE' (DROP i p)),(\i. AK' (DROP i p)),(\i. EL i inds))` >>
  (impl_tac >- (conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  ntac 16 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `!a e. _ ==> FLOOKUP m' (a,e) = _ /\ _`
    (fn th => map_every (fn i => assume_tac
      (MATCH_MP block_closing_row_lookup (cj i th))) [1,2,3]) >>
  conj_tac >- suspend "open_rows" >>
  conj_tac >- suspend "closed_row" >>
  conj_tac >- suspend "invoke_cells" >>
  suspend "completion"
QED

Resume block_initialized_replay[completion]:
  qpat_assum `blocks' = _` (fn edit =>
  qpat_assum `FLOOKUP blocks (p,d) = SOME _` (fn old =>
  qpat_assum `!q. q < LENGTH xs /\ _ ==> MEM q (TAKE cnt0 rho0)` (fn cover =>
  qpat_assum `!a e bb bt ps xs ys ord hin h be hb cnt front closed rest.
    _ ==> !q. _ ==> ?ch b done child ir child_out caller_post. _` (fn complete =>
  POP_ASSUM_LIST (K (map_every assume_tac [edit,old,cover,complete])))))) >>
  rpt gen_tac >> strip_tac
  >- (gvs[FLOOKUP_UPDATE] >> gen_tac >> strip_tac >>
      qpat_assum `!a e bb bt ps xs ys ord hin h be hb cnt front closed rest. _`
        (drule_then irule) >> simp[]) >>
  gvs[FLOOKUP_UPDATE]
QED

Resume block_initialized_replay[closed_row]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`N <= N'`, `blocks' = _`, `acts' = _`,
     `FLOOKUP m' (p,d) = FLOOKUP m (p,d)`,
     `FLOOKUP es' (p,d) = FLOOKUP es (p,d)`,
     `FLOOKUP ks' (p,d) = FLOOKUP ks (p,d)`,
     `FLOOKUP m (p,d) = SOME ms`, `FLOOKUP es (p,d) = SOME ess`,
     `FLOOKUP ks (p,d) = SOME keys`, `terminates (OK post)`,
     `PERM _ be.vs_gas_readings`, `!v. _ ==> EVERY IS_SOME (FLAT ms) /\ _`,
     `!F. N <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK ys be = OK post /\ _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  rpt gen_tac >> strip_tac
  >- (gvs[FLOOKUP_UPDATE] >> qx_gen_tac `fuel` >> disch_tac >>
      qpat_assum `!F. N <= F ==> _` (qspec_then `fuel` mp_tac) >>
      (impl_tac >- decide_tac) >> simp[]) >>
  gvs[FLOOKUP_UPDATE]
QED

Resume block_initialized_replay[open_rows]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`N <= N'`, `blocks' = _`, `acts' = _`, `FLOOKUP acts p = SOME _`,
     `FLOOKUP blocks (p,d) = SOME _`,
     `FLOOKUP m' (p,d) = FLOOKUP m (p,d)`,
     `FLOOKUP es' (p,d) = FLOOKUP es (p,d)`,
     `FLOOKUP ks' (p,d) = FLOOKUP ks (p,d)`,
     `FLOOKUP m (p,d) = SOME ms`, `FLOOKUP es (p,d) = SOME ess`,
     `FLOOKUP ks (p,d) = SOME keys`, `FLOOKUP m' (p,SUC d) = SOME cm`,
     `FLOOKUP es' (p,SUC d) = SOME ce`, `FLOOKUP ks' (p,SUC d) = SOME ck`,
     `body1 <> NONE ==> _`,
     `!q. q < LENGTH xs /\ _ ==> MEM q (TAKE cnt0 rho0)`,
     `!a e bb bt ps xs ys rho hin h be hb cnt front closed brest ms ess keys
        sf tf inc entry order res nrest. _ ==> !F k kgss tail. _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  rpt gen_tac >> strip_tac
  >- (gvs[FLOOKUP_UPDATE] >>
      map_every qx_gen_tac [`fuel`,`npre`,`vals`,`tail0`] >> strip_tac >>
      `N <= fuel` by decide_tac >>
      qpat_assum `!q. q < LENGTH xs /\ _ ==> MEM q (TAKE cnt0 _)`
        (qspec_then `npre` mp_tac o MATCH_MP block_closing_invoke_prefix) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
      qpat_assum `!a e bb bt ps xs ys rho hin h be hb cnt front closed brest ms ess keys
        sf tf inc entry order res nrest. _ ==> !F k kgss tail. _`
        (drule_all_then mp_tac) >> simp[] >> metis_tac[FLOOKUP_UPDATE]) >>
  Cases_on `body1` >> gvs[FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  qpat_assum `!F k kgss tail. _ ==> _` (drule_all_then mp_tac) >> metis_tac[]
QED

Resume block_initialized_replay[invoke_cells]:
  `!a. a <> p ==> FLOOKUP acts' a = FLOOKUP acts a` by simp[FLOOKUP_UPDATE] >>
  `!i. i < LENGTH p ==>
    ?bb bt ps xs ys rho hin h be hb pos b0.
      FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),pos,OK b0,F,NONE)` by
    (rpt strip_tac >> qpat_assum `!i. i < LENGTH p ==> ?sf tf bb bt ps xs ys rho hin h be hb pos b0 done child ch. _`
      (drule_then strip_assume_tac) >> goal_assum drule) >>
  qpat_assum `!a e. _ ==> FLOOKUP m' (a,e) = _ /\ _`
    (fn th => map_every (assume_tac o (fn i => cj i th)) [1,2,3]) >>
  map_every (fn q => Q_TAC (fn args =>
    mp_tac (ISPECL (pairSyntax.strip_pair args) dft_packet_block_closed_frame)) q >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then (assume_tac o CONJUNCT2))
    [`(acts,acts',blocks,p,d,m,m',AM,AM')`,
     `(acts,acts',blocks,p,d,es,es',AE,AE')`,
     `(acts,acts',blocks,p,d,ks,ks',AK,AK')`] >>
  `!cid q h b done child ir out post1.
    FLOOKUP calls (p,d,cid) = SOME (q,h,b,done,child,SOME (ir,out,post1)) ==>
      AM' ((d,cid)::p) = AM ((d,cid)::p) /\
      AE' ((d,cid)::p) = AE ((d,cid)::p) /\
      AK' ((d,cid)::p) = AK ((d,cid)::p)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!a e cid q h b done child ir child_out caller_post. _ ==> ?csf ctf order rest. _`
       (drule_then strip_assume_tac) >>
     rpt conj_tac >> first_assum (drule_then (ACCEPT_TAC o cj 3))) >>
  `!cid. FLOOKUP calls (p,SUC d,cid) = NONE` by
    (gen_tac >> Cases_on `FLOOKUP calls (p,SUC d,cid)` >> simp[] >>
     PairCases_on `x` >>
     qpat_assum `!a e cid q h b done child ret. _ ==> ?bb bt ps xs ys rho hin h0 be hb pos front closed rest. _`
       (drule_then strip_assume_tac) >>
     qpat_assum `FLOOKUP blocks (p,SUC d) = SOME _`
       (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [flookup_thm]) >> simp[]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`blocks' = _`, `FLOOKUP blocks (p,d) = SOME _`,
     `FLOOKUP m' (p,d) = FLOOKUP m (p,d)`, `FLOOKUP es' (p,d) = FLOOKUP es (p,d)`,
     `FLOOKUP ks' (p,d) = FLOOKUP ks (p,d)`,
     `FLOOKUP m (p,d) = SOME ms`, `FLOOKUP es (p,d) = SOME ess`,
     `FLOOKUP ks (p,d) = SOME keys`, `FLOOKUP m' (p,SUC d) = SOME cm`,
     `FLOOKUP es' (p,SUC d) = SOME ce`, `FLOOKUP ks' (p,SUC d) = SOME ck`,
     `body1 <> NONE ==> _`, `!cid. FLOOKUP calls (p,SUC d,cid) = NONE`,
     `!cid q h b done child ir out post1. _ ==> AM' _ = _ /\ _`,
     `!q. q < LENGTH xs /\ _ ==> MEM q (TAKE cnt0 rho0)`,
     `!a e bb bt ps xs ys ord hin h be hb cnt front closed rest.
       _ ==> !q. _ ==> ?ch b done child ir child_out caller_post. _`,
     `!a e bb bt ps xs ys rho hin h be hb cnt front closed rest ms ess keys.
       _ ==> !q. _ ==> case FLOOKUP calls _ of NONE => _ | SOME call => _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  rpt gen_tac >> strip_tac
  >- (gvs[FLOOKUP_UPDATE] >> gen_tac >> strip_tac >>
      qpat_assum `!a e bb bt ps xs ys ord hin h be hb cnt front closed rest. _`
        (drule_then (qspec_then `q` mp_tac)) >> (impl_tac >- metis_tac[]) >>
      disch_then strip_assume_tac >>
      qpat_assum `!cid q h b done child ir out post1. _ ==> AM' _ = _ /\ _`
        (drule_then strip_assume_tac) >>
      metis_tac[]) >>
  Cases_on `body1` >> gvs[FLOOKUP_UPDATE] >> rpt strip_tac >>
  first_assum irule >> simp[]
QED

Finalise block_initialized_replay
