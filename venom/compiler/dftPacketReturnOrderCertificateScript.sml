Theory dftPacketReturnOrderCertificate
Ancestors
  dftPacketReturnOrder dftPacketReturnOrderEnumeration
  dftPacketReturnActivation dftGasFromListTraceDefs dftIndexedExec
  venomWf venomExecSemantics venomState venomInst gasEvents
  finite_map list rich_list arithmetic sorting

Theorem dft_packet_return_order_certificate:
  FLOOKUP (acts : ((num # num) list,
    ir_function # ir_function # num # venom_state # num list #
    exec_result option # bytes32 list option) fmap) b =
    SOME (sf,tf,inc,entry,order,NONE,NONE) /\
  order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
  LAST order = d /\ wf_function sf /\ wf_function tf /\
  FLOOKUP (blocks : (((num # num) list # num),
    basic_block # basic_block # instruction list # instruction list #
    instruction list # num list # venom_state # num #
    (venom_state # num) option # num # exec_result # bool #
    bytes32 list option) fmap) (b,d) =
    SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE) /\
  FLOOKUP blocks' (b,d) =
    SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),
      LENGTH cys,IntRet ir out,T,SOME out.vs_gas_readings) /\
  (!f. MEM f order /\ f <> d ==> FLOOKUP blocks' (b,f) = FLOOKUP blocks (b,f)) /\
  FDOM blocks = FDOM ms_tab /\ FDOM blocks = FDOM es_tab /\
  FDOM blocks = FDOM ks_tab /\
  (!f. MEM f order ==>
    ?bb bt ps xs ys rho ini h0 body count front closed brest sp.
      FLOOKUP blocks (b,f) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,body,count,front,closed,brest) /\
      f <= N /\
      lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
      lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      lookup_block ini.vs_current_bb sf.fn_blocks = SOME bb /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\x. is_pseudo x.inst_opcode) ps /\
      EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
      EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
      eval_phis ini bt.bb_instructions = OK sp /\
      (if f = SUC inc then ini = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc pu.
          FLOOKUP blocks (b,f-1) =
            SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK ini,T,SOME pu) /\
          ~ini.vs_halted) /\
      (closed <=> IS_SOME brest) /\ (body = NONE ==> f = d) /\
      (!be hbe. body = SOME (be,hbe) ==>
        be.vs_inst_idx = LENGTH ps /\
        FOLDR (dft_exec_cons (N-f) C8) OK
          (DROP (phi_prefix_length bt.bb_instructions) ps)
          (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be) /\
      (f <> d ==> closed /\ ?post. front = OK post /\ ~post.vs_halted)) /\
  (!f bb bt ps xs ys rho ini h0 be hbe count front closed brest ms es ks.
    MEM f order /\
    FLOOKUP blocks (b,f) =
      SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (b,f) = SOME ms /\
    FLOOKUP es_tab (b,f) = SOME es /\
    FLOOKUP ks_tab (b,f) = SOME ks ==>
    LIST_REL (\m es. LENGTH m = LENGTH es) ms es /\
    LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks) /\
  (!f bb bt ps xs ys rho ini h0 be hbe count front rest ms es ks.
    MEM f order /\ f <> d /\
    FLOOKUP blocks (b,f) =
      SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,T,SOME rest) /\
    FLOOKUP ms_tab (b,f) = SOME ms /\
    FLOOKUP es_tab (b,f) = SOME es /\
    FLOOKUP ks_tab (b,f) = SOME ks ==>
    terminates front /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ rest) be.vs_gas_readings /\
    (!v. (front = OK v \/ ?ir. front = IntRet ir v) ==>
      EVERY IS_SOME (FLAT ms) /\ rest = v.vs_gas_readings) /\
    (!F. N <= F ==>
      FOLDR (dft_exec_cons (F-f) C8) OK ys be = front /\
      (!gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
        (?extra. FLAT es =
          gas_events_block (F-f) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?g. terminates (FOLDR (dft_exec_cons g C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) ==>
          terminates (FOLDR (dft_exec_cons (F-f) C7) OK xs
            (be with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (FOLDR (dft_exec_cons (F-f) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)))
            (restore_result [] front) /\
          (((?v. front = OK v) \/ (?ir v. front = IntRet ir v)) ==>
            gas_events_block (F-f) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT es /\
            residual_result tail front
              (FOLDR (dft_exec_cons (F-f) C7) OK xs
                (be with vs_gas_readings := gs ++ tail)))) /\
        (!v. (FOLDR (dft_exec_cons (F-f) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = OK v \/
              ?ir. FOLDR (dft_exec_cons (F-f) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          trace_gas (trace_block b f (F-f) C7 sf
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs))))) /\
  FLOOKUP ms_tab (b,d) = SOME cms /\
  FLOOKUP es_tab (b,d) = SOME ces /\
  FLOOKUP ks_tab (b,d) = SOME cks /\
  terminates (IntRet ir out) /\
  PERM (MAP THE (FILTER IS_SOME (FLAT cms)) ++ out.vs_gas_readings)
    cbe.vs_gas_readings /\
  (!v. (IntRet ir out = OK v \/ ?ret. IntRet ir out = IntRet ret v) ==>
    EVERY IS_SOME (FLAT cms) /\ out.vs_gas_readings = v.vs_gas_readings) /\
  (!F. N <= F ==>
    FOLDR (dft_exec_cons (F-d) C8) OK cys cbe = IntRet ir out /\
    (!gs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT cms) gs ==>
      (?extra. FLAT ces =
        gas_events_block (F-d) C7 sf.fn_name
          <|bb_label := cbe.vs_current_bb; bb_instructions :=
            REPLICATE cbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ cxs|>
          (cbe with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?g. terminates (FOLDR (dft_exec_cons g C7) OK cxs
          (cbe with vs_gas_readings := gs ++ tail))) ==>
        terminates (FOLDR (dft_exec_cons (F-d) C7) OK cxs
          (cbe with vs_gas_readings := gs ++ tail)) /\
        dft_res_rel
          (restore_result [] (FOLDR (dft_exec_cons (F-d) C7) OK cxs
            (cbe with vs_gas_readings := gs ++ tail)))
          (restore_result [] (IntRet ir out)) /\
        (((?v. IntRet ir out = OK v) \/ (?ret v. IntRet ir out = IntRet ret v)) ==>
          gas_events_block (F-d) C7 sf.fn_name
            <|bb_label := cbe.vs_current_bb; bb_instructions :=
              REPLICATE cbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ cxs|>
            (cbe with vs_gas_readings := gs ++ tail) = FLAT ces /\
          residual_result tail (IntRet ir out)
            (FOLDR (dft_exec_cons (F-d) C7) OK cxs
              (cbe with vs_gas_readings := gs ++ tail)))) /\
      (!v. (FOLDR (dft_exec_cons (F-d) C7) OK cxs
              (cbe with vs_gas_readings := gs ++ tail) = OK v \/
            ?ret. FOLDR (dft_exec_cons (F-d) C7) OK cxs
              (cbe with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
        trace_gas (trace_block b d (F-d) C7 sf
          <|bb_label := cbe.vs_current_bb; bb_instructions :=
            REPLICATE cbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ cxs|>
          (cbe with vs_gas_readings := gs ++ tail)) = ZIP (FLAT cks,gs)))) ==>
  ?bbs bts entries mss ess kss.
    bbs = MAP (\f. FST (THE (FLOOKUP blocks' (b,f)))) order /\
    bts = MAP (\f. case THE (FLOOKUP blocks' (b,f)) of
      (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) => btf) order /\
    entries = MAP (\f. case THE (FLOOKUP blocks' (b,f)) of
      (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) => inf) order /\
    order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
    LAST order <= N /\
    LENGTH bbs = LENGTH order /\ LENGTH bts = LENGTH order /\
    LENGTH entries = LENGTH order /\ HD entries = entry /\
    mss = MAP (\e. FLAT (THE (FLOOKUP ms_tab (b,e)))) order /\
    ess = MAP (\e. FLAT (THE (FLOOKUP es_tab (b,e)))) order /\
    kss = MAP (\e. FLAT (THE (FLOOKUP ks_tab (b,e)))) order /\
    (!i. i < LENGTH order ==>
      lookup_block (EL i entries).vs_current_bb sf.fn_blocks = SOME (EL i bbs) /\
      lookup_block (EL i entries).vs_current_bb tf.fn_blocks = SOME (EL i bts) /\
      (SUC i < LENGTH order ==> ~(EL (SUC i) entries).vs_halted) /\
      ?ps xs ys rho h0 be hbe count r8 rest ms es ks sp g D.
        FLOOKUP blocks' (b,EL i order) =
          SOME (EL i bbs,EL i bts,ps,xs,ys,rho,EL i entries,h0,
            SOME (be,hbe),count,r8,T,SOME rest) /\
        FLOOKUP ms_tab (b,EL i order) = SOME ms /\
        FLOOKUP es_tab (b,EL i order) = SOME es /\
        FLOOKUP ks_tab (b,EL i order) = SOME ks /\
        (EL i bbs).bb_instructions = ps ++ xs /\
        (EL i bts).bb_instructions = ps ++ ys /\
        EVERY (\x. is_pseudo x.inst_opcode) ps /\
        EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
        EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
        xs <> [] /\ is_terminator (LAST xs).inst_opcode /\
        ys <> [] /\ is_terminator (LAST ys).inst_opcode /\
        eval_phis (EL i entries) ps = OK sp /\
        FOLDR (dft_exec_cons g D) OK (DROP (phi_prefix_length ps) ps)
          (sp with vs_inst_idx := phi_prefix_length ps) = OK be /\
        be.vs_inst_idx = LENGTH ps /\
        r8 = (if SUC i < LENGTH order then OK (EL (SUC i) entries) else IntRet ir out) /\
        rest = (if SUC i < LENGTH order then (EL (SUC i) entries).vs_gas_readings
                else out.vs_gas_readings) /\
        EVERY IS_SOME (FLAT ms) /\
        LENGTH (FLAT ms) = LENGTH (FLAT es) /\ LENGTH (FLAT ms) = LENGTH (FLAT ks) /\
        PERM (MAP THE (FLAT ms) ++ rest) be.vs_gas_readings /\
        (!F. N <= F ==>
          FOLDR (dft_exec_cons (F-EL i order) C8) OK ys be = r8 /\
          (!gs tail.
            LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
            (?extra. FLAT es = gas_events_block (F-EL i order) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) ++ extra) /\
            ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
                (be with vs_gas_readings := gs ++ tail))) ==>
              terminates (FOLDR (dft_exec_cons (F-EL i order) C7) OK xs
                (be with vs_gas_readings := gs ++ tail)) /\
              dft_res_rel
                (restore_result [] (FOLDR (dft_exec_cons (F-EL i order) C7) OK xs
                  (be with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
              gas_events_block (F-EL i order) C7 sf.fn_name
                <|bb_label := be.vs_current_bb; bb_instructions :=
                  REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
                (be with vs_gas_readings := gs ++ tail) = FLAT es /\
              residual_result tail r8 (FOLDR (dft_exec_cons (F-EL i order) C7) OK xs
                (be with vs_gas_readings := gs ++ tail))) /\
            (!v. (FOLDR (dft_exec_cons (F-EL i order) C7) OK xs
                    (be with vs_gas_readings := gs ++ tail) = OK v \/
                  ?ret. FOLDR (dft_exec_cons (F-EL i order) C7) OK xs
                    (be with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
              trace_gas (trace_block b (EL i order) (F-EL i order) C7 sf
                <|bb_label := be.vs_current_bb; bb_instructions :=
                  REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
                (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs)))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. i < LENGTH order ==>
    EL i order = inc + SUC i /\
    (EL i order = d <=> SUC i = LENGTH order) /\
    (SUC i < LENGTH order ==> EL (SUC i) order - 1 = EL i order)` by
    (qx_gen_tac `i` >> disch_tac >> drule_all return_order_indices >> simp[]) >>
  `!f. MEM f order ==>
    ?bb bt ps xs ys rho ini h0 body count front closed brest.
      FLOOKUP blocks (b,f) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,body,count,front,closed,brest) /\
      f <= N /\
      (if f = SUC inc then ini = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc pu.
          FLOOKUP blocks (b,f-1) =
            SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK ini,T,SOME pu) /\
          ~ini.vs_halted) /\
      (f <> d ==> closed /\ ?post. front = OK post /\ ~post.vs_halted) /\
      (body = NONE ==> f = d) /\ (closed <=> IS_SOME brest)` by
    (qx_gen_tac `f` >> strip_tac >>
     qpat_assum `!f. MEM f order ==> ?bb. _` (drule_then strip_assume_tac) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `d = LAST order` by simp[] >>
  drule_all dft_packet_return_order_enumerate >> strip_tac >>
  qpat_x_assum `!f. MEM f order ==> ?bb bt ps xs ys rho ini h0 body count front closed brest. _` kall_tac >>
  qexistsl [`bbs`,`bts`,`entries`,
    `MAP (\e. FLAT (THE (FLOOKUP ms_tab (b,e)))) order`,
    `MAP (\e. FLAT (THE (FLOOKUP es_tab (b,e)))) order`,
    `MAP (\e. FLAT (THE (FLOOKUP ks_tab (b,e)))) order`] >>
  ntac 10 (conj_tac >- first_assum ACCEPT_TAC) >>
  simp[NoAsms] >> qx_gen_tac `i` >> disch_tac >>
  `MEM (EL i order) order` by metis_tac[MEM_EL] >>
  qpat_assum `!f. MEM f order ==> ?bb. _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!f. MEM f order ==> ?bb. _` kall_tac >>
  qpat_x_assum `!i. i < LENGTH order ==> (SUC i < LENGTH order ==> _) /\ _`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH order ==> _` (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `bbs = MAP _ _` kall_tac >>
  qpat_x_assum `bts = MAP _ _` kall_tac >>
  qpat_x_assum `entries = MAP _ _` kall_tac >>
  qpat_x_assum `order = GENLIST _ _` kall_tac >>
  qpat_x_assum `LAST order = d` kall_tac >>
  qpat_x_assum `d = LAST order` kall_tac >>
  qpat_x_assum `if EL i order = SUC inc then _ else _` kall_tac >>
  Cases_on `EL i order = d`
  >- (qpat_x_assum `!f bb bt ps xs ys rho ini h0 be hbe count front rest ms es ks. _` kall_tac >>
      qpat_x_assum `!f. MEM f order /\ _ ==> _` kall_tac >>
      qpat_x_assum `EL i order = inc + SUC i` kall_tac >>
      qpat_x_assum `!F. N <= F ==> _` (mk_asm "terminal_semantics") >>
      gvs[] >>
      qpat_x_assum `!f bb bt ps xs ys rho ini h0 be hbe count front closed brest ms es ks. _`
        (drule_all_then strip_assume_tac) >>
      `eval_phis (EL i entries) (EL i bts).bb_instructions = OK sp /\
       FOLDR (dft_exec_cons (N-EL i order) C8) OK
         (DROP (phi_prefix_length (EL i bts).bb_instructions) cps)
         (sp with vs_inst_idx := phi_prefix_length (EL i bts).bb_instructions) = OK be`
        by simp[] >>
      drule_all return_order_row_shape >> strip_tac >>
      asm_x "terminal_semantics" (assume_tac o SRULE []) >>
      `LENGTH (FLAT cms) = LENGTH (FLAT ces) /\
       LENGTH (FLAT cms) = LENGTH (FLAT cks)` by
        metis_tac[LENGTH_FLAT,MAP_EQ_LIST_REL,LIST_REL_LENGTH] >>
      `FILTER IS_SOME (FLAT cms) = FLAT cms` by metis_tac[FILTER_EQ_ID] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`sp`,`N-EL i order`,`C8`] >> fs[] >>
      qpat_x_assum `!F. N <= F ==> _` mp_tac >>
      qpat_x_assum `be.vs_inst_idx = _` (fn th => rewrite_tac[th]) >>
      metis_tac[]) >>
  qpat_x_assum `!F. N <= F ==> _` kall_tac >>
  qpat_x_assum `!f bb bt ps xs ys rho ini h0 be hbe count front rest ms es ks. _`
    (mk_asm "closed_rows") >>
  `SUC i < LENGTH order` by decide_tac >>
  `FLOOKUP blocks' (b,EL i order) = FLOOKUP blocks (b,EL i order)` by
    (first_x_assum irule >> simp[]) >>
  gvs[] >>
  `?ms es ks. FLOOKUP ms_tab (b,inc + SUC i) = SOME ms /\
    FLOOKUP es_tab (b,inc + SUC i) = SOME es /\
    FLOOKUP ks_tab (b,inc + SUC i) = SOME ks` by
    metis_tac[flookup_thm] >>
  qpat_x_assum `!f bb bt ps xs ys rho ini h0 be hbe count front closed brest ms es ks. _`
    (drule_all_then strip_assume_tac) >>
  asm_x "closed_rows" (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!F. N <= F ==> _` (mk_asm "old_semantics") >>
  gvs[] >>
  `eval_phis (EL i entries) (EL i bts).bb_instructions = OK sp /\
   FOLDR (dft_exec_cons (N-(inc + SUC i)) C8) OK
     (DROP (phi_prefix_length (EL i bts).bb_instructions) ps)
     (sp with vs_inst_idx := phi_prefix_length (EL i bts).bb_instructions) = OK be`
    by simp[] >>
  drule_all return_order_row_shape >> strip_tac >>
  asm_x "old_semantics" (assume_tac o SRULE []) >>
  `LENGTH (FLAT ms) = LENGTH (FLAT es) /\
   LENGTH (FLAT ms) = LENGTH (FLAT ks)` by
    metis_tac[LENGTH_FLAT,MAP_EQ_LIST_REL,LIST_REL_LENGTH] >>
  `FILTER IS_SOME (FLAT ms) = FLAT ms` by metis_tac[FILTER_EQ_ID] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`sp`,`N-(inc + SUC i)`,`C8`] >> fs[] >>
  qpat_x_assum `!F. N <= F ==> _` mp_tac >>
  qpat_x_assum `be.vs_inst_idx = _` (fn th => rewrite_tac[th]) >>
  metis_tac[]
QED
