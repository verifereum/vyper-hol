Theory dftPacketReturnChildClosure
Ancestors
  dftPacketReturnOrderCertificate dftPacketReturnActivation
  dftGasFromListTraceDefs dftIndexedExec venomWf venomExecSemantics
  venomState venomInst gasEvents finite_map list rich_list arithmetic sorting

(* Use the actual child order, changing only the completion fields at d.
   Earlier closed rows and the terminal row have the same replay interface. *)
Theorem dft_packet_return_child_closure:
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
    (!v. (front = OK v \/ ?ret. front = IntRet ret v) ==>
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
          (((?v. front = OK v) \/ (?ret v. front = IntRet ret v)) ==>
            gas_events_block (F-f) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT es /\
            residual_result tail front
              (FOLDR (dft_exec_cons (F-f) C7) OK xs
                (be with vs_gas_readings := gs ++ tail)))) /\
        (!v. (FOLDR (dft_exec_cons (F-f) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = OK v \/
              ?ret. FOLDR (dft_exec_cons (F-f) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
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
          (cbe with vs_gas_readings := gs ++ tail)) = ZIP (FLAT cks,gs)))) /\
  AM b = FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (b,f)))) order) /\
  AE b = FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (b,f)))) order) /\
  AK b = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (b,f)))) order) ==>
  terminates (IntRet ir out) /\
  LENGTH (AM b) = LENGTH (AE b) /\ LENGTH (AM b) = LENGTH (AK b) /\
  PERM (MAP THE (FILTER IS_SOME (AM b)) ++ out.vs_gas_readings) entry.vs_gas_readings /\
  EVERY IS_SOME (AM b) /\
  (!F. N <= F ==>
    run_blocks (F-inc) C8 tf entry = IntRet ir out /\
    (!gs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM b) gs ==>
      (?extra. AE b = gas_events_blocks (F-inc) C7 sf
        (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?f. terminates (run_blocks f C7 sf
          (entry with vs_gas_readings := gs ++ tail))) ==>
        terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
        dft_res_rel
          (restore_result [] (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)))
          (restore_result [] (IntRet ir out)) /\
        gas_events_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = AE b /\
        residual_result tail (IntRet ir out)
          (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail))) /\
      (!v. (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = OK v \/
            ?ret. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
        trace_gas (trace_blocks b inc (F-inc) C7 sf
          (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK b,gs))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dft_packet_return_order_certificate >> strip_tac >>
  drule_all_then (mk_asm "activation") dft_packet_return_closed_activation >>
  qpat_assum `AM b = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `AE b = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `AK b = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `mss = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `ess = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `kss = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  asm "activation" ACCEPT_TAC
QED
