Theory dftPacketBlockReplayUQ
Ancestors
  dftPacketPseudoReplayFrame finite_map list rich_list arithmetic

(* The two exceptional rows use local successor semantics.  In particular,
   the newly closed row is not treated as an unchanged-count old row. *)
Theorem dft_packet_block_U_frame:
  !N N' C7 p d
    (acts:((num # num) list, ir_function # ir_function # num # venom_state #
      num list # exec_result option # bytes32 list option) fmap)
    (acts':((num # num) list, ir_function # ir_function # num # venom_state #
      num list # exec_result option # bytes32 list option) fmap)
    (blocks:(((num # num) list # num), basic_block # basic_block #
      instruction list # instruction list # instruction list # num list #
      venom_state # num # (venom_state # num) option # num # exec_result #
      bool # bytes32 list option) fmap)
    (blocks':(((num # num) list # num), basic_block # basic_block #
      instruction list # instruction list # instruction list # num list #
      venom_state # num # (venom_state # num) option # num # exec_result #
      bool # bytes32 list option) fmap)
    (ms_tab:(((num # num) list # num), bytes32 option list list) fmap)
    (es_tab:(((num # num) list # num), (string # num) list list) fmap)
    (ks_tab:(((num # num) list # num), gas_event list list) fmap)
    (ms_out:(((num # num) list # num), bytes32 option list list) fmap)
    (es_out:(((num # num) list # num), (string # num) list list) fmap)
    (ks_out:(((num # num) list # num), gas_event list list) fmap).
    N <= N' /\
    (!a sf tf inc entry order res nrest.
      FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      ?old_order. FLOOKUP acts a = SOME (sf,tf,inc,entry,old_order,res,nrest)) /\
    (!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest.
      FLOOKUP blocks' (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      (a,e) <> (p,d) /\ (a,e) <> (p,SUC d) ==>
      ?old_front old_closed old_rest ms ess ks.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,old_front,old_closed,old_rest) /\
        FLOOKUP ms_tab (a,e) = SOME ms /\
        FLOOKUP es_tab (a,e) = SOME ess /\
        FLOOKUP ks_tab (a,e) = SOME ks /\
        (!k. k <= LENGTH xs /\
          EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
          (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==>
            MEM q (TAKE count rho)) ==>
          TAKE k (THE (FLOOKUP ms_out (a,e))) = TAKE k ms /\
          TAKE k (THE (FLOOKUP es_out (a,e))) = TAKE k ess /\
          TAKE k (THE (FLOOKUP ks_out (a,e))) = TAKE k ks)) /\
    (!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest
        ms ess ks sf tf inc entry order res nrest.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      FLOOKUP ms_tab (a,e) = SOME ms /\
      FLOOKUP es_tab (a,e) = SOME ess /\
      FLOOKUP ks_tab (a,e) = SOME ks /\
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      !F k kgss tail.
        N <= F /\ k <= LENGTH xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
        (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==>
          MEM q (TAKE count rho)) /\
        LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
          (TAKE k ms) kgss ==>
        (?extra. FLAT (TAKE k ess) =
          gas_events_block (F-e) C7 sf.fn_name
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
          dftGasFromListTraceDefs$trace_gas
            (dftGasFromListTraceDefs$trace_block a e (F-e) C7 sf
              (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
              (be with vs_gas_readings := FLAT kgss ++ tail)) =
            ZIP (FLAT (TAKE k ks),FLAT kgss) /\
          (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
              (be with vs_gas_readings := FLAT kgss ++ tail') =
                OK (u with vs_gas_readings := tail') /\
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
              (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) /\
    (!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest
        ms ess ks sf tf inc entry order res nrest.
      ((a,e) = (p,d) \/ (a,e) = (p,SUC d)) /\
      FLOOKUP blocks' (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      FLOOKUP ms_out (a,e) = SOME ms /\
      FLOOKUP es_out (a,e) = SOME ess /\
      FLOOKUP ks_out (a,e) = SOME ks /\
      FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      !F k kgss tail.
        N' <= F /\ k <= LENGTH xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
        (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==>
          MEM q (TAKE count rho)) /\
        LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
          (TAKE k ms) kgss ==>
        (?extra. FLAT (TAKE k ess) =
          gas_events_block (F-e) C7 sf.fn_name
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
          dftGasFromListTraceDefs$trace_gas
            (dftGasFromListTraceDefs$trace_block a e (F-e) C7 sf
              (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
              (be with vs_gas_readings := FLAT kgss ++ tail)) =
            ZIP (FLAT (TAKE k ks),FLAT kgss) /\
          (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
              (be with vs_gas_readings := FLAT kgss ++ tail') =
                OK (u with vs_gas_readings := tail') /\
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
              (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) ==>
    (!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest
        ms ess ks sf tf inc entry order res nrest.
      FLOOKUP blocks' (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      FLOOKUP ms_out (a,e) = SOME ms /\
      FLOOKUP es_out (a,e) = SOME ess /\
      FLOOKUP ks_out (a,e) = SOME ks /\
      FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      !F k kgss tail.
        N' <= F /\ k <= LENGTH xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
        (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==>
          MEM q (TAKE count rho)) /\
        LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
          (TAKE k ms) kgss ==>
        (?extra. FLAT (TAKE k ess) =
          gas_events_block (F-e) C7 sf.fn_name
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
          dftGasFromListTraceDefs$trace_gas
            (dftGasFromListTraceDefs$trace_block a e (F-e) C7 sf
              (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
              (be with vs_gas_readings := FLAT kgss ++ tail)) =
            ZIP (FLAT (TAKE k ks),FLAT kgss) /\
          (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
              (be with vs_gas_readings := FLAT kgss ++ tail') =
                OK (u with vs_gas_readings := tail') /\
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
              (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess))))
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (mk_asm "acts")
      (CONJUNCTS_THEN2 (mk_asm "rows")
        (CONJUNCTS_THEN2 (mk_asm "old_U") (mk_asm "local_U"))))) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `(a,e) = (p,d) \/ (a,e) = (p,SUC d)`
  >- (asm_x "local_U" match_mp_tac >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  asm_x "local_U" kall_tac >>
  `(a,e) <> (p,d) /\ (a,e) <> (p,SUC d)` by fs[] >>
  asm_x "rows" (drule_all_then strip_assume_tac) >>
  asm_x "acts" (drule_all_then strip_assume_tac) >>
  asm_x "old_U" (drule_then mp_tac) >>
  simp[] >> disch_then assume_tac >>
  map_every qx_gen_tac [`fuel`,`k`,`kgss`,`tail`] >> strip_tac >>
  `N <= fuel` by decide_tac >>
  qpat_x_assum `!k. k <= LENGTH xs /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!F' k kgss tail. _`
    (qspecl_then [`fuel`,`k`,`kgss`,`tail`] mp_tac) >>
  gvs[]
QED

(* The immutable call map is used without distinguishing live and returned
   calls.  The closing row may change count, front, and completion fields. *)
Theorem dft_packet_block_Q_frame:
  !N N' C7
    (calls:(gas_event, num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (blocks:(((num # num) list # num), basic_block # basic_block #
      instruction list # instruction list # instruction list # num list #
      venom_state # num # (venom_state # num) option # num # exec_result #
      bool # bytes32 list option) fmap)
    (blocks':(((num # num) list # num), basic_block # basic_block #
      instruction list # instruction list # instruction list # num list #
      venom_state # num # (venom_state # num) option # num # exec_result #
      bool # bytes32 list option) fmap)
    (ms_tab:(((num # num) list # num), bytes32 option list list) fmap)
    (ms_out:(((num # num) list # num), bytes32 option list list) fmap).
    N <= N' /\
    (!a e cid q h b0 done child ret bb bt ps xs ys rho hin h0 be hbe
        count front closed brest ms.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child,ret) /\
      FLOOKUP blocks' (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      FLOOKUP ms_out (a,e) = SOME ms ==>
      ?old_count old_front old_closed old_rest old_ms.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),old_count,old_front,old_closed,old_rest) /\
        FLOOKUP ms_tab (a,e) = SOME old_ms /\ TAKE q ms = TAKE q old_ms) /\
    (!a e cid q h b0 done child ret bb bt ps xs ys rho hin h0 be hbe
        count front closed brest ms.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child,ret) /\
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      FLOOKUP ms_tab (a,e) = SOME ms ==>
      !F kgss tail u.
        N <= F /\
        LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
          (TAKE q ms) kgss /\
        FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        (!op. MEM op (EL q xs).inst_operands ==>
          eval_operand op u = eval_operand op b0) /\
        (!callee args.
          setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
          setup_callee callee args b0)) ==>
    (!a e cid q h b0 done child ret bb bt ps xs ys rho hin h0 be hbe
        count front closed brest ms.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child,ret) /\
      FLOOKUP blocks' (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      FLOOKUP ms_out (a,e) = SOME ms ==>
      !F kgss tail u.
        N' <= F /\
        LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
          (TAKE q ms) kgss /\
        FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        (!op. MEM op (EL q xs).inst_operands ==>
          eval_operand op u = eval_operand op b0) /\
        (!callee args.
          setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
          setup_callee callee args b0))
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (mk_asm "frame") (mk_asm "old_Q"))) >>
  rpt gen_tac >> strip_tac >>
  asm_x "frame" (drule_all_then strip_assume_tac) >>
  asm_x "old_Q" (drule_then mp_tac) >>
  simp[] >> disch_then assume_tac >>
  map_every qx_gen_tac [`fuel`,`kgss`,`tail`,`u`] >> strip_tac >>
  `N <= fuel` by decide_tac >>
  qpat_x_assum `!F kgss tail u. _`
    (qspecl_then [`fuel`,`kgss`,`tail`,`u`] mp_tac) >>
  gvs[]
QED
