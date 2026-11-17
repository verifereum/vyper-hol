Theory dftPacketPseudoReplayFrame
Ancestors
  dftPacketClosedRows dftGasFromListTraceDefs dftGasFromListRestore
  dftRunRel dftIndexedExec gasEvents venomExecSemantics
  list rich_list sorting arithmetic

(* Only eligible source prefixes are framed; a live ancestor row may have
   changed cells after every such prefix. *)
Theorem dft_packet_pseudo_U_transport:
  !N C7 sf a e bb ps xs be count rho ms ess ks ms' ess' ks'.
    (!k. k <= LENGTH xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==>
        MEM q (TAKE count rho)) ==>
      TAKE k ms' = TAKE k ms /\ TAKE k ess' = TAKE k ess /\
      TAKE k ks' = TAKE k ks) /\
    (!F k kgss tail.
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
        (!tail'.
          FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
            (be with vs_gas_readings := FLAT kgss ++ tail') =
              OK (u with vs_gas_readings := tail') /\
          gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) ==>
    (!F k kgss tail.
      N <= F /\ k <= LENGTH xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==>
        MEM q (TAKE count rho)) /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
        (TAKE k ms') kgss ==>
      (?extra. FLAT (TAKE k ess') =
        gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
      (!u. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess') /\
        u.vs_gas_readings = tail /\
        dftGasFromListTraceDefs$trace_gas
          (dftGasFromListTraceDefs$trace_block a e (F-e) C7 sf
            (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
            (be with vs_gas_readings := FLAT kgss ++ tail)) =
          ZIP (FLAT (TAKE k ks'),FLAT kgss) /\
        (!tail'.
          FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
            (be with vs_gas_readings := FLAT kgss ++ tail') =
              OK (u with vs_gas_readings := tail') /\
          gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess'))))
Proof
  rpt gen_tac >> strip_tac >>
  map_every qx_gen_tac [`fuel`,`k`,`kgss`,`tail`] >> strip_tac >>
  `TAKE k ms' = TAKE k ms /\ TAKE k ess' = TAKE k ess /\
   TAKE k ks' = TAKE k ks` by
    (first_x_assum irule >> simp[]) >>
  qpat_x_assum `!F k kgss tail. _` (qspecl_then [`fuel`,`k`,`kgss`,`tail`] mp_tac) >>
  fs[]
QED

(* Q is transported for every retained call, whether live or returned. *)
Theorem dft_packet_pseudo_Q_transport:
  !N C7 e q xs be b0 ms ms'.
    TAKE q ms' = TAKE q ms /\
    (!F kgss tail u.
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
    (!F kgss tail u.
      N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
        (TAKE q ms') kgss /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==>
        eval_operand op u = eval_operand op b0) /\
      (!callee args.
        setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
        setup_callee callee args b0))
Proof
  rpt gen_tac >> strip_tac >> asm_rewrite_tac[]
QED

Theorem dft_packet_pseudo_closed_row_transport:
  !N C7 C8 sf a e xs ys be r8 u0 ms ess ks ms' ess' ks'.
    ms' = ms /\ ess' = ess /\ ks' = ks /\
    (terminates r8 /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ u0) be.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (FLAT ms) /\ u0 = v.vs_gas_readings) /\
    (!F. N <= F ==>
      FOLDR (dft_exec_cons (F-e) C8) OK ys be = r8 /\
      (!gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
        (?extra. FLAT ess =
          gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) ==>
          terminates (FOLDR (dft_exec_cons (F-e) C7) OK xs
            (be with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (FOLDR (dft_exec_cons (F-e) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)))
            (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
            residual_result tail r8
              (FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail)))) /\
        (!v. (FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = OK v \/
              ?ir. FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          dftGasFromListTraceDefs$trace_gas
            (dftGasFromListTraceDefs$trace_block a e (F-e) C7 sf
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs))))) ==>
    terminates r8 /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms')) ++ u0) be.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (FLAT ms') /\ u0 = v.vs_gas_readings) /\
    (!F. N <= F ==>
      FOLDR (dft_exec_cons (F-e) C8) OK ys be = r8 /\
      (!gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms') gs ==>
        (?extra. FLAT ess' =
          gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) ==>
          terminates (FOLDR (dft_exec_cons (F-e) C7) OK xs
            (be with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (FOLDR (dft_exec_cons (F-e) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)))
            (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT ess' /\
            residual_result tail r8
              (FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail)))) /\
        (!v. (FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = OK v \/
              ?ir. FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          dftGasFromListTraceDefs$trace_gas
            (dftGasFromListTraceDefs$trace_block a e (F-e) C7 sf
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks',gs))))
Proof
  rpt gen_tac >> strip_tac >> asm_rewrite_tac[]
QED

Theorem dft_packet_pseudo_closed_activation_transport:
  !N C7 C8 sf tf a inc entry r8 u0 AM AE AK AM' AE' AK'.
    AM' a = AM a /\ AE' a = AE a /\ AK' a = AK a /\
    (terminates r8 /\
    LENGTH (AM a) = LENGTH (AE a) /\ LENGTH (AM a) = LENGTH (AK a) /\
    PERM (MAP THE (FILTER IS_SOME (AM a)) ++ u0) entry.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (AM a) /\ u0 = v.vs_gas_readings) /\
    (!F. N <= F ==>
      run_blocks (F-inc) C8 tf entry = r8 /\
      (!gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM a) gs ==>
        (?extra. AE a = gas_events_blocks (F-inc) C7 sf
          (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (run_blocks f C7 sf
            (entry with vs_gas_readings := gs ++ tail))) ==>
          terminates (run_blocks (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (run_blocks (F-inc) C7 sf
              (entry with vs_gas_readings := gs ++ tail)))
            (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_blocks (F-inc) C7 sf
              (entry with vs_gas_readings := gs ++ tail) = AE a /\
            residual_result tail r8
              (run_blocks (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail)))) /\
        (!v. (run_blocks (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail) = OK v \/
              ?ir. run_blocks (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          dftGasFromListTraceDefs$trace_gas
            (dftGasFromListTraceDefs$trace_blocks a inc (F-inc) C7 sf
              (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK a,gs))))) ==>
    terminates r8 /\
    LENGTH (AM' a) = LENGTH (AE' a) /\ LENGTH (AM' a) = LENGTH (AK' a) /\
    PERM (MAP THE (FILTER IS_SOME (AM' a)) ++ u0) entry.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (AM' a) /\ u0 = v.vs_gas_readings) /\
    (!F. N <= F ==>
      run_blocks (F-inc) C8 tf entry = r8 /\
      (!gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM' a) gs ==>
        (?extra. AE' a = gas_events_blocks (F-inc) C7 sf
          (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (run_blocks f C7 sf
            (entry with vs_gas_readings := gs ++ tail))) ==>
          terminates (run_blocks (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (run_blocks (F-inc) C7 sf
              (entry with vs_gas_readings := gs ++ tail)))
            (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_blocks (F-inc) C7 sf
              (entry with vs_gas_readings := gs ++ tail) = AE' a /\
            residual_result tail r8
              (run_blocks (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail)))) /\
        (!v. (run_blocks (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail) = OK v \/
              ?ir. run_blocks (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          dftGasFromListTraceDefs$trace_gas
            (dftGasFromListTraceDefs$trace_blocks a inc (F-inc) C7 sf
              (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK' a,gs))))
Proof
  rpt gen_tac >> strip_tac >> asm_rewrite_tac[]
  >> (simp[])
QED
