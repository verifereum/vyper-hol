Theory dftPacketCallFreshReplay
Ancestors
  dftPacketFreshRow list

(* Initial child rows have no completed INVOKE cells. *)
Theorem dft_packet_call_fresh_child_U:
  bb.bb_instructions = ps ++ xs /\ be.vs_inst_idx = LENGTH ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  ms = GENLIST (\q. if (EL q xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs) /\
  ess = GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(sf.fn_name,(EL q xs).inst_id)] else []) (LENGTH xs) /\
  ks = GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(a,e,(EL q xs).inst_id)] else []) (LENGTH xs) ==>
  !F k kgss tail.
    (N:num) <= F /\ k <= LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
    (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==>
      MEM q (TAKE 0 (sched:num list))) /\
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
          (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule dft_packet_fresh_row_replay >>
  simp[] >>
  gvs[EVERY_EL, EL_TAKE] >> metis_tac[]
QED
