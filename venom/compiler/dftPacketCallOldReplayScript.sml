Theory dftPacketCallOldReplay
Ancestors
  dftPacketCallReplayPreservation dftPacketPseudoReplayFrame
  dftPacketPseudoHistory dftPacketTableSplice list rich_list finite_map arithmetic

(* Both the newly suspended parent and a strict live ancestor are covered.
   Returned records use INVOKE ordering, not arbitrary source-index ordering. *)
Theorem dft_packet_call_old_row_bounds:
  !(calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    p a e livecid liveq b0 sf tf bb bt ps xs ys sched cnt.
    dft_fn_rel sf tf /\
    lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
    lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
    bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
    EVERY (\x. is_pseudo x.inst_opcode) ps /\
    EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ LENGTH xs = LENGTH ys /\
    PERM sched (COUNT_LIST (LENGTH xs)) /\
    LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
      from_block [EL q xs] y) sched ys /\
    liveq < LENGTH xs /\ (EL liveq xs).inst_opcode = INVOKE /\
    b0.vs_inst_idx = LENGTH ps + cnt /\
    get_instruction bt b0.vs_inst_idx = SOME (EL liveq xs) /\
    (a = p \/ ?i h done child.
      i < LENGTH p /\ a = DROP (SUC i) p /\ (e,livecid) = EL i p /\
      FLOOKUP calls (a,e,livecid) = SOME (liveq,h,b0,done,child,NONE)) /\
    (!cid q h b done child ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
      q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
      (case ret of
        NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
      | SOME triple => MEM q (TAKE cnt sched))) ==>
    (!k. k <= LENGTH xs /\
      (!r. r < k /\ (EL r xs).inst_opcode = INVOKE ==>
        MEM r (TAKE cnt sched)) ==> k <= liveq) /\
    (!cid q h b done child ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==> q <= liveq)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all dft_packet_history_suspended_schedule >> strip_tac >>
  `~MEM liveq (TAKE cnt sched)` by
    (strip_tac >>
     `MEM liveq (DROP cnt sched)` by
       (simp[DROP_CONS_EL] >> metis_tac[]) >>
     metis_tac[ALL_DISTINCT_TAKE_DROP]) >>
  conj_tac
  >- (rpt strip_tac >> spose_not_then assume_tac >>
      `liveq < k` by decide_tac >> metis_tac[]) >>
  `!r t. r < t /\ t < LENGTH xs /\
    (EL r xs).inst_opcode = INVOKE /\ (EL t xs).inst_opcode = INVOKE ==>
    id_before (MAP (\x. x.inst_id) ys) (EL r xs).inst_id (EL t xs).inst_id` by
    (rpt strip_tac >> irule dft_packet_history_invoke_order >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  `q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
    (case ret of
      NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
    | SOME triple => MEM q (TAKE cnt sched))` by metis_tac[] >>
  Cases_on `ret`
  >- (qpat_x_assum `a = p \/ _` strip_assume_tac
      >- (gvs[MEM_GENLIST] >>
          qpat_x_assum `_::_ = DROP _ _`
            (mp_tac o AP_TERM ``LENGTH:(num # num) list -> num``) >> simp[]) >>
      fs[] >>
      `cid = livecid` by metis_tac[dft_packet_history_live_child_unique] >> gvs[]) >>
  qpat_x_assum `a = p \/ _` kall_tac >>
  `MEM q (TAKE cnt sched)` by fs[] >>
  `LIST_REL (\r y. r < LENGTH xs /\ y.inst_id = (EL r xs).inst_id) sched ys` by
    (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `q < liveq` suffices_by decide_tac >>
  irule dft_packet_history_invoke_prefix_bound >>
  rpt (first_assum (irule_at Any)) >> simp[]
QED

(* Pointwise final-table transport.  The unchanged alternative covers every
   offpath row (and every completed row of a live activation).  The other
   alternative uses the literal final child aggregate in each changed cell. *)
Theorem dft_packet_call_old_U_transport:
  !N C7 sf p a e bb ps xs be cnt sched ms ess ks ms' ess' ks'
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    ms_out es_out ks_out.
    FLOOKUP ms_out (a,e) = SOME ms' /\
    FLOOKUP es_out (a,e) = SOME ess' /\
    FLOOKUP ks_out (a,e) = SOME ks' /\
    ((FLOOKUP ms_out (a,e) = SOME ms /\
      FLOOKUP es_out (a,e) = SOME ess /\ FLOOKUP ks_out (a,e) = SOME ks) \/
     ?livecid liveq b0 tf bt ys child_order.
      dft_fn_rel sf tf /\
      lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
      lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\x. is_pseudo x.inst_opcode) ps /\
      EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ LENGTH xs = LENGTH ys /\
      PERM sched (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
        from_block [EL q xs] y) sched ys /\
      liveq < LENGTH xs /\ (EL liveq xs).inst_opcode = INVOKE /\
      b0.vs_inst_idx = LENGTH ps + cnt /\
      get_instruction bt b0.vs_inst_idx = SOME (EL liveq xs) /\
      (a = p \/ ?i h done child.
        i < LENGTH p /\ a = DROP (SUC i) p /\ (e,livecid) = EL i p /\
        FLOOKUP calls (a,e,livecid) = SOME (liveq,h,b0,done,child,NONE)) /\
      (!cid q h b done child ret.
        FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
        q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
        (case ret of
          NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
        | SOME triple => MEM q (TAKE cnt sched))) /\
      FLOOKUP ms_out (a,e) = SOME (LUPDATE
        (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_out ((e,livecid)::a,f)))) child_order)) liveq ms) /\
      FLOOKUP es_out (a,e) = SOME (LUPDATE
        (FLAT (MAP (\f. FLAT (THE (FLOOKUP es_out ((e,livecid)::a,f)))) child_order)) liveq ess) /\
      FLOOKUP ks_out (a,e) = SOME (LUPDATE
        (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_out ((e,livecid)::a,f)))) child_order)) liveq ks)) /\
    (!F k kgss tail.
      N <= F /\ k <= LENGTH xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==>
        MEM q (TAKE cnt sched)) /\
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
        MEM q (TAKE cnt sched)) /\
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
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!k. k <= LENGTH xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==>
        MEM q (TAKE cnt sched)) ==>
      TAKE k ms' = TAKE k ms /\ TAKE k ess' = TAKE k ess /\
      TAKE k ks' = TAKE k ks` by
    (qpat_x_assum `(_ /\ _ /\ _) \/ _`
       (DISJ_CASES_THEN2 strip_assume_tac
         (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)))
     >- (rpt strip_tac >> gvs[]) >>
     drule_all dft_packet_call_old_row_bounds >> strip_tac >>
     rpt gen_tac >> strip_tac >>
     `k <= liveq` by metis_tac[] >>
     gvs[dft_packet_row_prefix_splice]) >>
  irule (INST_TYPE [alpha |-> ``:instruction``] dft_packet_pseudo_U_transport) >>
  rpt (first_assum (irule_at Any))
QED
