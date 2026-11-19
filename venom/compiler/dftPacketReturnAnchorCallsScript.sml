Theory dftPacketReturnAnchorCalls
Ancestors
  dftPacketCallReplayPreservation dftGasFromListTraceDefs
  dftGasInvCallerExtract finite_map list rich_list arithmetic

(* Chronology is independent of source replay.  The two quantified inputs
   are projections of immutable call history and live suspended parents. *)
Theorem dft_packet_return_anchor_done:
  !calls a e cid q h b0 done child_entry ret blocks bb bt ps xs ys sched
    hin h0 be hbe cnt front closed brest p.
  FLOOKUP (calls : (gas_event,
    num # num # venom_state # num list # venom_state #
    (internal_return # venom_state # venom_state) option) fmap)
    (a,e,cid) = SOME (q,h,b0,done,child_entry,ret) /\
  FLOOKUP (blocks : (((num # num) list # num),
    basic_block # basic_block # instruction list # instruction list #
    instruction list # num list # venom_state # num #
    (venom_state # num) option # num # exec_result # bool #
    bytes32 list option) fmap) (a,e) =
    SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),cnt,front,closed,brest) /\
  done = TAKE (b0.vs_inst_idx - LENGTH ps) sched /\ ~MEM q done /\
  (case ret of
     NONE => MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
   | SOME triple => MEM q (TAKE cnt sched)) /\
  (!k. k < LENGTH p ==>
    ?bb' bt' ps' xs' ys' sched' hin' h0' be' hbe' cnt'
      q' h' b0' done' child_entry' cid' e' a'.
      a' = DROP (SUC k) p /\ (e',cid') = EL k p /\
      FLOOKUP blocks (a',e') =
        SOME (bb',bt',ps',xs',ys',sched',hin',h0',SOME (be',hbe'),cnt',OK b0',F,NONE) /\
      FLOOKUP calls (a',e',cid') = SOME (q',h',b0',done',child_entry',NONE) /\
      done' = TAKE cnt' sched') ==>
  !r. MEM r done ==> MEM r (TAKE cnt sched)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ret`
  >- (gvs[MEM_GENLIST] >> rename1 `(e,cid)::a = DROP k p` >>
      `k < LENGTH p` by
        (Cases_on `k = LENGTH p` >> gvs[] >> decide_tac) >>
      `DROP k p = EL k p :: DROP (SUC k) p` by simp[DROP_CONS_EL] >>
      qpat_x_assum `!k. k < LENGTH p ==> _` (qspec_then `k` mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      `e' = e /\ cid' = cid` by metis_tac[pairTheory.PAIR_EQ] >> gvs[])
  >> gvs[] >> drule_all dft_packet_call_done_prefix >> simp[]
QED

(* The source-success premise is essential: U consumes gas only on success,
   while historical Q preserves the call's operands and setup.  All history
   inputs are selected literal conjuncts of the retained packet clauses. *)
Theorem dft_packet_return_anchor_call:
  !N fuel C7 C8 calls a e cid q h b0 done child_entry ret blocks bb bt ps xs ys sched
    hin h0 be hbe cnt front closed brest p ms_tab ms ess ks sf.
  N <= fuel /\
  FLOOKUP (calls : (gas_event,
    num # num # venom_state # num list # venom_state #
    (internal_return # venom_state # venom_state) option) fmap)
    (a,e,cid) = SOME (q,h,b0,done,child_entry,ret) /\
  FLOOKUP (blocks : (((num # num) list # num),
    basic_block # basic_block # instruction list # instruction list #
    instruction list # num list # venom_state # num #
    (venom_state # num) option # num # exec_result # bool #
    bytes32 list option) fmap) (a,e) =
    SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),cnt,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\
  q < LENGTH xs /\ (EL q xs).inst_id = cid /\ (EL q xs).inst_opcode = INVOKE /\
  (?nm ops args ctf.
    decode_invoke (EL q xs) = SOME (nm,ops) /\
    lookup_function nm C8.ctx_functions = SOME ctf /\
    eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry) /\
  done = TAKE (b0.vs_inst_idx - LENGTH ps) sched /\ ~MEM q done /\
  (case ret of
     NONE => MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
   | SOME triple => MEM q (TAKE cnt sched)) /\
  (!k. k < LENGTH p ==>
    ?bb' bt' ps' xs' ys' sched' hin' h0' be' hbe' cnt'
      q' h' b0' done' child_entry' cid' e' a'.
      a' = DROP (SUC k) p /\ (e',cid') = EL k p /\
      FLOOKUP blocks (a',e') =
        SOME (bb',bt',ps',xs',ys',sched',hin',h0',SOME (be',hbe'),cnt',OK b0',F,NONE) /\
      FLOOKUP calls (a',e',cid') = SOME (q',h',b0',done',child_entry',NONE) /\
      done' = TAKE cnt' sched') /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r done) /\
  (!F k kgss tail.
    N <= F /\ k <= LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
    (!r. r < k /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE cnt sched)) /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
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
      trace_gas (trace_block a e (F-e) C7 sf
        (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
        (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss) /\
      (!tail'.
        FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
        gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) /\
  (!F kgss tail u.
    N <= F /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
    FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
    (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
    (!callee argv. setup_callee callee argv (u with vs_gas_readings := b0.vs_gas_readings) =
      setup_callee callee argv b0)) ==>
  q < LENGTH xs /\ (EL q xs).inst_id = cid /\ (EL q xs).inst_opcode = INVOKE /\
  (?nm ops args ctf.
    decode_invoke (EL q xs) = SOME (nm,ops) /\
    lookup_function nm C8.ctx_functions = SOME ctf /\
    eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry) /\
  (!kgss rest caller.
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (TAKE q (THE (FLOOKUP ms_tab (a,e)))) kgss /\
    FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT kgss ++ rest) = OK caller ==>
    caller.vs_gas_readings = rest /\
    (!op. MEM op (EL q xs).inst_operands ==> eval_operand op caller = eval_operand op b0) /\
    (!callee argv. setup_callee callee argv (caller with vs_gas_readings := b0.vs_gas_readings) =
      setup_callee callee argv b0))
Proof
  rpt gen_tac >> strip_tac >>
  `!r. MEM r done ==> MEM r (TAKE cnt sched)` by
    (drule dft_packet_return_anchor_done >> disch_then drule >>
     disch_then (qspec_then `p` mp_tac) >> simp[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  reverse conj_tac
  >- (qpat_x_assum `!F kgss tail u. _` (drule_all_then strip_assume_tac) >> simp[]) >>
  qpat_x_assum `!F k kgss tail. _` (qspecl_then [`fuel`,`q`,`kgss`,`rest`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  strip_tac >> first_x_assum drule >> simp[]
QED
