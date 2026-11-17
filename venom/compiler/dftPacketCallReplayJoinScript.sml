Theory dftPacketCallReplayJoin
Ancestors
  dftPacketCallOldReplay dftPacketCallFreshReplay dftPacketCallFreshCaller
  list rich_list finite_map arithmetic

(* Concrete final-table join.  The pointwise structural disjunction is the
   final-aggregate lookup boundary of the bottom-up table construction. *)
Theorem dft_packet_call_replay_preservation:
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
    acts' blocks' calls' ms_tab' es_tab' ks_tab'
    N C7 C8 root_tf root_entry j p d inst s cnt sched q b
    sf fn inc entry order bb bt ps xs ys in_state h0 be hbe ms ess ks obs
    cs csf ctf cbb cbt cps cxs cys crho has_body s1 cbe cm ce ck.
  (* 1. Literal record insertion and old ownership/domain projections. *)
  b = (d,inst.inst_id)::p /\ q = EL cnt sched /\
  acts' = acts |+ (b,(csf,ctf,d,cs,[SUC d],NONE,NONE)) /\
  blocks' = blocks |+ ((b,SUC d),
    (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE)) /\
  calls' = calls |+ ((p,d,inst.inst_id),(q,j,s,TAKE cnt sched,cs,NONE)) /\
  FLOOKUP acts b = NONE /\
  (!a e rb rt rp rx ry rr ri rh rbe rbh rc rf rclosed rest.
    FLOOKUP blocks (a,e) =
      SOME (rb,rt,rp,rx,ry,rr,ri,rh,SOME(rbe,rbh),rc,rf,rclosed,rest) ==>
    ?owner target incoming ent ord res nrest rm re rk.
      FLOOKUP acts a = SOME(owner,target,incoming,ent,ord,res,nrest) /\
      FLOOKUP ms_tab (a,e) = SOME rm /\ FLOOKUP es_tab (a,e) = SOME re /\
      FLOOKUP ks_tab (a,e) = SOME rk) /\
  (!a e cid cq ch cb done child ret.
    FLOOKUP calls (a,e,cid) = SOME(cq,ch,cb,done,child,ret) ==>
    ?rb rt rp rx ry rr ri rh rbe rbh rc rf rclosed rest.
      FLOOKUP blocks (a,e) =
        SOME(rb,rt,rp,rx,ry,rr,ri,rh,SOME(rbe,rbh),rc,rf,rclosed,rest)) /\
  (* 2. Final row updates, at the actual old rows and owners. *)
  (!a e rb rt rp rx ry rr ri rh rbe rbh rc rf rclosed rest
      owner target incoming ent ord res nrest rm re rk.
    FLOOKUP blocks (a,e) =
      SOME(rb,rt,rp,rx,ry,rr,ri,rh,SOME(rbe,rbh),rc,rf,rclosed,rest) /\
    FLOOKUP acts a = SOME(owner,target,incoming,ent,ord,res,nrest) /\
    FLOOKUP ms_tab (a,e) = SOME rm /\ FLOOKUP es_tab (a,e) = SOME re /\
    FLOOKUP ks_tab (a,e) = SOME rk ==>
    ((FLOOKUP ms_tab' (a,e) = SOME rm /\
      FLOOKUP es_tab' (a,e) = SOME re /\ FLOOKUP ks_tab' (a,e) = SOME rk) \/
     ?livecid liveq b0 tf bt0 ys0 child_order.
      dft_fn_rel owner tf /\
      lookup_block rb.bb_label owner.fn_blocks = SOME rb /\
      lookup_block rb.bb_label tf.fn_blocks = SOME bt0 /\
      rb.bb_instructions = rp ++ rx /\ bt0.bb_instructions = rp ++ ys0 /\
      EVERY (\x. is_pseudo x.inst_opcode) rp /\
      EVERY (\x. ~is_pseudo x.inst_opcode) rx /\ LENGTH rx = LENGTH ys0 /\
      PERM rr (COUNT_LIST (LENGTH rx)) /\
      LIST_REL (\q y. q < LENGTH rx /\ y.inst_id = (EL q rx).inst_id /\
        from_block [EL q rx] y) rr ys0 /\
      liveq < LENGTH rx /\ (EL liveq rx).inst_opcode = INVOKE /\
      b0.vs_inst_idx = LENGTH rp + rc /\
      get_instruction bt0 b0.vs_inst_idx = SOME (EL liveq rx) /\
      (a = p \/ ?i h done child.
        i < LENGTH p /\ a = DROP (SUC i) p /\ (e,livecid) = EL i p /\
        FLOOKUP calls (a,e,livecid) = SOME(liveq,h,b0,done,child,NONE)) /\
      (!cid q h b0 done child ret.
        FLOOKUP calls (a,e,cid) = SOME(q,h,b0,done,child,ret) ==>
        q < LENGTH rx /\ (EL q rx).inst_opcode = INVOKE /\
        (case ret of
          NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
        | SOME triple => MEM q (TAKE rc rr))) /\
      FLOOKUP ms_tab' (a,e) = SOME (LUPDATE
        (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' ((e,livecid)::a,f)))) child_order)) liveq rm) /\
      FLOOKUP es_tab' (a,e) = SOME (LUPDATE
        (FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' ((e,livecid)::a,f)))) child_order)) liveq re) /\
      FLOOKUP ks_tab' (a,e) = SOME (LUPDATE
        (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' ((e,livecid)::a,f)))) child_order)) liveq rk))) /\
  FLOOKUP ms_tab' (b,SUC d) = SOME cm /\
  FLOOKUP es_tab' (b,SUC d) = SOME ce /\
  FLOOKUP ks_tab' (b,SUC d) = SOME ck /\
  cm = (if has_body then GENLIST (\r.
    if (EL r cxs).inst_opcode = GAS then [NONE] else []) (LENGTH cxs) else []) /\
  ce = (if has_body then GENLIST (\r.
    if (EL r cxs).inst_opcode = GAS then [(csf.fn_name,(EL r cxs).inst_id)] else []) (LENGTH cxs) else []) /\
  ck = (if has_body then GENLIST (\r.
    if (EL r cxs).inst_opcode = GAS then [(b,SUC d,(EL r cxs).inst_id)] else []) (LENGTH cxs) else []) /\
  (* 3. Old U and all-historical Q, on the old maps only. *)
  (!a e rb rt rp rx ry rr ri rh rbe rbh rc rf rclosed rest rm re rk
      owner target incoming ent ord res nrest.
    FLOOKUP blocks (a,e) =
      SOME(rb,rt,rp,rx,ry,rr,ri,rh,SOME(rbe,rbh),rc,rf,rclosed,rest) /\
    FLOOKUP ms_tab (a,e) = SOME rm /\ FLOOKUP es_tab (a,e) = SOME re /\
    FLOOKUP ks_tab (a,e) = SOME rk /\
    FLOOKUP acts a = SOME(owner,target,incoming,ent,ord,res,nrest) ==>
    !F k kgss tail.
      N <= F /\ k <= LENGTH rx /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k rx) /\
      (!q. q < k /\ (EL q rx).inst_opcode = INVOKE ==> MEM q (TAKE rc rr)) /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k rm) kgss ==>
      (?extra. FLAT (TAKE k re) =
        gas_events_block (F-e) C7 owner.fn_name
          <|bb_label := rbe.vs_current_bb; bb_instructions :=
            REPLICATE rbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k rx|>
          (rbe with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
      (!u. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k rx)
          (rbe with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        gas_events_block (F-e) C7 owner.fn_name
          <|bb_label := rbe.vs_current_bb; bb_instructions :=
            REPLICATE rbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k rx|>
          (rbe with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k re) /\
        u.vs_gas_readings = tail /\
        trace_gas (trace_block a e (F-e) C7 owner
          (rb with bb_instructions := TAKE (LENGTH rp + k) rb.bb_instructions)
          (rbe with vs_gas_readings := FLAT kgss ++ tail)) =
          ZIP (FLAT (TAKE k rk),FLAT kgss) /\
        (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k rx)
            (rbe with vs_gas_readings := FLAT kgss ++ tail') =
              OK (u with vs_gas_readings := tail') /\
          gas_events_block (F-e) C7 owner.fn_name
            <|bb_label := rbe.vs_current_bb; bb_instructions :=
              REPLICATE rbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k rx|>
            (rbe with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k re)))) /\
  (!a e cid cq ch cb done child ret
      rb rt rp rx ry rr ri rh rbe rbh rc rf rclosed rest rm.
    FLOOKUP calls (a,e,cid) = SOME(cq,ch,cb,done,child,ret) /\
    FLOOKUP blocks (a,e) =
      SOME(rb,rt,rp,rx,ry,rr,ri,rh,SOME(rbe,rbh),rc,rf,rclosed,rest) /\
    FLOOKUP ms_tab (a,e) = SOME rm ==>
    !F kgss tail u.
      N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE cq rm) kgss /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE cq rx)
        (rbe with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL cq rx).inst_operands ==> eval_operand op u = eval_operand op cb) /\
      (!callee args. setup_callee callee args (u with vs_gas_readings := cb.vs_gas_readings) =
        setup_callee callee args cb)) /\
  (* 4. Literal fresh child row specifications. *)
  cbe = (if has_body then SOME(s1,SUC j) else NONE) /\
  cbb.bb_instructions = cps ++ cxs /\ EVERY (\i. ~is_pseudo i.inst_opcode) cxs /\
  (has_body ==> s1.vs_inst_idx = LENGTH cps) /\
  (* 5. Actual old current row and the checked fresh-caller boundary inputs. *)
  FLOOKUP acts p = SOME(sf,fn,inc,entry,order,NONE,NONE) /\
  FLOOKUP blocks (p,d) =
    SOME(bb,bt,ps,xs,ys,sched,in_state,h0,SOME(be,hbe),cnt,OK s,F,NONE) /\
  FLOOKUP ms_tab (p,d) = SOME ms /\ FLOOKUP es_tab (p,d) = SOME ess /\
  FLOOKUP ks_tab (p,d) = SOME ks /\
  o1_ctx_shape C8 /\ MEM root_tf C8.ctx_functions /\
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\ hbe <= j /\
  EL hbe (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((p,d,(HD ys).inst_id),fn,HD ys,be) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((p,d,inst.inst_id),fn,inst,s) /\
  obs = trace_gas (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry)) /\
  lookup_block be.vs_current_bb fn.fn_blocks = SOME bt /\
  get_instruction bt s.vs_inst_idx = SOME inst /\
  bt.bb_instructions = ps ++ ys /\ bb_well_formed bt /\
  be.vs_inst_idx = LENGTH ps /\ cnt < LENGTH ys /\ inst = EL cnt ys /\
  FOLDR (dft_exec_cons (N-d) C8) OK (TAKE cnt ys) be = OK s /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\ dft_fn_rel sf fn /\
  MEM bb sf.fn_blocks /\ lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ EVERY (\x. is_pseudo x.inst_opcode) ps /\
  EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
  EVERY inst_shape_ok bb.bb_instructions /\ dft_remaining_inv sf bb xs be /\
  LIST_REL (\r y. r < LENGTH xs /\
    y.inst_id = (EL r xs).inst_id /\ from_block [EL r xs] y) sched ys /\
  (inv_memory_observation inst.inst_opcode ==>
    EL (EL cnt sched) xs = inst /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (EL cnt sched) xs) /\
    (!r. r < EL cnt sched /\ (EL r xs).inst_opcode = INVOKE ==>
      MEM r (TAKE cnt sched))) /\
  ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT (FLAT ks) /\
  (!r. LIST_REL (\key slot. slot = ALOOKUP obs key)
    (FLAT (TAKE r ks)) (FLAT (TAKE r ms))) /\ inst.inst_opcode = INVOKE /\
  (* 6. The current source prefix is unchanged by the final parent splice. *)
  (!ms_final. FLOOKUP ms_tab' (p,d) = SOME ms_final ==>
    TAKE q ms_final = TAKE q ms) ==>
  (* Final U, for every SOME-body row and its actual final owner. *)
  (!a e rb rt rp rx ry rr ri rh rbe rbh rc rf rclosed rest rm re rk
      owner target incoming ent ord res nrest.
    FLOOKUP blocks' (a,e) =
      SOME(rb,rt,rp,rx,ry,rr,ri,rh,SOME(rbe,rbh),rc,rf,rclosed,rest) /\
    FLOOKUP ms_tab' (a,e) = SOME rm /\ FLOOKUP es_tab' (a,e) = SOME re /\
    FLOOKUP ks_tab' (a,e) = SOME rk /\
    FLOOKUP acts' a = SOME(owner,target,incoming,ent,ord,res,nrest) ==>
    !F k kgss tail.
      N <= F /\ k <= LENGTH rx /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k rx) /\
      (!q. q < k /\ (EL q rx).inst_opcode = INVOKE ==> MEM q (TAKE rc rr)) /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k rm) kgss ==>
      (?extra. FLAT (TAKE k re) =
        gas_events_block (F-e) C7 owner.fn_name
          <|bb_label := rbe.vs_current_bb; bb_instructions :=
            REPLICATE rbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k rx|>
          (rbe with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
      (!u. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k rx)
          (rbe with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        gas_events_block (F-e) C7 owner.fn_name
          <|bb_label := rbe.vs_current_bb; bb_instructions :=
            REPLICATE rbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k rx|>
          (rbe with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k re) /\
        u.vs_gas_readings = tail /\
        trace_gas (trace_block a e (F-e) C7 owner
          (rb with bb_instructions := TAKE (LENGTH rp + k) rb.bb_instructions)
          (rbe with vs_gas_readings := FLAT kgss ++ tail)) =
          ZIP (FLAT (TAKE k rk),FLAT kgss) /\
        (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k rx)
            (rbe with vs_gas_readings := FLAT kgss ++ tail') =
              OK (u with vs_gas_readings := tail') /\
          gas_events_block (F-e) C7 owner.fn_name
            <|bb_label := rbe.vs_current_bb; bb_instructions :=
              REPLICATE rbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k rx|>
            (rbe with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k re)))) /\
  (* Final Q includes every returned historical call and the fresh call. *)
  (!a e cid cq ch cb done child ret
      rb rt rp rx ry rr ri rh rbe rbh rc rf rclosed rest rm.
    FLOOKUP calls' (a,e,cid) = SOME(cq,ch,cb,done,child,ret) /\
    FLOOKUP blocks' (a,e) =
      SOME(rb,rt,rp,rx,ry,rr,ri,rh,SOME(rbe,rbh),rc,rf,rclosed,rest) /\
    FLOOKUP ms_tab' (a,e) = SOME rm ==>
    !F kgss tail u.
      N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE cq rm) kgss /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE cq rx)
        (rbe with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL cq rx).inst_operands ==> eval_operand op u = eval_operand op cb) /\
      (!callee args. setup_callee callee args (u with vs_gas_readings := cb.vs_gas_readings) =
        setup_callee callee args cb))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  conj_tac >- suspend "U" >> suspend "Q"
QED

Resume dft_packet_call_replay_preservation[U]:
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `(a,e) = (b,SUC d)`
  >- (`a = b /\ e = SUC d` by gvs[] >>
      gvs[FLOOKUP_UPDATE] >>
      qpat_assum `rbe.vs_inst_idx = LENGTH cps` (fn th =>
        qpat_assum `cbb.bb_instructions = cps ++ cxs` (fn bh =>
          irule (SRULE [th,bh] (Q.INST [`be` |-> `rbe`, `bb` |-> `cbb`]
            dft_packet_call_fresh_child_U)))) >> simp[]) >>
  `FLOOKUP blocks (a,e) =
    SOME(rb,rt,rp,rx,ry,rr,ri,rh,SOME(rbe,rbh),rc,rf,rclosed,rest)` by
    fs[FLOOKUP_UPDATE] >>
  `?old_owner old_target old_inc old_ent old_ord old_res old_rest old_m old_e old_k.
    FLOOKUP acts a = SOME(old_owner,old_target,old_inc,old_ent,old_ord,old_res,old_rest) /\
    FLOOKUP ms_tab (a,e) = SOME old_m /\ FLOOKUP es_tab (a,e) = SOME old_e /\
    FLOOKUP ks_tab (a,e) = SOME old_k` by metis_tac[] >>
  `a <> b` by (strip_tac >> gvs[]) >>
  `FLOOKUP acts a = SOME(owner,target,incoming,ent,ord,res,nrest)` by
    fs[FLOOKUP_UPDATE] >>
  irule dft_packet_call_old_U_transport >>
  goal_assum (drule_at (Pat `FLOOKUP ms_tab' (a,e) = SOME rm`)) >>
  goal_assum (drule_at (Pat `FLOOKUP es_tab' (a,e) = SOME re`)) >>
  goal_assum (drule_at (Pat `FLOOKUP ks_tab' (a,e) = SOME rk`)) >>
  qexistsl [`calls`, `p`, `old_m`, `old_e`, `old_k`] >>
  FAIL_TAC "old U inputs"
QED

Resume dft_packet_call_replay_preservation[Q]:
  FAIL_TAC "Q join"
QED

Finalise dft_packet_call_replay_preservation
