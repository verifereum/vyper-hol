Theory dftPacketReturnEdgeAssembly
Ancestors
  dftRunRel dftIndexedExec dftGasFromListLookup frameInvokeReturn
  intCallStep venomWf venomInst list rich_list arithmetic
  dftPacketReturnChildClosure dftPacketReturnRootSuccessor
  dftPacketReturnTables dftPacketReturnLiveFrame dftPacketReturnVisitFrame
  dftPacketReturnRecordFrame dftPacketReturnParentRetained o1ScheduleDecompHelpers
  dftPacketReturnHistoricalCuts dftPacketReturnNewCuts
  dftPacketReturnParentCutApplication dftPacketReturnObservation
  dftContractGas dftWf gasOracleReplay stateEquiv
  venomExecSemantics sorting finite_map passSimulationDefs dftPacketReturnEdgeClauses
  venomExecProofs venomFnInstsProofs dftPacketPreterminalRows

(* Recover the ordered visits from the activation domain before composing
   the successful terminal row with the earlier closed child rows. *)
Theorem dft_packet_return_child_visits[local]:
  FLOOKUP acts (b : (num # num) list) =
    SOME (csf,ctf,e,ent,cord,NONE,NONE) /\
  (!f. MEM f cord <=> (b,f) IN FDOM blocks) /\
  (!x f bb bt ps xs ys rho ini h0 body count front closed brest.
    FLOOKUP blocks (x,f) = SOME (bb,bt,ps,xs,ys,rho,ini,h0,body,count,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp.
      FLOOKUP acts x = SOME (sf,tf,inc,entry,order,res,nrest) /\
      f <= N /\
      lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
      lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      lookup_block ini.vs_current_bb sf.fn_blocks = SOME bb /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\i. is_pseudo i.inst_opcode) ps /\
      EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
      EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
      eval_phis ini bt.bb_instructions = OK sp /\
      (if f = SUC inc then ini = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc (pu:bytes32 list).
          FLOOKUP blocks (x,f-1) =
            SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK ini,T,SOME pu) /\
          ~ini.vs_halted) /\
      (closed <=> IS_SOME brest) /\ (body = NONE ==> x = b /\ f = d) /\
      (!be hbe. body = SOME (be,hbe) ==>
        be.vs_inst_idx = LENGTH ps /\
        FOLDR (dft_exec_cons (N-f) C8) OK
          (DROP (phi_prefix_length bt.bb_instructions) ps)
          (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be) /\
      (f <> LAST order ==> closed /\ ?post. front = OK post /\ ~post.vs_halted)) /\
  LAST cord = d ==>
  !f. MEM f cord ==>
    ?bb bt ps xs ys rho ini h0 body count front closed brest sp.
      FLOOKUP blocks (b,f) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,body,count,front,closed,brest) /\
      f <= N /\
      lookup_block bb.bb_label csf.fn_blocks = SOME bb /\
      lookup_block bb.bb_label ctf.fn_blocks = SOME bt /\
      lookup_block ini.vs_current_bb csf.fn_blocks = SOME bb /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\i. is_pseudo i.inst_opcode) ps /\
      EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
      EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
      eval_phis ini bt.bb_instructions = OK sp /\
      (if f = SUC e then ini = ent else
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
      (f <> d ==> closed /\ ?post. front = OK post /\ ~post.vs_halted)
Proof
  strip_tac >> gen_tac >> disch_tac >>
  `?row. FLOOKUP blocks (b,f) = SOME row` by
    (fs[TO_FLOOKUP] >> Cases_on `FLOOKUP blocks (b,f)` >> gvs[]) >>
  PairCases_on `row` >>
  qpat_assum `!x f bb bt ps xs ys rho ini h0 body count front closed brest. _`
    drule >> strip_tac >> gvs[] >>
  rpt (goal_assum $ drule_at Any) >> simp[]
QED

(* The retained call uses the same source index as the schedule cursor. *)
Theorem dft_packet_return_index[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  LIST_REL (\k y. k < LENGTH xs /\ y.inst_id = (EL k xs).inst_id /\
    from_block [EL k xs] y) sched ys /\
  pn < LENGTH ys /\ c = EL pn ys /\ q < LENGTH xs /\
  (EL q xs).inst_id = c.inst_id ==>
  q = EL pn sched /\ pn < LENGTH sched
Proof
  strip_tac >>
  qpat_x_assum `LIST_REL _ sched ys`
    (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  `pn < LENGTH sched` by decide_tac >>
  first_x_assum (qspec_then `pn` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `ALL_DISTINCT _`
    (mp_tac o REWRITE_RULE [EL_ALL_DISTINCT_EL_EQ]) >>
  disch_then (qspecl_then [`q`,`EL pn sched`] mp_tac) >>
  simp[EL_MAP]
QED

Theorem dft_packet_return_source_callee[local]:
  o1_ctx_shape C7 /\ o1_ctx_shape C8 /\ MEM csf C7.ctx_functions /\
  dft_fn_rel csf ctf /\ lookup_function nm C8.ctx_functions = SOME ctf ==>
  lookup_function nm C7.ctx_functions = SOME csf
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) C7.ctx_functions) /\
   ALL_DISTINCT (MAP (\f. f.fn_name) C8.ctx_functions)` by
    fs[o1PassContractTheory.o1_ctx_shape_def,ctx_wf_def,ctx_distinct_fn_names_def,ctx_fn_names_def] >>
  gvs[lookup_function_member_iff,dft_fn_rel_def]
QED

(* Return replay only needs the successful IntRet part of the activation
   certificate, but still needs event coverage when that replay stops. *)
Theorem dft_packet_return_intret_replay[local]:
  (!F. N <= F ==>
    run_blocks (F-inc) C8 ctf entry = IntRet ir out /\
    (!gs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM a) gs ==>
      (?extra. AE a = gas_events_blocks (F-inc) C7 csf
        (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?f. terminates (run_blocks f C7 csf
          (entry with vs_gas_readings := gs ++ tail))) ==>
        terminates (run_blocks (F-inc) C7 csf (entry with vs_gas_readings := gs ++ tail)) /\
        dft_res_rel
          (restore_result [] (run_blocks (F-inc) C7 csf (entry with vs_gas_readings := gs ++ tail)))
          (restore_result [] (IntRet ir out)) /\
        gas_events_blocks (F-inc) C7 csf (entry with vs_gas_readings := gs ++ tail) = AE a /\
        residual_result tail (IntRet ir out)
          (run_blocks (F-inc) C7 csf (entry with vs_gas_readings := gs ++ tail))) /\
      (!v. (run_blocks (F-inc) C7 csf (entry with vs_gas_readings := gs ++ tail) = OK v \/
            ?ret. run_blocks (F-inc) C7 csf (entry with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
        trace_gas (trace_blocks a inc (F-inc) C7 csf
          (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK a,gs)))) ==>
  !F gs tail.
    N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM a) gs ==>
    (?extra. AE a = gas_events_blocks (F-inc) C7 csf
      (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
    (terminates (run_blocks (F-inc) C7 csf (entry with vs_gas_readings := gs ++ tail)) ==>
      residual_result tail (IntRet ir out)
        (run_blocks (F-inc) C7 csf (entry with vs_gas_readings := gs ++ tail)) /\
      gas_events_blocks (F-inc) C7 csf (entry with vs_gas_readings := gs ++ tail) = AE a) /\
    (!ret v. run_blocks (F-inc) C7 csf (entry with vs_gas_readings := gs ++ tail) = IntRet ret v ==>
      trace_gas (trace_blocks a inc (F-inc) C7 csf
        (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK a,gs))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  first_x_assum (drule_then (qspec_then `tail` strip_assume_tac)) >>
  rpt conj_tac >- (qexists_tac `extra` >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >> metis_tac[]
QED

(* A completed record projected from the primed visit and activation clauses. *)
Theorem dft_packet_return_replay_call[local]:
  o1_ctx_shape C7 /\ o1_ctx_shape C8 /\
  FLOOKUP (blocks : (((num # num) list # num),
    basic_block # basic_block # instruction list # instruction list #
    instruction list # num list # venom_state # num #
    (venom_state # num) option # num # exec_result # bool # bytes32 list option) fmap)
    (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),n,front,closed,brest) /\
  (!x sf tf inc entry order res nrest.
    FLOOKUP acts x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    MEM sf C7.ctx_functions /\ dft_fn_rel sf tf /\ (res = NONE <=> nrest = NONE)) /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE n sched) ==>
    ?h b0 done entry ir out post.
      FLOOKUP (calls : (gas_event,num # num # venom_state # num list # venom_state #
        (internal_return # venom_state # venom_state) option) fmap)
        (a,e,(EL q xs).inst_id) = SOME (q,h,b0,done,entry,SOME (ir,out,post))) /\
  (!id k t z done entry ir out post.
    FLOOKUP calls (a,e,id) = SOME (k,t,z,done,entry,SOME (ir,out,post)) ==>
    ?bb bt ps xs ys sched hin h0 be hbe n front closed rest csf ctf cord crest c nm ops args.
      FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),n,front,closed,rest) /\
      c = EL k xs /\
      FLOOKUP acts ((e,id)::a) = SOME (csf,ctf,e,entry,cord,SOME (IntRet ir out),crest) /\
      decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops z = SOME args /\ setup_callee ctf args z = SOME entry) ==>
  !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE n sched) ==>
    ?h b0 done entry ir out post nm ops ctf args.
      FLOOKUP calls (a,e,(EL q xs).inst_id) = SOME (q,h,b0,done,entry,SOME (ir,out,post)) /\
      decode_invoke (EL q xs) = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME entry /\
      (!csf. lookup_function nm C7.ctx_functions = SOME csf ==>
        ?ord rest. FLOOKUP acts ((e,(EL q xs).inst_id)::a) =
          SOME (csf,ctf,e,entry,ord,SOME (IntRet ir out),SOME rest))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!q. q < LENGTH xs /\ _ ==> _` (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!id k t z done entry ir out post. _ ==> _` (drule_then strip_assume_tac) >>
  gvs[] >>
  qpat_x_assum `!x sf tf inc entry order res nrest. _ ==> _` (drule_then strip_assume_tac) >>
  Cases_on `crest` >> gvs[] >>
  drule_all_then assume_tac dft_packet_return_source_callee >>
  rpt (goal_assum $ drule_at Any) >> simp[] >> metis_tac[]
QED

(* A return changes a call result but does not add or remove a call key.
   This is the only call-map information used by the slot rows. *)
Theorem dft_packet_return_row_call_domain[local]:
  calls' = calls |+ (key,ret) /\ FLOOKUP calls key = SOME pending ==>
  !k. FLOOKUP calls' k = NONE <=> FLOOKUP calls k = NONE
Proof
  strip_tac >> gen_tac >> Cases_on `key = k` >> gvs[FLOOKUP_UPDATE]
QED

Theorem dft_packet_return_old_membership[local]:
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
    MEM q (TAKE cn sched)) /\ k <= LENGTH xs ==>
  !q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE cn sched)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> first_x_assum irule >>
  simp[] >> decide_tac
QED

(* Replay at the parent frontier uses both its historical caller agreement
   and every retained closed child's same-budget certificate.  The new child
   is in the same updated activation map as the previously closed children. *)
Theorem dft_packet_return_parent_replay_join[local]:
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  bb.bb_instructions = ps ++ xs /\ be.vs_inst_idx = LENGTH ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
  LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
  LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\
  (!q. q < LENGTH xs ==>
    ((EL q xs).inst_opcode = GAS ==>
      EL q ms = [ALOOKUP obs (a,e,(EL q xs).inst_id)] /\
      EL q ess = [(sf.fn_name,(EL q xs).inst_id)] /\
      EL q ks = [(a,e,(EL q xs).inst_id)]) /\
    ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
      EL q ms = [] /\ EL q ess = [] /\ EL q ks = []) /\
    ((EL q xs).inst_opcode = INVOKE ==>
      case FLOOKUP calls (a,e,(EL q xs).inst_id) of
      NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
      | SOME cl =>
        EL q ms = AM ((e,(EL q xs).inst_id)::a) /\
        EL q ess = AE ((e,(EL q xs).inst_id)::a) /\
        EL q ks = AK ((e,(EL q xs).inst_id)::a))) /\
  (!key. FLOOKUP calls' key = NONE <=> FLOOKUP calls key = NONE) /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE (SUC pn) sched) ==>
    ?h b0 done entry ir out post nm ops ctf args.
      FLOOKUP (calls' : (gas_event,num # num # venom_state # num list # venom_state #
        (internal_return # venom_state # venom_state) option) fmap)
        (a,e,(EL q xs).inst_id) = SOME (q,h,b0,done,entry,SOME (ir,out,post)) /\
      decode_invoke (EL q xs) = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME entry /\
      (!csf. lookup_function nm C7.ctx_functions = SOME csf ==>
        ?ord rest. FLOOKUP acts' ((e,(EL q xs).inst_id)::a) =
          SOME (csf,ctf,e,entry,ord,SOME (IntRet ir out),SOME rest))) /\
  (!q h b0 done entry ir out post.
    FLOOKUP calls' (a,e,(EL q xs).inst_id) = SOME (q,h,b0,done,entry,SOME (ir,out,post)) ==>
    !F pg rest u.
      N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) pg /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT pg ++ rest) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
      (!callee args. setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
        setup_callee callee args b0)) /\
  FLOOKUP (acts' : ((num # num) list,ir_function # ir_function # num # venom_state #
    num list # exec_result option # bytes32 list option) fmap) b =
    SOME (csf,ctf,e,entry,ord,SOME (IntRet ir out),SOME rest) /\
  (!x xsf xtf inc ent ordr ret u rest.
    FLOOKUP acts' x = SOME (xsf,xtf,inc,ent,ordr,SOME (IntRet ret u),SOME rest) ==>
    !F gs tail.
      N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM x) gs ==>
      (?extra. AE x = gas_events_blocks (F-inc) C7 xsf
        (ent with vs_gas_readings := gs ++ tail) ++ extra) /\
      (terminates (run_blocks (F-inc) C7 xsf (ent with vs_gas_readings := gs ++ tail)) ==>
        residual_result tail (IntRet ret u)
          (run_blocks (F-inc) C7 xsf (ent with vs_gas_readings := gs ++ tail)) /\
        gas_events_blocks (F-inc) C7 xsf (ent with vs_gas_readings := gs ++ tail) = AE x) /\
      (!r v. run_blocks (F-inc) C7 xsf (ent with vs_gas_readings := gs ++ tail) = IntRet r v ==>
        trace_gas (trace_blocks x inc (F-inc) C7 xsf
          (ent with vs_gas_readings := gs ++ tail)) = ZIP (AK x,gs))) ==>
  !F k kgss tail.
    N <= F /\ k <= LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
    (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE (SUC pn) sched)) /\
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
        (be with vs_gas_readings := FLAT kgss ++ tail)) =
        ZIP (FLAT (TAKE k ks),FLAT kgss) /\
      (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail') =
            OK (u with vs_gas_readings := tail') /\
        gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!x xsf xtf inc ent ordr ret u rest. _` (drule_then assume_tac) >>
  `!q. q < LENGTH xs ==>
    ((EL q xs).inst_opcode = GAS ==>
      EL q ms = [ALOOKUP obs (a,e,(EL q xs).inst_id)] /\
      EL q ess = [(sf.fn_name,(EL q xs).inst_id)] /\
      EL q ks = [(a,e,(EL q xs).inst_id)]) /\
    ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
      EL q ms = [] /\ EL q ess = [] /\ EL q ks = []) /\
    ((EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE (SUC pn) sched) ==>
      EL q ms = AM ((e,(EL q xs).inst_id)::a) /\
      EL q ess = AE ((e,(EL q xs).inst_id)::a) /\
      EL q ks = AK ((e,(EL q xs).inst_id)::a))` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!q. q < LENGTH xs ==> _` (drule_then strip_assume_tac) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!q. q < LENGTH xs /\ _ ==> _` (drule_all_then strip_assume_tac) >>
     `FLOOKUP calls (a,e,(EL q xs).inst_id) <> NONE` by
       (qpat_assum `FLOOKUP calls' (a,e,(EL q xs).inst_id) = SOME _` mp_tac >>
        qpat_assum `!key. FLOOKUP calls' key = NONE <=> _` mp_tac >>
        POP_ASSUM_LIST kall_tac >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
     Cases_on `FLOOKUP calls (a,e,(EL q xs).inst_id)` >> gvs[]) >>
  rpt gen_tac >>
  match_mp_tac (Q.INST [`acts` |-> `acts'`, `calls` |-> `calls'`,
    `child0` |-> `b`, `csf0` |-> `csf`, `entry0` |-> `entry`,
    `ir0` |-> `ir`, `out0` |-> `out`] dft_packet_return_parent_U_retained) >>
  simp[] >>
  conj_tac >-
   (qx_gen_tac `q` >> strip_tac >>
    qpat_x_assum `!q. q < LENGTH xs /\ _ ==> _`
      (qspec_then `q` mp_tac) >>
    simp[] >> strip_tac >>
    rpt (goal_assum $ drule_at Any) >> simp[] >>
    rpt gen_tac >> strip_tac >> disj1_tac >> first_x_assum irule >> simp[]) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!x xsf xtf inc ent ordr ret u rest. _`
    (drule_then assume_tac) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >> simp[]
QED

Theorem dft_packet_return_old_act[local]:
  FLOOKUP (acts : ((num # num) list, ir_function # ir_function # num # venom_state #
    num list # exec_result option # bytes32 list option) fmap) b =
      SOME (csf,ctf,e,ent,ord,NONE,NONE) /\
  acts' = acts |+ (b,(csf,ctf,e,ent,ord,SOME (IntRet ir out),SOME out.vs_gas_readings)) /\
  FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
  ?old_res old_rest. FLOOKUP acts x = SOME (sf,tf,inc,entry,order,old_res,old_rest)
Proof
  strip_tac >> Cases_on `x = b` >> gvs[FLOOKUP_UPDATE] >> metis_tac[]
QED

(* Source replay uses the old prefix membership at every unchanged row.
   At the popped row all source INVOKEs already belonged to the old prefix. *)

Theorem dft_packet_return_old_U_row[local]:
  FLOOKUP (blocks : (((num # num) list # num), basic_block # basic_block #
    instruction list # instruction list # instruction list # num list # venom_state #
    num # (venom_state # num) option # num # exec_result # bool # bytes32 list option) fmap)
    (b,d) = SOME (cbb,cbt,cps,cxs,cys,csched,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE) /\
  blocks' = blocks |+
    ((b,d),(cbb,cbt,cps,cxs,cys,csched,cin,ch0,SOME (cbe,chbe),
      LENGTH cys,IntRet ir out,T,SOME out.vs_gas_readings)) |+
    ((a,e),(pbb,pbt,pps,pxs,pys,psched,pin,ph0,SOME (pbe,phbe),SUC pn,
      OK (post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
  (!q. q < LENGTH cxs /\ (EL q cxs).inst_opcode = INVOKE ==> MEM q (TAKE cn csched)) /\
  (x,f) <> (a,e) /\
  FLOOKUP blocks' (x,f) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),n,front,closed,brest) ==>
  ?on ofront oclosed orest.
    FLOOKUP blocks (x,f) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),on,ofront,oclosed,orest) /\
    (!k. k <= LENGTH xs /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE n sched)) ==>
      !q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE on sched))
Proof
  strip_tac >> `(a,e) <> (x,f)` by metis_tac[] >>
  qpat_x_assum `FLOOKUP blocks' _ = _` mp_tac >>
  asm_rewrite_tac[FLOOKUP_UPDATE] >>
  Cases_on `(b,d) = (x,f)` >> asm_rewrite_tac[]
  >- (strip_tac >> gvs[] >> qexistsl [`cn`,`OK s`,`F`,`NONE`] >>
      simp[] >> rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  strip_tac >> rpt (goal_assum $ drule_at Any) >> simp[]
QED

(* Reuse the exact old replay certificate, including its success-conditional
   trace and arbitrary-tail clauses, at all rows except the resumed one. *)

Theorem dft_packet_return_off_parent_U[local]:
  FLOOKUP (acts : ((num # num) list, ir_function # ir_function # num # venom_state #
    num list # exec_result option # bytes32 list option) fmap) b =
      SOME (csf,ctf,e,ent,ord,NONE,NONE) /\
  acts' = acts |+ (b,(csf,ctf,e,ent,ord,SOME (IntRet ir out),SOME out.vs_gas_readings)) /\
  FLOOKUP (blocks : (((num # num) list # num), basic_block # basic_block #
    instruction list # instruction list # instruction list # num list # venom_state #
    num # (venom_state # num) option # num # exec_result # bool # bytes32 list option) fmap)
    (b,d) = SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE) /\
  blocks' = blocks |+
    ((b,d),(cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),
      LENGTH cys,IntRet ir out,T,SOME out.vs_gas_readings)) |+
    ((a,e),(pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),SUC pn,
      OK (post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
  (!q. q < LENGTH cxs /\ (EL q cxs).inst_opcode = INVOKE ==> MEM q (TAKE cn crho)) /\
  (!x f bb bt ps xs ys sched hin h0 be hbe n front closed brest
    ms ess ks sf tf inc entry order res nrest.
    FLOOKUP blocks (x,f) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),n,front,closed,brest) /\
    FLOOKUP ms_tab (x,f) = SOME ms /\ FLOOKUP es_tab (x,f) = SOME ess /\
    FLOOKUP ks_tab (x,f) = SOME ks /\ FLOOKUP acts x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    !F k kgss tail.
      N <= F /\ k <= LENGTH xs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE n sched)) /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
      (?extra. FLAT (TAKE k ess) =
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
      (!u. FOLDR (dft_exec_cons (F-f) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
        u.vs_gas_readings = tail /\
        trace_gas (trace_block x f (F-f) C7 sf
          (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
          (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss) /\
        (!tail'. FOLDR (dft_exec_cons (F-f) C7) OK (TAKE k xs)
            (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
          gas_events_block (F-f) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) ==>
  !x f bb bt ps xs ys sched hin h0 be hbe n front closed brest
    ms ess ks sf tf inc entry order res nrest.
    (x,f) <> (a,e) /\
    FLOOKUP blocks' (x,f) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),n,front,closed,brest) /\
    FLOOKUP ms_tab (x,f) = SOME ms /\ FLOOKUP es_tab (x,f) = SOME ess /\
    FLOOKUP ks_tab (x,f) = SOME ks /\ FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    !F k kgss tail.
      N <= F /\ k <= LENGTH xs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE n sched)) /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
      (?extra. FLAT (TAKE k ess) =
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
      (!u. FOLDR (dft_exec_cons (F-f) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
        u.vs_gas_readings = tail /\
        trace_gas (trace_block x f (F-f) C7 sf
          (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
          (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss) /\
        (!tail'. FOLDR (dft_exec_cons (F-f) C7) OK (TAKE k xs)
            (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
          gas_events_block (F-f) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))
Proof
  disch_then (fn th => let val hs = CONJUNCTS th in
    map_every assume_tac (List.take (hs,5)) >> mk_asm "old_U" (List.last hs)
    end) >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac dft_packet_return_old_act >>
  drule_all_then strip_assume_tac dft_packet_return_old_U_row >>
  asm_x "old_U" (drule_then mp_tac) >>
  simp[] >> disch_then (mk_asm "old_replay") >>
  rpt gen_tac >> strip_tac >>
  asm_x "old_replay" match_mp_tac >>
  asm_rewrite_tac[] >>
  qpat_x_assum `!k. k <= LENGTH xs /\ _ ==> _`
    (qspec_then `k` mp_tac) >> asm_rewrite_tac[]
QED

(* A return adds just the popped child to the closed activation domain.
   The three aggregates retain their old orders and component tables. *)
Theorem dft_packet_return_closed_activations[local]:
  acts' = (acts : ((num # num) list, ir_function # ir_function # num # venom_state #
    num list # exec_result option # bytes32 list option) fmap) |+
    (b,(csf,ctf,e,ent,ord,SOME (IntRet ir out),SOME out.vs_gas_readings)) /\
  terminates (IntRet ir out) /\
  LENGTH (AM b) = LENGTH (AE b) /\ LENGTH (AM b) = LENGTH (AK b) /\
  PERM (MAP THE (FILTER IS_SOME (AM b)) ++ out.vs_gas_readings) ent.vs_gas_readings /\
  EVERY IS_SOME (AM b) /\
  (!F. N <= F ==>
    run_blocks (F-e) C8 ctf ent = IntRet ir out /\
    (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM b) gs ==>
      (?extra. AE b = gas_events_blocks (F-e) C7 csf
        (ent with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?f. terminates (run_blocks f C7 csf (ent with vs_gas_readings := gs ++ tail))) ==>
        terminates (run_blocks (F-e) C7 csf (ent with vs_gas_readings := gs ++ tail)) /\
        dft_res_rel (restore_result [] (run_blocks (F-e) C7 csf
          (ent with vs_gas_readings := gs ++ tail))) (restore_result [] (IntRet ir out)) /\
        gas_events_blocks (F-e) C7 csf (ent with vs_gas_readings := gs ++ tail) = AE b /\
        residual_result tail (IntRet ir out)
          (run_blocks (F-e) C7 csf (ent with vs_gas_readings := gs ++ tail))) /\
      (!v. (run_blocks (F-e) C7 csf (ent with vs_gas_readings := gs ++ tail) = OK v \/
        ?ret. run_blocks (F-e) C7 csf (ent with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
        trace_gas (trace_blocks b e (F-e) C7 csf
          (ent with vs_gas_readings := gs ++ tail)) = ZIP (AK b,gs)))) /\
  (!x sf tf inc entry order r8 u0.
    FLOOKUP acts x = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
    terminates r8 /\
    LENGTH (AM x) = LENGTH (AE x) /\ LENGTH (AM x) = LENGTH (AK x) /\
    PERM (MAP THE (FILTER IS_SOME (AM x)) ++ u0) entry.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (AM x) /\ u0 = v.vs_gas_readings) /\
    (!F. N <= F ==>
      run_blocks (F-inc) C8 tf entry = r8 /\
      (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM x) gs ==>
        (?extra. AE x = gas_events_blocks (F-inc) C7 sf
          (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (run_blocks f C7 sf (entry with vs_gas_readings := gs ++ tail))) ==>
          terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel (restore_result [] (run_blocks (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = AE x /\
            residual_result tail r8
              (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)))) /\
        (!v. (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = OK v \/
          ?ir. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          trace_gas (trace_blocks x inc (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK x,gs))))) ==>
  !x sf tf inc entry order r8 u0.
    FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
    terminates r8 /\
    LENGTH (AM x) = LENGTH (AE x) /\ LENGTH (AM x) = LENGTH (AK x) /\
    PERM (MAP THE (FILTER IS_SOME (AM x)) ++ u0) entry.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (AM x) /\ u0 = v.vs_gas_readings) /\
    (!F. N <= F ==>
      run_blocks (F-inc) C8 tf entry = r8 /\
      (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM x) gs ==>
        (?extra. AE x = gas_events_blocks (F-inc) C7 sf
          (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (run_blocks f C7 sf (entry with vs_gas_readings := gs ++ tail))) ==>
          terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel (restore_result [] (run_blocks (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = AE x /\
            residual_result tail r8
              (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)))) /\
        (!v. (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = OK v \/
          ?ir. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          trace_gas (trace_blocks x inc (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK x,gs))))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `x = b`
  >- (gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
  `b <> x` by metis_tac[] >>
  gvs[FLOOKUP_UPDATE] >> first_x_assum drule >> metis_tac[]
QED

(* Specialize the closed-activation replay clause at a returned call. *)
Theorem dft_packet_return_closed_intret_supplier[local]:
  (!x sf tf inc entry order r8 u0.
    FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
    !F. N <= F ==>
      run_blocks (F-inc) C8 tf entry = r8 /\
      (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM x) gs ==>
        (?extra. AE x = gas_events_blocks (F-inc) C7 sf
          (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (run_blocks f C7 sf (entry with vs_gas_readings := gs ++ tail))) ==>
          terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel (restore_result [] (run_blocks (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = AE x /\
            residual_result tail r8
              (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)))) /\
        (!v. (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = OK v \/
          ?ir. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          trace_gas (trace_blocks x inc (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK x,gs)))) ==>
  !x sf tf inc entry order ret u rest.
    FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,SOME (IntRet ret u),SOME rest) ==>
    !F gs tail.
      N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM x) gs ==>
      (?extra. AE x = gas_events_blocks (F-inc) C7 sf
        (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
      (terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) ==>
        residual_result tail (IntRet ret u)
          (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
        gas_events_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = AE x) /\
      (!r v. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet r v ==>
        trace_gas (trace_blocks x inc (F-inc) C7 sf
          (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK x,gs))
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  first_x_assum (drule_then (assume_tac o SRULE [])) >>
  drule_then ACCEPT_TAC dft_packet_return_intret_replay
QED

(* At a fixed parent row the body, schedule and entry from the visit
   certificate identify the arguments of historical Q and the call setup. *)
Theorem dft_packet_return_parent_call_inputs[local]:
  o1_ctx_shape C7 /\ o1_ctx_shape C8 /\
  FLOOKUP (blocks' : (((num # num) list # num), basic_block # basic_block #
    instruction list # instruction list # instruction list # num list # venom_state #
    num # (venom_state # num) option # num # exec_result # bool # bytes32 list option) fmap)
    (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),n,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\
  (!x sf tf inc entry order res nrest.
    FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    MEM sf C7.ctx_functions /\ dft_fn_rel sf tf /\ (res = NONE <=> nrest = NONE)) /\
  (!x v bb bt ps xs ys rho ini h0 be hbe count front closed brest.
    FLOOKUP blocks' (x,v) =
      SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE count rho) ==>
      ?h b0 done entry ir out post.
        FLOOKUP calls' (x,v,(EL q xs).inst_id) = SOME (q,h,b0,done,entry,SOME (ir,out,post))) /\
  (!x v id k t s done entry ret.
    FLOOKUP (calls' : (gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
      (x,v,id) = SOME (k,t,s,done,entry,ret) ==>
    ?bb bt ps xs ys rho ini h0 be hbe count front closed brest csf ctf cord cres crest c nm ops args.
      FLOOKUP blocks' (x,v) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) /\
      c = EL k xs /\
      FLOOKUP acts' ((v,id)::x) = SOME (csf,ctf,v,entry,cord,cres,crest) /\
      decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops s = SOME args /\ setup_callee ctf args s = SOME entry /\
      (case ret of NONE => cres = NONE | SOME (ir,out,post) => cres = SOME (IntRet ir out))) /\
  (!x v id q h s done entry ret bb bt ps xs ys rho ini h0 be hbe count front closed brest ms.
    FLOOKUP calls' (x,v,id) = SOME (q,h,s,done,entry,ret) /\
    FLOOKUP blocks' (x,v) =
      SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (x,v) = SOME ms ==>
    !F kgss tail u. N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
      FOLDR (dft_exec_cons (F-v) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op s) /\
      (!callee args. setup_callee callee args (u with vs_gas_readings := s.vs_gas_readings) =
        setup_callee callee args s)) ==>
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE n sched) ==>
    ?h b0 done entry ir out post nm ops ctf args.
      FLOOKUP calls' (a,e,(EL q xs).inst_id) = SOME (q,h,b0,done,entry,SOME (ir,out,post)) /\
      decode_invoke (EL q xs) = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME entry /\
      (!csf. lookup_function nm C7.ctx_functions = SOME csf ==>
        ?ord rest. FLOOKUP acts' ((e,(EL q xs).inst_id)::a) =
          SOME (csf,ctf,e,entry,ord,SOME (IntRet ir out),SOME rest))) /\
  (!q h b0 done entry ir out post.
    FLOOKUP calls' (a,e,(EL q xs).inst_id) = SOME (q,h,b0,done,entry,SOME (ir,out,post)) ==>
    !F kgss tail u. N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
      (!callee args. setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
        setup_callee callee args b0))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule dft_packet_return_replay_call >>
      rpt (goal_assum $ drule_at Any) >>
      reverse conj_tac
      >- (qpat_assum `!x v bb bt ps xs ys rho ini h0 be hbe count front closed brest. _`
            (drule_then ACCEPT_TAC)) >>
      rpt gen_tac >> disch_tac >>
      qpat_assum `FLOOKUP calls' (a,e,id) = SOME _` (fn record =>
        qpat_assum `!x v id k t s done entry ret. _`
          (mp_tac o C MATCH_MP record)) >>
      qpat_assum `FLOOKUP blocks' (a,e) = SOME _` (fn row => simp[NoAsms,row]) >>
      strip_tac >> rpt (goal_assum $ drule_at Any) >> simp[]) >>
  rpt gen_tac >> disch_tac >> metis_tac[]
QED

Theorem dft_packet_return_resumed_U[local]:
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  o1_ctx_shape C7 /\ o1_ctx_shape C8 /\
  bb.bb_instructions = ps ++ xs /\ be.vs_inst_idx = LENGTH ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
  LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
  LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\
  (!q. q < LENGTH xs ==>
    ((EL q xs).inst_opcode = GAS ==>
      EL q ms = [ALOOKUP obs (a,e,(EL q xs).inst_id)] /\
      EL q ess = [(sf.fn_name,(EL q xs).inst_id)] /\
      EL q ks = [(a,e,(EL q xs).inst_id)]) /\
    ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
      EL q ms = [] /\ EL q ess = [] /\ EL q ks = []) /\
    ((EL q xs).inst_opcode = INVOKE ==>
      case FLOOKUP calls (a,e,(EL q xs).inst_id) of
        NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
      | SOME cl => EL q ms = AM ((e,(EL q xs).inst_id)::a) /\
        EL q ess = AE ((e,(EL q xs).inst_id)::a) /\
        EL q ks = AK ((e,(EL q xs).inst_id)::a))) /\
  (!key. FLOOKUP calls' key = NONE <=> FLOOKUP calls key = NONE) /\
  FLOOKUP (acts' : ((num # num) list,ir_function # ir_function # num # venom_state #
    num list # exec_result option # bytes32 list option) fmap) b =
    SOME (csf,ctf,e,entry,ord,SOME (IntRet ir out),SOME rest) /\
  FLOOKUP (blocks' : (((num # num) list # num), basic_block # basic_block #
    instruction list # instruction list # instruction list # num list # venom_state #
    num # (venom_state # num) option # num # exec_result # bool # bytes32 list option) fmap)
    (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),SUC pn,front,F,NONE) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\
  (!x sf tf inc entry order res nrest.
    FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    MEM sf C7.ctx_functions /\ dft_fn_rel sf tf /\ (res = NONE <=> nrest = NONE)) /\
  (!x v bb bt ps xs ys rho ini h0 be hbe count front closed brest.
    FLOOKUP blocks' (x,v) =
      SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE count rho) ==>
      ?h b0 done entry ir out post.
        FLOOKUP calls' (x,v,(EL q xs).inst_id) = SOME (q,h,b0,done,entry,SOME (ir,out,post))) /\
  (!x v id k t s done entry ret.
    FLOOKUP (calls' : (gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
      (x,v,id) = SOME (k,t,s,done,entry,ret) ==>
    ?bb bt ps xs ys rho ini h0 be hbe count front closed brest csf ctf cord cres crest c nm ops args.
      FLOOKUP blocks' (x,v) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) /\
      c = EL k xs /\
      FLOOKUP acts' ((v,id)::x) = SOME (csf,ctf,v,entry,cord,cres,crest) /\
      decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops s = SOME args /\ setup_callee ctf args s = SOME entry /\
      (case ret of NONE => cres = NONE | SOME (ir,out,post) => cres = SOME (IntRet ir out))) /\
  (!x v id q h s done entry ret bb bt ps xs ys rho ini h0 be hbe count front closed brest ms.
    FLOOKUP calls' (x,v,id) = SOME (q,h,s,done,entry,ret) /\
    FLOOKUP blocks' (x,v) =
      SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (x,v) = SOME ms ==>
    !F kgss tail u. N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
      FOLDR (dft_exec_cons (F-v) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op s) /\
      (!callee args. setup_callee callee args (u with vs_gas_readings := s.vs_gas_readings) =
        setup_callee callee args s)) /\
  (!x sf tf inc entry order r8 u0.
    FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
    !F. N <= F ==>
      run_blocks (F-inc) C8 tf entry = r8 /\
      (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM x) gs ==>
        (?extra. AE x = gas_events_blocks (F-inc) C7 sf
          (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (run_blocks f C7 sf (entry with vs_gas_readings := gs ++ tail))) ==>
          terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel (restore_result [] (run_blocks (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = AE x /\
            residual_result tail r8
              (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)))) /\
        (!v. (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = OK v \/
          ?ir. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          trace_gas (trace_blocks x inc (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK x,gs)))) ==>
  !F k kgss tail.
    N <= F /\ k <= LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
    (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE (SUC pn) sched)) /\
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
        (be with vs_gas_readings := FLAT kgss ++ tail)) =
          ZIP (FLAT (TAKE k ks),FLAT kgss) /\
      (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail') =
            OK (u with vs_gas_readings := tail') /\
        gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) dft_packet_return_parent_call_inputs >>
  first_assum (assume_tac o MATCH_MP dft_packet_return_closed_intret_supplier) >>
  match_mp_tac dft_packet_return_parent_replay_join >>
  rpt (goal_assum $ drule_at Any)
QED

(* Only the optional return payload changes; array cells depend on the
   presence of a call, not on its payload. *)
Theorem dft_packet_return_array_frame[local]:
  FLOOKUP (acts : ((num # num) list, ir_function # ir_function # num # venom_state #
    num list # exec_result option # bytes32 list option) fmap) b =
      SOME (csf,ctf,e,ent,ord,NONE,NONE) /\
  acts' = acts |+ (b,(csf,ctf,e,ent,ord,SOME (IntRet ir out),SOME out.vs_gas_readings)) /\
  FLOOKUP (blocks : (((num # num) list # num), basic_block # basic_block #
    instruction list # instruction list # instruction list # num list # venom_state #
    num # (venom_state # num) option # num # exec_result # bool # bytes32 list option) fmap)
    (b,d) = SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE) /\
  FLOOKUP blocks (a,e) =
    SOME (pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),pn,OK b0,F,NONE) /\
  blocks' = blocks |+
    ((b,d),(cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),
      LENGTH cys,IntRet ir out,T,SOME out.vs_gas_readings)) |+
    ((a,e),(pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),SUC pn,
      OK (post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
  (!key. FLOOKUP calls' key = NONE <=> FLOOKUP calls key = NONE) /\
  (!x f bb bt ps xs ys rho ini h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (x,f) =
      SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (x,f) = SOME ms /\ FLOOKUP es_tab (x,f) = SOME ess /\
    FLOOKUP ks_tab (x,f) = SOME ks ==>
    LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
    LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
    LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\ ALL_DISTINCT (FLAT ks) /\
    (!sf tf inc entry order res nrest.
      FLOOKUP acts x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      (!q. q < LENGTH xs ==>
        ((EL q xs).inst_opcode = GAS ==>
          EL q ms = [ALOOKUP obs (x,f,(EL q xs).inst_id)] /\
          EL q ess = [(sf.fn_name,(EL q xs).inst_id)] /\ EL q ks = [(x,f,(EL q xs).inst_id)]) /\
        ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
          EL q ms = [] /\ EL q ess = [] /\ EL q ks = []) /\
        ((EL q xs).inst_opcode = INVOKE ==>
          case FLOOKUP calls (x,f,(EL q xs).inst_id) of
            NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
          | SOME cl => EL q ms = AM ((f,(EL q xs).inst_id)::x) /\
            EL q ess = AE ((f,(EL q xs).inst_id)::x) /\
            EL q ks = AK ((f,(EL q xs).inst_id)::x))))) ==>
  (!x f bb bt ps xs ys rho ini h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks' (x,f) =
      SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (x,f) = SOME ms /\ FLOOKUP es_tab (x,f) = SOME ess /\
    FLOOKUP ks_tab (x,f) = SOME ks ==>
    LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
    LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
    LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\ ALL_DISTINCT (FLAT ks) /\
    (!sf tf inc entry order res nrest.
      FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      (!q. q < LENGTH xs ==>
        ((EL q xs).inst_opcode = GAS ==>
          EL q ms = [ALOOKUP obs (x,f,(EL q xs).inst_id)] /\
          EL q ess = [(sf.fn_name,(EL q xs).inst_id)] /\ EL q ks = [(x,f,(EL q xs).inst_id)]) /\
        ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
          EL q ms = [] /\ EL q ess = [] /\ EL q ks = []) /\
        ((EL q xs).inst_opcode = INVOKE ==>
          case FLOOKUP calls' (x,f,(EL q xs).inst_id) of
            NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
          | SOME cl => EL q ms = AM ((f,(EL q xs).inst_id)::x) /\
            EL q ess = AE ((f,(EL q xs).inst_id)::x) /\
            EL q ks = AK ((f,(EL q xs).inst_id)::x)))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP blocks' (x,f) =
    SOME (bb,bt,ps,xs,ys,sched,ini,h0,SOME (be,hbe),cnt,front,closed,brest)` >>
  `?n res cl rest. FLOOKUP blocks (x,f) =
    SOME (bb,bt,ps,xs,ys,sched,ini,h0,SOME (be,hbe),n,res,cl,rest)` by
    (qpat_x_assum `FLOOKUP blocks' (x,f) = _` mp_tac >>
     asm_rewrite_tac[FLOOKUP_UPDATE] >> Cases_on `(a,e) = (x,f)`
     >- gvs[] >>
     asm_rewrite_tac[] >> Cases_on `(b,d) = (x,f)`
     >- gvs[] >>
     asm_rewrite_tac[] >> strip_tac >> rpt (goal_assum $ drule_at Any)) >>
  qpat_x_assum `!x f bb bt ps xs ys rho ini h0 be hbe count front closed brest ms ess ks. _`
    (drule_all_then (map_every assume_tac o CONJUNCTS)) >>
  ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >> rpt gen_tac >> disch_tac >>
  drule_all_then strip_assume_tac dft_packet_return_old_act >>
  qpat_x_assum `!sf tf inc entry order res nrest. _` (drule_then assume_tac) >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!q. q < LENGTH xs ==> _` (drule_then strip_assume_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!key. FLOOKUP calls' key = NONE <=> _`
    (qspec_then `(x,f,(EL q xs).inst_id)` mp_tac) >>
  Cases_on `FLOOKUP calls (x,f,(EL q xs).inst_id)` >>
  Cases_on `FLOOKUP calls' (x,f,(EL q xs).inst_id)` >> gvs[]
QED

(* The only new replay eligibility is in the resumed row. The popped row
   already covered every INVOKE before its terminal instruction. *)
Theorem dft_packet_return_U_frame[local]:
  FLOOKUP (acts : ((num # num) list, ir_function # ir_function # num # venom_state #
    num list # exec_result option # bytes32 list option) fmap) b =
      SOME (csf,ctf,e,ent,ord,NONE,NONE) /\
  acts' = acts |+ (b,(csf,ctf,e,ent,ord,SOME (IntRet ir out),SOME out.vs_gas_readings)) /\
  FLOOKUP (blocks : (((num # num) list # num), basic_block # basic_block #
    instruction list # instruction list # instruction list # num list # venom_state #
    num # (venom_state # num) option # num # exec_result # bool # bytes32 list option) fmap)
    (b,d) = SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE) /\
  blocks' = blocks |+
    ((b,d),(cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),
      LENGTH cys,IntRet ir out,T,SOME out.vs_gas_readings)) |+
    ((a,e),(pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),SUC pn,
      OK (post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
  (!q. q < LENGTH cxs /\ (EL q cxs).inst_opcode = INVOKE ==> MEM q (TAKE cn crho)) /\
  FLOOKUP acts' a = SOME (parent_sf,ptf,pinc,pentry,porder,NONE,NONE) /\
  (!x f bb bt ps xs ys sched hin h0 be hbe n front closed brest
    ms ess ks sf tf inc entry order res nrest.
    FLOOKUP blocks (x,f) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),n,front,closed,brest) /\
    FLOOKUP ms_tab (x,f) = SOME ms /\ FLOOKUP es_tab (x,f) = SOME ess /\
    FLOOKUP ks_tab (x,f) = SOME ks /\ FLOOKUP acts x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    !F k kgss tail.
      N <= F /\ k <= LENGTH xs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE n sched)) /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
      (?extra. FLAT (TAKE k ess) =
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
      (!u. FOLDR (dft_exec_cons (F-f) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
        u.vs_gas_readings = tail /\
        trace_gas (trace_block x f (F-f) C7 sf
          (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
          (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss) /\
        (!tail'. FOLDR (dft_exec_cons (F-f) C7) OK (TAKE k xs)
            (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
          gas_events_block (F-f) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) /\
  (!ms ess ks.
    FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP es_tab (a,e) = SOME ess /\
    FLOOKUP ks_tab (a,e) = SOME ks ==>
    !F k kgss tail.
      N <= F /\ k <= LENGTH pxs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k pxs) /\
      (!q. q < k /\ (EL q pxs).inst_opcode = INVOKE ==> MEM q (TAKE (SUC pn) prho)) /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
      (?extra. FLAT (TAKE k ess) =
        gas_events_block (F-e) C7 parent_sf.fn_name
          <|bb_label := pbe.vs_current_bb; bb_instructions :=
            REPLICATE pbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k pxs|>
          (pbe with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
      (!u. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k pxs)
          (pbe with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        gas_events_block (F-e) C7 parent_sf.fn_name
          <|bb_label := pbe.vs_current_bb; bb_instructions :=
            REPLICATE pbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k pxs|>
          (pbe with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
        u.vs_gas_readings = tail /\
        trace_gas (trace_block a e (F-e) C7 parent_sf
          (pbb with bb_instructions := TAKE (LENGTH pps + k) pbb.bb_instructions)
          (pbe with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss) /\
        (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k pxs)
            (pbe with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
          gas_events_block (F-e) C7 parent_sf.fn_name
            <|bb_label := pbe.vs_current_bb; bb_instructions :=
              REPLICATE pbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k pxs|>
            (pbe with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) ==>
  !x f bb bt ps xs ys sched hin h0 be hbe n front closed brest
    ms ess ks sf tf inc entry order res nrest.
    FLOOKUP blocks' (x,f) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),n,front,closed,brest) /\
    FLOOKUP ms_tab (x,f) = SOME ms /\ FLOOKUP es_tab (x,f) = SOME ess /\
    FLOOKUP ks_tab (x,f) = SOME ks /\ FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    !F k kgss tail.
      N <= F /\ k <= LENGTH xs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE n sched)) /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
      (?extra. FLAT (TAKE k ess) =
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
      (!u. FOLDR (dft_exec_cons (F-f) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
        u.vs_gas_readings = tail /\
        trace_gas (trace_block x f (F-f) C7 sf
          (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
          (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss) /\
        (!tail'. FOLDR (dft_exec_cons (F-f) C7) OK (TAKE k xs)
            (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
          gas_events_block (F-f) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))
Proof
  disch_then (fn th => let val hs = CONJUNCTS th in
    map_every assume_tac hs >>
    mk_asm "off_parent" (MATCH_MP dft_packet_return_off_parent_U
      (LIST_CONJ (List.take (hs,5) @ [List.nth (hs,6)])))
    end) >>
  rpt gen_tac >> disch_then (fn th =>
    map_every assume_tac (CONJUNCTS th) >> mk_asm "lookups" th) >>
  Cases_on `(x,f) = (a,e)`
  >- (fs[pairTheory.PAIR_EQ] >>
      qpat_x_assum `FLOOKUP blocks' (a,e) = _` mp_tac >>
      asm_rewrite_tac[FLOOKUP_UPDATE] >> strip_tac >> gvs[] >>
      qpat_assum `!ms ess ks. FLOOKUP ms_tab _ = SOME ms /\ _ ==> _`
        (drule_all_then ACCEPT_TAC)) >>
  pop_assum (fn neq => asm "lookups" (fn lks =>
    asm "off_parent" (fn off => ACCEPT_TAC (MATCH_MP off (CONJ neq lks)))))
QED

(* Reflect cut eligibility away from the resumed parent. The updated terminal
   row is the only other changed key; all of its source INVOKEs were done
   before the return. *)
Theorem dft_packet_return_historical_eligibility[local]:
  FLOOKUP (blocks : (((num # num) list # num), basic_block # basic_block #
    instruction list # instruction list # instruction list # num list # venom_state #
    num # (venom_state # num) option # num # exec_result # bool # bytes32 list option) fmap)
    (b,d) = SOME (cbb,cbt,cps,cxs,cys,csched,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE) /\
  blocks' = blocks |+
    ((b,d),(cbb,cbt,cps,cxs,cys,csched,cin,ch0,SOME (cbe,chbe),
      LENGTH cys,IntRet ir out,T,SOME out.vs_gas_readings)) |+
    ((a,e),(pbb,pbt,pps,pxs,pys,psched,pin,ph0,SOME (pbe,phbe),SUC pn,
      OK (post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
  (!q. q < LENGTH cxs /\ (EL q cxs).inst_opcode = INVOKE ==> MEM q (TAKE cn csched)) /\
  (x,f) <> (a,e) /\
  FLOOKUP blocks' (x,f) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),n,front,closed,brest) /\
  q < LENGTH xs /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE n sched)) ==>
  ?on ofront oclosed orest.
    FLOOKUP blocks (x,f) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),on,ofront,oclosed,orest) /\
    (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE on sched))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac dft_packet_return_old_U_row >>
  goal_assum (drule_at Any) >>
  qpat_assum `!k. k <= LENGTH xs /\ _ ==> _` (qspec_then `q` mp_tac) >>
  simp[]
QED

(* The precall anchor is the zero-body cut, not a separately chosen visit. *)
Theorem dft_packet_return_anchor_eligibility[local]:
  (0:num) < LENGTH (xs:instruction list) ==>
  IS_SOME (SOME (be:venom_state,hbe:num)) /\ 0 < LENGTH xs /\
  DROP (phi_prefix_length bb.bb_instructions) ps =
    DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE 0 xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE 0 xs) /\
  (!r. r < 0 /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE cnt (sched:num list)))
Proof
  simp[]
QED

(* Package the historical transport with the original witnesses. Case
   projections in the old clause are normalized only at this boundary. *)
Theorem dft_packet_return_historical_witnesses[local]:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls:(gas_event, num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ms_tab:(((num # num) list # num),bytes32 option list list) fmap)
    (es_tab:(((num # num) list # num),(string # num) list list) fmap)
    (ks_tab:(((num # num) list # num),gas_event list list) fmap).
  b = (e,cid)::a /\
  FLOOKUP acts b = SOME (csf,ctf,e,ent,cord,NONE,NONE) /\
  FLOOKUP blocks (b,d) =
    SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE) /\
  FLOOKUP blocks (a,e) =
    SOME (pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),pn,OK b0,F,NONE) /\
  FLOOKUP calls (a,e,cid) = SOME (cq,call_h,b0,done,ent,NONE) /\
  acts' = acts |+ (b,(csf,ctf,e,ent,cord,SOME (IntRet ir out),SOME out.vs_gas_readings)) /\
  blocks' = blocks |+
    ((b,d),(cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),
      LENGTH cys,IntRet ir out,T,SOME out.vs_gas_readings)) |+
    ((a,e),(pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),SUC pn,
      OK (post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
  calls' = calls |+ ((a,e,cid),(cq,call_h,b0,done,ent,SOME (ir,out,post))) /\
  ms_tab' = ms_tab /\ es_tab' = es_tab /\ ks_tab' = ks_tab /\
  (?cuts levels Mcut Ecut Kcut mr er kr.
    MAP (\(ai,ds,ei,qi,zi). ai) cuts = REVERSE (GENLIST (\i. DROP i x) (SUC (LENGTH x))) /\
    LENGTH cuts = LENGTH levels /\
    (!i ai ds ei qi zi.
      i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
        ini hi bei counti fronti closedi resti later.
        FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
        FLOOKUP blocks (ai,ei) =
          SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
        orderi = ds ++ ei::later /\
        (if SUC i = LENGTH cuts then ai = x /\ ei = f /\ qi = q /\ zi = z
         else ?cid h b0 done child_entry ret.
           EL (SUC i) (MAP (\(aj,dj,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
           FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done,child_entry,ret) /\
           qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
           zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
           EVERY (\j. ~is_terminator j.inst_opcode) (TAKE qi xsi) /\
           (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done)) /\
        EL i levels =
          (sfi,MAP (\f. case THE (FLOOKUP blocks (ai,f)) of
              (bf,_,_,_,_,_,_,_,_,_,_,_,_) =>
                (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds ++
              [(bbi,ei,zi)], if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
    Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
    Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
    Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
    FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab ([],e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) = Mcut ++ mr /\
    FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab ([],e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) = Ecut ++ er /\
    FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) = Kcut ++ kr /\
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
        OK u => FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
          u.vs_gas_readings = tail /\
          (?before after.
            trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
              before ++ [((x,f,(EL (LENGTH z)
                (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
                EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
            trace_gas before = ZIP (Kcut,gs)) /\
          (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
            (Ecut,OK (u with vs_gas_readings := tail')))
        | stopped => run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
          gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
            FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))) ==>
  ?cuts levels Mcut Ecut Kcut mr er kr.
    MAP (\(ai,ds,ei,qi,zi). ai) cuts = REVERSE (GENLIST (\i. DROP i x) (SUC (LENGTH x))) /\
    LENGTH cuts = LENGTH levels /\
    (!i ai ds ei qi zi.
      i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
        ini hi bei counti fronti closedi resti later.
        FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
        FLOOKUP blocks' (ai,ei) =
          SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
        orderi = ds ++ ei::later /\
        (if SUC i = LENGTH cuts then ai = x /\ ei = f /\ qi = q /\ zi = z
         else ?cid h b0 done child_entry ret.
           EL (SUC i) (MAP (\(aj,dj,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
           FLOOKUP calls' (ai,ei,cid) = SOME (qi,h,b0,done,child_entry,ret) /\
           qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
           zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
           EVERY (\j. ~is_terminator j.inst_opcode) (TAKE qi xsi) /\
           (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done)) /\
        EL i levels =
          (sfi,MAP (\f. case THE (FLOOKUP blocks' (ai,f)) of
              (bf,_,_,_,_,_,_,_,_,_,_,_,_) =>
                (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds ++
              [(bbi,ei,zi)], if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
    Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab' (ai,ei))))) cuts) /\
    Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab' (ai,ei))))) cuts) /\
    Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab' (ai,ei))))) cuts) /\
    FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab' ([],e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Mcut ++ mr /\
    FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab' ([],e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Ecut ++ er /\
    FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab' ([],e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Kcut ++ kr /\
    LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
    (!F gs tail.
      N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
      levels_ok F C7 levels (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
        (MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts' ai) of
          (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts)
        root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
      (?extra. Ecut = FST (rooted_eval F C7 levels
        (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
      (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
        OK u => FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
          u.vs_gas_readings = tail /\
          (?before after.
            trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
              before ++ [((x,f,(EL (LENGTH z)
                (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
                EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
            trace_gas before = ZIP (Kcut,gs)) /\
          (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
            (Ecut,OK (u with vs_gas_readings := tail')))
        | stopped => run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
          gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
            FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?cuts levels Mcut Ecut Kcut mr er kr. _`
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS o
      BETA_RULE o PURE_REWRITE_RULE [pairTheory.pair_CASE_def])) >>
  qexistsl [`cuts`,`levels`,`Mcut`,`Ecut`,`Kcut`,`mr`,`er`,`kr`] >>
  pure_rewrite_tac [pairTheory.pair_CASE_def] >> BETA_TAC >>
  (* The historical transport leaves the depth argument opaque; its
     unconstrained zero was parsed as rational. Specialize that unused
     argument away and retain the literal natural root depth here. *)
  drule_all_then ACCEPT_TAC
    (BETA_RULE (PURE_REWRITE_RULE [pairTheory.pair_CASE_def]
      (Q.INST [`levels_ok` |->
         `\F C ls paths incoming fn ent rp (depth:rat).
            levels_ok_num F C ls paths incoming fn ent rp (0:num)`]
        (SPEC_ALL dft_packet_return_historical_cut_frame))))
QED

(* Some frame rules do not constrain every field of their map ranges. *)
val return_edge_mp = fn names => fn th => fn (asl,w) =>
  let
    val vars = free_varsl (w::asl)
    fun named name = List.find (fn v => fst (dest_var v) = name)
    fun at_goal_type (name,rule) =
      let
        val source = valOf (named name (free_vars (concl rule)))
        val target = valOf (named name vars)
      in
        INST_TYPE (match_type (type_of source) (type_of target)) rule
      end
  in
    mp_tac (List.foldl at_goal_type th names) (asl,w)
  end

(* Return updates the two adjacent cursors and the immutable call's return
   payload. Event arrays and observation history do not change on the pop. *)
Theorem dft_packet_return_edge_clauses:
  !(N:num) C7 C8 root_sf root_tf root_entry j obs
    (acts:((num # num) list,
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
    (ks_tab:(((num # num) list # num),gas_event list list) fmap).
  b = (e,cid)::a /\ stk = f::rest /\ LENGTH stk = LENGTH b /\
  f.cf_fn = tf /\ f.cf_state = b0 /\ f.cf_inst = c /\
  bind_outputs c.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state b0 out)) = SOME post /\
  active_inst tf next (post with vs_inst_idx := SUC b0.vs_inst_idx) /\
  MEM r.inst_opcode [RET;RETFMP;DRET] /\ step_inst fuel C8 r s = IntRet ir out /\
  FLOOKUP acts b = SOME (csf,ctf,e,ent,cord,NONE,NONE) /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
  LAST cord = d /\ LAST order = e /\
  FLOOKUP blocks (b,d) =
    SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE) /\
  FLOOKUP blocks (a,e) =
    SOME (pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),pn,OK b0,F,NONE) /\
  FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done,ent,NONE) /\
  r = EL cn cys /\ cn < LENGTH cys /\
  o1_ctx_shape C7 /\ o1_ctx_shape C8 /\ MEM root_tf C8.ctx_functions /\
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) = ((b,d,r.inst_id),ctf,r,s) /\
  obs = trace_gas (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry)) /\
  root_entry.vs_gas_readings = MAP SND obs ++ s.vs_gas_readings /\
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AE = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  raw_slots = AM [] /\ sites = AE [] /\ unused = s.vs_gas_readings /\
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
  ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT (AK []) /\
  LENGTH (AM []) = LENGTH (AK []) /\
  PERM (MAP (\(key,slot). (key,THE slot))
    (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],AM [])))) obs /\
  FDOM blocks = FDOM ms_tab /\ FDOM blocks = FDOM es_tab /\ FDOM blocks = FDOM ks_tab /\
  (?order. FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)) /\
  (!x sfx tfx aix ex ox rx ux.
    FLOOKUP acts x = SOME (sfx,tfx,aix,ex,ox,rx,ux) ==>
    MEM sfx C7.ctx_functions /\ tfx = dft_fn sfx /\ dft_fn_rel sfx tfx /\
    aix = (case x of [] => 0 | (v,id)::parent => v) /\
    ox <> [] /\ ox = GENLIST (\i. aix + SUC i) (LENGTH ox) /\
    (!v. MEM v ox <=> (x,v) IN FDOM blocks) /\
    (rx = NONE <=> ux = NONE) /\
    (rx = NONE <=> MEM x (GENLIST (\i. DROP i b) (SUC (LENGTH b)))) /\
    (!v id parent. x = (v,id)::parent ==>
      ?rq h u ds ret. FLOOKUP calls (parent,v,id) = SOME (rq,h,u,ds,ex,ret))) /\
  (!x v bb bt ps xs ys rho ini h0 body count front closed brest.
    FLOOKUP blocks (x,v) = SOME (bb,bt,ps,xs,ys,rho,ini,h0,body,count,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp.
      FLOOKUP acts x = SOME (sf,tf,inc,entry,order,res,nrest) /\
      MEM v order /\ v <= N /\ h0 <= j /\
      lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
      lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      lookup_block ini.vs_current_bb sf.fn_blocks = SOME bb /\
      bt.bb_label = bb.bb_label /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\i. is_pseudo i.inst_opcode) ps /\
      EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
      EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
      EVERY inst_shape_ok bb.bb_instructions /\ LENGTH xs = LENGTH ys /\
      PERM rho (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
        from_block [EL q xs] y) rho ys /\
      strict_dom_vars_defined sf ini /\ fn_reachable sf ini.vs_current_bb /\
      ctx_labels_bound C7 ini.vs_labels /\ ctx_labels_bound C8 ini.vs_labels /\
      eval_phis ini bt.bb_instructions = OK sp /\
      EL h0 (trace_blocks [] 0 N C8 root_tf root_entry) =
        ((x,v,(EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions).inst_id),tf,
          EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions,
          sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) /\
      (if v = SUC inc then ini = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc pu.
          FLOOKUP blocks (x,v-1) =
            SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK ini,T,SOME pu) /\
          ~ini.vs_halted) /\
      count <= LENGTH ys /\ (closed <=> IS_SOME brest) /\
      (case body of
        NONE => x = b /\ v = d /\ count = 0 /\ front = OK s /\
          FLOOKUP ms_tab (x,v) = SOME [] /\ FLOOKUP es_tab (x,v) = SOME [] /\
          FLOOKUP ks_tab (x,v) = SOME []
      | SOME (be,hbe) =>
          hbe <= j /\ be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
          dft_remaining_inv sf bb xs be /\
          EL hbe (trace_blocks [] 0 N C8 root_tf root_entry) = ((x,v,(HD ys).inst_id),tf,HD ys,be) /\
          FOLDR (dft_exec_cons (N-v) C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
            (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
          (!F. N <= F ==> FOLDR (dft_exec_cons (F-v) C8) OK (TAKE count ys) be = front) /\
          (closed ==> count = LENGTH ys /\ terminates front /\
            (!u. (front = OK u \/ (?r. front = IntRet r u)) ==>
              brest = SOME u.vs_gas_readings))) /\
      (v <> LAST order ==> closed /\ ?u. front = OK u /\ ~u.vs_halted) /\
      (v = LAST order ==> res = (if closed then SOME front else NONE) /\ nrest = brest)) /\
  (!x v id k t z done ent ret.
    FLOOKUP calls (x,v,id) = SOME (k,t,z,done,ent,ret) ==>
    ?sf tf inc inp order res nrest bb bt ps xs ys rho ini h0
     be hbe count front closed brest csf ctf cord cres crest c nm ops args.
      FLOOKUP acts x = SOME (sf,tf,inc,inp,order,res,nrest) /\
      FLOOKUP blocks (x,v) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) /\
      k < LENGTH xs /\ c = EL k xs /\ c.inst_id = id /\ c.inst_opcode = INVOKE /\
      t < j /\ EL t (trace_blocks [] 0 N C8 root_tf root_entry) = ((x,v,id),tf,c,z) /\
      LENGTH ps <= z.vs_inst_idx /\ get_instruction bt z.vs_inst_idx = SOME c /\
      (!F. N <= F ==> FOLDR (dft_exec_cons (F-v) C8) OK
        (TAKE (z.vs_inst_idx - LENGTH ps) ys) be = OK z) /\
      done = TAKE (z.vs_inst_idx - LENGTH ps) rho /\ ~MEM k done /\
      FLOOKUP acts ((v,id)::x) = SOME (csf,ctf,v,ent,cord,cres,crest) /\
      decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops z = SOME args /\ setup_callee ctf args z = SOME ent /\
      (case ret of
        NONE => cres = NONE /\ MEM ((v,id)::x) (GENLIST (\i. DROP i b) (SUC (LENGTH b)))
      | SOME (r,u,post) => cres = SOME (IntRet r u) /\
          bind_outputs c.inst_outputs r.iret_values
            (adopt_return_fmp r (merge_callee_state z u)) = SOME post /\
          t + SUC (LENGTH (trace_blocks ((v,id)::x) v (N-v) C8 ctf ent)) <= j /\
          MEM k (TAKE count rho))) /\
  (!k. k < LENGTH b ==>
    ?sf tf inc entry order q call_h b0 done child_entry v id x.
      x = DROP (SUC k) b /\ (v,id) = EL k b /\
      FLOOKUP acts x = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      FLOOKUP calls (x,v,id) = SOME (q,call_h,b0,done,child_entry,NONE) /\
      (EL k stk).cf_fn = tf /\ (EL k stk).cf_state = b0 /\
      (EL k stk).cf_inst.inst_id = id /\ (EL k stk).cf_inst.inst_opcode = INVOKE /\
      active_inst tf (EL k stk).cf_inst b0) /\
  (!k. k < LENGTH b ==>
    ?sf tf inc entry order bb bt ps xs ys rho ini h0 be hbe count
      q h b0 done child_entry id v x.
      x = DROP (SUC k) b /\ (v,id) = EL k b /\
      FLOOKUP acts x = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      LAST order = v /\
      FLOOKUP blocks (x,v) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
      FLOOKUP calls (x,v,id) = SOME (q,h,b0,done,child_entry,NONE) /\
      done = TAKE count rho /\ b0.vs_inst_idx = LENGTH ps + count /\
      get_instruction bt b0.vs_inst_idx = SOME (EL q xs)) /\
  (* Retained row array alignment and replay of earlier closed rows. *)
  (!x v bb bt ps xs ys rho ini h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (x,v) =
      SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (x,v) = SOME ms /\ FLOOKUP es_tab (x,v) = SOME ess /\
    FLOOKUP ks_tab (x,v) = SOME ks ==>
    LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
    LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
    LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\ ALL_DISTINCT (FLAT ks) /\
    (!sf tf inc entry order res nrest.
      FLOOKUP acts x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      (!q. q < LENGTH xs ==>
        ((EL q xs).inst_opcode = GAS ==>
          EL q ms = [ALOOKUP obs (x,v,(EL q xs).inst_id)] /\
          EL q ess = [(sf.fn_name,(EL q xs).inst_id)] /\ EL q ks = [(x,v,(EL q xs).inst_id)]) /\
        ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
          EL q ms = [] /\ EL q ess = [] /\ EL q ks = []) /\
        ((EL q xs).inst_opcode = INVOKE ==>
          case FLOOKUP calls (x,v,(EL q xs).inst_id) of
            NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
          | SOME cl => EL q ms = AM ((v,(EL q xs).inst_id)::x) /\
            EL q ess = AE ((v,(EL q xs).inst_id)::x) /\
            EL q ks = AK ((v,(EL q xs).inst_id)::x))))) /\
  (!x v sf tf inc entry order res nrest
      bb bt ps xs ys rho ini h0 be hbe count r8 u0 ms ess ks.
    FLOOKUP acts x = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (x,v) =
      SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,r8,T,SOME u0) /\
    FLOOKUP ms_tab (x,v) = SOME ms /\ FLOOKUP es_tab (x,v) = SOME ess /\
    FLOOKUP ks_tab (x,v) = SOME ks ==>
    terminates r8 /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ u0) be.vs_gas_readings /\
    (!u. (r8 = OK u \/ (?ir. r8 = IntRet ir u)) ==>
      EVERY IS_SOME (FLAT ms) /\ u0 = u.vs_gas_readings) /\
    (!F. N <= F ==>
      FOLDR (dft_exec_cons (F-v) C8) OK ys be = r8 /\
      (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
        (?extra. FLAT ess = gas_events_block (F-v) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?g. terminates (FOLDR (dft_exec_cons g C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) ==>
          terminates (FOLDR (dft_exec_cons (F-v) C7) OK xs
            (be with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (FOLDR (dft_exec_cons (F-v) C7) OK xs
              (be with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
          (((?u. r8 = OK u) \/ (?ir u. r8 = IntRet ir u)) ==>
            gas_events_block (F-v) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
            residual_result tail r8 (FOLDR (dft_exec_cons (F-v) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)))) /\
        (!u. (FOLDR (dft_exec_cons (F-v) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = OK u \/
              ?ir. FOLDR (dft_exec_cons (F-v) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = IntRet ir u) ==>
          trace_gas (trace_block x v (F-v) C7 sf
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs))))) /\
  (* Successful terminal row certificate. *)
  FLOOKUP ms_tab (b,d) = SOME cms /\ FLOOKUP es_tab (b,d) = SOME ces /\
  FLOOKUP ks_tab (b,d) = SOME cks /\
  PERM (MAP THE (FILTER IS_SOME (FLAT cms)) ++ out.vs_gas_readings) cbe.vs_gas_readings /\
  EVERY IS_SOME (FLAT cms) /\
  (!F. N <= F ==>
    FOLDR (dft_exec_cons (F-d) C8) OK cys cbe = IntRet ir out /\
    (!gs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT cms) gs ==>
      (?extra. FLAT ces = gas_events_block (F-d) C7 csf.fn_name
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
        gas_events_block (F-d) C7 csf.fn_name
          <|bb_label := cbe.vs_current_bb; bb_instructions :=
            REPLICATE cbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ cxs|>
          (cbe with vs_gas_readings := gs ++ tail) = FLAT ces /\
        residual_result tail (IntRet ir out) (FOLDR (dft_exec_cons (F-d) C7) OK cxs
          (cbe with vs_gas_readings := gs ++ tail))) /\
      (!v. (FOLDR (dft_exec_cons (F-d) C7) OK cxs
              (cbe with vs_gas_readings := gs ++ tail) = OK v \/
            ?ret. FOLDR (dft_exec_cons (F-d) C7) OK cxs
              (cbe with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
        trace_gas (trace_block b d (F-d) C7 csf
          <|bb_label := cbe.vs_current_bb; bb_instructions :=
            REPLICATE cbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ cxs|>
          (cbe with vs_gas_readings := gs ++ tail)) = ZIP (FLAT cks,gs)))) /\
  (!r. r < LENGTH cxs /\ (EL r cxs).inst_opcode = INVOKE ==>
    MEM r (TAKE cn crho) /\
    ?h b0 done entry ir out post.
      FLOOKUP calls (b,d,(EL r cxs).inst_id) =
        SOME (r,h,b0,done,entry,SOME (ir,out,post))) /\
  row_eval = (\F C owner (bb,e,z) s.
      case eval_phis s bb.bb_instructions of
        OK sp =>
         (gas_events_block (F-e) C owner
           (bb with bb_instructions :=
             TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
          FOLDR (dft_exec_cons (F-e) C) OK z
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
      | other => ([],other)) /\
    plan_eval = (\F C owner plan entry.
      FOLDL (\(es,r) row.
        case r of
          OK s => (es ++ FST (row_eval F C owner row s), SND (row_eval F C owner row s))
        | other => (es,other)) ([],OK entry) plan) /\
    call_setup = (\C c s.
      case decode_invoke c of
        NONE => Error "invoke: bad operand format"
      | SOME (nm,ops) =>
        case lookup_function nm C.ctx_functions of
          NONE => Error "invoke: function not found"
        | SOME callee =>
          case eval_operands ops s of
            NONE => Error "invoke: undefined argument"
          | SOME args =>
            case setup_callee callee args s of
              NONE => Error "invoke: empty function"
            | SOME cs => OK cs) /\
    rooted_eval = (\F C levels entry.
      FOLDL (\(prior,r) (sf,plan,call).
        case r of
          OK ent =>
           (prior ++ FST (plan_eval F C sf.fn_name plan ent),
            case SND (plan_eval F C sf.fn_name plan ent) of
              OK caller =>
                (case call of NONE => OK caller | SOME c => call_setup C c caller)
            | other => other)
        | other => (prior,other)) ([],OK entry) levels) /\
    plan_ok = (\F C sf a plan entry.
      plan <> [] /\
      MAP (\(bb,e,z). e) plan =
        GENLIST (\r. a + SUC r) (LENGTH plan) /\
      (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
        e <= F /\ MEM bb sf.fn_blocks /\
        (if SUC r < LENGTH plan then
          bb.bb_instructions <> [] /\
          EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
          is_terminator (LAST bb.bb_instructions).inst_opcode /\
          ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
          z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions
         else
          LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions)
            bb.bb_instructions) /\
          z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
            bb.bb_instructions) /\
          EVERY (\i. ~is_terminator i.inst_opcode) z)) /\
      (!r bb e z es s.
        r < LENGTH plan /\ EL r plan = (bb,e,z) /\
        plan_eval F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
        lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
        (0 < r ==> ~s.vs_halted))) /\
    levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
      levels <> [] /\ LENGTH paths = LENGTH levels /\
      LENGTH incoming = LENGTH levels /\
      HD paths = root_path /\ HD incoming = root_depth /\
      FST (HD levels) = root_fn /\
      (!i sf plan call.
        i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
        plan <> [] /\
        (!prior ent.
          rooted_eval F C (TAKE i levels) root_entry = (prior,OK ent) ==>
          plan_ok F C sf (EL i incoming) plan ent) /\
        (if SUC i < LENGTH levels then
          ?c nm ops bb e z.
            call = SOME c /\ LAST plan = (bb,e,z) /\
            c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
              bb.bb_instructions) /\
            c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
            lookup_function nm C.ctx_functions = SOME (FST (EL (SUC i) levels)) /\
            EL (SUC i) incoming = e /\
            EL (SUC i) paths = (e,c.inst_id)::EL i paths
         else call = NONE))) /\
  (!x f bb bt ps xs ys sched hin h0 be hbe n front closed brest
    ms ess ks sf tf inc entry order res nrest.
    FLOOKUP blocks (x,f) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),n,front,closed,brest) /\
    FLOOKUP ms_tab (x,f) = SOME ms /\ FLOOKUP es_tab (x,f) = SOME ess /\
    FLOOKUP ks_tab (x,f) = SOME ks /\ FLOOKUP acts x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    !F k kgss tail.
      N <= F /\ k <= LENGTH xs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE n sched)) /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
      (?extra. FLAT (TAKE k ess) =
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
      (!u. FOLDR (dft_exec_cons (F-f) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
        u.vs_gas_readings = tail /\
        trace_gas (trace_block x f (F-f) C7 sf
          (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
          (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss) /\
        (!tail'. FOLDR (dft_exec_cons (F-f) C7) OK (TAKE k xs)
            (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
          gas_events_block (F-f) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) /\
    (!a e cid q h b0 done_at_call child_entry ret
      bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms.
  FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms ==>
  (* Q remains for returned calls as well as suspended calls. *)
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
      setup_callee callee args b0)) /\
  (!a sf tf inc entry order r8 u0.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
    terminates r8 /\
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
          trace_gas (trace_blocks a inc (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK a,gs))))) /\
  (!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
      MEM q (TAKE count rho) ==>
      ?h b0 done_at_call child_entry ir child_out caller_post.
        FLOOKUP calls (a,e,(EL q xs).inst_id) =
          SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post))) /\
  (!a e q z sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
    ((IS_SOME body_entry /\ q < LENGTH xs /\
      z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
      (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
        MEM r (TAKE count rho))) \/
     (body_entry = NONE /\ a = b /\ e = d /\ q = 0 /\
      z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s.vs_inst_idx ps))) ==>
    ?cuts levels Mcut Ecut Kcut mr er kr.
      MAP (\(ai,ds,ei,qi,zi). ai) cuts =
        REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
      LENGTH cuts = LENGTH levels /\
      (!i ai ds ei qi zi.
        i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
        ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
          ini hi bei counti fronti closedi resti later.
          FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
          FLOOKUP blocks (ai,ei) =
            SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
          orderi = ds ++ ei::later /\
          (if SUC i = LENGTH cuts then ai = a /\ ei = e /\ qi = q /\ zi = z
           else ?cid h b0 done_at_call child_entry ret.
             EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
             FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
             qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
             zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
             EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
             (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
          EL i levels =
            (sfi, MAP (\f. case THE (FLOOKUP blocks (ai,f)) of
               (bf,_,_,_,_,_,_,_,_,_,_,_,_) =>
                 (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds ++
               [(bbi,ei,zi)],
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
        levels_ok F C7 levels
          (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
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
              trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
                before ++ [((a,e,(EL (LENGTH z)
                  (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
                  EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
              trace_gas before = ZIP (Kcut,gs)) /\
            (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
              (Ecut,OK (u with vs_gas_readings := tail'))) /\
            (body_entry = NONE ==> u with vs_gas_readings := s.vs_gas_readings = s) /\
            (a = b /\ e = d /\ IS_SOME body_entry /\
             inv_memory_observation r.inst_opcode /\ EL q xs = r ==>
              (!op. MEM op r.inst_operands ==> eval_operand op u = eval_operand op s) /\
              u.vs_initial_fmp = s.vs_initial_fmp)
        | stopped =>
            run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
            gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
              FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))) /\
  (* The final packet join supplies the selected-cut projection on the retained tables. *)
  (!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest q z cuts levels Mcut fuel gs tail events u.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    q < LENGTH xs /\ z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
    MAP (\(ai,ds,ei,qi,zi). ai) cuts =
      REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
    LENGTH cuts = LENGTH levels /\
    (!i ai ds ei qi zi.
      i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
        ini hi bei counti fronti closedi resti later.
        FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
        FLOOKUP blocks (ai,ei) =
          SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
        orderi = ds ++ ei::later /\
        (if SUC i = LENGTH cuts then
          ai = a /\ ei = e /\ qi = q /\ zi = z
        else
          ?cid call_h b0 done_at_call child_entry ret.
            EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
            FLOOKUP calls (ai,ei,cid) =
              SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
            qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
            zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
            EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
            (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
              MEM r done_at_call)) /\
        EL i levels =
          (sfi,
           MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
             DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
               (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
             [(bbi,ei,zi)],
           if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
    Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
    N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
    rooted_eval fuel C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
      (events,OK u) ==>
    ?kgss.
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
        (TAKE q (THE (FLOOKUP ms_tab (a,e)))) kgss /\
      FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u) ==>
  ?acts' blocks' calls' ms_tab' es_tab' ks_tab' packet' raw_slots' sites' unused'.
    acts' = acts |+ (b,(csf,ctf,e,ent,cord,SOME (IntRet ir out),SOME out.vs_gas_readings)) /\
    blocks' = blocks |+
      ((b,d),(cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),
        LENGTH cys,IntRet ir out,T,SOME out.vs_gas_readings)) |+
      ((a,e),(pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),SUC pn,
        OK (post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
    calls' = calls |+ ((a,e,cid),(q,call_h,b0,done,ent,SOME (ir,out,post))) /\
    ms_tab' = ms_tab /\ es_tab' = es_tab /\ ks_tab' = ks_tab /\
    packet' = (SUC j,obs) /\ raw_slots' = AM [] /\ sites' = AE [] /\
    unused' = (post with vs_inst_idx := SUC b0.vs_inst_idx).vs_gas_readings /\
    LENGTH raw_slots' = LENGTH sites' /\
    PERM (MAP THE (FILTER IS_SOME raw_slots') ++ unused') (gas_readings es0) /\
    SUC j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
    EL (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) =
      ((a,e,next.inst_id),tf,next,post with vs_inst_idx := SUC b0.vs_inst_idx) /\
    trace_gas (TAKE (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry)) = obs /\
    root_entry.vs_gas_readings = MAP SND obs ++ unused' /\
    FDOM blocks' = FDOM ms_tab' /\ FDOM blocks' = FDOM es_tab' /\ FDOM blocks' = FDOM ks_tab' /\
    (!x. AM x = FLAT (MAP (\v. FLAT (THE (FLOOKUP ms_tab' (x,v))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' x))))))))) /\
    (!x. AE x = FLAT (MAP (\v. FLAT (THE (FLOOKUP es_tab' (x,v))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' x))))))))) /\
    (!x. AK x = FLAT (MAP (\v. FLAT (THE (FLOOKUP ks_tab' (x,v))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' x))))))))) /\
    (?order. FLOOKUP acts' [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)) /\
    FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
    FLOOKUP blocks' (a,e) =
      SOME (pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),SUC pn,
        OK (post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE) /\
    lookup_block post.vs_current_bb tf.fn_blocks = SOME pbt /\
    get_instruction pbt (SUC b0.vs_inst_idx) = SOME next /\
    SUC b0.vs_inst_idx = LENGTH pps + SUC pn /\
    SUC pn < LENGTH pys /\ next = EL (SUC pn) pys /\
    LENGTH rest = LENGTH a /\
  (!k. k < LENGTH a ==>
    ?sf tf inc entry order q call_h b0 done child_entry v id x.
      x = DROP (SUC k) a /\ (v,id) = EL k a /\
      FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      FLOOKUP calls' (x,v,id) = SOME (q,call_h,b0,done,child_entry,NONE) /\
      (EL k rest).cf_fn = tf /\ (EL k rest).cf_state = b0 /\
      (EL k rest).cf_inst.inst_id = id /\ (EL k rest).cf_inst.inst_opcode = INVOKE /\
      active_inst tf (EL k rest).cf_inst b0) /\
  (!k. k < LENGTH a ==>
    ?sf tf inc entry order bb bt ps xs ys rho ini h0 be hbe count
      q h b0 done child_entry id v x.
      x = DROP (SUC k) a /\ (v,id) = EL k a /\
      FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      LAST order = v /\
      FLOOKUP blocks' (x,v) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
      FLOOKUP calls' (x,v,id) = SOME (q,h,b0,done,child_entry,NONE) /\
      done = TAKE count rho /\ b0.vs_inst_idx = LENGTH ps + count /\
      get_instruction bt b0.vs_inst_idx = SOME (EL q xs)) /\
  (!x sf tf inc entry order res nrest.
    FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    MEM sf C7.ctx_functions /\ tf = dft_fn sf /\ dft_fn_rel sf tf /\
    inc = (case x of [] => 0 | (e,cid)::parent => e) /\
    order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
    (!v. MEM v order <=> (x,v) IN FDOM blocks') /\
    (res = NONE <=> nrest = NONE) /\
    (res = NONE <=> MEM x (GENLIST (\i. DROP i a) (SUC (LENGTH a)))) /\
    (!v id parent. x = (v,id)::parent ==>
      ?q h s done ret. FLOOKUP calls' (parent,v,id) = SOME (q,h,s,done,entry,ret))) /\
  (!x v bb bt ps xs ys rho ini h0 body count front closed brest.
    FLOOKUP blocks' (x,v) = SOME (bb,bt,ps,xs,ys,rho,ini,h0,body,count,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp.
      FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) /\
      MEM v order /\ v <= N /\ h0 <= SUC j /\
      lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
      lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      lookup_block ini.vs_current_bb sf.fn_blocks = SOME bb /\
      bt.bb_label = bb.bb_label /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\i. is_pseudo i.inst_opcode) ps /\
      EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
      EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
      EVERY inst_shape_ok bb.bb_instructions /\ LENGTH xs = LENGTH ys /\
      PERM rho (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
        from_block [EL q xs] y) rho ys /\
      strict_dom_vars_defined sf ini /\ fn_reachable sf ini.vs_current_bb /\
      ctx_labels_bound C7 ini.vs_labels /\ ctx_labels_bound C8 ini.vs_labels /\
      eval_phis ini bt.bb_instructions = OK sp /\
      EL h0 (trace_blocks [] 0 N C8 root_tf root_entry) =
        ((x,v,(EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions).inst_id),tf,
          EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions,
          sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) /\
      (if v = SUC inc then ini = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc pu.
          FLOOKUP blocks' (x,v-1) =
            SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK ini,T,SOME pu) /\
          ~ini.vs_halted) /\
      count <= LENGTH ys /\ (closed <=> IS_SOME brest) /\
      (?be hbe. body = SOME (be,hbe)) /\
      (case body of NONE => F
       | SOME (be,hbe) =>
          hbe <= SUC j /\ be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
          dft_remaining_inv sf bb xs be /\
          EL hbe (trace_blocks [] 0 N C8 root_tf root_entry) = ((x,v,(HD ys).inst_id),tf,HD ys,be) /\
          FOLDR (dft_exec_cons (N-v) C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
            (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
          (!F. N <= F ==> FOLDR (dft_exec_cons (F-v) C8) OK (TAKE count ys) be = front) /\
          (closed ==> count = LENGTH ys /\ terminates front /\
            (!u. (front = OK u \/ (?r. front = IntRet r u)) ==>
              brest = SOME u.vs_gas_readings))) /\
      (v <> LAST order ==> closed /\ ?u. front = OK u /\ ~u.vs_halted) /\
      (v = LAST order ==> res = (if closed then SOME front else NONE) /\ nrest = brest)) /\
  (!x v id k t z done entry ret.
    FLOOKUP calls' (x,v,id) = SOME (k,t,z,done,entry,ret) ==>
    ?sf tf inc inp order res nrest bb bt ps xs ys rho ini h0
     be hbe count front closed brest csf ctf cord cres crest c nm ops args.
      FLOOKUP acts' x = SOME (sf,tf,inc,inp,order,res,nrest) /\
      FLOOKUP blocks' (x,v) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) /\
      k < LENGTH xs /\ c = EL k xs /\ c.inst_id = id /\ c.inst_opcode = INVOKE /\
      t < SUC j /\ EL t (trace_blocks [] 0 N C8 root_tf root_entry) = ((x,v,id),tf,c,z) /\
      LENGTH ps <= z.vs_inst_idx /\ get_instruction bt z.vs_inst_idx = SOME c /\
      (!F. N <= F ==> FOLDR (dft_exec_cons (F-v) C8) OK
        (TAKE (z.vs_inst_idx - LENGTH ps) ys) be = OK z) /\
      done = TAKE (z.vs_inst_idx - LENGTH ps) rho /\ ~MEM k done /\
      FLOOKUP acts' ((v,id)::x) = SOME (csf,ctf,v,entry,cord,cres,crest) /\
      decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops z = SOME args /\ setup_callee ctf args z = SOME entry /\
      (case ret of
        NONE => cres = NONE /\ MEM ((v,id)::x) (GENLIST (\i. DROP i a) (SUC (LENGTH a)))
      | SOME (r,u,post) => cres = SOME (IntRet r u) /\
          bind_outputs c.inst_outputs r.iret_values
            (adopt_return_fmp r (merge_callee_state z u)) = SOME post /\
          t + SUC (LENGTH (trace_blocks ((v,id)::x) v (N-v) C8 ctf entry)) <= SUC j /\
          MEM k (TAKE count rho))) /\
  (!x f bb bt ps xs ys rho ini h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks' (x,f) =
      SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (x,f) = SOME ms /\ FLOOKUP es_tab (x,f) = SOME ess /\
    FLOOKUP ks_tab (x,f) = SOME ks ==>
    LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
    LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
    LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\ ALL_DISTINCT (FLAT ks) /\
    (!sf tf inc entry order res nrest.
      FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      (!q. q < LENGTH xs ==>
        ((EL q xs).inst_opcode = GAS ==>
          EL q ms = [ALOOKUP obs (x,f,(EL q xs).inst_id)] /\
          EL q ess = [(sf.fn_name,(EL q xs).inst_id)] /\ EL q ks = [(x,f,(EL q xs).inst_id)]) /\
        ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
          EL q ms = [] /\ EL q ess = [] /\ EL q ks = []) /\
        ((EL q xs).inst_opcode = INVOKE ==>
          case FLOOKUP calls' (x,f,(EL q xs).inst_id) of
            NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
          | SOME cl => EL q ms = AM ((f,(EL q xs).inst_id)::x) /\
            EL q ess = AE ((f,(EL q xs).inst_id)::x) /\
            EL q ks = AK ((f,(EL q xs).inst_id)::x))))) /\
  (!a e cid q h b done entry ret
      bb bt ps xs ys sched in_state bh be hbe count front closed brest ms.
    FLOOKUP calls' (a,e,cid) = SOME(q,h,b,done,entry,ret) /\
    FLOOKUP blocks' (a,e) =
      SOME(bb,bt,ps,xs,ys,sched,in_state,bh,SOME(be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab' (a,e) = SOME ms ==>
    !F kgss tail u.
      N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b) /\
      (!callee args. setup_callee callee args (u with vs_gas_readings := b.vs_gas_readings) =
        setup_callee callee args b)) /\
  (!a e bb bt ps xs ys sched in_state h0 be hbe count front closed brest.
    FLOOKUP blocks' (a,e) =
      SOME(bb,bt,ps,xs,ys,sched,in_state,h0,SOME(be,hbe),count,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
      MEM q (TAKE count sched) ==>
      ?h b0 done entry ir out post.
        FLOOKUP calls' (a,e,(EL q xs).inst_id) =
          SOME(q,h,b0,done,entry,SOME(ir,out,post))) /\
  (!x sf tf inc entry order r8 u0.
    FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
    terminates r8 /\
    LENGTH (AM x) = LENGTH (AE x) /\ LENGTH (AM x) = LENGTH (AK x) /\
    PERM (MAP THE (FILTER IS_SOME (AM x)) ++ u0) entry.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (AM x) /\ u0 = v.vs_gas_readings) /\
    (!F. N <= F ==>
      run_blocks (F-inc) C8 tf entry = r8 /\
      (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM x) gs ==>
        (?extra. AE x = gas_events_blocks (F-inc) C7 sf
          (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (run_blocks f C7 sf (entry with vs_gas_readings := gs ++ tail))) ==>
          terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel (restore_result [] (run_blocks (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = AE x /\
            residual_result tail r8
              (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)))) /\
        (!v. (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = OK v \/
          ?ir. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          trace_gas (trace_blocks x inc (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK x,gs))))) /\
  (!x f bb bt ps xs ys sched hin h0 be hbe n front closed brest
    ms ess ks sf tf inc entry order res nrest.
    FLOOKUP blocks' (x,f) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),n,front,closed,brest) /\
    FLOOKUP ms_tab (x,f) = SOME ms /\ FLOOKUP es_tab (x,f) = SOME ess /\
    FLOOKUP ks_tab (x,f) = SOME ks /\ FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    !F k kgss tail.
      N <= F /\ k <= LENGTH xs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE n sched)) /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
      (?extra. FLAT (TAKE k ess) =
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
      (!u. FOLDR (dft_exec_cons (F-f) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
        u.vs_gas_readings = tail /\
        trace_gas (trace_block x f (F-f) C7 sf
          (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
          (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss) /\
        (!tail'. FOLDR (dft_exec_cons (F-f) C7) OK (TAKE k xs)
            (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
          gas_events_block (F-f) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) /\
  (!x v sf tf inc entry order res nrest
      bb bt ps xs ys rho ini h0 be hbe count r8 u0 ms ess ks.
    FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks' (x,v) =
      SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,r8,T,SOME u0) /\
    FLOOKUP ms_tab (x,v) = SOME ms /\ FLOOKUP es_tab (x,v) = SOME ess /\
    FLOOKUP ks_tab (x,v) = SOME ks ==>
    terminates r8 /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ u0) be.vs_gas_readings /\
    (!u. (r8 = OK u \/ (?ir. r8 = IntRet ir u)) ==>
      EVERY IS_SOME (FLAT ms) /\ u0 = u.vs_gas_readings) /\
    (!F. N <= F ==>
      FOLDR (dft_exec_cons (F-v) C8) OK ys be = r8 /\
      (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
        (?extra. FLAT ess = gas_events_block (F-v) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?g. terminates (FOLDR (dft_exec_cons g C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) ==>
          terminates (FOLDR (dft_exec_cons (F-v) C7) OK xs
            (be with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (FOLDR (dft_exec_cons (F-v) C7) OK xs
              (be with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
          (((?u. r8 = OK u) \/ (?ir u. r8 = IntRet ir u)) ==>
            gas_events_block (F-v) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
            residual_result tail r8 (FOLDR (dft_exec_cons (F-v) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)))) /\
        (!u. (FOLDR (dft_exec_cons (F-v) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = OK u \/
              ?ir. FOLDR (dft_exec_cons (F-v) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = IntRet ir u) ==>
          trace_gas (trace_block x v (F-v) C7 sf
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs))))) /\
  (!x f sf tf inc entry order res nrest bb bt ps xs ys rho hin h0 be hbe
      count front closed brest q z.
    FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks' (x,f) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    q < LENGTH xs /\ z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
    (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) ==>
    ?cuts levels Mcut Ecut Kcut mr er kr.
      MAP (\(ai,ds,ei,qi,zi). ai) cuts = REVERSE (GENLIST (\i. DROP i x) (SUC (LENGTH x))) /\
      LENGTH cuts = LENGTH levels /\
      (!i ai ds ei qi zi.
        i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
        ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
          ini hi bei counti fronti closedi resti later.
          FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
          FLOOKUP blocks' (ai,ei) =
            SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
          orderi = ds ++ ei::later /\
          (if SUC i = LENGTH cuts then ai = x /\ ei = f /\ qi = q /\ zi = z
           else ?cid h b0 done child_entry ret.
             EL (SUC i) (MAP (\(aj,dj,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
             FLOOKUP calls' (ai,ei,cid) = SOME (qi,h,b0,done,child_entry,ret) /\
             qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
             zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
             EVERY (\j. ~is_terminator j.inst_opcode) (TAKE qi xsi) /\
             (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done)) /\
          EL i levels =
            (sfi,MAP (\f. case THE (FLOOKUP blocks' (ai,f)) of
                (bf,_,_,_,_,_,_,_,_,_,_,_,_) =>
                  (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds ++
                [(bbi,ei,zi)], if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
      Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
        FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP ms_tab' (ai,ei))))) cuts) /\
      Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
        FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP es_tab' (ai,ei))))) cuts) /\
      Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
        FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP ks_tab' (ai,ei))))) cuts) /\
      FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab' ([],e))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Mcut ++ mr /\
      FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab' ([],e))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Ecut ++ er /\
      FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab' ([],e))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Kcut ++ kr /\
      LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
      (!F gs tail.
        N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
        levels_ok F C7 levels (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
          (MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts' ai) of
            (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts)
          root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
        (?extra. Ecut = FST (rooted_eval F C7 levels
          (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
        (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
          OK u => FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
            u.vs_gas_readings = tail /\
            (?before after.
              trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
                before ++ [((x,f,(EL (LENGTH z)
                  (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
                  EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
              trace_gas before = ZIP (Kcut,gs)) /\
            (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
              (Ecut,OK (u with vs_gas_readings := tail'))) /\
            (x = a /\ f = e /\ inv_memory_observation next.inst_opcode /\ EL q xs = next ==>
              (!op. MEM op next.inst_operands ==>
                eval_operand op u = eval_operand op (post with vs_inst_idx := SUC b0.vs_inst_idx)) /\
              u.vs_initial_fmp = (post with vs_inst_idx := SUC b0.vs_inst_idx).vs_initial_fmp)
          | stopped => run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
            gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
              FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)))))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  map_every (fn pat => qpat_assum pat (fn act =>
    qpat_assum `!x sfx tfx aix ex ox rx ux.
           FLOOKUP acts x = SOME (sfx,tfx,aix,ex,ox,rx,ux) ==> _`
      (map_every assume_tac o CONJUNCTS o (C MATCH_MP act))))
    [`FLOOKUP acts b = SOME _`, `FLOOKUP acts a = SOME _`] >>
  `MEM ctf C8.ctx_functions /\ MEM tf C8.ctx_functions` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`MEM csf C7.ctx_functions`, `MEM sf C7.ctx_functions`,
       `ctf = dft_fn csf`, `tf = dft_fn sf`] >>
     qpat_assum `LIST_REL (\f g. g = dft_fn f) _ _`
      (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] LIST_REL_MEM_IMP)) >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  `wf_function csf /\ wf_function ctf /\ wf_function tf` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`MEM csf C7.ctx_functions`, `MEM ctf C8.ctx_functions`, `MEM tf C8.ctx_functions`,
        `o1_ctx_shape C7`, `o1_ctx_shape C8`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[o1_ctx_shape_wf_functions, EVERY_MEM]) >>
  qpat_assum `FLOOKUP acts a = SOME _` (fn act =>
    qpat_assum `!x v bb bt ps xs ys rho ini h0 body count front closed brest.
      FLOOKUP blocks (x,v) = _ ==> _`
      (fn visit => qpat_assum `FLOOKUP blocks (a,e) = SOME _`
        (strip_assume_tac o SRULE [act] o MATCH_MP visit))) >>
  qpat_assum `FLOOKUP acts a = SOME _` (fn act =>
    qpat_assum `FLOOKUP acts b = SOME _` (fn child =>
      qpat_assum `b = (e,cid)::a` (fn path =>
        qpat_assum `FLOOKUP blocks (a,e) = SOME _` (fn row =>
          qpat_assum `!x v id k t z done ent ret. FLOOKUP calls (x,v,id) = _ ==> _`
            (fn call => qpat_assum `FLOOKUP calls (a,e,cid) = SOME _`
              (strip_assume_tac o SRULE [GSYM path,act,child,row] o MATCH_MP call)))))) >>
  qpat_assum `b = (e,cid)::a` (fn path =>
    qpat_assum `stk = f::rest` (fn stack =>
    qpat_assum `f.cf_fn = tf` (fn fn_eq =>
    qpat_assum `f.cf_state = b0` (fn state_eq =>
    qpat_assum `f.cf_inst = c` (fn inst_eq =>
    qpat_assum `!k. k < LENGTH b ==>
      ?sf tf inc entry order q h z ds ent v id x.
        _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ active_inst tf (EL k stk).cf_inst z`
      (qspec_then `0` (strip_assume_tac o SRULE
        [path,stack,fn_eq,state_eq,inst_eq,SF CONJ_ss]))))))) >>
  qpat_assum `b = (e,cid)::a` (fn path =>
    qpat_assum `FLOOKUP blocks (a,e) = SOME _` (fn row =>
    qpat_assum `FLOOKUP calls (a,e,cid) = SOME _` (fn call =>
    qpat_assum `!k. k < LENGTH b ==>
      ?sf tf inc entry order bb bt ps xs ys rho ini h0 be hbe count q h z ds ent id v x.
        _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ get_instruction bt z.vs_inst_idx = SOME (EL q xs)`
      (qspec_then `0` (strip_assume_tac o SRULE [path,row,call,SF CONJ_ss]))))) >>
  `!v. MEM v cord <=> (b,v) IN FDOM blocks` by
    (qpat_assum `FLOOKUP acts b = SOME _` (fn act =>
      qpat_assum `!x sfx tfx aix ex ox rx ux.
           FLOOKUP acts x = SOME (sfx,tfx,aix,ex,ox,rx,ux) ==> _`
        (ACCEPT_TAC o List.nth o (fn hs => (hs,6)) o CONJUNCTS o (fn th => MATCH_MP th act)))) >>
  qpat_assum `FLOOKUP acts b = SOME _`
    (mp_then Any (Q.ISPECL_THEN [`d`,`blocks`,`N`,`C8`] mp_tac)
      dft_packet_return_child_visits) >>
  CONV_TAC (LAND_CONV (QUANT_CONV ANTE_CONJ_CONV THENC FORALL_IMP_CONV)) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> disch_then (fn row =>
       qpat_assum `!x v bb bt ps xs ys rho ini h0 body count front closed brest.
         FLOOKUP blocks (x,v) = _ ==> _`
         (strip_assume_tac o (C MATCH_MP row))) >>
     rpt (goal_assum $ drule_at Any) >>
     rename1 `(body0 = NONE ==> _) /\ _` >>
     namedCases_on `body0` ["","bp"] >-
       (qpat_x_assum `(case NONE of NONE => _ | SOME _ => _)` mp_tac >>
        simp[NoAsms]) >>
     PairCases_on `bp` >>
     qpat_x_assum `(case SOME _ of NONE => _ | SOME _ => _)` mp_tac >>
     simp[NoAsms])) >>
  disch_then assume_tac >>
  `c = EL q pxs /\ bb_well_formed pbt /\
   lookup_block b0.vs_current_bb tf.fn_blocks = SOME pbt` by
    (drule_all wf_active_lookup >> strip_tac >>
     rename1 `lookup_block b0.vs_current_bb tf.fn_blocks = SOME active_bb` >>
     `MEM pbt tf.fn_blocks /\ MEM active_bb tf.fn_blocks` by
       (conj_tac >> first_assum (ACCEPT_TAC o MATCH_MP lookup_block_MEM)) >>
     `MEM (EL q pxs) pbt.bb_instructions /\ MEM c active_bb.bb_instructions` by
       (conj_tac >|
          [qpat_assum `get_instruction pbt b0.vs_inst_idx = SOME (EL q pxs)` mp_tac,
           qpat_assum `get_instruction active_bb b0.vs_inst_idx = SOME c` mp_tac] >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[get_instruction_def, AllCaseEqs(), MEM_EL] >> metis_tac[]) >>
     `c = EL q pxs` by
       (qspecl_then [`tf`,`c`,`EL q pxs`] mp_tac fn_insts_id_unique >>
        impl_tac >- (rpt conj_tac
        >- (qpat_assum `wf_function tf` mp_tac >> simp[NoAsms,wf_function_def])
        >- (irule MEM_fn_insts >> qexists_tac `active_bb` >> simp[])
        >- (irule MEM_fn_insts >> qexists_tac `pbt` >> simp[])
        >> simp[]) >> simp[]) >>
     `active_bb = pbt` by
       (qspecl_then [`tf`,`active_bb`,`pbt`,`c`] mp_tac inst_in_unique_block >>
        impl_tac >-
          (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
             qpat_assum `wf_function tf` (ACCEPT_TAC o cj 5 o REWRITE_RULE [wf_function_def]),
             qpat_assum `c = EL q pxs` (fn eq => PURE_REWRITE_TAC [eq] >> first_assum ACCEPT_TAC)]) >>
        simp[]) >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (qspecl_then [`tf`,`pbt`] mp_tac wf_function_bb_well_formed >>
         impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> simp[])
     >> qpat_assum `active_bb = pbt` (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `c = EL q pxs` (fn eq =>
    map_every (fn pat => qpat_assum pat (assume_tac o REWRITE_RULE [GSYM eq]))
      [`get_instruction pbt b0.vs_inst_idx = SOME (EL q pxs)`,
       `decode_invoke (EL q pxs) = SOME _`,
       `EL call_h (trace_blocks [] 0 N C8 root_tf root_entry) = ((a,e,cid),tf,EL q pxs,b0)`]) >>
  `AM b = FLAT (MAP (\v. FLAT (THE (FLOOKUP ms_tab (b,v)))) cord) /\
   AE b = FLAT (MAP (\v. FLAT (THE (FLOOKUP es_tab (b,v)))) cord) /\
   AK b = FLAT (MAP (\v. FLAT (THE (FLOOKUP ks_tab (b,v)))) cord)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`AM = _`,`AE = _`,`AK = _`,`FLOOKUP acts b = SOME _`] >> simp[NoAsms]) >>
  mp_tac (Q.INST [`order` |-> `cord`] (SPEC_ALL dft_packet_return_native_tables)) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[NoAsms]
     >- (map_every qx_gen_tac [`v`,`bb`,`bt`,`ps`,`xs`,`ys`,`sched`,`ini`,`h0`,
           `be`,`hbe`,`n`,`front`,`closed`,`brest`,`ms`,`es`,`ks`] >>
         disch_then (map_every assume_tac o CONJUNCTS) >>
         qpat_assum `!x v bb bt ps xs ys rho ini h0 be hbe count front closed brest ms ess ks.
           _ ==> LENGTH ms = _ /\ _`
           (qspecl_then [`b`,`v`,`bb`,`bt`,`ps`,`xs`,`ys`,`sched`,`ini`,`h0`,
              `be`,`hbe`,`n`,`front`,`closed`,`brest`,`ms`,`es`,`ks`] mp_tac) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[NoAsms])
     >- (map_every qx_gen_tac [`v`,`bb`,`bt`,`ps`,`xs`,`ys`,`sched`,`ini`,`h0`,
           `be`,`hbe`,`n`,`front`,`u0`,`ms`,`es`,`ks`] >>
         disch_then (map_every assume_tac o CONJUNCTS) >>
         qpat_assum `!x v sf tf inc entry order res nrest bb bt ps xs ys rho ini h0 be hbe
           count front u0 ms ess ks. _ ==> terminates front /\ _`
           (qspecl_then [`b`,`v`,`csf`,`ctf`,`e`,`ent`,`cord`,`NONE`,`NONE`,
             `bb`,`bt`,`ps`,`xs`,`ys`,`sched`,`ini`,`h0`,`be`,`hbe`,`n`,`front`,
             `u0`,`ms`,`es`,`ks`] mp_tac) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[NoAsms])
     >> qpat_assum `!F. N <= F ==> FOLDR _ OK cys cbe = IntRet ir out /\ _` mp_tac >>
     simp[NoAsms]) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `a <> b /\ [] <> b` by
    (qpat_assum `b = (e,cid)::a` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[] >> strip_tac >>
     pop_assum (mp_tac o AP_TERM ``LENGTH : (num # num) list -> num``) >> simp[]) >>
  `FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,NONE,NONE)` by
    (qpat_assum `!x. x <> b ==> FLOOKUP acts' x = FLOOKUP acts x`
       (qspec_then `a` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `?order. FLOOKUP acts' [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)` by
    (qpat_assum `!x. x <> b ==> FLOOKUP acts' x = FLOOKUP acts x`
       (qspec_then `[]` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  return_edge_mp ["acts","blocks","calls"]
    (Q.INST [`p` |-> `b`] (SPEC_ALL dft_packet_return_live_frames)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x. AM x = FLAT (MAP (\v. FLAT (THE (FLOOKUP ms_tab' (x,v))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' x))))))))` by
    (map_every (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC [th]))
       [`ms_tab' = ms_tab`,`!x. FST (SND (SND (SND (SND (THE (FLOOKUP acts' x)))))) = _`,
        `AM = _`] >> BETA_TAC >> simp[NoAsms]) >>
  `!x. AE x = FLAT (MAP (\v. FLAT (THE (FLOOKUP es_tab' (x,v))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' x))))))))` by
    (map_every (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC [th]))
       [`es_tab' = es_tab`,`!x. FST (SND (SND (SND (SND (THE (FLOOKUP acts' x)))))) = _`,
        `AE = _`] >> BETA_TAC >> simp[NoAsms]) >>
  `!x. AK x = FLAT (MAP (\v. FLAT (THE (FLOOKUP ks_tab' (x,v))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' x))))))))` by
    (map_every (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC [th]))
       [`ks_tab' = ks_tab`,`!x. FST (SND (SND (SND (SND (THE (FLOOKUP acts' x)))))) = _`,
        `AK = _`] >> BETA_TAC >> simp[NoAsms]) >>
  `!key. FLOOKUP calls' key = NONE <=> FLOOKUP calls key = NONE` by
    (qpat_assum `calls' = _` (fn updated =>
       qpat_assum `FLOOKUP calls (a,e,cid) = SOME _` (fn old =>
         ACCEPT_TAC (MATCH_MP dft_packet_return_row_call_domain (CONJ updated old))))) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) pxs)` by
    (qspecl_then [`sf`,`pbb`] mp_tac venomFnInstsProofsTheory.fn_inst_ids_block_distinct >>
     impl_tac >-
      (conj_tac
       >- (qpat_assum `o1_ctx_shape C7`
             (mp_tac o REWRITE_RULE [EVERY_MEM] o MATCH_MP o1_ctx_shape_wf_functions) >>
           disch_then (qspec_then `sf` mp_tac) >>
           qpat_assum `MEM sf C7.ctx_functions` (fn th => simp[NoAsms,th,wf_function_def]))
       >> first_assum (ACCEPT_TAC o MATCH_MP lookup_block_MEM)) >>
     qpat_assum `pbb.bb_instructions = pps ++ pxs`
       (fn th => simp[NoAsms,th,MAP_APPEND,ALL_DISTINCT_APPEND])) >>
  `pn < LENGTH pys` by
    (qpat_assum `SUC pn < LENGTH pys` mp_tac >> decide_tac) >>
  `(EL q pxs).inst_id = c.inst_id` by
    (qpat_assum `c = EL q pxs` (fn th => simp[NoAsms,th])) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) dft_packet_return_index >>
  `cn <= LENGTH cys` by
    (qpat_assum `cn < LENGTH cys` mp_tac >> decide_tac) >>
  `call_h + SUC (LENGTH (trace_blocks b e (N-e) C8 ctf ent)) <= SUC j` by
    (qpat_assum `call_h + SUC (LENGTH (trace_blocks b e (N-e) C8 ctf ent)) = SUC j`
       (fn th => simp[NoAsms,th])) >>
  qpat_assum `c = EL q pxs` (fn eq =>
    qpat_assum `bind_outputs c.inst_outputs _ _ = SOME post`
      (assume_tac o REWRITE_RULE [eq])) >>
  let
    fun return_fact places th =
      return_edge_mp places th >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (map_every assume_tac o CONJUNCTS)
    val child =
      [`child_entry` |-> `ent`, `child_out` |-> `out`,
       `csched` |-> `crho`, `caller_post` |-> `post`]
    val parent =
      [`bb` |-> `pbb`, `bt` |-> `pbt`, `ps` |-> `pps`,
       `xs` |-> `pxs`, `ys` |-> `pys`, `sched` |-> `prho`, `n` |-> `pn`,
       `h0` |-> `ph0`, `be` |-> `pbe`, `hbe` |-> `phbe`]
  in
    qpat_assum `b = (e,cid)::a` (fn path =>
      return_fact ["blocks","blocks'"] (PURE_REWRITE_RULE [GSYM path]
        (Q.INST [`child_entry` |-> `ent`, `child_order` |-> `cord`, `h` |-> `call_h`]
          (let val rel = ``dftRunRel$dft_fn_rel`` in
             INST [mk_var ("dft_fn_rel",type_of rel) |-> rel]
               (SPEC_ALL dft_packet_return_activation_frame)
           end)))) >>
    return_fact [] (Q.INST [`ord` |-> `cord`, `h` |-> `call_h`]
      (SPEC_ALL dft_packet_return_visit_frame)) >>
    return_fact [] (Q.INST (child @ parent) (SPEC_ALL dft_packet_return_Q_tables)) >>
    return_fact [] (Q.INST (child @ parent) (SPEC_ALL dft_packet_return_completed_tables)) >>
    return_fact ["calls","calls'","ms_tab"]
      (Q.INST [`ord` |-> `cord`] (SPEC_ALL dft_packet_return_array_frame)) >>
    return_fact [] (Q.INST [`ord` |-> `cord`] (SPEC_ALL dft_packet_return_closed_activations))
  end >>
  `?pms pes pks. FLOOKUP ms_tab (a,e) = SOME pms /\
    FLOOKUP es_tab (a,e) = SOME pes /\ FLOOKUP ks_tab (a,e) = SOME pks` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP blocks (a,e) = SOME _`, `FDOM blocks = FDOM ms_tab`,
        `FDOM blocks = FDOM es_tab`, `FDOM blocks = FDOM ks_tab`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[FDOM_FLOOKUP]) >>
  first_x_assum (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!x v bb bt ps xs ys rho ini h0 be hbe count front closed brest ms ess ks.
     FLOOKUP blocks (x,v) = _ /\ _ ==> LENGTH ms = _ /\ _`
    (qspecl_then [`a`,`e`,`pbb`,`pbt`,`pps`,`pxs`,`pys`,`prho`,`pin`,`ph0`,
       `pbe`,`phbe`,`pn`,`OK b0`,`F`,`NONE`,`pms`,`pes`,`pks`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (fn th =>
    let val fields = CONJUNCTS th in
      map_every assume_tac (List.take (fields,6)) >>
      qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE)`
        (assume_tac o MATCH_MP (List.last fields))
    end) >>
  `!rq. LIST_REL (\key slot. slot = ALOOKUP obs key)
    (FLAT (TAKE rq pks)) (FLAT (TAKE rq pms))` by
    (return_edge_mp ["ms_tab","ks_tab"] (Q.INST [`ms` |-> `pms`,`ks` |-> `pks`]
       (Q.SPECL [`acts`,`blocks`,`calls`] dft_packet_preterminal_row_lookup)) >>
     impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
        >- (rpt gen_tac >> disch_then (fn lk =>
              qpat_assum `!x sfx tfx aix ex ox rx ux.
                FLOOKUP acts x = SOME (sfx,tfx,aix,ex,ox,rx,ux) ==> _`
                (map_every assume_tac o CONJUNCTS o (C MATCH_MP lk))) >>
            conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC)
        >- (map_every qx_gen_tac
              [`x0`,`v0`,`bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`ini0`,`h00`,
               `body0`,`count0`,`front0`,`closed0`,`brest0`] >>
            disch_then (fn lk =>
              qpat_assum `!x v bb bt ps xs ys rho ini h0 body count front closed brest.
                FLOOKUP blocks (x,v) = _ ==> _`
                (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o (C MATCH_MP lk))) >>
            conj_tac >- (rpt (goal_assum (drule_at Any)) >> first_assum ACCEPT_TAC) >>
            disch_then SUBST_ALL_TAC >>
            qpat_assum `case NONE of NONE => _ | SOME _ => _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[])
        >- (map_every qx_gen_tac
              [`x0`,`v0`,`bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`ini0`,`h00`,
               `be0`,`hbe0`,`n0`,`front0`,`closed0`,`brest0`,`ms0`,`ks0`] >>
            disch_then (map_every assume_tac o CONJUNCTS) >>
            `?ess0. FLOOKUP es_tab (x0,v0) = SOME ess0` by
              (qpat_assum `FLOOKUP blocks (x0,v0) = SOME _` mp_tac >>
               qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
               POP_ASSUM_LIST (K all_tac) >> metis_tac[FDOM_FLOOKUP]) >>
            qpat_assum `!x v bb bt ps xs ys rho ini h0 be hbe count front closed brest ms ess ks.
               FLOOKUP blocks (x,v) = _ /\ _ ==> LENGTH ms = _ /\ _`
              (qspecl_then [`x0`,`v0`,`bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`ini0`,`h00`,
                 `be0`,`hbe0`,`n0`,`front0`,`closed0`,`brest0`,`ms0`,`ess0`,`ks0`] mp_tac) >>
            impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
            disch_then (map_every assume_tac o CONJUNCTS) >>
            conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
            qpat_assum `FLOOKUP blocks (x0,v0) = SOME _` (fn lk =>
              qpat_assum `!x v bb bt ps xs ys rho ini h0 body count front closed brest.
                FLOOKUP blocks (x,v) = _ ==> _`
                (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o (C MATCH_MP lk))) >>
            qpat_assum `FLOOKUP acts x0 = SOME _` (fn lk =>
              qpat_assum `!sf tf inc entry order res nrest.
                FLOOKUP acts x0 = _ ==> !q. q < LENGTH xs0 ==> _`
                (assume_tac o (C MATCH_MP lk))) >>
            qx_gen_tac `r0` >> disch_then (fn pre =>
              qpat_assum `!q. q < LENGTH xs0 ==> _`
                (mp_tac o CONJUNCT2 o CONJUNCT2 o (C MATCH_MP (CONJUNCT1 pre))) >>
              assume_tac (CONJUNCT2 pre)) >>
            impl_tac >- first_assum ACCEPT_TAC >>
            Cases_on `FLOOKUP calls (x0,v0,(EL r0 xs0).inst_id)` >>
            simp[NoAsms])
        >> (rpt gen_tac >> disch_then (fn lk =>
             qpat_assum `!x v id k t z done ent ret. FLOOKUP calls (x,v,id) = _ ==> _`
               (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o (C MATCH_MP lk))) >>
           rpt (goal_assum (drule_at Any)) >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `!r. r < LENGTH cxs /\ (EL r cxs).inst_opcode = INVOKE ==>
     MEM r (TAKE cn crho)` by
    (gen_tac >> disch_then (fn pre =>
       qpat_assum `!r. r < LENGTH cxs /\ _ ==> MEM r (TAKE cn crho) /\ _`
         (ACCEPT_TAC o CONJUNCT1 o (C MATCH_MP pre)))) >>
  qpat_assum `ms_tab' = ms_tab` (fn eq =>
    qpat_assum `!x v id q h b0 done entry ret bb bt ps xs ys rho ini h0 be hbe count front closed brest ms.
        FLOOKUP calls' (x,v,id) = _ /\ FLOOKUP blocks' (x,v) = _ /\ FLOOKUP ms_tab' (x,v) = _ ==> _`
      (assume_tac o PURE_REWRITE_RULE [eq])) >>
  return_edge_mp ["calls"] (Q.INST
    [`bb` |-> `pbb`, `bt` |-> `pbt`, `ps` |-> `pps`, `xs` |-> `pxs`,
     `ys` |-> `pys`, `sched` |-> `prho`, `hin` |-> `pin`, `h0` |-> `ph0`,
     `be` |-> `pbe`, `hbe` |-> `phbe`, `entry` |-> `ent`, `ord` |-> `cord`,
     `ms` |-> `pms`, `ess` |-> `pes`, `ks` |-> `pks`,
     `rest` |-> `out.vs_gas_readings`,
     `front` |-> `OK (post with vs_inst_idx := SUC b0.vs_inst_idx)`]
    (SPEC_ALL dft_packet_return_resumed_U)) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (rpt gen_tac >> disch_then (fn lk =>
         qpat_assum `!x sf tf inc entry order res nrest.
           FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`
           (map_every assume_tac o CONJUNCTS o (C MATCH_MP lk))) >>
         rpt conj_tac >> first_assum ACCEPT_TAC)
     >- (map_every qx_gen_tac
           [`x0`,`v0`,`id0`,`k0`,`t0`,`s0`,`ds0`,`en0`,`ret0`] >>
         disch_then (fn lk =>
           qpat_assum `!x v id k t z done ent ret. FLOOKUP calls' (x,v,id) = _ ==> _`
             (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o (C MATCH_MP lk))) >>
         rpt (goal_assum (drule_at Any)) >>
         qpat_assum `case ret0 of NONE => _ | SOME _ => _` mp_tac >>
         Cases_on `ret0` >> simp[NoAsms] >>
         PairCases_on `x` >> simp[NoAsms])
     >- (rpt gen_tac >> disch_then (fn lk =>
         qpat_assum `!x sf tf inc entry order r8 u0.
           FLOOKUP acts' x = _ ==> terminates r8 /\ _`
           (ACCEPT_TAC o List.last o CONJUNCTS o (C MATCH_MP lk))))) >>
  strip_tac >>
  mp_tac (Q.INST [`ord` |-> `cord`, `parent_sf` |-> `sf`,
    `ptf` |-> `tf`, `pinc` |-> `inc`, `pentry` |-> `entry`, `porder` |-> `order`]
    (SPEC_ALL dft_packet_return_U_frame)) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `ms = pms /\ ess = pes /\ ks = pks` by
       (map_every (fn pat => qpat_assum pat mp_tac)
         [`FLOOKUP ms_tab (a,e) = SOME ms`,`FLOOKUP ms_tab (a,e) = SOME pms`,
          `FLOOKUP es_tab (a,e) = SOME ess`,`FLOOKUP es_tab (a,e) = SOME pes`,
          `FLOOKUP ks_tab (a,e) = SOME ks`,`FLOOKUP ks_tab (a,e) = SOME pks`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
     map_every (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC [th]))
       [`ms = pms`, `ess = pes`, `ks = pks`] >>
     first_assum ACCEPT_TAC) >>
  strip_tac >>
  mp_tac (SPEC_ALL dft_packet_return_block_visits) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (qpat_assum `!F. N <= F ==> FOLDR _ OK cys cbe = IntRet ir out /\ _`
       (fn th => rpt gen_tac >> disch_tac >>
         qpat_assum `N <= _` (ACCEPT_TAC o CONJUNCT1 o MATCH_MP (SPEC_ALL th)))) >>
     map_every qx_gen_tac
       [`x0`,`v0`,`bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`ini0`,`h00`,
        `body0`,`count0`,`front0`,`closed0`,`brest0`] >>
     disch_then (fn lk =>
       qpat_assum `!x v bb bt ps xs ys rho ini h0 body count front closed brest.
         FLOOKUP blocks (x,v) = SOME (bb,bt,ps,xs,ys,rho,ini,h0,body,count,front,closed,brest) ==> _`
         (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o (C MATCH_MP lk))) >>
     rpt (goal_assum (drule_at Any)) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `case body0 of NONE => _ /\ _ | SOME _ => _` mp_tac >>
     Cases_on `body0` >> simp[NoAsms] >>
     PairCases_on `x` >> simp[NoAsms]) >>
  strip_tac >>
  map_every (fn pat => qpat_assum pat (assume_tac o SIMP_RULE (srw_ss()) []))
    [`(post with vs_inst_idx := SUC b0.vs_inst_idx).vs_inst_idx = _`,
     `get_instruction pbt (post with vs_inst_idx := SUC b0.vs_inst_idx).vs_inst_idx = _`,
     `lookup_block (post with vs_inst_idx := SUC b0.vs_inst_idx).vs_current_bb _ = _`] >>
  qpat_assum `FLOOKUP blocks' (a,e) = SOME _` (mk_asm "resumed_row") >>
  qexistsl [`acts'`,`blocks'`,`calls'`,`ms_tab'`,`es_tab'`,`ks_tab'`,`(SUC j,obs)`,
    `AM []`,`AE []`,`(post with vs_inst_idx := SUC b0.vs_inst_idx).vs_gas_readings`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[NoAsms] >> NO_TAC) >>
  FIRST
    [map_every (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC [GSYM th]))
       [`raw_slots = AM []`, `sites = AE []`] >> first_assum ACCEPT_TAC,
     qpat_assum `(post with vs_inst_idx := SUC b0.vs_inst_idx).vs_gas_readings = _`
       (fn th => PURE_REWRITE_TAC [th]) >>
     map_every (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC [GSYM th]))
       [`raw_slots = AM []`, `unused = s.vs_gas_readings`] >> first_assum ACCEPT_TAC,
     qpat_assum `FDOM blocks' = FDOM blocks` (fn blocks =>
       FIRST (map (fn pat => qpat_assum pat (fn th =>
         PURE_REWRITE_TAC [blocks,th] >> first_assum ACCEPT_TAC))
         [`ms_tab' = ms_tab`,`es_tab' = es_tab`,`ks_tab' = ks_tab`])),
     goal_assum (drule_at Any) >> NO_TAC,
     all_tac]
  >- (
    map_every qx_gen_tac
      [`xp`,`vp`,`sfp`,`tfp`,`ip`,`ep`,`op`,`rp`,`up`,`bbp`,`btp`,`psp`,
       `xsp`,`ysp`,`rhop`,`inp`,`h0p`,`bep`,`hbep`,`cp0`,`fp`,`bp`,`mp`,`sites0`,`kp`] >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    `(xp,vp) <> (a,e)` by
      (strip_tac >>
       qpat_assum `(xp,vp) = (a,e)` (fn key =>
         qpat_assum `FLOOKUP blocks' (xp,vp) = SOME _`
           (mp_tac o PURE_REWRITE_RULE [key])) >>
       qpat_assum `FLOOKUP blocks' (a,e) = SOME _` (fn th => simp[NoAsms,th])) >>
    Cases_on `(xp,vp) = (b,d)`
    >- (`xp = b /\ vp = d` by
          (qpat_assum `(xp,vp) = (b,d)` mp_tac >> simp[NoAsms,pairTheory.PAIR_EQ]) >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`FLOOKUP acts' xp = SOME _`, `FLOOKUP acts' b = SOME _`,
           `FLOOKUP blocks' (xp,vp) = SOME _`, `FLOOKUP blocks' (b,d) = SOME _`,
           `FLOOKUP ms_tab (xp,vp) = SOME mp`, `FLOOKUP ms_tab (b,d) = SOME cms`,
           `FLOOKUP es_tab (xp,vp) = SOME sites0`, `FLOOKUP es_tab (b,d) = SOME ces`,
           `FLOOKUP ks_tab (xp,vp) = SOME kp`, `FLOOKUP ks_tab (b,d) = SOME cks`,
           `xp = b`, `vp = d`, `terminates (IntRet ir out)`, `EVERY IS_SOME (FLAT cms)`,
           `PERM (MAP THE (FILTER IS_SOME (FLAT cms)) ++ out.vs_gas_readings) cbe.vs_gas_readings`,
           `!F. N <= F ==> FOLDR _ OK cys cbe = IntRet ir out /\ _`] >>
        POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[] >>
        rpt gen_tac >> disch_tac >>
        first_x_assum (drule_then (map_every assume_tac o CONJUNCTS)) >>
        map_every qx_gen_tac [`gg`,`tt`] >>
        disch_then (fn pre =>
          qpat_assum `!gs tail. LIST_REL _ (FLAT cms) gs ==> _`
            (qspecl_then [`gg`,`tt`] (ACCEPT_TAC o List.last o CONJUNCTS o (C MATCH_MP pre))))) >>
    `FLOOKUP blocks (xp,vp) =
      SOME (bbp,btp,psp,xsp,ysp,rhop,inp,h0p,SOME (bep,hbep),cp0,fp,T,SOME bp)` by
      (qpat_assum `!x f. (x,f) <> (b,d) /\ (x,f) <> (a,e) ==> _`
         (qspecl_then [`xp`,`vp`] mp_tac) >>
       impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
       disch_then (fn eq => PURE_REWRITE_TAC [GSYM eq]) >> first_assum ACCEPT_TAC) >>
    mp_tac (Q.INST
      [`ord` |-> `cord`, `x` |-> `xp`, `sf` |-> `sfp`, `tf` |-> `tfp`,
       `inc` |-> `ip`, `entry` |-> `ep`, `order` |-> `op`, `res` |-> `rp`,
       `nrest` |-> `up`]
      (SPEC_ALL dft_packet_return_old_act)) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then (qx_choose_then `orp` (qx_choose_then `oup` assume_tac)) >>
    qpat_assum `!x v sf tf inc entry order res nrest bb bt ps xs ys rho ini h0 be hbe count r8 u0 ms ess ks.
      FLOOKUP acts x = _ /\ FLOOKUP blocks (x,v) = _ /\ _ ==> terminates r8 /\ _`
      (qspecl_then [`xp`,`vp`,`sfp`,`tfp`,`ip`,`ep`,`op`,`orp`,`oup`,
        `bbp`,`btp`,`psp`,`xsp`,`ysp`,`rhop`,`inp`,`h0p`,`bep`,`hbep`,`cp0`,`fp`,
        `bp`,`mp`,`sites0`,`kp`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then ACCEPT_TAC) >>
  map_every qx_gen_tac
    [`xp`,`vp`,`sfp`,`tfp`,`ip`,`ep`,`op`,`rp`,`up`,`bbp`,`btp`,`psp`,
     `xsp`,`ysp`,`rhop`,`inp`,`h0p`,`bep`,`hbep`,`cp0`,`fp`,`clp`,`bp`,`rq`,`rz`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `(xp,vp) = (a,e)`
  >- (qpat_assum `(xp,vp) = (a,e)`
        (map_every SUBST_ALL_TAC o CONJUNCTS o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
      qpat_assum `FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,NONE,NONE)` (fn law =>
        qpat_assum `FLOOKUP acts' a = SOME (sfp,tfp,ip,ep,op,rp,up)`
          (map_every (TRY o SUBST_ALL_TAC o SYM) o CONJUNCTS o
            SIMP_RULE bool_ss [optionTheory.SOME_11,pairTheory.PAIR_EQ] o PURE_REWRITE_RULE [law])) >>
      asm "resumed_row" (fn fixed => first_assum (fn chosen =>
        let val t = concl chosen in
          if is_eq t andalso aconv (lhs t) (lhs (concl fixed)) andalso
             not (aconv t (concl fixed)) then
            map_every (SUBST_ALL_TAC o SYM)
              (filter (is_eq o concl)
                (CONJUNCTS (SIMP_RULE bool_ss [optionTheory.SOME_11,pairTheory.PAIR_EQ]
                  (TRANS (SYM fixed) chosen))))
          else NO_TAC
        end)) >>
      mp_tac (Q.INST
        [`p` |-> `b`, `st` |-> `s`, `inst` |-> `r`, `cq` |-> `q`,
         `child_entry` |-> `ent`, `child_order` |-> `cord`, `child_out` |-> `out`,
         `caller_post` |-> `post`, `cb` |-> `cbb`, `ct` |-> `cbt`,
         `cx` |-> `cxs`, `cy` |-> `cys`, `cr` |-> `crho`, `ci` |-> `cin`,
         `ch` |-> `ch0`, `cc` |-> `cn`, `cnt` |-> `pn`,
         `bb` |-> `pbb`, `bt` |-> `pbt`, `ps` |-> `pps`, `xs` |-> `pxs`,
         `ys` |-> `pys`, `hin` |-> `pin`, `h0` |-> `ph0`,
         `be` |-> `pbe`, `hbe` |-> `phbe`, `ms` |-> `pms`, `ess` |-> `pes`,
         `ks` |-> `pks`, `q` |-> `rq`, `z` |-> `rz`]
        (Q.SPECL [`N`,`C7`,`C8`,`root_sf`,`root_tf`,`root_entry`,`acts`,`blocks`,`calls`,
           `ms_tab`,`es_tab`,`ks_tab`,`row_eval`,`plan_eval`,`call_setup`,`rooted_eval`,
           `plan_ok`,`levels_ok`,`cps`,`prho`] dft_packet_return_parent_cut_application)) >>
      impl_tac >-
        (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
         >- (rpt gen_tac >> disch_then (fn lk =>
               qpat_assum `!x sfx tfx aix ex ox rx ux.
                 FLOOKUP acts x = SOME (sfx,tfx,aix,ex,ox,rx,ux) ==> _`
                 (map_every assume_tac o CONJUNCTS o (C MATCH_MP lk))) >>
             rpt conj_tac >> first_assum ACCEPT_TAC)
         >- (map_every qx_gen_tac
               [`x0`,`v0`,`bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`ini0`,`h00`,
                `body0`,`count0`,`front0`,`closed0`,`brest0`] >>
             disch_then (fn lk =>
               qpat_assum `!x v bb bt ps xs ys rho ini h0 body count front closed brest.
                 FLOOKUP blocks (x,v) = SOME (bb,bt,ps,xs,ys,rho,ini,h0,body,count,front,closed,brest) ==> _`
                 (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o (C MATCH_MP lk))) >>
             rpt (goal_assum (drule_at Any)) >>
             rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
             >- (qpat_assum `case body0 of NONE => _ /\ _ | SOME _ => _` mp_tac >>
                 Cases_on `body0` >> simp[NoAsms] >>
                 PairCases_on `x` >> simp[NoAsms])
             >> disch_then (fn pre => first_assum (ACCEPT_TAC o CONJUNCT1 o (C MATCH_MP pre))))
         >- (rpt gen_tac >> disch_then (fn lookups =>
               qpat_assum `!x v bb bt ps xs ys rho ini h0 be hbe count front closed brest ms ess ks.
                 FLOOKUP blocks (x,v) = _ /\ _ ==> LENGTH ms = _ /\ _`
                 (map_every assume_tac o CONJUNCTS o (C MATCH_MP lookups)) >>
               ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >>
               rpt gen_tac >> disch_then (fn lk =>
                 conj_tac >- first_assum (ACCEPT_TAC o (C MATCH_MP lk)) >>
                 qpat_assum `!x f bb bt ps xs ys sched hin h0 be hbe n front closed brest
                     ms ess ks sf tf inc entry order res nrest.
                     FLOOKUP blocks (x,f) = _ /\ _ ==> !F k kgss tail. _`
                   (ACCEPT_TAC o (C MATCH_MP (LIST_CONJ (CONJUNCTS lookups @ [lk])))))))
         >- (rpt gen_tac >> disch_then (fn lookups =>
               qpat_assum `!x v sf tf inc entry order res nrest bb bt ps xs ys rho ini h0 be hbe
                   count r8 u0 ms ess ks.
                   FLOOKUP acts x = _ /\ FLOOKUP blocks (x,v) = _ /\ _ ==> terminates r8 /\ _`
                 (mp_tac o List.last o CONJUNCTS o (C MATCH_MP lookups))) >>
             POP_ASSUM_LIST (K all_tac) >> metis_tac[])
         >- (map_every qx_gen_tac
               [`x0`,`v0`,`id0`,`k0`,`t0`,`s0`,`ds0`,`en0`,`ret0`] >>
             disch_then (fn lk =>
               qpat_assum `!x v id k t z done ent ret. FLOOKUP calls (x,v,id) = _ ==> _`
                 (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o (C MATCH_MP lk))) >>
             qpat_assum `c' = EL k0 _` SUBST_ALL_TAC >>
             rpt (goal_assum (drule_at Any)) >>
             rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
             qpat_assum `case ret0 of NONE => _ | SOME _ => _` mp_tac >>
             Cases_on `ret0` >> simp[NoAsms] >>
             PairCases_on `x` >> simp[NoAsms])
         >> gen_tac >> disch_then (fn bound =>
              qpat_assum `!k. k < LENGTH b ==> ?sf tf inc entry order bb bt ps xs ys rho ini h0
                be hbe count q h b0 done child_entry id v x.
                _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ get_instruction bt b0.vs_inst_idx = SOME (EL q xs)`
                (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o (C MATCH_MP bound))) >>
            rpt (goal_assum (drule_at Any)) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then mp_tac >>
      map_every (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC [GSYM th]))
        [`ms_tab' = ms_tab`,`es_tab' = es_tab`,`ks_tab' = ks_tab`] >>
      map_every (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC [GSYM (SPEC_ALL th)]))
        [`!x. AM x = _`,`!x. AE x = _`,`!x. AK x = _`] >>
      PURE_REWRITE_TAC [pairTheory.pair_CASE_def] >> BETA_TAC >>
      disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
      qexistsl [`cuts`,`levels`,`Mcut`,`Ecut`,`Kcut`,`mr`,`er`,`kr`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      map_every qx_gen_tac [`B`,`gs0`,`tail0`] >>
      disch_then (fn pre =>
        first_assum (qspec_then `tail0` mp_tac o (C MATCH_MP pre)) >>
        map_every assume_tac (CONJUNCTS pre)) >>
      Cases_on `SND (rooted_eval B C7 levels (root_entry with vs_gas_readings := gs0 ++ tail0))` >>
      simp[NoAsms] >> strip_tac >> strip_tac >>
      `?gss. LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
                (TAKE rq pms) gss /\
             FOLDR (dft_exec_cons (B-e) C7) OK (TAKE rq pxs)
               (pbe with vs_gas_readings := FLAT gss ++ tail0) = OK v` suffices_by
      (disch_then (qx_choose_then `gss` (map_every assume_tac o CONJUNCTS)) >>
      `trace_gas (trace_block a e (B-e) C7 sf
        (pbb with bb_instructions := TAKE (LENGTH pps + rq) pbb.bb_instructions)
        (pbe with vs_gas_readings := FLAT gss ++ tail0)) = ZIP (FLAT (TAKE rq pks),FLAT gss)` by
        (qpat_assum `!F k kgss tail. _ /\ _ /\ _ /\
             (!q. q < k /\ (EL q pxs).inst_opcode = INVOKE ==> MEM q (TAKE (SUC pn) prho)) /\ _ ==> _`
           (qspecl_then [`B`,`rq`,`gss`,`tail0`] mp_tac) >>
         impl_tac >-
           (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            qpat_assum `rq < LENGTH pxs` mp_tac >> decide_tac) >>
         disch_then (qspec_then `v` mp_tac o CONJUNCT2) >>
         impl_tac >- first_assum ACCEPT_TAC >>
         disch_then (ACCEPT_TAC o (List.nth o (fn th => (CONJUNCTS th,2))))) >>
      `MEM pbb sf.fn_blocks` by first_assum (ACCEPT_TAC o MATCH_MP lookup_block_MEM) >>
      qpat_assum `!rq. LIST_REL (\key slot. slot = ALOOKUP obs key) _ _`
        (qspec_then `rq` assume_tac) >>
      qpat_assum `!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE (SUC pn) pys) pbe = _`
        (qspec_then `N` (assume_tac o SIMP_RULE bool_ss [LESS_EQ_REFL])) >>
      mp_tac (Q.INST
        [`hbe` |-> `phbe`, `bb` |-> `pbb`, `bt` |-> `pbt`, `ps` |-> `pps`,
         `xs` |-> `pxs`, `ys` |-> `pys`, `be` |-> `pbe`, `q` |-> `rq`,
         `F'` |-> `B`, `u` |-> `v`, `v` |-> `post with vs_inst_idx := SUC b0.vs_inst_idx`,
         `kgss` |-> `gss`, `tail` |-> `tail0`, `ms` |-> `pms`, `ks` |-> `pks`]
        (SPEC_ALL dft_packet_return_observation)) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])) >>
      (* Read the selected cut back through the unchanged fields of the old tables. *)
      qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest
        q z cuts levels Mcut fuel gs tail events u. _`
        (qspecl_then [`a`,`e`,`pbb`,`pbt`,`pps`,`pxs`,`pys`,`prho`,`pin`,`ph0`,
          `pbe`,`phbe`,`pn`,`OK b0`,`F`,`NONE`,`rq`,`rz`,`cuts`,`levels`,`Mcut`,
          `B`,`gs0`,`tail0`,
          `FST (rooted_eval B C7 levels (root_entry with vs_gas_readings := gs0 ++ tail0))`,`v`]
          mp_tac) >>
      impl_tac >-
        (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
         >- (map_every qx_gen_tac [`ij`,`aj`,`dsj`,`ej`,`qj`,`zj`] >>
             disch_then (fn pre =>
               qpat_assum `!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
                 ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
                   ini hi bei counti fronti closedi resti later. FLOOKUP acts' ai = _ /\ _`
                 (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o (C MATCH_MP pre))) >>
             `?oldres oldrest. FLOOKUP acts aj = SOME (sfi,tfi,inci,enti,orderi,oldres,oldrest)` by
               (map_every (fn pat => qpat_assum pat mp_tac)
                  [`FLOOKUP acts' aj = SOME _`,`acts' = _`,`FLOOKUP acts b = SOME _`] >>
                POP_ASSUM_LIST (K all_tac) >> Cases_on `aj = b` >>
                gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
             `?oldcount oldfront oldclosed oldrowrest. FLOOKUP blocks (aj,ej) =
               SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,oldcount,oldfront,oldclosed,oldrowrest)` by
               (map_every (fn pat => qpat_assum pat mp_tac)
                  [`FLOOKUP blocks' (aj,ej) = SOME _`,`blocks' = _`,
                   `FLOOKUP blocks (a,e) = SOME _`,`FLOOKUP blocks (b,d) = SOME _`,`a <> b`] >>
                POP_ASSUM_LIST (K all_tac) >>
                Cases_on `aj = a` >- (Cases_on `ej = e` >> gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
                Cases_on `aj = b` >- (Cases_on `ej = d` >> gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
                gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
             `!x f. FST (THE (FLOOKUP blocks' (x,f))) = FST (THE (FLOOKUP blocks (x,f)))` by
               (map_every (fn pat => qpat_assum pat mp_tac)
                  [`blocks' = _`,`FLOOKUP blocks (a,e) = SOME _`,
                   `FLOOKUP blocks (b,d) = SOME _`,`a <> b`] >>
                POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
                map_every qx_gen_tac [`xx`,`ff`] >>
                Cases_on `xx = a` >- (Cases_on `ff = e` >> gvs[FLOOKUP_UPDATE]) >>
                Cases_on `xx = b` >- (Cases_on `ff = d` >> gvs[FLOOKUP_UPDATE]) >>
                gvs[FLOOKUP_UPDATE]) >>
             goal_assum (drule_at (Pat `FLOOKUP acts aj = _`)) >>
             goal_assum (drule_at (Pat `FLOOKUP blocks (aj,ej) = _`)) >>
             goal_assum (drule_at (Pat `_ = dsj ++ ej::later`)) >>
             reverse conj_tac >-
               (qpat_assum `!x f. FST (THE (FLOOKUP blocks' (x,f))) = _`
                  (fn th => PURE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
             IF_CASES_TAC
             >- (pop_assum (fn eq => first_assum (fn th =>
                   if is_cond (concl th) andalso
                      aconv (#1 (dest_cond (concl th))) (concl eq) then
                     ACCEPT_TAC (REWRITE_RULE [eq] th)
                   else NO_TAC))) >>
             pop_assum (fn neq => first_assum (fn th =>
               if is_cond (concl th) andalso
                  aconv (#1 (dest_cond (concl th))) (dest_neg (concl neq)) then
                 REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)
                   (PURE_REWRITE_RULE [neq,COND_CLAUSES] th)
               else NO_TAC)) >>
             rename1 `FLOOKUP calls' (aj,ej,ci) = SOME (qj,hh,zz,done0,ent0,ret0)` >>
             `?oldret. FLOOKUP calls (aj,ej,ci) = SOME (qj,hh,zz,done0,ent0,oldret)` by
               (map_every (fn pat => qpat_assum pat mp_tac)
                  [`calls' = _`,`FLOOKUP calls' (aj,ej,ci) = SOME _`,
                   `FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done,ent,NONE)`] >>
                POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
                Cases_on `(aj,ej,ci) = (a,e,cid)` >>
                gvs[FLOOKUP_UPDATE,pairTheory.PAIR_EQ] >> metis_tac[]) >>
             rpt (goal_assum (drule_at Any)) >> rpt conj_tac >> first_assum ACCEPT_TAC)
         >- (qpat_assum `ms_tab' = ms_tab` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
             first_assum ACCEPT_TAC)
         >> qpat_assum `SND (rooted_eval B C7 levels _) = OK v` (fn th =>
              CONV_TAC (RHS_CONV (RAND_CONV (REWR_CONV (GSYM th)))) >>
              REWRITE_TAC [pairTheory.PAIR])) >>
      qpat_assum `FLOOKUP ms_tab (a,e) = SOME pms` (fn lk =>
        disch_then (ACCEPT_TAC o REWRITE_RULE [lk,optionTheory.THE_DEF]))) >>
  mp_tac (Q.INST
    [`csched` |-> `crho`, `psched` |-> `prho`,
     `x` |-> `xp`, `f` |-> `vp`, `q` |-> `rq`,
     `bb` |-> `bbp`, `bt` |-> `btp`, `ps` |-> `psp`, `xs` |-> `xsp`,
     `ys` |-> `ysp`, `sched` |-> `rhop`, `hin` |-> `inp`, `h0` |-> `h0p`,
     `be` |-> `bep`, `hbe` |-> `hbep`, `n` |-> `cp0`, `front` |-> `fp`,
     `closed` |-> `clp`, `brest` |-> `bp`]
    (SPEC_ALL dft_packet_return_historical_eligibility)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  mp_tac (Q.INST
    [`ord` |-> `cord`, `x` |-> `xp`, `sf` |-> `sfp`, `tf` |-> `tfp`,
     `inc` |-> `ip`, `entry` |-> `ep`, `order` |-> `op`, `res` |-> `rp`,
     `nrest` |-> `up`]
    (SPEC_ALL dft_packet_return_old_act)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `orp` (qx_choose_then `oup` assume_tac)) >>
  qpat_assum `!a e q z sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest. FLOOKUP acts a = _ /\ _ ==> _`
    (qspecl_then [`xp`,`vp`,`rq`,`rz`,`sfp`,`tfp`,`ip`,`ep`,`op`,`orp`,`oup`,
      `bbp`,`btp`,`psp`,`xsp`,`ysp`,`rhop`,`inp`,`h0p`,`SOME (bep,hbep)`,
      `on`,`ofront`,`oclosed`,`orest`] mp_tac) >>
  impl_tac >-
    (ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     disj1_tac >> simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  return_edge_mp ["levels_ok"] (Q.INST
    [`cq` |-> `q`, `f` |-> `vp`, `x` |-> `xp`, `q` |-> `rq`, `z` |-> `rz`,
     `sf` |-> `sfp`, `bb` |-> `bbp`, `levels_ok_num` |-> `levels_ok`]
    (SPEC_ALL dft_packet_return_historical_witnesses)) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexistsl [`cuts`,`levels`,`Mcut`,`Ecut`,`Kcut`,`mr`,`er`,`kr`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qpat_assum `AM [] = Mcut ++ mr` mp_tac >>
         qpat_assum `AM = _` (fn th => simp[NoAsms,th]))
     >- (qpat_assum `AE [] = Ecut ++ er` mp_tac >>
         qpat_assum `AE = _` (fn th => simp[NoAsms,th]))
     >- (qpat_assum `AK [] = Kcut ++ kr` mp_tac >>
         qpat_assum `AK = _` (fn th => simp[NoAsms,th]))
     >> map_every qx_gen_tac [`B`,`gs0`,`tail0`] >>
     disch_then (fn pre => first_assum (qspec_then `tail0` mp_tac o (C MATCH_MP pre))) >>
     Cases_on `SND (rooted_eval B C7 levels (root_entry with vs_gas_readings := gs0 ++ tail0))` >>
     simp[NoAsms]) >>
  disch_then mp_tac >>
  `!P. ~(xp = a /\ vp = e /\ P)` by
    (qpat_assum `(xp,vp) <> (a,e)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[pairTheory.PAIR_EQ] >> metis_tac[]) >>
  qpat_assum `!P. ~(xp = a /\ vp = e /\ P)` (fn th => simp[NoAsms,th])
QED
