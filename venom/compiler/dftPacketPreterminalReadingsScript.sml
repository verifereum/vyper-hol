Theory dftPacketPreterminalReadings
Ancestors
  dftPacketObservedGasHead dftPacketPrefixVisitState
  dftPacketReturnedCellReadings dftPacketScheduleReadings
  dftPacketScheduledPlainCell dftPacketScheduledCallRecord
  dftWf venomExecProps dftStructural dftDefs passSharedDefs
  venomState venomInst venomEffects venomExecSemantics dftIndexedExec
  dftGasFromListTraceDefs finite_map rich_list list sorting alist

Theorem dft_packet_preterminal_readings:
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,sched,(in_state:venom_state),(h0:num),SOME (be,hbe),ct,
          OK s,F,(NONE:bytes32 list option)) /\
  wf_function tf /\ lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bt.bb_instructions = ps ++ ys /\ be.vs_inst_idx = LENGTH ps /\
  LENGTH xs = LENGTH ys /\ LENGTH ms = LENGTH xs /\ LENGTH ys = SUC ct /\
  PERM sched (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
                   from_block [EL q xs] y) sched ys /\
  inst = EL ct ys /\ inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE ct ys) /\
  FOLDR (dft_exec_cons (N-e) C8) OK (TAKE ct ys) be = OK s /\
  R = trace_blocks [] 0 N C8 root_tf root_entry /\
  TAKE j R = TAKE hbe R ++ trace_block a e (N-e) C8 tf
    (bt with bb_instructions := TAKE (be.vs_inst_idx + ct) bt.bb_instructions) be /\
  obs = trace_gas (TAKE j R) /\ LENGTH obs <= LENGTH root_entry.vs_gas_readings /\
  ALL_DISTINCT (MAP FST obs) /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = GAS ==>
    EL q ms = [ALOOKUP obs (a,e,(EL q xs).inst_id)]) /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode <> GAS /\
        (EL q xs).inst_opcode <> INVOKE ==> EL q ms = []) /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
        MEM q (TAKE ct sched) ==>
    ?h b0 done_at_call child_entry ir child_out caller_post.
      FLOOKUP calls (a,e,(EL q xs).inst_id) =
        SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post))) /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
    case FLOOKUP calls (a,e,(EL q xs).inst_id) of
      NONE => EL q ms = []
    | SOME call => EL q ms = AM ((e,(EL q xs).inst_id)::a)) /\
  (!q cid h b0 done_at_call child_entry ir child_out caller_post.
    FLOOKUP calls (a,e,cid) =
      SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post)) ==>
    ?bb' bt' ps' xs' ys' sched' in_state' h0' be' hbe' ct' front' closed' brest'
      csf ctf child_order child_rest c nm ops args.
      FLOOKUP blocks (a,e) =
        SOME (bb',bt',ps',xs',ys',sched',in_state',h0',SOME (be',hbe'),ct',front',closed',brest') /\
      c = EL q xs' /\
      LENGTH ps' <= b0.vs_inst_idx /\
      get_instruction bt' b0.vs_inst_idx = SOME c /\
      (!F. N <= F ==>
        FOLDR (dft_exec_cons (F-e) C8) OK
          (TAKE (b0.vs_inst_idx - LENGTH ps') ys') be' = OK b0) /\
      FLOOKUP acts ((e,cid)::a) =
        SOME (csf,ctf,e,child_entry,child_order,SOME (IntRet ir child_out),child_rest) /\
      decode_invoke c = SOME (nm,ops) /\
      lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops b0 = SOME args /\
      setup_callee ctf args b0 = SOME child_entry /\
      bind_outputs c.inst_outputs ir.iret_values
        (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post) /\
  (!cid csf ctf ent ord res rest.
    FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,ent,ord,res,rest) ==>
    (res = NONE <=> rest = NONE)) /\
  (!cid csf ctf ent ord r8 u0.
    FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,ent,ord,SOME r8,SOME u0) ==>
    PERM (MAP THE (FILTER IS_SOME (AM ((e,cid)::a))) ++ u0) ent.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==> u0 = v.vs_gas_readings) /\
    (!F. N <= F ==> run_blocks (F-e) C8 ctf ent = r8)) ==>
  PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ s.vs_gas_readings)
    be.vs_gas_readings
Proof
  strip_tac >>
  `MEM bt tf.fn_blocks` by metis_tac[lookup_block_MEM] >>
  drule_all_then assume_tac wf_fn_block_inst_ids_distinct >>
  `LENGTH sched = LENGTH ys /\
   (!i. i < LENGTH ys ==> EL i sched < LENGTH xs /\
      (EL i ys).inst_id = (EL (EL i sched) xs).inst_id /\
      from_block [EL (EL i sched) xs] (EL i ys))` by
    (qpat_assum `LIST_REL _ sched ys` (mp_tac o REWRITE_RULE[LIST_REL_EL_EQN]) >>
     simp[] >> strip_tac >> fs[]) >>
  `ct < LENGTH ys` by simp[] >>
  `ct <= LENGTH ys` by simp[] >>
  `EL (EL ct sched) ms = []` by
    (qpat_assum `!i. i < LENGTH ys ==> _` (qspec_then `ct` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     strip_tac >>
     `(EL (EL ct sched) xs).inst_opcode <> GAS /\
      (EL (EL ct sched) xs).inst_opcode <> INVOKE` by
       ((qpat_assum `from_block _ _` (mp_tac o REWRITE_RULE[from_block_def]) >>
        strip_tac >> gvs[is_flippable_def,is_commutative_def,is_comparator_def] >> (metis_tac[is_flippable_def, is_commutative_def, is_comparator_def]))) >>
     first_x_assum irule >> simp[]) >>
  irule dft_packet_schedule_readings >>
  qexistsl [`C8`,`ct`,`N-e`,`sched`,`ys`] >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `(EL (EL i sched) xs).inst_opcode = INVOKE`
  >- (drule_all dft_packet_scheduled_call_record >> strip_tac >>
      drule_all dft_packet_returned_cell_readings >> simp[]) >>
  `EL i sched < LENGTH xs /\
   (EL i ys).inst_id = (EL (EL i sched) xs).inst_id /\
   from_block [EL (EL i sched) xs] (EL i ys)` by simp[] >>
  `((EL (EL i sched) xs).inst_opcode = GAS ==>
      EL (EL i sched) ms = [ALOOKUP obs (a,e,(EL (EL i sched) xs).inst_id)]) /\
   ((EL (EL i sched) xs).inst_opcode <> GAS ==> EL (EL i sched) ms = [])` by simp[] >>
  `(EL i ys).inst_opcode = GAS ==>
    u.vs_gas_readings <> [] /\ MEM ((a,e,(EL (EL i sched) xs).inst_id),HD u.vs_gas_readings) obs` by
    (strip_tac >>
     `ys = DROP be.vs_inst_idx bt.bb_instructions` by simp[DROP_LENGTH_APPEND] >>
     drule_all_then assume_tac dft_packet_prefix_visit_state >>
     drule_all dft_packet_observed_gas_head >>
     qpat_assum `(EL i ys).inst_id = _` (fn th => REWRITE_TAC[th])) >>
  drule_all dft_packet_scheduled_plain_cell >> simp[]
QED
