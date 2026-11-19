Theory dftPacketScheduledCallRecord
Ancestors
  dftIndexedExec dftStructural dftDefs passSharedDefs venomEffects
  venomExecSemantics venomInst venomState
  finite_map list rich_list arithmetic sorting

(* The successful target prefix ends at the immutable pre-state in the
   returned call record: the two instruction positions have the same id
   in the same block.  No source replay or caller-step invariant is used. *)
Theorem dft_packet_scheduled_call_record:
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),ct,front,closed,brest) /\
  bt.bb_instructions = ps ++ ys /\
  ALL_DISTINCT (MAP (\c. c.inst_id) bt.bb_instructions) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
                    from_block [EL q xs] y) sched ys /\
  i < ct /\ ct <= LENGTH ys /\
  (EL (EL i sched) xs).inst_opcode = INVOKE /\
  FOLDR (dft_exec_cons (N-e) C8) OK (TAKE i ys) be = OK u /\
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
  (EL i ys).inst_opcode = INVOKE /\
  ?nm ops ctf args ent ir out bound.
    decode_invoke (EL i ys) = SOME (nm,ops) /\
    lookup_function nm C8.ctx_functions = SOME ctf /\
    eval_operands ops u = SOME args /\
    setup_callee ctf args u = SOME ent /\
    run_blocks (N-e) C8 ctf ent = IntRet ir out /\
    bind_outputs (EL i ys).inst_outputs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state u out)) = SOME bound /\
    PERM (MAP THE (FILTER IS_SOME (EL (EL i sched) ms)) ++ out.vs_gas_readings)
      ent.vs_gas_readings
Proof
  strip_tac >>
  `LENGTH sched = LENGTH ys /\ i < LENGTH sched` by gvs[LIST_REL_EL_EQN] >>
  `EL i sched < LENGTH xs /\ from_block [EL (EL i sched) xs] (EL i ys)` by
    (qpat_x_assum `LIST_REL _ sched ys` mp_tac >> simp[LIST_REL_EL_EQN] >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  `EL i ys = EL (EL i sched) xs` by
    gvs[from_block_def,is_flippable_def,is_commutative_def,is_comparator_def] >>
  conj_tac >- metis_tac[] >>
  `MEM (EL i sched) (TAKE ct sched)` by
    (`EL i (TAKE ct sched) = EL i sched` by simp[EL_TAKE] >>
     `i < LENGTH (TAKE ct sched)` by simp[LENGTH_TAKE] >>
     metis_tac[EL_MEM]) >>
  qpat_x_assum `!q. _ /\ _ /\ MEM q (TAKE ct sched) ==> _`
    (qspec_then `EL i sched` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!q cid h b0 done ent ir out post. _ ==> _`
    (fn th => drule_then strip_assume_tac th) >>
  gvs[] >>
  `b0.vs_inst_idx = LENGTH ps + i` by
    (`b0.vs_inst_idx < LENGTH ps + LENGTH ys` by
       gvs[get_instruction_def,AllCaseEqs()] >>
     `EL b0.vs_inst_idx (ps ++ ys) = EL (LENGTH ps + i) (ps ++ ys)` by
       gvs[get_instruction_def,EL_APPEND2] >>
     qspecl_then [`MAP (\c. c.inst_id) (ps ++ ys)`, `b0.vs_inst_idx`,
                  `LENGTH ps + i`] mp_tac ALL_DISTINCT_EL_IMP >>
     simp[EL_MAP]) >>
  `b0 = u` by
    (qpat_x_assum `!F. N <= F ==> FOLDR _ _ _ _ = OK b0`
       (qspec_then `N` mp_tac) >> simp[]) >>
  `EL (EL i sched) ms = AM ((e,(EL (EL i sched) xs).inst_id)::a)` by
    (qpat_x_assum `!q. _ ==> (case FLOOKUP calls _ of NONE => _ | SOME c => _)`
       (qspec_then `EL i sched` mp_tac) >> simp[]) >>
  qpat_x_assum `!cid csf ctf ent ord res rest. _ ==> (res = NONE <=> rest = NONE)`
    (fn th => drule_then mp_tac th) >>
  Cases_on `child_rest` >> simp[] >>
  qpat_x_assum `!cid csf ctf ent ord r8 u0. _ ==> _`
    (fn th => drule_then strip_assume_tac th) >>
  qexistsl [`args`,`child_entry`,`ir`,`child_out`,`caller_post`] >>
  gvs[] >> metis_tac[LESS_EQ_REFL]
QED
