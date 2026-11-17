Theory dftPacketCallRecordFrame
Ancestors
  dftPacketCallRecords dftRunRel frameJointTransition
  list rich_list finite_map arithmetic pred_set

(* The current caller becomes index zero; all older suspended callers retain
   their exact block cursor and immutable setup record. *)
Theorem dft_packet_call_suspended_parents:
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
    p d inst s sf fn inc entry order bb bt ps xs ys sched hin h0 be hbe n_done
    call_q j cs csf ctf cbb cbt cps cxs cys crho cbe s1.
    FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
    LAST order = d /\
    FLOOKUP blocks (p,d) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),n_done,OK s,F,NONE) /\
    s.vs_inst_idx = LENGTH ps + n_done /\
    get_instruction bt s.vs_inst_idx = SOME (EL call_q xs) /\
    (!k. k < LENGTH p ==>
      ?sf tf inc entry order bb bt ps xs ys rho hin h0 be hbe count
       q h b0 done child cid e a.
        a = DROP (SUC k) p /\ (e,cid) = EL k p /\
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
        LAST order = e /\
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
        FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child,NONE) /\
        done = TAKE count rho /\ b0.vs_inst_idx = LENGTH ps + count /\
        get_instruction bt b0.vs_inst_idx = SOME (EL q xs)) ==>
    !k. k < LENGTH ((d,inst.inst_id)::p) ==>
      ?sf tf inc entry order bb bt ps xs ys rho hin h0 be hbe count
       q h b0 done child cid e a.
        a = DROP (SUC k) ((d,inst.inst_id)::p) /\
        (e,cid) = EL k ((d,inst.inst_id)::p) /\
        FLOOKUP (acts |+ ((d,inst.inst_id)::p,
          (csf,ctf,d,cs,[SUC d],NONE,NONE))) a =
          SOME (sf,tf,inc,entry,order,NONE,NONE) /\
        LAST order = e /\
        FLOOKUP (blocks |+ (((d,inst.inst_id)::p,SUC d),
          (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE))) (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
        FLOOKUP (calls |+ ((p,d,inst.inst_id),(call_q,j,s,TAKE n_done sched,cs,NONE)))
          (a,e,cid) = SOME (q,h,b0,done,child,NONE) /\
        done = TAKE count rho /\ b0.vs_inst_idx = LENGTH ps + count /\
        get_instruction bt b0.vs_inst_idx = SOME (EL q xs)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >> Cases_on `k`
  >- (simp[FLOOKUP_UPDATE] >> gvs[ADD_COMM] >> metis_tac[]) >>
  `n < LENGTH p` by gvs[] >>
  `DROP (SUC n) p <> p /\ DROP (SUC n) p <> (d,inst.inst_id)::p` by
    (conj_tac >> strip_tac >>
     pop_assum (mp_tac o AP_TERM ``LENGTH:(num # num) list -> num``) >> simp[]) >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  simp[FLOOKUP_UPDATE] >> metis_tac[]
QED

(* This is structural framing, not replay transport.  In particular, the
   returned-child bind and the retained child activation are preserved even
   for calls no longer on the live stack.  Raw tuple preservation below lets
   consumers reuse the separate native-occurrence and replay clauses. *)
Theorem dft_packet_call_immutable_frame:
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
    C8 p d inst s sf fn inc entry order bb bt ps xs ys sched hin h0 be hbe n_done
    call_q j cs csf ctf cbb cbt cps cxs cys crho cbe s1 nm ops args
    acts' blocks' calls'.
    FLOOKUP acts ((d,inst.inst_id)::p) = NONE /\
    FLOOKUP calls (p,d,inst.inst_id) = NONE /\
    (!a e. (a,e) IN FDOM blocks ==> a IN FDOM acts) /\
    FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
    FLOOKUP blocks (p,d) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),n_done,OK s,F,NONE) /\
    call_q < LENGTH xs /\ EL call_q xs = inst /\ inst.inst_opcode = INVOKE /\
    s.vs_inst_idx = LENGTH ps + n_done /\
    get_instruction bt s.vs_inst_idx = SOME inst /\
    ~MEM call_q (TAKE n_done sched) /\
    decode_invoke inst = SOME (nm,ops) /\
    lookup_function nm C8.ctx_functions = SOME ctf /\
    eval_operands ops s = SOME args /\ setup_callee ctf args s = SOME cs /\
    (!a e cid q h b0 done child ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child,ret) ==>
      ?sf tf inc entry order res rest bb bt ps xs ys rho hin h0 be hbe
       count front closed brest csf ctf child_order child_res child_rest c nm ops args.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
        q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE /\
        LENGTH ps <= b0.vs_inst_idx /\
        get_instruction bt b0.vs_inst_idx = SOME c /\
        done = TAKE (b0.vs_inst_idx - LENGTH ps) rho /\ ~MEM q done /\
        FLOOKUP acts ((e,cid)::a) =
          SOME (csf,ctf,e,child,child_order,child_res,child_rest) /\
        decode_invoke c = SOME (nm,ops) /\
        lookup_function nm C8.ctx_functions = SOME ctf /\
        eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child /\
        (case ret of
          NONE => child_res = NONE /\
            MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
        | SOME (ir,child_out,caller_post) =>
            child_res = SOME (IntRet ir child_out) /\
            bind_outputs c.inst_outputs ir.iret_values
              (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
            MEM q (TAKE count rho))) /\
    acts' = acts |+ ((d,inst.inst_id)::p,(csf,ctf,d,cs,[SUC d],NONE,NONE)) /\
    blocks' = blocks |+ (((d,inst.inst_id)::p,SUC d),
      (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE)) /\
    calls' = calls |+ ((p,d,inst.inst_id),(call_q,j,s,TAKE n_done sched,cs,NONE)) ==>
    (!a. a <> (d,inst.inst_id)::p ==> FLOOKUP acts' a = FLOOKUP acts a) /\
    (!a e. (a,e) <> ((d,inst.inst_id)::p,SUC d) ==>
      FLOOKUP blocks' (a,e) = FLOOKUP blocks (a,e)) /\
    (!key. key <> (p,d,inst.inst_id) ==> FLOOKUP calls' key = FLOOKUP calls key) /\
    (!a value. FLOOKUP acts a = SOME value ==> FLOOKUP acts' a = SOME value) /\
    (!key value. FLOOKUP blocks key = SOME value ==> FLOOKUP blocks' key = SOME value) /\
    (!key value. FLOOKUP calls key = SOME value ==> FLOOKUP calls' key = SOME value) /\
    FLOOKUP calls' (p,d,inst.inst_id) = SOME (call_q,j,s,TAKE n_done sched,cs,NONE) /\
    (!a e cid q h b0 done child ret.
      FLOOKUP calls' (a,e,cid) = SOME (q,h,b0,done,child,ret) ==>
      ?sf tf inc entry order res rest bb bt ps xs ys rho hin h0 be hbe
       count front closed brest csf ctf child_order child_res child_rest c nm ops args.
        FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,rest) /\
        FLOOKUP blocks' (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
        q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE /\
        LENGTH ps <= b0.vs_inst_idx /\
        get_instruction bt b0.vs_inst_idx = SOME c /\
        done = TAKE (b0.vs_inst_idx - LENGTH ps) rho /\ ~MEM q done /\
        FLOOKUP acts' ((e,cid)::a) =
          SOME (csf,ctf,e,child,child_order,child_res,child_rest) /\
        decode_invoke c = SOME (nm,ops) /\
        lookup_function nm C8.ctx_functions = SOME ctf /\
        eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child /\
        (case ret of
          NONE => child_res = NONE /\
            MEM ((e,cid)::a) (GENLIST (\i. DROP i ((d,inst.inst_id)::p))
              (SUC (LENGTH ((d,inst.inst_id)::p))))
        | SOME (ir,child_out,caller_post) =>
            child_res = SOME (IntRet ir child_out) /\
            bind_outputs c.inst_outputs ir.iret_values
              (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
            MEM q (TAKE count rho)))
Proof
  rpt gen_tac >> strip_tac >>
  `acts SUBMAP acts' /\ calls SUBMAP calls'` by
    simp[SUBMAP_FUPDATE_FLOOKUP] >>
  `FLOOKUP blocks ((d,inst.inst_id)::p,SUC d) = NONE` by
    (Cases_on `FLOOKUP blocks ((d,inst.inst_id)::p,SUC d)` >- simp[] >>
     `((d,inst.inst_id)::p,SUC d) IN FDOM blocks` by gvs[FLOOKUP_DEF] >>
     qpat_x_assum `!a e. (a,e) IN FDOM blocks ==> _`
       (qspecl_then [`(d,inst.inst_id)::p`,`SUC d`] mp_tac) >>
     gvs[FLOOKUP_DEF]) >>
  `blocks SUBMAP blocks'` by simp[SUBMAP_FUPDATE_FLOOKUP] >>
  rpt conj_tac
  >- (rpt strip_tac >> simp[FLOOKUP_UPDATE])
  >- (rpt strip_tac >> simp[FLOOKUP_UPDATE])
  >- (rpt strip_tac >> simp[FLOOKUP_UPDATE] >> metis_tac[])
  >- metis_tac[FLOOKUP_SUBMAP]
  >- metis_tac[FLOOKUP_SUBMAP]
  >- metis_tac[FLOOKUP_SUBMAP]
  >- simp[FLOOKUP_UPDATE] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `(a,e,cid) = (p,d,inst.inst_id)`
  >- (gvs[FLOOKUP_UPDATE,dft_packet_live_suffix_cons] >>
      simp[ADD_COMM] >> metis_tac[]) >>
  `FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child,ret)` by
    gvs[FLOOKUP_UPDATE] >>
  qpat_x_assum `!a e cid q h b0 done child ret. _` drule >> strip_tac >>
  `a <> (d,inst.inst_id)::p /\ (e,cid)::a <> (d,inst.inst_id)::p` by
    (conj_tac >> strip_tac >> gvs[]) >>
  simp[FLOOKUP_UPDATE,dft_packet_live_suffix_cons] >>
  Cases_on `ret` >> gvs[] >> PairCases_on `x` >> gvs[]
QED
