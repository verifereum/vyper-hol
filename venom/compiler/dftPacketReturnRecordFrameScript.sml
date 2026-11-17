Theory dftPacketReturnRecordFrame
Ancestors
  dftPacketReturnTables dftPacketReturnParentReplay
  finite_map list rich_list arithmetic

(* Historical agreement sees the immutable fields of both retained rows. *)
Theorem dft_packet_return_Q_tables:
  FLOOKUP (blocks : (((num # num) list # num),
    basic_block # basic_block # instruction list # instruction list #
    instruction list # num list # venom_state # num #
    (venom_state # num) option # num # exec_result # bool #
    bytes32 list option) fmap) (b,d) =
    SOME(cbb,cbt,cps,cxs,cys,csched,cin,ch0,SOME(cbe,chbe),cn,OK s,F,NONE) /\
  FLOOKUP blocks (a,e) =
    SOME(bb,bt,ps,xs,ys,sched,pin,h0,SOME(be,hbe),n,OK b0,F,NONE) /\
  FLOOKUP (calls : (gas_event,
    num # num # venom_state # num list # venom_state #
    (internal_return # venom_state # venom_state) option) fmap)
    (a,e,cid) = SOME(q,call_h,b0,done,child_entry,NONE) /\
  blocks' = blocks |+
    ((b,d),(cbb,cbt,cps,cxs,cys,csched,cin,ch0,SOME(cbe,chbe),
      LENGTH cys,IntRet ir child_out,T,SOME child_out.vs_gas_readings)) |+
    ((a,e),(bb,bt,ps,xs,ys,sched,pin,h0,SOME(be,hbe),SUC n,
      OK (caller_post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
  calls' = calls |+ ((a,e,cid),
    (q,call_h,b0,done,child_entry,SOME(ir,child_out,caller_post))) /\
  ms_tab' = ms_tab /\
  (!a e cid q h b done entry ret
      bb bt ps xs ys sched in_state bh be hbe count front closed brest ms.
    FLOOKUP calls (a,e,cid) = SOME(q,h,b,done,entry,ret) /\
    FLOOKUP blocks (a,e) =
      SOME(bb,bt,ps,xs,ys,sched,in_state,bh,SOME(be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms ==>
    !F kgss tail u.
      N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b) /\
      (!callee args. setup_callee callee args (u with vs_gas_readings := b.vs_gas_readings) =
        setup_callee callee args b)) ==>
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
        setup_callee callee args b))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP calls' (aa,ee,cc) = SOME(qq,hh,ss,dd,ent,rr)` >>
  Cases_on `(aa,ee) = (a,e)` >>
  Cases_on `(aa,ee) = (b,d)` >>
  Cases_on `(aa,ee,cc) = (a,e,cid)` >>
  gvs[FLOOKUP_UPDATE] >>
  first_x_assum drule >> disch_then drule >> simp[]
QED

(* A returned record is never lost: the overwritten call was still pending.
   The only new eligible parent index is the just-returned call. *)
Theorem dft_packet_return_completed_tables:
  b = (e,cid)::a /\
  FLOOKUP (blocks : (((num # num) list # num),
    basic_block # basic_block # instruction list # instruction list #
    instruction list # num list # venom_state # num #
    (venom_state # num) option # num # exec_result # bool #
    bytes32 list option) fmap) (b,d) =
    SOME(cbb,cbt,cps,cxs,cys,csched,cin,ch0,SOME(cbe,chbe),cn,OK s,F,NONE) /\
  FLOOKUP blocks (a,e) =
    SOME(bb,bt,ps,xs,ys,sched,pin,h0,SOME(be,hbe),n,OK b0,F,NONE) /\
  FLOOKUP (calls : (gas_event,
    num # num # venom_state # num list # venom_state #
    (internal_return # venom_state # venom_state) option) fmap)
    (a,e,cid) = SOME(q,call_h,b0,done,child_entry,NONE) /\
  blocks' = blocks |+
    ((b,d),(cbb,cbt,cps,cxs,cys,csched,cin,ch0,SOME(cbe,chbe),
      LENGTH cys,IntRet ir child_out,T,SOME child_out.vs_gas_readings)) |+
    ((a,e),(bb,bt,ps,xs,ys,sched,pin,h0,SOME(be,hbe),SUC n,
      OK (caller_post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
  calls' = calls |+ ((a,e,cid),
    (q,call_h,b0,done,child_entry,SOME(ir,child_out,caller_post))) /\
  q = EL n sched /\ q < LENGTH xs /\ n < LENGTH sched /\
  (EL q xs).inst_id = cid /\ (EL q xs).inst_opcode = INVOKE /\
  (!r. r < LENGTH cxs /\ (EL r cxs).inst_opcode = INVOKE ==>
    MEM r (TAKE cn csched) /\
    ?h b0 done entry ir out post.
      FLOOKUP calls (b,d,(EL r cxs).inst_id) =
        SOME(r,h,b0,done,entry,SOME(ir,out,post))) /\
  (!a e bb bt ps xs ys sched in_state h0 be hbe count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME(bb,bt,ps,xs,ys,sched,in_state,h0,SOME(be,hbe),count,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
      MEM q (TAKE count sched) ==>
      ?h b0 done entry ir out post.
        FLOOKUP calls (a,e,(EL q xs).inst_id) =
          SOME(q,h,b0,done,entry,SOME(ir,out,post))) ==>
  (!a e bb bt ps xs ys sched in_state h0 be hbe count front closed brest.
    FLOOKUP blocks' (a,e) =
      SOME(bb,bt,ps,xs,ys,sched,in_state,h0,SOME(be,hbe),count,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
      MEM q (TAKE count sched) ==>
      ?h b0 done entry ir out post.
        FLOOKUP calls' (a,e,(EL q xs).inst_id) =
          SOME(q,h,b0,done,entry,SOME(ir,out,post)))
Proof
  strip_tac >>
  `!aa ee rr rrr hh ss dd ent irr out post.
    FLOOKUP calls (aa,ee,rr) = SOME(rrr,hh,ss,dd,ent,SOME(irr,out,post)) ==>
    FLOOKUP calls' (aa,ee,rr) = SOME(rrr,hh,ss,dd,ent,SOME(irr,out,post))` by
    (rpt strip_tac >> Cases_on `(a,e,cid) = (aa,ee,rr)` >>
     gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP blocks' (aa,ee) = SOME(bba,bta,psa,xsa,ysa,scheda,ina,ha,
    SOME(bea,hbea),cnt,fr,cl,rest)` >>
  Cases_on `(aa,ee) = (a,e)`
  >- (gvs[FLOOKUP_UPDATE,TAKE_SUC_BY_TAKE,MEM_SNOC] >>
      rename1 `MEM rq (TAKE n sched)` >>
      qpat_x_assum `!a e bb bt ps xs ys sched in_state h0 be hbe count front closed brest. _`
        drule >> disch_then (qspec_then `rq` mp_tac) >>
      simp[] >> metis_tac[]) >>
  Cases_on `(aa,ee) = (b,d)`
  >- (gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
  gvs[FLOOKUP_UPDATE] >> metis_tac[]
QED
