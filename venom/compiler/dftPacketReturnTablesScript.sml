Theory dftPacketReturnTables
Ancestors
  dftGasFromListTraceDefs venomExecSemantics venomState venomInst
  finite_map list pred_set

(* Returning changes completion fields, not the retained execution tree or
   the instruction-indexed mask/site/key arrays. *)
Theorem dft_packet_return_tables:
  !(acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls:(gas_event,
      num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ms_tab:(((num # num) list # num),bytes32 option list list) fmap)
    (es_tab:(((num # num) list # num),(string # num) list list) fmap)
    (ks_tab:(((num # num) list # num),gas_event list list) fmap)
    a b e cid d csf ctf child_entry child_order
    cbb cbt cps cxs cys cschedule cin ch0 cbe chbe cn_done s
    bb bt ps xs ys schedule pin h0 be hbe n_done b0
    q call_h done ir child_out caller_post.
    b = (e,cid)::a /\
    FLOOKUP acts b = SOME (csf,ctf,e,child_entry,child_order,NONE,NONE) /\
    FLOOKUP blocks (b,d) =
      SOME (cbb,cbt,cps,cxs,cys,cschedule,cin,ch0,SOME (cbe,chbe),cn_done,OK s,F,NONE) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,schedule,pin,h0,SOME (be,hbe),n_done,OK b0,F,NONE) /\
    FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done,child_entry,NONE) ==>
    ?acts' blocks' calls' ms_tab' es_tab' ks_tab'.
      acts' = acts |+ (b,(csf,ctf,e,child_entry,child_order,
        SOME (IntRet ir child_out),SOME child_out.vs_gas_readings)) /\
      blocks' = blocks |+
        ((b,d),(cbb,cbt,cps,cxs,cys,cschedule,cin,ch0,SOME (cbe,chbe),
          LENGTH cys,IntRet ir child_out,T,SOME child_out.vs_gas_readings)) |+
        ((a,e),(bb,bt,ps,xs,ys,schedule,pin,h0,SOME (be,hbe),SUC n_done,
          OK (caller_post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
      calls' = calls |+ ((a,e,cid),
        (q,call_h,b0,done,child_entry,SOME (ir,child_out,caller_post))) /\
      ms_tab' = ms_tab /\ es_tab' = es_tab /\ ks_tab' = ks_tab /\
      FLOOKUP acts' b = SOME (csf,ctf,e,child_entry,child_order,
        SOME (IntRet ir child_out),SOME child_out.vs_gas_readings) /\
      FLOOKUP blocks' (b,d) =
        SOME (cbb,cbt,cps,cxs,cys,cschedule,cin,ch0,SOME (cbe,chbe),
          LENGTH cys,IntRet ir child_out,T,SOME child_out.vs_gas_readings) /\
      FLOOKUP blocks' (a,e) =
        SOME (bb,bt,ps,xs,ys,schedule,pin,h0,SOME (be,hbe),SUC n_done,
          OK (caller_post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE) /\
      FLOOKUP calls' (a,e,cid) =
        SOME (q,call_h,b0,done,child_entry,SOME (ir,child_out,caller_post)) /\
      (!x. x <> b ==> FLOOKUP acts' x = FLOOKUP acts x) /\
      (!x f. (x,f) <> (b,d) /\ (x,f) <> (a,e) ==>
        FLOOKUP blocks' (x,f) = FLOOKUP blocks (x,f)) /\
      (!key. key <> (a,e,cid) ==> FLOOKUP calls' key = FLOOKUP calls key) /\
      FDOM acts' = FDOM acts /\ FDOM blocks' = FDOM blocks /\
      FDOM calls' = FDOM calls /\ FDOM ms_tab' = FDOM ms_tab /\
      FDOM es_tab' = FDOM es_tab /\ FDOM ks_tab' = FDOM ks_tab /\
      (!x. FST (SND (SND (SND (SND (THE (FLOOKUP acts' x)))))) =
        FST (SND (SND (SND (SND (THE (FLOOKUP acts x))))))) /\
      (!x.
        FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (x,f))))
          (FST (SND (SND (SND (SND (THE (FLOOKUP acts' x)))))))) =
        FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (x,f))))
          (FST (SND (SND (SND (SND (THE (FLOOKUP acts x))))))))) /\
      (!x.
        FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (x,f))))
          (FST (SND (SND (SND (SND (THE (FLOOKUP acts' x)))))))) =
        FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (x,f))))
          (FST (SND (SND (SND (SND (THE (FLOOKUP acts x))))))))) /\
      (!x.
        FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (x,f))))
          (FST (SND (SND (SND (SND (THE (FLOOKUP acts' x)))))))) =
        FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (x,f))))
          (FST (SND (SND (SND (SND (THE (FLOOKUP acts x)))))))))
Proof
  rpt gen_tac >> strip_tac >>
  `b <> a` by (strip_tac >> gvs[]) >>
  `b IN FDOM acts /\ (b,d) IN FDOM blocks /\ (a,e) IN FDOM blocks /\
   (a,e,cid) IN FDOM calls` by metis_tac[FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  qexistsl
    [`acts |+ (b,(csf,ctf,e,child_entry,child_order,
        SOME (IntRet ir child_out),SOME child_out.vs_gas_readings))`,
     `blocks |+
        ((b,d),(cbb,cbt,cps,cxs,cys,cschedule,cin,ch0,SOME (cbe,chbe),
          LENGTH cys,IntRet ir child_out,T,SOME child_out.vs_gas_readings)) |+
        ((a,e),(bb,bt,ps,xs,ys,schedule,pin,h0,SOME (be,hbe),SUC n_done,
          OK (caller_post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE))`,
     `calls |+ ((a,e,cid),
        (q,call_h,b0,done,child_entry,SOME (ir,child_out,caller_post)))`,
     `ms_tab`,`es_tab`,`ks_tab`] >>
  simp[FLOOKUP_UPDATE,FDOM_EQ_FDOM_FUPDATE] >>
  rpt conj_tac >> rpt gen_tac >> Cases_on `x = b` >> gvs[] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED
