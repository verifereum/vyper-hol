Theory dftPacketBlockReplayClosed
Ancestors
  dftPacketPseudoReplayFrame finite_map arithmetic list rich_list

(* The closing row is supplied locally, at the new threshold.  All other
   closed rows retain their literal records and their three row tables. *)
Theorem dft_packet_block_closed_replay_frame:
  !N N' C7 C8 p d acts acts' blocks blocks' ms_tab es_tab ks_tab
    ms_tab' es_tab' ks_tab'.
  N <= N' /\
  (!a e bb bt ps xs ys sched hin h be hb cnt r8 u0 ms ess ks.
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,r8,T,SOME u0) /\
    FLOOKUP ms_tab' (a,e) = SOME ms /\
    FLOOKUP es_tab' (a,e) = SOME ess /\
    FLOOKUP ks_tab' (a,e) = SOME ks /\ (a,e) <> (p,d) ==>
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,r8,T,SOME u0) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP es_tab (a,e) = SOME ess /\
    FLOOKUP ks_tab (a,e) = SOME ks) /\
  (!a sf tf inc entry order res rest.
    FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,rest) ==>
    ?old_order old_res old_rest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,old_order,old_res,old_rest)) /\
  (!a e sf tf inc entry order res rest
      bb bt ps xs ys sched hin h be hb cnt r8 u0 ms ess ks.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,r8,T,SOME u0) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP es_tab (a,e) = SOME ess /\
    FLOOKUP ks_tab (a,e) = SOME ks ==>
    terminates r8 /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ u0) be.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (FLAT ms) /\ u0 = v.vs_gas_readings) /\
    (!F. N <= F ==>
      FOLDR (dft_exec_cons (F-e) C8) OK ys be = r8 /\
      (!gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
        (?extra. FLAT ess =
          gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) ==>
          terminates (FOLDR (dft_exec_cons (F-e) C7) OK xs
            (be with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (FOLDR (dft_exec_cons (F-e) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)))
            (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
            residual_result tail r8
              (FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail)))) /\
        (!v. (FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = OK v \/
              ?ir. FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          dftGasFromListTraceDefs$trace_gas
            (dftGasFromListTraceDefs$trace_block a e (F-e) C7 sf
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs))))) /\
  (!sf tf inc entry order res rest
      bb bt ps xs ys sched hin h be hb cnt r8 u0 ms ess ks.
    FLOOKUP acts' p = SOME (sf,tf,inc,entry,order,res,rest) /\
    FLOOKUP blocks' (p,d) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,r8,T,SOME u0) /\
    FLOOKUP ms_tab' (p,d) = SOME ms /\
    FLOOKUP es_tab' (p,d) = SOME ess /\
    FLOOKUP ks_tab' (p,d) = SOME ks ==>
    terminates r8 /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ u0) be.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (FLAT ms) /\ u0 = v.vs_gas_readings) /\
    (!F. N' <= F ==>
      FOLDR (dft_exec_cons (F-d) C8) OK ys be = r8 /\
      (!gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
        (?extra. FLAT ess =
          gas_events_block (F-d) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) ==>
          terminates (FOLDR (dft_exec_cons (F-d) C7) OK xs
            (be with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (FOLDR (dft_exec_cons (F-d) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)))
            (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_block (F-d) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
            residual_result tail r8
              (FOLDR (dft_exec_cons (F-d) C7) OK xs
                (be with vs_gas_readings := gs ++ tail)))) /\
        (!v. (FOLDR (dft_exec_cons (F-d) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = OK v \/
              ?ir. FOLDR (dft_exec_cons (F-d) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          dftGasFromListTraceDefs$trace_gas
            (dftGasFromListTraceDefs$trace_block p d (F-d) C7 sf
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs))))) ==>
  (!a e sf tf inc entry order res rest
      bb bt ps xs ys sched hin h be hb cnt r8 u0 ms ess ks.
    FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,rest) /\
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,r8,T,SOME u0) /\
    FLOOKUP ms_tab' (a,e) = SOME ms /\
    FLOOKUP es_tab' (a,e) = SOME ess /\
    FLOOKUP ks_tab' (a,e) = SOME ks ==>
    terminates r8 /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ u0) be.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (FLAT ms) /\ u0 = v.vs_gas_readings) /\
    (!F. N' <= F ==>
      FOLDR (dft_exec_cons (F-e) C8) OK ys be = r8 /\
      (!gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
        (?extra. FLAT ess =
          gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) ==>
          terminates (FOLDR (dft_exec_cons (F-e) C7) OK xs
            (be with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (FOLDR (dft_exec_cons (F-e) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)))
            (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
            residual_result tail r8
              (FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail)))) /\
        (!v. (FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = OK v \/
              ?ir. FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          dftGasFromListTraceDefs$trace_gas
            (dftGasFromListTraceDefs$trace_block a e (F-e) C7 sf
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs)))))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `(a,e) = (p,d)`
  >- (qpat_x_assum `(a,e) = (p,d)`
        (strip_assume_tac o SIMP_RULE pure_ss [pairTheory.PAIR_EQ]) >>
      qpat_x_assum `a = p` SUBST_ALL_TAC >>
      qpat_x_assum `e = d` SUBST_ALL_TAC >>
      first_x_assum irule >> rpt (first_assum (irule_at Any))) >>
  qpat_x_assum `!sf tf inc entry order res rest bb bt ps xs ys sched hin h be hb cnt r8 u0 ms ess ks. _` kall_tac >>
  qpat_x_assum `!a e bb bt ps xs ys sched hin h be hb cnt r8 u0 ms ess ks. _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!a sf tf inc entry order res rest. _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!a e sf tf inc entry order res rest bb bt ps xs ys sched hin h be hb cnt r8 u0 ms ess ks. _`
    (drule_all_then strip_assume_tac) >>
  asm_rewrite_tac[] >> qx_gen_tac `fuel` >> disch_tac >>
  qpat_x_assum `!F. N <= F ==> _` (qspec_then `fuel` mp_tac) >>
  (impl_tac >- decide_tac) >> disch_then ACCEPT_TAC
QED

(* Completed activations are not live path suffixes.  Only their aggregates,
   not the aggregates of live activations, are required to be equal. *)
Theorem dft_packet_block_closed_activation_frame:
  !N N' C7 C8 acts acts' AM AE AK AM' AE' AK'.
  N <= N' /\
  (!a sf tf inc entry order r8 u0.
    FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) /\
    AM' a = AM a /\ AE' a = AE a /\ AK' a = AK a) /\
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
          dftGasFromListTraceDefs$trace_gas
            (dftGasFromListTraceDefs$trace_blocks a inc (F-inc) C7 sf
              (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK a,gs))))) ==>
  (!a sf tf inc entry order r8 u0.
    FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
    terminates r8 /\
    LENGTH (AM' a) = LENGTH (AE' a) /\ LENGTH (AM' a) = LENGTH (AK' a) /\
    PERM (MAP THE (FILTER IS_SOME (AM' a)) ++ u0) entry.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (AM' a) /\ u0 = v.vs_gas_readings) /\
    (!F. N' <= F ==>
      run_blocks (F-inc) C8 tf entry = r8 /\
      (!gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM' a) gs ==>
        (?extra. AE' a = gas_events_blocks (F-inc) C7 sf
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
              (entry with vs_gas_readings := gs ++ tail) = AE' a /\
            residual_result tail r8
              (run_blocks (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail)))) /\
        (!v. (run_blocks (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail) = OK v \/
              ?ir. run_blocks (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          dftGasFromListTraceDefs$trace_gas
            (dftGasFromListTraceDefs$trace_blocks a inc (F-inc) C7 sf
              (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK' a,gs)))))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  qpat_x_assum `!a sf tf inc entry order r8 u0. FLOOKUP acts' a = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!a sf tf inc entry order r8 u0. _`
    (drule_then strip_assume_tac) >>
  asm_rewrite_tac[] >> (conj_tac >- metis_tac[]) >>
  qx_gen_tac `fuel` >> disch_tac >>
  qpat_x_assum `!F. N <= F ==> _` (qspec_then `fuel` mp_tac) >>
  (impl_tac >- decide_tac) >> disch_then ACCEPT_TAC
QED

(* A pending cell is replaced by the FINAL child aggregate.  At a returned
   cell the old call record identifies a completed child, so completed-only
   aggregate framing is sufficient. *)
Theorem dft_packet_block_invoke_cell_transport[local]:
  !calls acts AM AE AK AM' AE' AK' a e cid m es ks m' es' ks'.
  (case FLOOKUP calls (a,e,cid) of
    NONE => m = [] /\ es = [] /\ ks = []
  | SOME call => m = AM ((e,cid)::a) /\ es = AE ((e,cid)::a) /\
      ks = AK ((e,cid)::a)) /\
  (~(?q h b done child.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,NONE)) ==>
    m' = m /\ es' = es /\ ks' = ks) /\
  (!q h b done child.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,NONE) ==>
    m' = AM' ((e,cid)::a) /\ es' = AE' ((e,cid)::a) /\
    ks' = AK' ((e,cid)::a)) /\
  (!q h b done child ir child_out caller_post.
    FLOOKUP calls (a,e,cid) =
      SOME (q,h,b,done,child,SOME (ir,child_out,caller_post)) ==>
    ?csf ctf order rest.
      FLOOKUP acts ((e,cid)::a) =
        SOME (csf,ctf,e,child,order,SOME (IntRet ir child_out),rest)) /\
  (!a sf tf inc entry order r8 rest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,rest) ==>
    AM' a = AM a /\ AE' a = AE a /\ AK' a = AK a) ==>
  (case FLOOKUP calls (a,e,cid) of
    NONE => m' = [] /\ es' = [] /\ ks' = []
  | SOME call => m' = AM' ((e,cid)::a) /\ es' = AE' ((e,cid)::a) /\
      ks' = AK' ((e,cid)::a))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP calls (a,e,cid)`
  >- (fs[] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  PairCases_on `x` >>
  Cases_on `x5`
  >- (simp[] >> metis_tac[]) >>
  PairCases_on `x` >> fs[] >>
  qpat_x_assum `!a sf tf inc entry order r8 rest. _`
    (drule_then strip_assume_tac) >>
  fs[] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

(* The two exceptional rows have their own cell and completion certificates:
   the old last row changes its cnt, and the fresh row has no old record.
   Everywhere else the row record (including cnt) is unchanged. *)
Theorem dft_packet_block_invoke_frame:
  !p d acts blocks blocks' calls AM AE AK AM' AE' AK'
    ms_tab es_tab ks_tab ms_tab' es_tab' ks_tab'.
  (!a e bb bt ps xs ys sched hin h be hb cnt front closed brest ms' ess' ks'.
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,front,closed,brest) /\
    FLOOKUP ms_tab' (a,e) = SOME ms' /\
    FLOOKUP es_tab' (a,e) = SOME ess' /\
    FLOOKUP ks_tab' (a,e) = SOME ks' /\
    (a,e) <> (p,d) /\ (a,e) <> (p,SUC d) ==>
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,front,closed,brest) /\
    ?ms ess ks.
      FLOOKUP ms_tab (a,e) = SOME ms /\
      FLOOKUP es_tab (a,e) = SOME ess /\
      FLOOKUP ks_tab (a,e) = SOME ks /\
      (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
        ~(?cq ch b done child.
          FLOOKUP calls (a,e,(EL q xs).inst_id) =
            SOME (cq,ch,b,done,child,NONE)) ==>
        EL q ms' = EL q ms /\ EL q ess' = EL q ess /\ EL q ks' = EL q ks)) /\
  (!a e bb bt ps xs ys sched hin h be hb cnt front closed brest.
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,front,closed,brest) /\
    (a,e) <> (p,d) /\ (a,e) <> (p,SUC d) ==>
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,front,closed,brest)) /\
  (!a e bb bt ps xs ys sched hin h be hb cnt front closed brest ms ess ks q.
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,front,closed,brest) /\
    FLOOKUP ms_tab' (a,e) = SOME ms /\
    FLOOKUP es_tab' (a,e) = SOME ess /\
    FLOOKUP ks_tab' (a,e) = SOME ks /\
    q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
    !cq ch b done child.
      FLOOKUP calls (a,e,(EL q xs).inst_id) =
        SOME (cq,ch,b,done,child,NONE) ==>
      EL q ms = AM' ((e,(EL q xs).inst_id)::a) /\
      EL q ess = AE' ((e,(EL q xs).inst_id)::a) /\
      EL q ks = AK' ((e,(EL q xs).inst_id)::a)) /\
  (!a e cid q h b done child ir child_out caller_post.
    FLOOKUP calls (a,e,cid) =
      SOME (q,h,b,done,child,SOME (ir,child_out,caller_post)) ==>
    ?csf ctf order rest.
      FLOOKUP acts ((e,cid)::a) =
        SOME (csf,ctf,e,child,order,SOME (IntRet ir child_out),rest)) /\
  (!a sf tf inc entry order r8 rest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,rest) ==>
    AM' a = AM a /\ AE' a = AE a /\ AK' a = AK a) /\
  (!a e bb bt ps xs ys sched hin h be hb cnt front closed brest ms ess ks.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP es_tab (a,e) = SOME ess /\
    FLOOKUP ks_tab (a,e) = SOME ks ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
      (case FLOOKUP calls (a,e,(EL q xs).inst_id) of
        NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
      | SOME call =>
          EL q ms = AM ((e,(EL q xs).inst_id)::a) /\
          EL q ess = AE ((e,(EL q xs).inst_id)::a) /\
          EL q ks = AK ((e,(EL q xs).inst_id)::a))) /\
  (!a e bb bt ps xs ys sched hin h be hb cnt front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
      MEM q (TAKE cnt sched) ==>
      ?h b0 done_at_call child_entry ir child_out caller_post.
        FLOOKUP calls (a,e,(EL q xs).inst_id) =
          SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post))) /\
  (!e bb bt ps xs ys sched hin h be hb cnt front closed brest ms ess ks.
    (e = d \/ e = SUC d) /\
    FLOOKUP blocks' (p,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,front,closed,brest) /\
    FLOOKUP ms_tab' (p,e) = SOME ms /\
    FLOOKUP es_tab' (p,e) = SOME ess /\
    FLOOKUP ks_tab' (p,e) = SOME ks ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
      (case FLOOKUP calls (p,e,(EL q xs).inst_id) of
        NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
      | SOME call =>
          EL q ms = AM' ((e,(EL q xs).inst_id)::p) /\
          EL q ess = AE' ((e,(EL q xs).inst_id)::p) /\
          EL q ks = AK' ((e,(EL q xs).inst_id)::p))) /\
  (!e bb bt ps xs ys sched hin h be hb cnt front closed brest.
    (e = d \/ e = SUC d) /\
    FLOOKUP blocks' (p,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
      MEM q (TAKE cnt sched) ==>
      ?h b0 done_at_call child_entry ir child_out caller_post.
        FLOOKUP calls (p,e,(EL q xs).inst_id) =
          SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post))) ==>
  (!a e bb bt ps xs ys sched hin h be hb cnt front closed brest ms ess ks.
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,front,closed,brest) /\
    FLOOKUP ms_tab' (a,e) = SOME ms /\
    FLOOKUP es_tab' (a,e) = SOME ess /\
    FLOOKUP ks_tab' (a,e) = SOME ks ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
      (case FLOOKUP calls (a,e,(EL q xs).inst_id) of
        NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
      | SOME call =>
          EL q ms = AM' ((e,(EL q xs).inst_id)::a) /\
          EL q ess = AE' ((e,(EL q xs).inst_id)::a) /\
          EL q ks = AK' ((e,(EL q xs).inst_id)::a))) /\
  (!a e bb bt ps xs ys sched hin h be hb cnt front closed brest.
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
      MEM q (TAKE cnt sched) ==>
      ?h b0 done_at_call child_entry ir child_out caller_post.
        FLOOKUP calls (a,e,(EL q xs).inst_id) =
          SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post)))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (map_every qx_gen_tac
        [`a`,`e`,`bb`,`bt`,`ps`,`xs`,`ys`,`sched`,`hin`,`h`,`be`,`hb`,
         `cnt`,`front`,`closed`,`brest`,`ms`,`ess`,`ks`] >>
      strip_tac >> qx_gen_tac `q` >> strip_tac >>
      Cases_on `a = p /\ (e = d \/ e = SUC d)`
      >- (fs[] >> gvs[]) >>
      `FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,front,closed,brest) /\
       ?old_ms old_ess old_ks.
        FLOOKUP ms_tab (a,e) = SOME old_ms /\
        FLOOKUP es_tab (a,e) = SOME old_ess /\
        FLOOKUP ks_tab (a,e) = SOME old_ks /\
        (!r. r < LENGTH xs /\ (EL r xs).inst_opcode = INVOKE /\
          ~(?cq ch b done child.
            FLOOKUP calls (a,e,(EL r xs).inst_id) =
              SOME (cq,ch,b,done,child,NONE)) ==>
          EL r ms = EL r old_ms /\ EL r ess = EL r old_ess /\
          EL r ks = EL r old_ks)` by
        (qpat_x_assum `!a e bb bt ps xs ys sched hin h be hb cnt front closed brest ms' ess' ks'. _`
          irule >> rpt (first_assum (irule_at Any)) >> fs[]) >>
      qpat_x_assum `!a e bb bt ps xs ys sched hin h be hb cnt front closed brest ms ess ks.
        FLOOKUP blocks _ = _ /\ _ ==> _`
        (drule_all_then assume_tac) >>
      (* The activation-map field types do not occur in the cell goal. *)
      Q_TAC (fn callmap => Q_TAC (fn actmap =>
        drule (ISPECL [callmap,actmap] dft_packet_block_invoke_cell_transport))
          `acts`) `calls` >>
      disch_then irule >>
      conj_tac
      >- (qexists `acts` >> conj_tac >- first_assum ACCEPT_TAC >>
          qpat_x_assum `!a e cid q h b done child ir child_out caller_post. _`
            (qspecl_then [`a`,`e`,`(EL q xs).inst_id`] ACCEPT_TAC)) >>
      conj_tac
      >- (rpt gen_tac >> disch_tac >>
          qpat_x_assum `!a e bb bt ps xs ys sched hin h be hb cnt front closed brest ms ess ks q.
            FLOOKUP blocks' _ = _ /\ _ ==> _`
            (drule_all_then ACCEPT_TAC)) >>
      disch_tac >> qpat_x_assum `!r. r < LENGTH xs /\ _ ==> _`
        (drule_all_then ACCEPT_TAC)) >>
  map_every qx_gen_tac
    [`a`,`e`,`bb`,`bt`,`ps`,`xs`,`ys`,`sched`,`hin`,`h`,`be`,`hb`,
     `cnt`,`front`,`closed`,`brest`] >>
  disch_tac >> qx_gen_tac `q` >> strip_tac >>
  Cases_on `a = p /\ (e = d \/ e = SUC d)`
  >- (fs[] >> gvs[]) >>
  `FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,sched,hin,h,SOME (be,hb),cnt,front,closed,brest)` by
    (qpat_x_assum `!a e bb bt ps xs ys sched hin h be hb cnt front closed brest. _ /\ _ ==> _`
      irule >> rpt (first_assum (irule_at Any)) >> fs[]) >>
  qpat_x_assum `!a e bb bt ps xs ys sched hin h be hb cnt front closed brest. FLOOKUP blocks _ = _ ==> _`
    (drule_then mp_tac) >> disch_then irule >> simp[]
QED
