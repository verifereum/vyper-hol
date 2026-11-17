Theory dftPacketPseudoHistoryReplay
Ancestors
  dftPacketPseudoHistoryFrame dftPacketPseudoReplayFrame dftPacketPseudoPrefixFrame
  list rich_list finite_map arithmetic pred_set

(* The concrete final equations, not equality of historical prefixes, are
   the update inputs.  The payload uses the actual retained activation order. *)

Theorem dft_packet_pseudo_history_Q:
  !(blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (acts:((num # num) list,ir_function # ir_function # num # venom_state #
      num list # exec_result option # bytes32 list option) fmap)
    p d inds ms_tab ms_out bb0 bt0 ps0 xs0 ys0 rho0 in0 h0 s
    N C7 a e cid q call_h b0 done_at_call child_entry ret xs be.
    LENGTH inds = LENGTH p /\
    FLOOKUP blocks (p,d) =
      SOME (bb0,bt0,ps0,xs0,ys0,rho0,in0,h0,NONE,0,OK s,F,NONE) /\
    (!i. i < LENGTH p ==>
      ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done_at_call child_entry call_h.
        FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,OK b0,F,NONE) /\
        FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
          SOME (EL i inds,call_h,b0,done_at_call,child_entry,NONE) /\
        dft_fn_rel sf tf /\
        lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
        lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
        bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
        EVERY (\x. is_pseudo x.inst_opcode) ps /\
        EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ LENGTH xs = LENGTH ys /\
        PERM rho (COUNT_LIST (LENGTH xs)) /\
        LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
          from_block [EL q xs] y) rho ys /\
        EL i inds < LENGTH xs /\ (EL (EL i inds) xs).inst_opcode = INVOKE /\
        b0.vs_inst_idx = LENGTH ps + pos /\
        get_instruction bt b0.vs_inst_idx = SOME (EL (EL i inds) xs)) /\
    (!a e cid q h b done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done_at_call,child_entry,ret) ==>
      ?bb bt ps xs ys rho hin h0 be hbe pos front closed brest.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),pos,front,closed,brest) /\
        q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
        (case ret of
          NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
        | SOME triple => MEM q (TAKE pos rho))) /\
    (!i. i < LENGTH p ==>
      ?ms. FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME ms) /\
    (ms_out = ms_tab \/
      ((!a e. (a,e) <> (p,d) /\
         (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
         FLOOKUP ms_out (a,e) = FLOOKUP ms_tab (a,e)) /\
       (!i ms. i < LENGTH p /\
         FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME ms ==>
         FLOOKUP ms_out (DROP (SUC i) p,FST (EL i p)) =
           SOME (LUPDATE (FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_out (DROP i p,e))))
             (FST (SND (SND (SND (SND (THE (FLOOKUP acts (DROP i p)))))))))) (EL i inds) ms)))) /\
    FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done_at_call,child_entry,ret) /\
    (!F kgss tail u.
      N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
        (TAKE q (THE (FLOOKUP ms_tab (a,e)))) kgss /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==>
        eval_operand op u = eval_operand op b0) /\
      (!callee args.
        setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
        setup_callee callee args b0)) ==>
    (!F kgss tail u.
      N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
        (TAKE q (THE (FLOOKUP ms_out (a,e)))) kgss /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==>
        eval_operand op u = eval_operand op b0) /\
      (!callee args.
        setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
        setup_callee callee args b0))
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac dft_packet_pseudo_Q_transport >>
  qexists_tac `THE (FLOOKUP ms_tab (a,e))` >>
  asm_rewrite_tac[] >>
  irule (cj 1 (cj 3 dft_packet_pseudo_prefix_frame)) >>
  rpt (first_assum (irule_at Any)) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `?ms. FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME ms` by metis_tac[] >>
  qpat_assum `!i ms. _` (drule_all_then strip_assume_tac) >> metis_tac[]
QED

Theorem dft_packet_pseudo_history_closed_row:
  !(blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    p d ms_tab es_tab ks_tab ms_out es_out ks_out
    bb0 bt0 ps0 xs0 ys0 rho0 in0 h0 s
    N C7 C8 sf a e bb bt ps xs ys rho hin h be hbe count r8 u0 ms ess ks.
    FLOOKUP blocks (p,d) =
      SOME (bb0,bt0,ps0,xs0,ys0,rho0,in0,h0,NONE,0,OK s,F,NONE) /\
    (!i. i < LENGTH p ==>
      ?bb bt ps xs ys rho hin h be hbe pos b0.
        FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,OK b0,F,NONE)) /\
    ((ms_out = ms_tab /\ es_out = es_tab /\ ks_out = ks_tab) \/
      (!a e. (a,e) <> (p,d) /\
         (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
         FLOOKUP ms_out (a,e) = FLOOKUP ms_tab (a,e) /\
         FLOOKUP es_out (a,e) = FLOOKUP es_tab (a,e) /\
         FLOOKUP ks_out (a,e) = FLOOKUP ks_tab (a,e))) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),count,r8,T,SOME u0) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP es_tab (a,e) = SOME ess /\
    FLOOKUP ks_tab (a,e) = SOME ks /\
    (terminates r8 /\
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
              (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs))))) ==>
    terminates r8 /\
    PERM (MAP THE (FILTER IS_SOME (FLAT (THE (FLOOKUP ms_out (a,e))))) ++ u0) be.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (FLAT (THE (FLOOKUP ms_out (a,e)))) /\ u0 = v.vs_gas_readings) /\
    (!F. N <= F ==>
      FOLDR (dft_exec_cons (F-e) C8) OK ys be = r8 /\
      (!gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (THE (FLOOKUP ms_out (a,e)))) gs ==>
        (?extra. FLAT (THE (FLOOKUP es_out (a,e))) =
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
              (be with vs_gas_readings := gs ++ tail) = FLAT (THE (FLOOKUP es_out (a,e))) /\
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
              (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT (THE (FLOOKUP ks_out (a,e))),gs))))
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac dft_packet_pseudo_closed_row_transport >>
  rpt (first_assum (irule_at Any)) >>
  qexistsl [`ks`,`ess`] >> asm_rewrite_tac[] >> simp[] >>
  `(a,e) <> (p,d)` by (strip_tac >> gvs[]) >>
  `!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))` by
    (rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH p ==> ?bb bt ps xs ys rho hin h be hbe pos b0. _`
       (drule_then strip_assume_tac) >> gvs[]) >>
  qpat_x_assum `!a e. _` (drule_all_then strip_assume_tac) >> simp[]
QED

Theorem dft_packet_pseudo_history_closed_activation:
  !(acts:((num # num) list,ir_function # ir_function # num # venom_state #
      num list # exec_result option # bytes32 list option) fmap)
    p d ms_tab es_tab ks_tab ms_out es_out ks_out AM AE AK AM' AE' AK'
    N C7 C8 a sf tf inc entry order r8 u0.
    (!a sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      (res = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p))))) /\
    ((ms_out = ms_tab /\ es_out = es_tab /\ ks_out = ks_tab) \/
      (!a e. (a,e) <> (p,d) /\
         (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
         FLOOKUP ms_out (a,e) = FLOOKUP ms_tab (a,e) /\
         FLOOKUP es_out (a,e) = FLOOKUP es_tab (a,e) /\
         FLOOKUP ks_out (a,e) = FLOOKUP ks_tab (a,e))) /\
    AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    AE = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    AM' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    AE' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es_out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    AK' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) /\
    (terminates r8 /\
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
    terminates r8 /\
    LENGTH (AM' a) = LENGTH (AE' a) /\ LENGTH (AM' a) = LENGTH (AK' a) /\
    PERM (MAP THE (FILTER IS_SOME (AM' a)) ++ u0) entry.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (AM' a) /\ u0 = v.vs_gas_readings) /\
    (!F. N <= F ==>
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
              (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK' a,gs))))
Proof
  rpt gen_tac >> strip_tac
  >- (`AM' = AM /\ AE' = AE /\ AK' = AK` by simp[] >>
      match_mp_tac dft_packet_pseudo_closed_activation_transport >>
      rpt (first_assum (irule_at Any)) >> asm_rewrite_tac[]) >>
  `~MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p)))` by
    (qpat_x_assum `!a sf tf inc entry order res nrest. _`
      (drule_then mp_tac) >> simp[] >> metis_tac[]) >>
  `!i. i <= LENGTH p ==> a <> DROP i p` by
    (qpat_x_assum `~MEM a _` mp_tac >>
     simp[MEM_GENLIST,LESS_EQ_IFF_LESS_SUC] >> metis_tac[]) >>
  `!e. FLOOKUP ms_out (a,e) = FLOOKUP ms_tab (a,e) /\
        FLOOKUP es_out (a,e) = FLOOKUP es_tab (a,e) /\
        FLOOKUP ks_out (a,e) = FLOOKUP ks_tab (a,e)` by
    (simp[] >> gen_tac >> qpat_x_assum `!a e. _` match_mp_tac >>
     conj_tac
     >- (qpat_x_assum `!i. i <= LENGTH p ==> a <> DROP i p`
           (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
     rpt strip_tac >>
     qpat_x_assum `!i. i <= LENGTH p ==> a <> DROP i p`
       (qspec_then `SUC i` mp_tac) >> gvs[]) >>
  `AM' a = AM a /\ AE' a = AE a /\ AK' a = AK a` by simp[] >>
  match_mp_tac dft_packet_pseudo_closed_activation_transport >>
  rpt (first_assum (irule_at Any)) >> asm_rewrite_tac[]
QED

Theorem dft_packet_pseudo_history_U:
  !(blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (acts:((num # num) list,ir_function # ir_function # num # venom_state #
      num list # exec_result option # bytes32 list option) fmap)
    p d inds ms_tab es_tab ks_tab ms_out es_out ks_out
    bb0 bt0 ps0 xs0 ys0 rho0 in0 h0 s
    N C7 sf a e bb bt ps xs ys rho hin h be hbe count front closed brest.
    LENGTH inds = LENGTH p /\
    FLOOKUP blocks (p,d) =
      SOME (bb0,bt0,ps0,xs0,ys0,rho0,in0,h0,NONE,0,OK s,F,NONE) /\
    (!i. i < LENGTH p ==>
      ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done_at_call child_entry call_h.
        FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,OK b0,F,NONE) /\
        FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
          SOME (EL i inds,call_h,b0,done_at_call,child_entry,NONE) /\
        dft_fn_rel sf tf /\
        lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
        lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
        bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
        EVERY (\x. is_pseudo x.inst_opcode) ps /\
        EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ LENGTH xs = LENGTH ys /\
        PERM rho (COUNT_LIST (LENGTH xs)) /\
        LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
          from_block [EL q xs] y) rho ys /\
        EL i inds < LENGTH xs /\ (EL (EL i inds) xs).inst_opcode = INVOKE /\
        b0.vs_inst_idx = LENGTH ps + pos /\
        get_instruction bt b0.vs_inst_idx = SOME (EL (EL i inds) xs)) /\
    (!a e cid q h b done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done_at_call,child_entry,ret) ==>
      ?bb bt ps xs ys rho hin h0 be hbe pos front closed brest.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),pos,front,closed,brest) /\
        q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
        (case ret of
          NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
        | SOME triple => MEM q (TAKE pos rho))) /\
    (!i. i < LENGTH p ==>
      ?ms es ks.
        FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME ms /\
        FLOOKUP es_tab (DROP (SUC i) p,FST (EL i p)) = SOME es /\
        FLOOKUP ks_tab (DROP (SUC i) p,FST (EL i p)) = SOME ks) /\
    ((ms_out = ms_tab /\ es_out = es_tab /\ ks_out = ks_tab) \/
      ((!a e. (a,e) <> (p,d) /\
         (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
         FLOOKUP ms_out (a,e) = FLOOKUP ms_tab (a,e) /\
         FLOOKUP es_out (a,e) = FLOOKUP es_tab (a,e) /\
         FLOOKUP ks_out (a,e) = FLOOKUP ks_tab (a,e)) /\
       (!i ms es ks. i < LENGTH p /\
         FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME ms /\
         FLOOKUP es_tab (DROP (SUC i) p,FST (EL i p)) = SOME es /\
         FLOOKUP ks_tab (DROP (SUC i) p,FST (EL i p)) = SOME ks ==>
         FLOOKUP ms_out (DROP (SUC i) p,FST (EL i p)) =
           SOME (LUPDATE (FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_out (DROP i p,e))))
             (FST (SND (SND (SND (SND (THE (FLOOKUP acts (DROP i p)))))))))) (EL i inds) ms) /\
         FLOOKUP es_out (DROP (SUC i) p,FST (EL i p)) =
           SOME (LUPDATE (FLAT (MAP (\e. FLAT (THE (FLOOKUP es_out (DROP i p,e))))
             (FST (SND (SND (SND (SND (THE (FLOOKUP acts (DROP i p)))))))))) (EL i inds) es) /\
         FLOOKUP ks_out (DROP (SUC i) p,FST (EL i p)) =
           SOME (LUPDATE (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_out (DROP i p,e))))
             (FST (SND (SND (SND (SND (THE (FLOOKUP acts (DROP i p)))))))))) (EL i inds) ks)))) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),count,front,closed,brest) /\
    (!F k kgss tail.
      N <= F /\ k <= LENGTH xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE count rho)) /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
        (TAKE k (THE (FLOOKUP ms_tab (a,e)))) kgss ==>
      (?extra. FLAT (TAKE k (THE (FLOOKUP es_tab (a,e)))) =
        gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
      (!u. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k (THE (FLOOKUP es_tab (a,e)))) /\
        u.vs_gas_readings = tail /\
        dftGasFromListTraceDefs$trace_gas
          (dftGasFromListTraceDefs$trace_block a e (F-e) C7 sf
            (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
            (be with vs_gas_readings := FLAT kgss ++ tail)) =
          ZIP (FLAT (TAKE k (THE (FLOOKUP ks_tab (a,e)))),FLAT kgss) /\
        (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
            (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
          gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k (THE (FLOOKUP es_tab (a,e))))))) ==>
    (!F k kgss tail.
      N <= F /\ k <= LENGTH xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE count rho)) /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
        (TAKE k (THE (FLOOKUP ms_out (a,e)))) kgss ==>
      (?extra. FLAT (TAKE k (THE (FLOOKUP es_out (a,e)))) =
        gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
      (!u. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k (THE (FLOOKUP es_out (a,e)))) /\
        u.vs_gas_readings = tail /\
        dftGasFromListTraceDefs$trace_gas
          (dftGasFromListTraceDefs$trace_block a e (F-e) C7 sf
            (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
            (be with vs_gas_readings := FLAT kgss ++ tail)) =
          ZIP (FLAT (TAKE k (THE (FLOOKUP ks_out (a,e)))),FLAT kgss) /\
        (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
            (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
          gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k (THE (FLOOKUP es_out (a,e)))))))
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac dft_packet_pseudo_U_transport >>
  rpt (first_assum (irule_at Any)) >>
  qexistsl [`THE (FLOOKUP ms_tab (a,e))`,`THE (FLOOKUP es_tab (a,e))`,
    `THE (FLOOKUP ks_tab (a,e))`] >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  irule (cj 1 (cj 2 dft_packet_pseudo_prefix_frame)) >>
  rpt (first_assum (irule_at Any)) >>
  (qexists_tac `calls` >>
   asm_rewrite_tac[] >> conj_tac
   >- metis_tac[] >> rpt strip_tac >>
   `?ms es ks.
      FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME ms /\
      FLOOKUP es_tab (DROP (SUC i) p,FST (EL i p)) = SOME es /\
      FLOOKUP ks_tab (DROP (SUC i) p,FST (EL i p)) = SOME ks` by metis_tac[] >>
   qpat_assum `!i ms es ks. _` (drule_all_then strip_assume_tac) >>
   metis_tac[])
QED
