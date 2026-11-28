Theory dftPacketReturnEdgeClauses
Ancestors
  dftRunRel dftIndexedExec dftGasFromListLookup frameInvokeReturn
  intCallStep venomWf venomInst list rich_list arithmetic
  dftPacketReturnChildClosure dftPacketReturnRootSuccessor
  dftPacketReturnTables dftPacketReturnLiveFrame dftPacketReturnVisitFrame
  dftPacketReturnRecordFrame dftPacketReturnParentRetained o1ScheduleDecompHelpers
  dftPacketReturnHistoricalCuts dftPacketReturnNewCuts
  dftPacketReturnParentCutApplication dftPacketReturnObservation
  dftContractGas dftWf gasOracleReplay stateEquiv
  venomExecSemantics sorting finite_map passSimulationDefs

Theorem dft_packet_return_parent_cursor:
  wf_function tf /\ bb_well_formed bt /\
  bt.bb_instructions = ps ++ ys /\
  lookup_block b0.vs_current_bb tf.fn_blocks = SOME bt /\
  b0.vs_inst_idx = LENGTH ps + cnt /\
  get_instruction bt b0.vs_inst_idx = SOME c /\ c.inst_opcode = INVOKE /\
  decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C8.ctx_functions = SOME child /\
  eval_operands ops b0 = SOME args /\ setup_callee child args b0 = SOME ent /\
  bind_outputs c.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state b0 out)) = SOME caller_post /\
  (!F. N <= F ==> run_blocks (F-e) C8 child ent = IntRet ir out) /\
  (!F. N <= F ==>
    FOLDR (dft_exec_cons (F-e) C8) OK (TAKE cnt ys) pbe = OK b0) /\
  active_inst tf next (caller_post with vs_inst_idx := SUC b0.vs_inst_idx) ==>
  c = EL cnt ys /\ SUC cnt < LENGTH ys /\ next = EL (SUC cnt) ys /\
  lookup_block caller_post.vs_current_bb tf.fn_blocks = SOME bt /\
  get_instruction bt (SUC b0.vs_inst_idx) = SOME next /\
  (!F. N <= F ==>
    FOLDR (dft_exec_cons (F-e) C8) OK (TAKE (SUC cnt) ys) pbe =
      OK (caller_post with vs_inst_idx := SUC b0.vs_inst_idx))
Proof
  strip_tac >>
  `cnt < LENGTH ys /\ c = EL cnt ys` by
    gvs[get_instruction_def, EL_APPEND2] >>
  `!F. N <= F ==> step_inst (F-e) C8 c b0 = OK caller_post` by
    (rpt strip_tac >> irule (cj 1 matched_run_invoke_return) >>
     metis_tac[]) >>
  `caller_post.vs_current_bb = b0.vs_current_bb` by
    (qpat_assum `!F. N <= F ==> step_inst _ _ _ _ = _`
      (qspec_then `N` (assume_tac o SRULE [])) >>
     drule_all (cj 1 step_inst_invoke_OK_control) >> simp[]) >>
  `get_instruction bt (SUC b0.vs_inst_idx) = SOME next` by
    (drule_all wf_active_lookup >> simp[] >> metis_tac[]) >>
  `SUC cnt < LENGTH ys /\ next = EL (SUC cnt) ys` by
    (`SUC b0.vs_inst_idx = LENGTH ps + SUC cnt` by decide_tac >>
     qpat_assum `get_instruction bt (SUC _) = SOME next` mp_tac >>
     qpat_assum `SUC b0.vs_inst_idx = _` (fn th => pure_rewrite_tac[th]) >>
     simp[get_instruction_def, EL_APPEND2]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE cnt ys)` by
    (simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
     qpat_assum `bb_well_formed bt`
       (qspec_then `LENGTH ps + n` mp_tac o cj 3 o
        REWRITE_RULE [bb_well_formed_def]) >>
     simp[EL_APPEND2] >> decide_tac) >>
  simp[] >> rpt strip_tac >>
  `TAKE (SUC cnt) ys = TAKE cnt ys ++ [EL cnt ys]` by
    simp[TAKE_SUC_BY_TAKE, SNOC_APPEND] >>
  simp[FOLDR_APPEND, Once dft_exec_prefix_continue] >>
  qpat_assum `c = EL cnt ys` (fn th => pure_rewrite_tac[GSYM th]) >>
  simp[dft_exec_cons_def, is_terminator_def]
QED

(* Resume in the same root trace: the successful child run gives the
   caller fold at every budget, and the actual return visit adds no reading. *)
Theorem dft_packet_return_resume:
  o1_ctx_shape C8 /\ MEM root_tf C8.ctx_functions /\
  call_h < j /\ j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL call_h (trace_blocks [] 0 N C8 root_tf root_entry) = ((a,e,c.inst_id),tf,c,b0) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) = (((e,c.inst_id)::a,d,r.inst_id),child,r,s) /\
  obs = trace_gas (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry)) /\
  root_entry.vs_gas_readings = MAP SND obs ++ s.vs_gas_readings /\
  MEM r.inst_opcode [RET;RETFMP;DRET] /\
  step_inst fuel C8 r s = IntRet ir out /\
  wf_function tf /\ bb_well_formed bt /\ bt.bb_instructions = ps ++ ys /\
  lookup_block b0.vs_current_bb tf.fn_blocks = SOME bt /\
  b0.vs_inst_idx = LENGTH ps + cnt /\
  get_instruction bt b0.vs_inst_idx = SOME c /\ c.inst_opcode = INVOKE /\
  decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME child /\
  eval_operands ops b0 = SOME args /\ setup_callee child args b0 = SOME ent /\
  bind_outputs c.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state b0 out)) = SOME caller_post /\
  (!F. N <= F ==> run_blocks (F-e) C8 child ent = IntRet ir out) /\
  (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE cnt ys) pbe = OK b0) /\
  active_inst tf next (caller_post with vs_inst_idx := SUC b0.vs_inst_idx) ==>
  c = EL cnt ys /\ SUC cnt < LENGTH ys /\ next = EL (SUC cnt) ys /\
  lookup_block (caller_post with vs_inst_idx := SUC b0.vs_inst_idx).vs_current_bb tf.fn_blocks = SOME bt /\
  get_instruction bt (caller_post with vs_inst_idx := SUC b0.vs_inst_idx).vs_inst_idx = SOME next /\
  (caller_post with vs_inst_idx := SUC b0.vs_inst_idx).vs_inst_idx = LENGTH ps + SUC cnt /\
  (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE (SUC cnt) ys) pbe = OK (caller_post with vs_inst_idx := SUC b0.vs_inst_idx)) /\
  call_h + SUC (LENGTH (trace_blocks ((e,c.inst_id)::a) e (N-e) C8 child ent)) = SUC j /\
  SUC j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) = ((a,e,next.inst_id),tf,next,(caller_post with vs_inst_idx := SUC b0.vs_inst_idx)) /\
  trace_gas (TAKE (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry)) = obs /\
  (caller_post with vs_inst_idx := SUC b0.vs_inst_idx).vs_gas_readings = s.vs_gas_readings /\
  root_entry.vs_gas_readings = MAP SND obs ++ (caller_post with vs_inst_idx := SUC b0.vs_inst_idx).vs_gas_readings
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all dft_packet_return_parent_cursor >> strip_tac >>
  `r.inst_opcode <> INVOKE /\ r.inst_opcode <> GAS` by gvs[] >>
  `step_inst_base r s = IntRet ir out` by fs[step_inst_non_invoke] >>
  `step_inst (N-d) C8 r s = IntRet ir out` by simp[step_inst_non_invoke] >>
  `run_blocks (N-e) C8 child ent = IntRet ir out` by simp[] >>
  `EVERY wf_function C8.ctx_functions` by metis_tac[o1_ctx_shape_wf_functions] >>
  `EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
      f.fn_blocks) C8.ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[wf_fn_block_inst_ids_distinct]) >>
  `EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) root_tf.fn_blocks` by
    (fs[EVERY_MEM] >> metis_tac[wf_fn_block_inst_ids_distinct]) >>
  qmatch_asmsub_abbrev_tac `j < LENGTH tr` >>
  `j = call_h + LENGTH (trace_blocks ((e,c.inst_id)::a) e (N-e) C8 child ent) /\
   SUC j < LENGTH tr /\
   EL (SUC j) tr = ((a,e,next.inst_id),tf,next,
     caller_post with vs_inst_idx := SUC b0.vs_inst_idx) /\
   trace_gas (TAKE (SUC j) tr) = trace_gas (TAKE j tr)` by
     (unabbrev_all_tac >>
      irule (CONV_RULE (DEPTH_CONV BETA_CONV)
        (PURE_REWRITE_RULE [LET_THM] dft_packet_return_root_successor)) >>
      rpt (goal_assum $ drule_at Any) >> gvs[ADD_COMM] >>
      gvs[CONV_RULE (DEPTH_CONV BETA_CONV)
        (PURE_REWRITE_RULE [LET_THM] dft_packet_return_root_successor)]) >>
  unabbrev_all_tac >>
  `out.vs_gas_readings = s.vs_gas_readings` by
    (`gas_replay_at 0 (step_inst_base r) s` by (irule gas_base_non_gas >> simp[]) >>
     qpat_x_assum `gas_replay_at 0 (step_inst_base r) s`
       (qspec_then `[]` mp_tac o REWRITE_RULE [gas_replay_at_def]) >>
     simp[gas_prefix_def] >>
     Cases_on `step_inst_base r (s with vs_gas_readings := [])` >> simp[lift_result_def]) >>
  drule gas_bind_outputs_readings >> simp[ADD_COMM] >>
  gvs[ADD_COMM]
QED

(* An earlier closed predecessor is not either of the two formerly open
   rows. Changes to those rows affect only their frontier fields. *)
Theorem dft_packet_return_block_visits:
  b = (e,cid)::a /\
  FLOOKUP (acts : ((num # num) list,
    ir_function # ir_function # num # venom_state # num list #
    exec_result option # bytes32 list option) fmap) b =
      SOME (csf,ctf,e,ent,cord,NONE,NONE) /\
  FLOOKUP (blocks : (((num # num) list # num),
    basic_block # basic_block # instruction list # instruction list #
    instruction list # num list # venom_state # num #
    (venom_state # num) option # num # exec_result # bool # bytes32 list option) fmap)
    (b,d) = SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE) /\
  FLOOKUP blocks (a,e) =
    SOME (pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),pn,OK b0,F,NONE) /\
  acts' = acts |+ (b,(csf,ctf,e,ent,cord,SOME (IntRet ir out),SOME out.vs_gas_readings)) /\
  blocks' = blocks |+
    ((b,d),(cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),
      LENGTH cys,IntRet ir out,T,SOME out.vs_gas_readings)) |+
    ((a,e),(pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),SUC pn,
      OK (post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
  SUC pn < LENGTH pys /\
  (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE (SUC pn) pys) pbe =
    OK (post with vs_inst_idx := SUC b0.vs_inst_idx)) /\
  (!F. N <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK cys cbe = IntRet ir out) /\
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
      (case body of NONE => x = b /\ v = d
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
      (v = LAST order ==> res = (if closed then SOME front else NONE) /\ nrest = brest)) ==>
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
      (v = LAST order ==> res = (if closed then SOME front else NONE) /\ nrest = brest))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x v bb bt ps xs ys rho ini h0 body count dst rest.
    (FLOOKUP blocks' (x,v) = SOME (bb,bt,ps,xs,ys,rho,ini,h0,body,count,OK dst,T,SOME rest)) <=>
    (FLOOKUP blocks (x,v) = SOME (bb,bt,ps,xs,ys,rho,ini,h0,body,count,OK dst,T,SOME rest))` by
    (rpt gen_tac >> Cases_on `(x,v) = (a,e)` >> Cases_on `(x,v) = (b,d)` >>
     gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
  pop_assum (fn th => pure_rewrite_tac [th]) >>
  `d = LAST cord` by
    (qpat_assum `!x v bb bt ps xs ys rho ini h0 body count front closed brest. _`
       (fn th => qpat_assum `FLOOKUP blocks (b,d) = _` (mp_tac o MATCH_MP th)) >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  `a <> b` by (strip_tac >> gvs[]) >>
  Cases_on `(x,v) = (b,d)`
  >- (qpat_x_assum `!x v bb bt ps xs ys rho ini h0 body count front closed brest. _`
        (fn th => qpat_assum `FLOOKUP blocks (b,d) = _` (strip_assume_tac o MATCH_MP th)) >>
      gvs[FLOOKUP_UPDATE] >>
      rpt (goal_assum $ drule_at Any) >>
      simp[terminates_def] >>
      qpat_assum `LENGTH cys = LENGTH cxs` (once_rewrite_tac o single o GSYM) >> simp[]) >>
  Cases_on `(x,v) = (a,e)`
  >- (qpat_x_assum `!x v bb bt ps xs ys rho ini h0 body count front closed brest. _`
        (fn th => qpat_assum `FLOOKUP blocks (a,e) = _` (strip_assume_tac o MATCH_MP th)) >>
      gvs[FLOOKUP_UPDATE] >>
      rpt (goal_assum $ drule_at Any) >> simp[]) >>
  `FLOOKUP blocks' (x,v) = FLOOKUP blocks (x,v)` by
    (qpat_x_assum `FLOOKUP blocks' (x,v) = SOME _` kall_tac >>
     `~((b,d) = (x,v))` by (once_rewrite_tac[EQ_SYM_EQ] >> simp[]) >>
     `~((a,e) = (x,v))` by (once_rewrite_tac[EQ_SYM_EQ] >> simp[]) >>
     qpat_assum `blocks' = _` (fn th => pure_rewrite_tac [th,FLOOKUP_UPDATE]) >>
     simp[]) >>
  pop_assum (fn eq => qpat_x_assum `FLOOKUP blocks' (x,v) = SOME _`
    (assume_tac o REWRITE_RULE [eq])) >>
  qpat_x_assum `!x v bb bt ps xs ys rho ini h0 body count front closed brest. _`
    (fn th => qpat_assum `FLOOKUP blocks (x,v) = SOME _`
      (strip_assume_tac o MATCH_MP th)) >>
  Cases_on `body'` >> gvs[] >>
  rpt (split_pair_case_tac >> gvs[]) >>
  Cases_on `x = (e,cid)::a`
  >- (gvs[FLOOKUP_UPDATE] >>
      rpt (goal_assum $ drule_at Any) >> simp[] >>
      rpt strip_tac >> res_tac >> gvs[]) >>
  `(e,cid)::a <> x` by (once_rewrite_tac[EQ_SYM_EQ] >> simp[]) >>
  gvs[FLOOKUP_UPDATE] >>
  rpt (goal_assum $ drule_at Any) >> simp[] >>
  rpt strip_tac >> res_tac >> gvs[]
QED

(* Semantic part of the return-table join. Closed rows outside (b,d) are
   passed through unchanged; the selected terminal row has one certificate
   shared by the target run and the closed activation's source replay. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qspecl_then [`ms_tab`,`es_tab`,`ks_tab`,`ir`,`out`,`post`]
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
    dft_packet_return_tables >>
  qpat_x_assum `order = cord` SUBST_ALL_TAC >>
  `!f. MEM f cord /\ f <> d ==> FLOOKUP blocks' (b,f) = FLOOKUP blocks (b,f)` by
    (rpt strip_tac >> qpat_assum `!x f. (x,f) <> (b,d) /\ _ ==> _` irule >>
     simp[] >> metis_tac[]) >>
  `terminates (IntRet ir out)` by simp[terminates_def] >>
  `!v. (IntRet ir out = OK v \/ ?ret. IntRet ir out = IntRet ret v) ==>
    EVERY IS_SOME (FLAT cms) /\ out.vs_gas_readings = v.vs_gas_readings` by simp[] >>
  drule_all_then (map_every assume_tac o CONJUNCTS) dft_packet_return_child_closure >>
  qpat_assum `!F. N <= F ==> run_blocks _ _ _ _ = _ /\ _`
    (assume_tac o cj 1) >>
  qpat_x_assum `b = (e,cid)::a` SUBST_ALL_TAC >>
  qpat_x_assum `c.inst_id = cid` (SUBST_ALL_TAC o SYM) >>
  drule_all_then (map_every assume_tac o CONJUNCTS)
    (CONV_RULE (DEPTH_CONV BETA_CONV)
      (PURE_REWRITE_RULE [LET_THM] dft_packet_return_resume)) >>
  qexistsl [`acts'`,`blocks'`,`calls'`,`ms_tab'`,`es_tab'`,`ks_tab'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)
Theorem dft_packet_return_native_tables:
  b = (e,cid)::a /\
  FLOOKUP (acts : ((num # num) list,
    ir_function # ir_function # num # venom_state # num list #
    exec_result option # bytes32 list option) fmap) b =
      SOME (csf,ctf,e,ent,cord,NONE,NONE) /\
  FLOOKUP (blocks : (((num # num) list # num),
    basic_block # basic_block # instruction list # instruction list #
    instruction list # num list # venom_state # num #
    (venom_state # num) option # num # exec_result # bool # bytes32 list option) fmap)
    (b,d) = SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE) /\
  FLOOKUP blocks (a,e) =
    SOME (pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),pn,OK b0,F,NONE) /\
  FLOOKUP (calls : (gas_event, num # num # venom_state # num list # venom_state #
    (internal_return # venom_state # venom_state) option) fmap) (a,e,cid) =
    SOME (q,call_h,b0,done,ent,NONE) /\
  order <> [] /\ order = cord /\ order = GENLIST (\i. e + SUC i) (LENGTH order) /\
  LAST order = d /\ wf_function csf /\ wf_function ctf /\
  FDOM blocks = FDOM ms_tab /\ FDOM blocks = FDOM es_tab /\ FDOM blocks = FDOM ks_tab /\
  (!f. MEM f order ==>
    ?bb bt ps xs ys rho ini h0 body count front closed brest sp.
      FLOOKUP blocks (b,f) =
        SOME (bb,bt,ps,xs,ys,rho,ini,h0,body,count,front,closed,brest) /\
      f <= N /\
      lookup_block bb.bb_label csf.fn_blocks = SOME bb /\
      lookup_block bb.bb_label ctf.fn_blocks = SOME bt /\
      lookup_block ini.vs_current_bb csf.fn_blocks = SOME bb /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\x. is_pseudo x.inst_opcode) ps /\
      EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
      EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
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
      (f <> d ==> closed /\ ?post. front = OK post /\ ~post.vs_halted)) /\
  (!f bb bt ps xs ys rho ini h0 be hbe count front closed brest ms es ks.
    MEM f order /\
    FLOOKUP blocks (b,f) =
      SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (b,f) = SOME ms /\
    FLOOKUP es_tab (b,f) = SOME es /\
    FLOOKUP ks_tab (b,f) = SOME ks ==>
    LIST_REL (\m es. LENGTH m = LENGTH es) ms es /\
    LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks) /\
  (!f bb bt ps xs ys rho ini h0 be hbe count front rest ms es ks.
    MEM f order /\ f <> d /\
    FLOOKUP blocks (b,f) =
      SOME (bb,bt,ps,xs,ys,rho,ini,h0,SOME (be,hbe),count,front,T,SOME rest) /\
    FLOOKUP ms_tab (b,f) = SOME ms /\
    FLOOKUP es_tab (b,f) = SOME es /\
    FLOOKUP ks_tab (b,f) = SOME ks ==>
    terminates front /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ rest) be.vs_gas_readings /\
    (!v. (front = OK v \/ ?ret. front = IntRet ret v) ==>
      EVERY IS_SOME (FLAT ms) /\ rest = v.vs_gas_readings) /\
    (!F. N <= F ==>
      FOLDR (dft_exec_cons (F-f) C8) OK ys be = front /\
      (!gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
        (?extra. FLAT es =
          gas_events_block (F-f) C7 csf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?g. terminates (FOLDR (dft_exec_cons g C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) ==>
          terminates (FOLDR (dft_exec_cons (F-f) C7) OK xs
            (be with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (FOLDR (dft_exec_cons (F-f) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)))
            (restore_result [] front) /\
          (((?v. front = OK v) \/ (?ret v. front = IntRet ret v)) ==>
            gas_events_block (F-f) C7 csf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT es /\
            residual_result tail front
              (FOLDR (dft_exec_cons (F-f) C7) OK xs
                (be with vs_gas_readings := gs ++ tail)))) /\
        (!v. (FOLDR (dft_exec_cons (F-f) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = OK v \/
              ?ret. FOLDR (dft_exec_cons (F-f) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
          trace_gas (trace_block b f (F-f) C7 csf
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs))))) /\
  FLOOKUP ms_tab (b,d) = SOME cms /\ FLOOKUP es_tab (b,d) = SOME ces /\
  FLOOKUP ks_tab (b,d) = SOME cks /\
  PERM (MAP THE (FILTER IS_SOME (FLAT cms)) ++ out.vs_gas_readings) cbe.vs_gas_readings /\
  EVERY IS_SOME (FLAT cms) /\
  (!F. N <= F ==>
    FOLDR (dft_exec_cons (F-d) C8) OK cys cbe = IntRet ir out /\
    (!gs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT cms) gs ==>
      (?extra. FLAT ces =
        gas_events_block (F-d) C7 csf.fn_name
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
        (((?v. IntRet ir out = OK v) \/ (?ret v. IntRet ir out = IntRet ret v)) ==>
          gas_events_block (F-d) C7 csf.fn_name
            <|bb_label := cbe.vs_current_bb; bb_instructions :=
              REPLICATE cbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ cxs|>
            (cbe with vs_gas_readings := gs ++ tail) = FLAT ces /\
          residual_result tail (IntRet ir out)
            (FOLDR (dft_exec_cons (F-d) C7) OK cxs
              (cbe with vs_gas_readings := gs ++ tail)))) /\
      (!v. (FOLDR (dft_exec_cons (F-d) C7) OK cxs
              (cbe with vs_gas_readings := gs ++ tail) = OK v \/
            ?ret. FOLDR (dft_exec_cons (F-d) C7) OK cxs
              (cbe with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
        trace_gas (trace_block b d (F-d) C7 csf
          <|bb_label := cbe.vs_current_bb; bb_instructions :=
            REPLICATE cbe.vs_inst_idx (mk_inst 0 STOP [] []) ++ cxs|>
          (cbe with vs_gas_readings := gs ++ tail)) = ZIP (FLAT cks,gs)))) /\
  AM b = FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (b,f)))) order) /\
  AE b = FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (b,f)))) order) /\
  AK b = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (b,f)))) order) /\
  bind_outputs c.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state b0 out)) = SOME post /\
  o1_ctx_shape C8 /\ MEM root_tf C8.ctx_functions /\
  call_h < j /\ j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL call_h (trace_blocks [] 0 N C8 root_tf root_entry) = ((a,e,cid),tf,c,b0) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) = ((b,d,r.inst_id),ctf,r,s) /\
  obs = trace_gas (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry)) /\
  root_entry.vs_gas_readings = MAP SND obs ++ s.vs_gas_readings /\
  MEM r.inst_opcode [RET;RETFMP;DRET] /\ step_inst fuel C8 r s = IntRet ir out /\
  wf_function tf /\ bb_well_formed pbt /\ pbt.bb_instructions = pps ++ pys /\
  lookup_block b0.vs_current_bb tf.fn_blocks = SOME pbt /\
  b0.vs_inst_idx = LENGTH pps + pn /\ get_instruction pbt b0.vs_inst_idx = SOME c /\
  c.inst_id = cid /\ c.inst_opcode = INVOKE /\
  decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
  eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME ent /\
  (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE pn pys) pbe = OK b0) /\
  active_inst tf next (post with vs_inst_idx := SUC b0.vs_inst_idx) ==>
  ?acts' blocks' calls' ms_tab' es_tab' ks_tab'.
    acts' = acts |+ (b,(csf,ctf,e,ent,cord,SOME (IntRet ir out),SOME out.vs_gas_readings)) /\
    blocks' = blocks |+
      ((b,d),(cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),
        LENGTH cys,IntRet ir out,T,SOME out.vs_gas_readings)) |+
      ((a,e),(pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),SUC pn,
        OK (post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
    calls' = calls |+ ((a,e,cid),(q,call_h,b0,done,ent,SOME (ir,out,post))) /\
    ms_tab' = ms_tab /\ es_tab' = es_tab /\ ks_tab' = ks_tab /\
    FLOOKUP acts' b = SOME (csf,ctf,e,ent,cord,SOME (IntRet ir out),SOME out.vs_gas_readings) /\
    FLOOKUP blocks' (b,d) = SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),
      LENGTH cys,IntRet ir out,T,SOME out.vs_gas_readings) /\
    FLOOKUP blocks' (a,e) = SOME (pbb,pbt,pps,pxs,pys,prho,pin,ph0,SOME (pbe,phbe),SUC pn,
      OK (post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE) /\
    FLOOKUP calls' (a,e,cid) = SOME (q,call_h,b0,done,ent,SOME (ir,out,post)) /\
    (!x. x <> b ==> FLOOKUP acts' x = FLOOKUP acts x) /\
    (!x f. (x,f) <> (b,d) /\ (x,f) <> (a,e) ==>
      FLOOKUP blocks' (x,f) = FLOOKUP blocks (x,f)) /\
    (!key. key <> (a,e,cid) ==> FLOOKUP calls' key = FLOOKUP calls key) /\
    FDOM acts' = FDOM acts /\ FDOM blocks' = FDOM blocks /\ FDOM calls' = FDOM calls /\
    (!x. FST (SND (SND (SND (SND (THE (FLOOKUP acts' x)))))) =
      FST (SND (SND (SND (SND (THE (FLOOKUP acts x))))))) /\
    terminates (IntRet ir out) /\
    LENGTH (AM b) = LENGTH (AE b) /\ LENGTH (AM b) = LENGTH (AK b) /\
    PERM (MAP THE (FILTER IS_SOME (AM b)) ++ out.vs_gas_readings) ent.vs_gas_readings /\
    EVERY IS_SOME (AM b) /\
    (!F. N <= F ==>
      run_blocks (F-e) C8 ctf ent = IntRet ir out /\
      (!gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM b) gs ==>
        (?extra. AE b = gas_events_blocks (F-e) C7 csf
          (ent with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (run_blocks f C7 csf
            (ent with vs_gas_readings := gs ++ tail))) ==>
          terminates (run_blocks (F-e) C7 csf (ent with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (run_blocks (F-e) C7 csf (ent with vs_gas_readings := gs ++ tail)))
            (restore_result [] (IntRet ir out)) /\
          gas_events_blocks (F-e) C7 csf (ent with vs_gas_readings := gs ++ tail) = AE b /\
          residual_result tail (IntRet ir out)
            (run_blocks (F-e) C7 csf (ent with vs_gas_readings := gs ++ tail))) /\
        (!v. (run_blocks (F-e) C7 csf (ent with vs_gas_readings := gs ++ tail) = OK v \/
              ?ret. run_blocks (F-e) C7 csf (ent with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
          trace_gas (trace_blocks b e (F-e) C7 csf
            (ent with vs_gas_readings := gs ++ tail)) = ZIP (AK b,gs)))) /\
    c = EL pn pys /\ SUC pn < LENGTH pys /\ next = EL (SUC pn) pys /\
    lookup_block (post with vs_inst_idx := SUC b0.vs_inst_idx).vs_current_bb tf.fn_blocks = SOME pbt /\
    get_instruction pbt (post with vs_inst_idx := SUC b0.vs_inst_idx).vs_inst_idx = SOME next /\
    (post with vs_inst_idx := SUC b0.vs_inst_idx).vs_inst_idx = LENGTH pps + SUC pn /\
    (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE (SUC pn) pys) pbe =
      OK (post with vs_inst_idx := SUC b0.vs_inst_idx)) /\
    call_h + SUC (LENGTH (trace_blocks b e (N-e) C8 ctf ent)) = SUC j /\
    SUC j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
    EL (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) =
      ((a,e,next.inst_id),tf,next,post with vs_inst_idx := SUC b0.vs_inst_idx) /\
    trace_gas (TAKE (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry)) = obs /\
    (post with vs_inst_idx := SUC b0.vs_inst_idx).vs_gas_readings = s.vs_gas_readings /\
    root_entry.vs_gas_readings = MAP SND obs ++
      (post with vs_inst_idx := SUC b0.vs_inst_idx).vs_gas_readings
Proof
  cheat
QED
