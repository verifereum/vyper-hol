Theory dftPacketCallRecordJoin
Ancestors
  dftPacketCallRecordFrame dftPacketCalleeInitialization
  dftPacketCallRecords dftPacketCalleeAlignment dftPacketCalleeStructure
  dftPacketCallLocalPreservation dftRunRel frameJointTransition
  dftLifting o1PassContract unitShapeDefs gasOracleReplay
  venomInst venomWf venomExecSemantics list rich_list finite_map arithmetic pred_set

(* Only structural packet clauses are joined here.  In particular, none of
   the inputs assumes fresh-child initialization or a successor packet. *)
Theorem dft_packet_call_record_preservation:
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
    N C7 C8 root_tf root_entry j p d inst s sf fn inc entry order
    bb bt ps xs ys sched hin h0 be hbe count q nm ops ctf args cs s1 ci
    stk PG G tv.
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  o1_ctx_shape C7 /\
  ctx_labels_bound C7 s.vs_labels /\ ctx_labels_bound C8 s.vs_labels /\
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) = ((p,d,inst.inst_id),fn,inst,s) /\
  inst.inst_opcode = INVOKE /\ active_inst fn inst s /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C8.ctx_functions = SOME ctf /\
  eval_operands ops s = SOME args /\ setup_callee ctf args s = SOME cs /\
  enters_block ctf cs s1 /\ active_inst ctf ci s1 /\
  FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\ LAST order = d /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,OK s,F,NONE) /\
  s.vs_inst_idx = LENGTH ps + count /\ get_instruction bt s.vs_inst_idx = SOME inst /\
  q < LENGTH xs /\ EL q xs = inst /\ ~MEM q (TAKE count sched) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  LENGTH stk = LENGTH p /\
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order q h b0 done child e cid a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child,NONE) /\
      (EL k stk).cf_fn = tf /\ (EL k stk).cf_state = b0 /\
      (EL k stk).cf_inst.inst_id = cid /\
      (EL k stk).cf_inst.inst_opcode = INVOKE /\
      active_inst tf (EL k stk).cf_inst b0) /\
  (!a sf tf inc entry order res rest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) ==>
    MEM sf C7.ctx_functions /\ tf = dft_fn sf /\ dft_fn_rel sf tf /\
    inc = (case a of [] => 0 | (e,cid)::parent => e) /\
    order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
    (!e. MEM e order <=> (a,e) IN FDOM blocks) /\
    (res = NONE <=> rest = NONE) /\
    (res = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p)))) /\
    (!e cid parent. a = (e,cid)::parent ==>
      ?q h b0 done ret.
        FLOOKUP calls (parent,e,cid) = SOME (q,h,b0,done,entry,ret))) /\
  (!a e. (a,e) IN FDOM blocks ==> a IN FDOM acts) /\
  (!a e cid q h b0 done child ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child,ret) ==>
    ?sf tf inc entry order res rest bb bt ps xs ys rho hin h0 be hbe
     count front closed brest csf ctf child_order child_res child_rest c nm ops args.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE /\
      LENGTH ps <= b0.vs_inst_idx /\ get_instruction bt b0.vs_inst_idx = SOME c /\
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
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order bb bt ps xs ys rho hin h0 be hbe count
     q h b0 done child cid e a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\ LAST order = e /\
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child,NONE) /\
      done = TAKE count rho /\ b0.vs_inst_idx = LENGTH ps + count /\
      get_instruction bt b0.vs_inst_idx = SOME (EL q xs)) ==>
  ?csf cbb cbt cps cxs cys crho sp N' suffix cbe acts' blocks' calls'.
    lookup_function nm C7.ctx_functions = SOME csf /\
    MEM csf C7.ctx_functions /\ ctf = dft_fn csf /\ dft_fn_rel csf ctf /\
    lookup_block cs.vs_current_bb csf.fn_blocks = SOME cbb /\
    lookup_block cs.vs_current_bb ctf.fn_blocks = SOME cbt /\
    cbt.bb_label = cbb.bb_label /\ cbb.bb_label = cs.vs_current_bb /\
    cbb.bb_instructions = cps ++ cxs /\ cbt.bb_instructions = cps ++ cys /\
    EVERY (\i. is_pseudo i.inst_opcode) cps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) cxs /\
    EVERY (\i. ~is_pseudo i.inst_opcode) cys /\
    EVERY inst_shape_ok cbb.bb_instructions /\ EVERY inst_wf cbb.bb_instructions /\
    ALL_DISTINCT (MAP (\i. i.inst_id) cxs) /\ LENGTH cxs = LENGTH cys /\
    PERM crho (COUNT_LIST (LENGTH cxs)) /\
    LIST_REL (\q y. q < LENGTH cxs /\
      y.inst_id = (EL q cxs).inst_id /\ from_block [EL q cxs] y) crho cys /\
    setup_callee csf args s = SOME cs /\ strict_dom_vars_defined csf cs /\
    fn_reachable csf cs.vs_current_bb /\
    ctx_labels_bound C7 cs.vs_labels /\ ctx_labels_bound C8 cs.vs_labels /\
    eval_phis cs cbt.bb_instructions = OK sp /\
    eval_phis cs cbb.bb_instructions = OK sp /\ eval_phis cs cps = OK sp /\
    phi_prefix_length cbb.bb_instructions = phi_prefix_length cps /\
    phi_prefix_length cbt.bb_instructions = phi_prefix_length cps /\
    s1 = sp with vs_inst_idx := phi_prefix_length cbt.bb_instructions /\
    get_instruction cbt s1.vs_inst_idx = SOME ci /\
    N <= N' /\
    trace_blocks [] 0 N' C8 root_tf root_entry =
      trace_blocks [] 0 N C8 root_tf root_entry ++ suffix /\
    SUC j < LENGTH (trace_blocks [] 0 N' C8 root_tf root_entry) /\
    EL (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry) =
      (((d,inst.inst_id)::p,SUC d,ci.inst_id),ctf,ci,s1) /\
    TAKE (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry) =
      TAKE (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) /\
    (!h. h < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) ==>
      EL h (trace_blocks [] 0 N' C8 root_tf root_entry) =
      EL h (trace_blocks [] 0 N C8 root_tf root_entry)) /\
    phi_prefix_length cbt.bb_instructions <= s1.vs_inst_idx /\
    s1.vs_inst_idx <= LENGTH cps /\
    (case cbe of
       NONE => s1.vs_inst_idx < LENGTH cps /\
         (!f C. FOLDR (dft_exec_cons f C) OK
           (DROP (phi_prefix_length cbt.bb_instructions) (TAKE s1.vs_inst_idx cps))
           (sp with vs_inst_idx := phi_prefix_length cbt.bb_instructions) = OK s1)
     | SOME (cb,hcb) =>
         cb = s1 /\ hcb = SUC j /\ s1.vs_inst_idx = LENGTH cps /\
         cys <> [] /\ ci = HD cys /\ dft_remaining_inv csf cbb cxs s1 /\
         (!f C. FOLDR (dft_exec_cons f C) OK
           (DROP (phi_prefix_length cbt.bb_instructions) cps)
           (sp with vs_inst_idx := phi_prefix_length cbt.bb_instructions) = OK s1)) /\
    FLOOKUP acts ((d,inst.inst_id)::p) = NONE /\
    FLOOKUP calls (p,d,inst.inst_id) = NONE /\
    acts' = acts |+ ((d,inst.inst_id)::p,(csf,ctf,d,cs,[SUC d],NONE,NONE)) /\
    blocks' = blocks |+ (((d,inst.inst_id)::p,SUC d),
      (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE)) /\
    calls' = calls |+ ((p,d,inst.inst_id),(q,j,s,TAKE count sched,cs,NONE)) /\
    FDOM acts' = FDOM acts UNION {(d,inst.inst_id)::p} /\
    FDOM blocks' = FDOM blocks UNION {((d,inst.inst_id)::p,SUC d)} /\
    FDOM calls' = FDOM calls UNION {(p,d,inst.inst_id)} /\
    FLOOKUP acts' ((d,inst.inst_id)::p) = SOME (csf,ctf,d,cs,[SUC d],NONE,NONE) /\
    FLOOKUP blocks' ((d,inst.inst_id)::p,SUC d) =
      SOME (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE) /\
    LENGTH (<|cf_fn := fn; cf_inst := inst; cf_state := s;
      cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk) =
      LENGTH ((d,inst.inst_id)::p) /\
    (!k. k < LENGTH ((d,inst.inst_id)::p) ==>
      ?sf tf inc entry order q h b0 done child e cid a.
        a = DROP (SUC k) ((d,inst.inst_id)::p) /\
        (e,cid) = EL k ((d,inst.inst_id)::p) /\
        FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
        FLOOKUP calls' (a,e,cid) = SOME (q,h,b0,done,child,NONE) /\
        (EL k (<|cf_fn := fn; cf_inst := inst; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk)).cf_fn = tf /\
        (EL k (<|cf_fn := fn; cf_inst := inst; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk)).cf_state = b0 /\
        (EL k (<|cf_fn := fn; cf_inst := inst; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk)).cf_inst.inst_id = cid /\
        (EL k (<|cf_fn := fn; cf_inst := inst; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk)).cf_inst.inst_opcode = INVOKE /\
        active_inst tf (EL k (<|cf_fn := fn; cf_inst := inst; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk)).cf_inst b0) /\
    (!a sf tf inc entry order res rest.
      FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,rest) ==>
      MEM sf C7.ctx_functions /\ tf = dft_fn sf /\ dft_fn_rel sf tf /\
      inc = (case a of [] => 0 | (e,cid)::parent => e) /\
      order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
      (!e. MEM e order <=> (a,e) IN FDOM blocks') /\
      (res = NONE <=> rest = NONE) /\
      (res = NONE <=> MEM a (GENLIST (\i. DROP i ((d,inst.inst_id)::p))
        (SUC (LENGTH ((d,inst.inst_id)::p))))) /\
      (!e cid parent. a = (e,cid)::parent ==>
        ?q h b0 done ret.
          FLOOKUP calls' (parent,e,cid) = SOME (q,h,b0,done,entry,ret))) /\
    (!a. a <> (d,inst.inst_id)::p ==> FLOOKUP acts' a = FLOOKUP acts a) /\
    (!a e. (a,e) <> ((d,inst.inst_id)::p,SUC d) ==>
      FLOOKUP blocks' (a,e) = FLOOKUP blocks (a,e)) /\
    (!key. key <> (p,d,inst.inst_id) ==> FLOOKUP calls' key = FLOOKUP calls key) /\
    (!a value. FLOOKUP acts a = SOME value ==> FLOOKUP acts' a = SOME value) /\
    (!key value. FLOOKUP blocks key = SOME value ==> FLOOKUP blocks' key = SOME value) /\
    (!key value. FLOOKUP calls key = SOME value ==> FLOOKUP calls' key = SOME value) /\
    FLOOKUP calls' (p,d,inst.inst_id) = SOME (q,j,s,TAKE count sched,cs,NONE) /\
    (!a e cid q h b0 done child ret.
      FLOOKUP calls' (a,e,cid) = SOME (q,h,b0,done,child,ret) ==>
      ?sf tf inc entry order res rest bb bt ps xs ys rho hin h0 be hbe
       count front closed brest csf ctf child_order child_res child_rest c nm ops args.
        FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,rest) /\
        FLOOKUP blocks' (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
        q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE /\
        LENGTH ps <= b0.vs_inst_idx /\ get_instruction bt b0.vs_inst_idx = SOME c /\
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
            MEM q (TAKE count rho))) /\
    (!k. k < LENGTH ((d,inst.inst_id)::p) ==>
      ?sf tf inc entry order bb bt ps xs ys rho hin h0 be hbe count
       q h b0 done child cid e a.
        a = DROP (SUC k) ((d,inst.inst_id)::p) /\
        (e,cid) = EL k ((d,inst.inst_id)::p) /\
        FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\ LAST order = e /\
        FLOOKUP blocks' (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
        FLOOKUP calls' (a,e,cid) = SOME (q,h,b0,done,child,NONE) /\
        done = TAKE count rho /\ b0.vs_inst_idx = LENGTH ps + count /\
        get_instruction bt b0.vs_inst_idx = SOME (EL q xs))
Proof
  rpt gen_tac >> strip_tac >> suspend "prepare"
QED

Resume dft_packet_call_record_preservation[prepare]:
  `FLOOKUP calls (p,d,inst.inst_id) = NONE /\
   FLOOKUP acts ((d,inst.inst_id)::p) = NONE` by suspend "fresh" >>
  `(!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op s) /\
   (!callee argv. setup_callee callee argv (s with vs_gas_readings := s.vs_gas_readings) =
     setup_callee callee argv s)` by simp[] >>
  drule_all dft_packet_callee_alignment >> strip_tac >>
  `MEM csf C7.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `cs.vs_gas_readings = s.vs_gas_readings` by
    metis_tac[gas_setup_callee_readings] >>
  `setup_callee csf args s = SOME cs` by
    gvs[venomStateTheory.venom_state_component_equality] >>
  `wf_function ctf` by
    (`EVERY inst_shape_ok (fn_insts csf)` by
       (qpat_x_assum `o1_ctx_shape C7` mp_tac >>
        simp[o1_ctx_shape_def,EVERY_MEM] >> strip_tac >>
        qpat_x_assum `!e. MEM e C7.ctx_functions ==> _`
          (qspec_then `csf` mp_tac) >>
        simp[o1_fn_shape_def,fn_shape_ok_def,EVERY_MEM] >> metis_tac[]) >>
     simp[] >> irule dft_fn_wf_function >> gvs[dft_fn_rel_def]) >>
  `ALL_DISTINCT (fn_labels ctf)` by gvs[wf_function_def] >>
  drule_all dft_packet_callee_entered_structure >> strip_tac >>
  rename1 `lookup_block cs.vs_current_bb csf.fn_blocks = SOME cbb` >>
  rename1 `lookup_block cs.vs_current_bb ctf.fn_blocks = SOME cbt` >>
  rename1 `cbb.bb_instructions = cps ++ cxs` >>
  rename1 `cbt.bb_instructions = cps ++ cys` >>
  rename1 `PERM crho (COUNT_LIST (LENGTH cxs))` >>
  drule_all dft_packet_callee_body_initialized >> strip_tac >>
  `s1.vs_inst_idx = LENGTH cps ==> dft_remaining_inv csf cbb cxs s1` by simp[] >>
  drule_all dft_packet_callee_native_initialization >> strip_tac >>
  qexistsl [`csf`,`cbb`,`cbt`,`cps`,`cxs`,`cys`,`crho`,`sp`,`N'`,`suffix`,`body_entry`,
    `acts |+ ((d,inst.inst_id)::p,(csf,ctf,d,cs,[SUC d],NONE,NONE))`,
    `blocks |+ (((d,inst.inst_id)::p,SUC d),
      (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,body_entry,0,OK s1,F,NONE))`,
    `calls |+ ((p,d,inst.inst_id),(q,j,s,TAKE count' sched,cs,NONE))`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  ntac 3 (conj_tac >- REFL_TAC) >>
  ntac 3 (conj_tac >- (simp[FDOM_FUPDATE,EXTENSION] >> metis_tac[])) >>
  ntac 2 (conj_tac >- simp[FLOOKUP_UPDATE]) >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "stack" >>
  conj_tac >- suspend "activations" >>
  suspend "frames"
QED

Resume dft_packet_call_record_preservation[fresh]:
  irule dft_packet_call_record_fresh >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!a sf tf inc entry order res rest. _` drule >>
      strip_tac >> metis_tac[]) >>
  qexistsl [`count'`,`q`,`sched`,`xs`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!a e cid q h b0 done child ret. _`
    drule >> strip_tac >> gvs[] >> Cases_on `ret` >> gvs[] >>
  PairCases_on `x` >> gvs[]
QED

Resume dft_packet_call_record_preservation[stack]:
  gen_tac >> strip_tac >>
  irule (cj 2 dft_packet_call_stack_linkage) >> simp[] >>
  qexistsl [`entry`,`inc`,`order`,`sf`] >> simp[]
QED

Resume dft_packet_call_record_preservation[activations]:
  rpt gen_tac >> disch_tac >>
  irule dft_packet_call_activation_linkage >> simp[] >>
  qexistsl [`acts`,`csf`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!a sf tf inc entry order res rest. _` drule >>
      simp[]) >>
  gvs[] >> first_assum ACCEPT_TAC
QED

Resume dft_packet_call_record_preservation[frames]:
  qabbrev_tac `acts' = acts |+ ((d,inst.inst_id)::p,(csf,ctf,d,cs,[SUC d],NONE,NONE))` >>
  qabbrev_tac `blocks' = blocks |+ (((d,inst.inst_id)::p,SUC d),
    (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,body_entry,0,OK s1,F,NONE))` >>
  qabbrev_tac `calls' = calls |+ ((p,d,inst.inst_id),(q,j,s,TAKE count' sched,cs,NONE))` >>
  `acts' = acts |+ ((d,inst.inst_id)::p,(csf,ctf,d,cs,[SUC d],NONE,NONE))` by
    simp[Abbr `acts'`] >>
  `blocks' = blocks |+ (((d,inst.inst_id)::p,SUC d),
    (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,body_entry,0,OK s1,F,NONE))` by
    simp[Abbr `blocks'`] >>
  `calls' = calls |+ ((p,d,inst.inst_id),(q,j,s,TAKE count' sched,cs,NONE))` by
    simp[Abbr `calls'`] >>
  drule_all dft_packet_call_immutable_frame >> strip_tac >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  unabbrev_all_tac >> gen_tac >> strip_tac >>
  irule dft_packet_call_suspended_parents >> simp[] >>
  gvs[ADD_COMM]
QED

Finalise dft_packet_call_record_preservation
