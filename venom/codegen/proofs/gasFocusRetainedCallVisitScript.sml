Theory gasFocusRetainedCallVisit
Ancestors
  dftFinitePacket frameJointTrace finite_map list arithmetic

(* key_at carries the path and block clock of each indexed native visit.
   The index in a retained call row selects the pre-vertex, not just a
   matching configuration somewhere in the trace. *)
Theorem focus_retained_call_visit:
  !T. T = dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry ==>
  !V. V = TAKE j T ==>
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
    joint_trace vs0 C8 q80 evs8 qs8 q8 /\ j = LENGTH evs8 /\
    (!k a0 e0 cid0 fn i s.
      k < j /\ EL k V = ((a0,e0,cid0),fn,i,s) ==>
      key_at k = (a0,e0) /\
      ?stk PG G tn oms om hs hist.
        EL k (q80::qs8) = JointConfig stk PG G tn fn i s oms om hs hist) /\
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
    h < j /\ h < LENGTH V /\ key_at h = (a,e) /\
    joint_config_reachable vs0 C8 (EL h (q80::qs8)) /\
    joint_transition C8 (EL h (q80::qs8)) (EL h evs8) (EL (SUC h) (q80::qs8)) /\
    ?sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
      be hbe count front closed brest csf ctf child_order child_res child_rest
      c nm ops args.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
      q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE /\
      EL h V = ((a,e,cid),tf,c,b0) /\
      (?stk PG G tn oms om hs hist.
        EL h (q80::qs8) = JointConfig stk PG G tn tf c b0 oms om hs hist) /\
      LENGTH ps <= b0.vs_inst_idx /\ get_instruction bt b0.vs_inst_idx = SOME c /\
      done_at_call = TAKE (b0.vs_inst_idx - LENGTH ps) rho /\ ~MEM q done_at_call /\
      FLOOKUP acts ((e,cid)::a) =
        SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
      decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry /\
      (case ret of
         NONE => child_res = NONE /\
           MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
       | SOME (ir,child_out,caller_post) =>
           child_res = SOME (IntRet ir child_out) /\
           bind_outputs c.inst_outputs ir.iret_values
             (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
           h + SUC (LENGTH (dftGasFromListTraceDefs$trace_blocks ((e,cid)::a) e (N-e)
             C8 ctf child_entry)) <= j /\ MEM q (TAKE count rho))
Proof
  CONV_TAC (TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV)) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o PURE_REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `(j,obs) = _`
    (SUBST_ALL_TAC o SYM o CONJUNCT1 o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!k a0 e0 cid0 fn i s. _ ==> _`
    (drule_all_then (CONJUNCTS_THEN assume_tac) o SRULE [SF CONJ_ss, EL_TAKE]) >>
  `h < LENGTH evs8` by
    (qpat_assum `j = LENGTH evs8` (once_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac joint_trace_edge_at >>
  `LENGTH (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry)) = j`
    by (irule LENGTH_TAKE >> irule LESS_IMP_LESS_OR_EQ >> first_assum ACCEPT_TAC) >>
  pop_assum (pure_once_rewrite_tac o single) >>
  qmatch_asmsub_rename_tac `EL h _ = ((a,e,cid),call_fn,call_inst,b0)` >>
  qpat_x_assum `call_inst = EL q _` SUBST_ALL_TAC >>
  qpat_x_assum `j = LENGTH evs8` SUBST_ALL_TAC >>
  simp[EL_TAKE] >>
  rename1 `decode_invoke (EL q rows) = SOME (call_nm,call_ops)` >>
  rename1 `eval_operands call_ops b0 = SOME call_args` >>
  qexistsl_tac [`call_nm`,`call_ops`,`call_args`] >>
  asm_rewrite_tac[]
QED
