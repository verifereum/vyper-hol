Theory requestCutPacketInvoke
Ancestors
  dftFinitePacket dftPacketCalleeAlignment dftRunRel o1PassContract o1ScheduleDecompHelpers
  venomWf venomExecSemantics venomInst venomState list finite_map

Theorem request_cut_packet_invoke_setup:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e cid q call_h b0 done centry ret
    bb bt ps xs ys rho hin h0 be hbe count front closed brest ms fuel kgss tail u
    csf ctf corder cres crest.
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
    FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done,centry,ret) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,centry,corder,cres,crest) /\
    N <= fuel /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
    FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
    q < LENGTH xs /\ (EL q xs).inst_id = cid /\ (EL q xs).inst_opcode = INVOKE /\
    ?nm ops args. decode_invoke (EL q xs) = SOME (nm,ops) /\
      lookup_function nm C7.ctx_functions = SOME csf /\
      eval_operands ops u = SOME args /\
      setup_callee csf args u = SOME (centry with vs_gas_readings := u.vs_gas_readings)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dft_packet_call_prefix_agreement >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`
    (fn cases => qpat_assum `FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,centry,corder,cres,crest)`
      (strip_assume_tac o MATCH_MP cases)) >>
  `?call_inst call_nm call_ops call_args. q < LENGTH xs /\ call_inst = EL q xs /\
    call_inst.inst_id = cid /\ call_inst.inst_opcode = INVOKE /\
    decode_invoke call_inst = SOME (call_nm,call_ops) /\
    lookup_function call_nm C8.ctx_functions = SOME ctf /\
    eval_operands call_ops b0 = SOME call_args /\
    setup_callee ctf call_args b0 = SOME centry` by suspend "record" >>
  `?source. lookup_function call_nm C7.ctx_functions = SOME source /\
    ctf = dft_fn source /\ dft_fn_rel source ctf /\
    eval_operands call_ops u = SOME call_args /\
    setup_callee source call_args u = SOME (centry with vs_gas_readings := u.vs_gas_readings)` by
    (mp_tac (Q.INST [`C7` |-> `C7`, `C8` |-> `C8`, `c` |-> `call_inst`,
       `nm` |-> `call_nm`, `ops` |-> `call_ops`, `ctf` |-> `ctf`, `b0` |-> `b0`,
       `args` |-> `call_args`, `child_entry` |-> `centry`, `u` |-> `u`]
      dft_packet_callee_alignment) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         qpat_assum `call_inst = EL q xs` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     DISCH_THEN ACCEPT_TAC) >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) C7.ctx_functions)` by
    (qpat_assum `o1_ctx_shape C7` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[o1_ctx_shape_def,venomWfTheory.ctx_wf_def,
       venomWfTheory.ctx_distinct_fn_names_def,venomInstTheory.ctx_fn_names_def]) >>
  `lookup_function call_nm C7.ctx_functions = SOME csf` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`lookup_function call_nm C7.ctx_functions = SOME source`,`MEM csf C7.ctx_functions`,
       `dft_fn_rel source ctf`,`dft_fn_rel csf ctf`,`ALL_DISTINCT _`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[lookup_function_member_iff,dft_fn_rel_def] >>
     metis_tac[]) >>
  `source = csf` by
    (qpat_assum `lookup_function call_nm C7.ctx_functions = SOME source` mp_tac >>
     qpat_assum `lookup_function call_nm C7.ctx_functions = SOME csf`
       (fn th => simp[NoAsms,th]) >> simp[NoAsms,EQ_SYM_EQ]) >>
  pop_assum SUBST_ALL_TAC >>
  rpt conj_tac >> TRY (qpat_assum `call_inst = EL q xs` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`call_nm`,`call_ops`,`call_args`] >>
  qpat_assum `call_inst = EL q xs` (SUBST1_TAC o SYM) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume request_cut_packet_invoke_setup[record]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,_,hin,h0,SOME (be,hbe),_,front,closed,brest)`,
     `FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,centry,corder,cres,crest)`,
     `FLOOKUP blocks (a,e) = SOME _`, `FLOOKUP acts ((e,cid)::a) = SOME _`,
     `c = EL q _`, `q < LENGTH _`, `c.inst_id = cid`, `c.inst_opcode = INVOKE`,
     `decode_invoke c = SOME _`, `lookup_function _ C8.ctx_functions = SOME _`,
     `eval_operands _ b0 = SOME _`, `setup_callee _ _ b0 = SOME centry`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Finalise request_cut_packet_invoke_setup
