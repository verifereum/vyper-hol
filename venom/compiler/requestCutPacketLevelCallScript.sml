Theory requestCutPacketLevelCall
Ancestors
  requestCutPacketCallTail requestCutPacketInvoke dftFinitePacket
  dftGasFromListTraceDefs dftIndexedExec venomExecSemantics venomState
  gasEvents list rich_list arithmetic finite_map

(* Finish a selected level at the suspended call. The caller's partial
   block already contributed exactly the keys before that INVOKE. *)
Theorem request_cut_packet_level_call:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e cid q call_h b0 done centry ret
    bb bt ps xs ys row_order hin h0 be hbe row_count front closed brest ms fuel kgss tail u
    csf ctf corder cres crest.
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
    FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done,centry,ret) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,row_order,hin,h0,SOME (be,hbe),row_count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,centry,corder,cres,crest) /\
    N <= fuel /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
    FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK u /\
    u.vs_inst_idx = LENGTH ps + q /\ u.vs_gas_readings = tail ==>
    ?nm ops args.
      decode_invoke (EL q xs) = SOME (nm,ops) /\
      lookup_function nm C7.ctx_functions = SOME csf /\
      eval_operands ops u = SOME args /\
      setup_callee csf args u = SOME (centry with vs_gas_readings := tail) /\
      !r. run_blocks (fuel-e) C7 csf (centry with vs_gas_readings := tail) = r /\
        ~(?v. r = OK v) /\ ~(?ir v. r = IntRet ir v) ==>
        exec_block (fuel-e) C7 bb u = r /\
        MAP FST (trace_gas (trace_block a e (fuel-e) C7 sf bb u)) =
        MAP FST (trace_gas (trace_blocks ((e,cid)::a) e (fuel-e) C7 csf
          (centry with vs_gas_readings := tail)))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all request_cut_packet_invoke_setup >> strip_tac >>
  `bb.bb_instructions = ps ++ xs` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_assum `!a e bb bt ps xs ys row_order hin h0 be row_count front closed rest.
       FLOOKUP blocks (a,e) = _ ==> _`
       (fn info => qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,_,hin,h0,SOME (be,hbe),_,front,closed,brest)`
         (strip_assume_tac o MATCH_MP info)) >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`nm`,`ops`,`args`] >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE simp[])) >>
  gen_tac >> strip_tac >>
  mp_tac (Q.INST [`C` |-> `C7`,`caller` |-> `u`,`stopped` |-> `r`,`f` |-> `fuel-e`,
    `inst` |-> `EL q xs`,`callee` |-> `csf`,
    `child` |-> `centry with vs_gas_readings := tail`] request_cut_packet_call_tail) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  simp[]
QED

Theorem request_cut_packet_level_call_records:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,centry,ret) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,row_order,hin,h0,body_entry,row_count,front,closed,brest) ==>
  (?be hbe. body_entry = SOME (be,hbe)) /\
  (?csf ctf corder cres crest.
    FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,centry,corder,cres,crest)) /\
  (!r. MEM r done ==> MEM r (TAKE row_count row_order))
Proof
  strip_tac >>
  `(?be hbe. body_entry = SOME (be,hbe)) /\
   (?csf ctf corder cres crest.
     FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,centry,corder,cres,crest))` by
    (qhdtm_x_assum `dft_focus_packet_rel`
      (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls (a,e,cid) = _ ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,hin,h0,body_entry,row_count,front,closed,brest)` mp_tac >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)` mp_tac >>
     qpat_assum `FLOOKUP acts ((e,cid)::a) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  gvs[] >>
  mp_tac (Q.SPECL
    [`N`,`C7`,`C8`,`root_sf`,`root_tf`,`root_entry`,`packet`,`acts`,`blocks`,`calls`,
     `ms_tab`,`es_tab`,`ks_tab`,`rooted_eval`,`p`,`d`,`q8`,`raw_slots`,`sites`,`unused`,
     `a`,`e`,`cid`,`q`,`h`,`b0`,`done`,`centry`,`ret`,`bb`,`bt`,`ps`,`xs`,`ys`,
     `row_order`,`hin`,`h0`,`be`,`hbe`,`row_count`,`front`,`closed`,`brest`]
    dft_packet_call_done_contained) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  DISCH_THEN ACCEPT_TAC
QED
