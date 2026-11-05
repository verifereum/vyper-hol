(* Shared proof-time syntax only: no new logical predicates. *)
Theory o1LowerDloadRunner
Ancestors
  o1LowerDloadEndpointConsumer o1LowerDloadRootEntry o1PassContract
  o1PassLift venomExecProofs venomExecSemantics venomWf venomInst
  o1LowerDloadJointRelation o1LowerDloadEntryFetch
  contextCodegenRel venomState list arithmetic
  o1LowerDloadOccurrence o1LowerDloadOccurrenceHeadroom ptrDiscipline
  o1LowerDloadRunnerBoundary passSimulationDefs

val ldA = ``ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  ptr_discipline lo C vs``;
val ldJ = ``ld_joint_boundary vs C C' lo D``;
val ldR = ``\stk PG fn a U HP ts A0 r r'.
  case r of
    Halt se => (?te. r' = Halt te /\ dead_result_rel D r r')
  | Abort ab se => (?te. r' = Abort ab te /\ dead_result_rel D r r')
  | Error e => F
  | IntRet ir se =>
    ?kr ri sr tr nr Gr tnr Br Hr sitesr Xr jr.
      ri.inst_opcode = RET /\ active_inst fn ri sr /\
      ^ldJ stk PG Gr tnr fn ri sr tr nr a U Br HP Hr sitesr Xr ts /\
      step_inst kr C ri sr = IntRet ir se /\ se = sr /\
      sr.vs_call_ctx.cc_address = A0 /\
      step_inst kr C' ri tr = IntRet jr tr /\ r' = IntRet jr tr /\
      jr.iret_values = ir.iret_values /\
      ir.iret_adopt_fmp = NONE /\ jr.iret_adopt_fmp = NONE
  | OK se =>
    ?kb bi sb tb nb Gb tnb Bb Hb sitesb Xb te.
      MEM bi.inst_opcode [JMP; JNZ; DJMP] /\ active_inst fn bi sb /\
      ^ldJ stk PG Gb tnb fn bi sb tb nb a U Bb HP Hb sitesb Xb ts /\
      step_inst kb C bi sb = OK se /\ step_inst kb C' bi tb = OK te /\
      r' = OK te /\ se.vs_current_bb = te.vs_current_bb /\
      se.vs_prev_bb = te.vs_prev_bb /\ se.vs_call_ctx.cc_address = A0``;
val ldPexec = ``\k ctx bb s.
  !stk PG G tn fn i t n a U B HP H sites X ts r.
    ctx = C /\ ^ldA /\ opaque_use_ok fn /\ ~s.vs_halted /\
    ^ldJ stk PG G tn fn i s t n a U B HP H sites X ts /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    exec_block k C bb s = r /\ terminates r ==>
    ?m fn' bb' r'.
      lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
      exec_block m C' bb' t = r' /\
      ^ldR stk PG fn a U HP ts s.vs_call_ctx.cc_address r r'``;
val ldPrun = ``\k ctx fn s0.
  !stk PG G tn i s1 t0 t1 n a U B HP H sites X ts r.
    ctx = C /\ ^ldA /\ opaque_use_ok fn /\ ~s0.vs_halted /\
    enters_block fn s0 s1 /\
    (?fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      enters_block fn' t0 t1) /\
    ^ldJ stk PG G tn fn i s1 t1 n a U B HP H sites X ts /\
    run_blocks k C fn s0 = r /\ terminates r ==>
    ?m fn' r'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      run_blocks m C' fn' t0 = r' /\
      ^ldR stk PG fn a U HP ts s0.vs_call_ctx.cc_address r r'``;
val ldPstep = ``\k ctx callinst s.
  !stk PG G tn fn t n a U B HP H sites X ts r.
    ctx = C /\ ^ldA /\ opaque_use_ok fn /\ ~s.vs_halted /\
    ^ldJ stk PG G tn fn callinst s t n a U B HP H sites X ts /\
    active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
    step_inst k C callinst s = r /\ terminates r ==>
    ?m r'. step_inst m C' callinst t = r' /\
    (case r of
      OK s1 => ?next t1 nr Gr tnr Br Hr sitesr Xr.
        r' = OK t1 /\
        ^ldJ stk PG Gr tnr fn next
          (s1 with vs_inst_idx := SUC s.vs_inst_idx)
          (t1 with vs_inst_idx := SUC t.vs_inst_idx)
          nr a U Br HP Hr sitesr Xr ts /\
        active_inst fn next (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
        s1.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address
    | Halt se => (?te. r' = Halt te /\ dead_result_rel D r r')
    | Abort ab se => (?te. r' = Abort ab te /\ dead_result_rel D r r')
    | IntRet ir se => F | Error e => F)``;

(* Specialization at the term level, retaining the literal recursive guards. *)
val (ldIndVars,ldIndBody) = strip_forall (concl run_defs_ind);
val ldInd = Term.subst (ListPair.map (fn (v,t) => v |-> t)
  (ldIndVars,[ldPstep,ldPexec,ldPrun])) ldIndBody;
val ldClauses = strip_conj (fst (dest_imp ldInd));

Theorem ld_runner_packet_terminates:
  ^ldR stk PG fn a U HP ts A0 r r' ==> terminates r'
Proof
  Cases_on `r` >> simp[terminates_def] >> rpt strip_tac >> gvs[terminates_def]
QED

Theorem ld_runner_run_clause:
  ^(List.nth(ldClauses,2))
Proof
  qabbrev_tac `RR = ^ldR` >> qabbrev_tac `AA = ^ldA` >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  `occ_frame_reachable vs C stk PG G tn fn i s1 n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `wf_function fn` by
    (drule occ_frame_reachable_annotation >> strip_tac >>
     fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  `active_inst fn i s1` by
    (drule occ_frame_reachable_projection >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_halted = s.vs_halted` by
    metis_tac[ld_enters_block_call_ctx, ld_enters_block_halted] >>
  Cases_on `fuel` >- fs[Once run_blocks_def, terminates_def] >>
  qpat_assum `enters_block fn s s1`
    (strip_assume_tac o REWRITE_RULE [enters_block_def]) >>
  qpat_assum `enters_block fn' t0 t1`
    (strip_assume_tac o REWRITE_RULE [enters_block_def]) >>
  gvs[] >>
  `s_phi.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `s_phi'.vs_current_bb = t0.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `get_instruction bb (phi_prefix_length bb.bb_instructions) = SOME i` by
    (qpat_x_assum `active_inst fn i _` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb''` by
       (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
     gvs[get_instruction_def]) >>
  qmatch_goalsub_abbrev_tac `run_blocks (SUC k) C fn s` >>
  qmatch_asmsub_abbrev_tac `terminates (run_blocks (SUC k) C fn s)` >>
  qmatch_asmsub_abbrev_tac `enters_block fn s sin` >>
  `terminates (exec_block k C bb sin)` by
    (qpat_x_assum `terminates (run_blocks _ _ _ _)` mp_tac >>
     simp[Once run_blocks_def, Abbr `sin`] >>
     Cases_on `exec_block k C bb
       (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
     simp[terminates_def]) >>
  `lookup_block sin.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb sin.vs_inst_idx = SOME i` by simp[Abbr `sin`] >>
  gvs[] >> first_x_assum (drule_all_then strip_assume_tac) >>
  gvs[] >>
  qpat_x_assum `occ_frame_reachable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `ld_joint_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `active_inst _ _ _` kall_tac >>
  qmatch_asmsub_abbrev_tac `RR stk PG fn a U HP ts A0 br bt` >>
  Cases_on `br`
  >- suspend "branch"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "return"
  >> fs[terminates_def]
QED

Resume ld_runner_run_clause[halt]:
  `?te. bt = Halt te` by fs[Abbr `RR`] >>
  qpat_x_assum `Abbrev (Halt v = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `exec_block m C' bb'
      (s_phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = Halt te` by
    fs[Abbr `bt`] >>
  qexists_tac `SUC m` >>
  simp[Once run_blocks_def] >> simp[Once run_blocks_def] >>
  qpat_x_assum `RR _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[]
QED
Resume ld_runner_run_clause[abort]:
  `?te. bt = Abort a' te` by fs[Abbr `RR`] >>
  qpat_x_assum `Abbrev (Abort _ _ = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `exec_block m C' bb'
      (s_phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = Abort a' te` by
    fs[Abbr `bt`] >>
  qexists_tac `SUC m` >>
  simp[Once run_blocks_def] >> simp[Once run_blocks_def] >>
  qpat_x_assum `RR _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[]
QED
Resume ld_runner_run_clause[return]:
  `?jr tr. bt = IntRet jr tr` by
    (fs[Abbr `RR`] >> metis_tac[]) >>
  qpat_x_assum `Abbrev (IntRet _ _ = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `exec_block m C' bb'
      (s_phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = IntRet jr tr` by
    fs[Abbr `bt`] >>
  qexists_tac `SUC m` >>
  simp[Once run_blocks_def] >> simp[Once run_blocks_def] >>
  qpat_x_assum `RR _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[]
QED
Resume ld_runner_run_clause[branch]:
  qpat_x_assum `Abbrev (OK v = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `~v.vs_halted` by metis_tac[exec_block_OK_not_halted] >>
  `terminates (run_blocks k C fn v)` by
    (qpat_x_assum `terminates (run_blocks (SUC k) C fn s)` mp_tac >>
     simp[Once run_blocks_def]) >>
  qpat_assum `Abbrev (RR = _)` (fn rr =>
    qpat_assum `RR _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o SIMP_RULE (srw_ss())
        [REWRITE_RULE [markerTheory.Abbrev_def] rr])) >>
  `MEM bi.inst_opcode [JMP; JNZ; DJMP]` by simp[] >>
  `?sn. enters_block fn v sn` by
    (Cases_on `k` >- fs[Once run_blocks_def, terminates_def] >>
     Cases_on `lookup_block v.vs_current_bb fn.fn_blocks`
     >- fs[Once run_blocks_def, terminates_def] >>
     rename1 `lookup_block v.vs_current_bb fn.fn_blocks = SOME dest` >>
     `(?p. eval_phis v dest.bb_instructions = OK p) \/
      (?e. eval_phis v dest.bb_instructions = Error e)` by
       metis_tac[eval_phis_ok_or_error_defs] >>
     fs[Once run_blocks_def, terminates_def] >>
     simp[enters_block_def] >> metis_tac[]) >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ld_branch_endpoint_consume) >>
  strip_tac >>
  gvs[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  `terminates (run_blocks m' C' fn' te)` by
    (qpat_assum `Abbrev (RR = _)` (fn rr =>
      qpat_assum `RR _ _ _ _ _ _ _ _ (run_blocks k C fn v) _`
        (mp_tac o REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] rr])) >>
     CONV_TAC (LAND_CONV (DEPTH_CONV BETA_CONV)) >>
     disch_tac >>
     drule (SIMP_RULE (srw_ss()) [] ld_runner_packet_terminates) >> simp[]) >>
  `run_blocks (MAX m m') C' fn' te = run_blocks m' C' fn' te` by
    (irule run_blocks_terminates_mono >> simp[]) >>
  `exec_block (MAX m m') C' bb'
     (s_phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = OK te` by
    (irule EQ_TRANS >>
     qexists_tac `exec_block m C' bb'
       (s_phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)` >>
     conj_tac >- (irule exec_block_terminates_mono >> simp[terminates_def]) >>
     simp[]) >>
  `~te.vs_halted` by metis_tac[exec_block_OK_not_halted] >>
  `run_blocks (SUC k) C fn s = run_blocks k C fn v` by
    (qpat_assum `run_block_non_phis k C bb sin = OK v`
       (mp_tac o SIMP_RULE (srw_ss()) [Abbr `sin`]) >>
     simp[Once run_blocks_def]) >>
  `run_blocks (SUC (MAX m m')) C' fn' t0 = run_blocks m' C' fn' te` by
    simp[Once run_blocks_def] >>
  qexists_tac `SUC (MAX m m')` >> simp[]
QED
Finalise ld_runner_run_clause

Theorem ld_runner_conditional_induction:
  ^(mk_imp(list_mk_conj [List.nth(ldClauses,0), List.nth(ldClauses,1)],
           snd(dest_imp ldInd)))
Proof
  strip_tac >> irule run_defs_ind >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  MATCH_ACCEPT_TAC ld_runner_run_clause

QED
