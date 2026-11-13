(* Shared proof-time syntax only: no new logical predicates. *)
Theory o1LowerDloadRunner
Ancestors
  o1LowerDloadEndpointConsumer o1LowerDloadRootEntry o1PassContract
  o1PassLift venomExecProofs venomExecSemantics venomWf venomInst
  o1LowerDloadJointRelation o1LowerDloadEntryFetch
  contextCodegenRel venomState list arithmetic gasEvents gasEventsFuel
  o1LowerDloadOccurrence o1LowerDloadOccurrenceHeadroom ptrDiscipline
  o1LowerDloadRunnerBoundary passSimulationDefs o1SafeUpto gasCount

val ldA = ``ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  callee_first names C.ctx_functions /\ o1_safe_upto D lo ncut C vs``;
val ldJ = ``ld_joint_boundary vs C C' lo D``;
(* A run from s can still read j gas events inside the cut: every state
   it reaches before its j-th event has popped fewer than ncut readings. *)
fun ldBud j s = ``^j + LENGTH vs.vs_gas_readings <= ncut + LENGTH (^s).vs_gas_readings /\
  0 < ^j``;
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
  !stk PG G tn fn i t n a U B HP H sites X ts r j.
    ctx = C /\ ^ldA /\ opaque_use_ok fn /\ ~s.vs_halted /\
    ^ldJ stk PG G tn fn i s t n a U B HP H sites X ts /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    exec_block k C bb s = r /\ ^(ldBud ``j:num`` ``s:venom_state``) ==>
    (terminates r /\ LENGTH (gas_events_block k C fn.fn_name bb s) < j ==>
     ?m fn' bb' r'.
      lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
      exec_block m C' bb' t = r' /\
      gas_events_block m C' fn'.fn_name bb' t =
        gas_events_block k C fn.fn_name bb s /\
      ^ldR stk PG fn a U HP ts s.vs_call_ctx.cc_address r r') /\
    (j <= LENGTH (gas_events_block k C fn.fn_name bb s) ==>
     ?m fn' bb'.
      lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
      TAKE j (gas_events_block m C' fn'.fn_name bb' t) =
        TAKE j (gas_events_block k C fn.fn_name bb s))``;
val ldPrun = ``\k ctx fn s0.
  !stk PG G tn i s1 t0 t1 n a U B HP H sites X ts r j.
    ctx = C /\ ^ldA /\ opaque_use_ok fn /\ ~s0.vs_halted /\
    enters_block fn s0 s1 /\
    (?fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      enters_block fn' t0 t1) /\
    ^ldJ stk PG G tn fn i s1 t1 n a U B HP H sites X ts /\
    run_blocks k C fn s0 = r /\ ^(ldBud ``j:num`` ``s0:venom_state``) ==>
    (terminates r /\ LENGTH (gas_events_blocks k C fn s0) < j ==>
     ?m fn' r'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      run_blocks m C' fn' t0 = r' /\
      gas_events_blocks m C' fn' t0 = gas_events_blocks k C fn s0 /\
      ^ldR stk PG fn a U HP ts s0.vs_call_ctx.cc_address r r') /\
    (j <= LENGTH (gas_events_blocks k C fn s0) ==>
     ?m fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      TAKE j (gas_events_blocks m C' fn' t0) =
        TAKE j (gas_events_blocks k C fn s0))``;
val ldPstep = ``\k ctx callinst s.
  !stk PG G tn fn t n a U B HP H sites X ts r j.
    ctx = C /\ ^ldA /\ opaque_use_ok fn /\ ~s.vs_halted /\
    ^ldJ stk PG G tn fn callinst s t n a U B HP H sites X ts /\
    active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
    step_inst k C callinst s = r /\ ^(ldBud ``j:num`` ``s:venom_state``) ==>
    (terminates r /\ LENGTH (gas_events_step k C fn.fn_name callinst s) < j ==>
     ?m r'. step_inst m C' callinst t = r' /\
     gas_events_step m C' fn.fn_name callinst t =
       gas_events_step k C fn.fn_name callinst s /\
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
     | IntRet ir se => F | Error e => F)) /\
    (j <= LENGTH (gas_events_step k C fn.fn_name callinst s) ==>
     ?m. TAKE j (gas_events_step m C' fn.fn_name callinst t) =
         TAKE j (gas_events_step k C fn.fn_name callinst s))``;

(* Specialization at the term level, retaining the literal recursive guards. *)
val (ldIndVars,ldIndBody) = strip_forall (concl run_defs_ind);
val ldInd = Term.subst (ListPair.map (fn (v,t) => v |-> t)
  (ldIndVars,[ldPstep,ldPexec,ldPrun])) ldIndBody;
val ldClauses = strip_conj (fst (dest_imp ldInd));

(* Exact-fuel packets preserve the original boundary and result relation. *)
val ldPexecFuel = ``\k ctx bb s.
  !stk PG G tn fn i t n a U B HP H sites X ts r.
    ctx = C /\ ^ldA /\ opaque_use_ok fn /\ ~s.vs_halted /\
    ^ldJ stk PG G tn fn i s t n a U B HP H sites X ts /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    exec_block k C bb s = r /\ terminates r ==>
    ?fn' bb' r'.
      lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
      exec_block k C' bb' t = r' /\
      ^ldR stk PG fn a U HP ts s.vs_call_ctx.cc_address r r'``;
val ldPrunFuel = ``\k ctx fn s0.
  !stk PG G tn i s1 t0 t1 n a U B HP H sites X ts r.
    ctx = C /\ ^ldA /\ opaque_use_ok fn /\ ~s0.vs_halted /\
    enters_block fn s0 s1 /\
    (?fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      enters_block fn' t0 t1) /\
    ^ldJ stk PG G tn fn i s1 t1 n a U B HP H sites X ts /\
    run_blocks k C fn s0 = r /\ terminates r ==>
    ?fn' r'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      run_blocks k C' fn' t0 = r' /\
      ^ldR stk PG fn a U HP ts s0.vs_call_ctx.cc_address r r'``;
val ldPstepFuel = ``\k ctx callinst s.
  !stk PG G tn fn t n a U B HP H sites X ts r.
    ctx = C /\ ^ldA /\ opaque_use_ok fn /\ ~s.vs_halted /\
    ^ldJ stk PG G tn fn callinst s t n a U B HP H sites X ts /\
    active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
    step_inst k C callinst s = r /\ terminates r ==>
    ?r'. step_inst k C' callinst t = r' /\
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
val ldIndFuel = Term.subst (ListPair.map (fn (v,t) => v |-> t)
  (ldIndVars,[ldPstepFuel,ldPexecFuel,ldPrunFuel])) ldIndBody;
val ldClausesFuel = strip_conj (fst (dest_imp ldIndFuel));

Theorem ld_runner_packet_terminates:
  ^ldR stk PG fn a U HP ts A0 r r' ==> terminates r'
Proof
  Cases_on `r` >> simp[terminates_def] >> rpt strip_tac >> gvs[terminates_def]
QED

(* ===== Cut budgets and event prefixes ===== *)

Theorem ld_budget_cut:
  j + LENGTH vs.vs_gas_readings <= ncut + LENGTH s.vs_gas_readings /\
  0 < j ==>
  gas_cut ncut vs s
Proof
  rw[gas_cut_def] >> decide_tac
QED

Theorem ld_budget_drop:
  v.vs_gas_readings = DROP k s.vs_gas_readings /\
  j + LENGTH vs.vs_gas_readings <= ncut + LENGTH s.vs_gas_readings /\
  k < j ==>
  j - k + LENGTH vs.vs_gas_readings <= ncut + LENGTH v.vs_gas_readings /\
  0 < j - k
Proof
  rw[LENGTH_DROP] >> decide_tac
QED

Theorem ld_step_ok_readings:
  step_inst fuel C inst s = OK v ==>
  v.vs_gas_readings =
    DROP (LENGTH (gas_events_step fuel C owner inst s)) s.vs_gas_readings
Proof
  strip_tac >> mp_tac (cj 1 gas_count_suffix) >>
  disch_then (qspecl_then [`fuel`,`C`,`inst`,`s`] mp_tac) >>
  simp[gas_count_suffix_def, gas_events_length]
QED

Theorem ld_block_ok_readings:
  exec_block fuel C bb s = OK v ==>
  v.vs_gas_readings =
    DROP (LENGTH (gas_events_block fuel C owner bb s)) s.vs_gas_readings
Proof
  strip_tac >> mp_tac (cj 2 gas_count_suffix) >>
  disch_then (qspecl_then [`fuel`,`C`,`bb`,`s`] mp_tac) >>
  simp[gas_count_suffix_def, gas_events_length]
QED

Theorem ld_take_length:
  TAKE j b = TAKE j a /\ j <= LENGTH a ==> j <= LENGTH b
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  qpat_x_assum `TAKE j b = _` (mp_tac o AP_TERM ``LENGTH:'a list -> num``) >>
  simp[LENGTH_TAKE_EQ] >> decide_tac
QED

Theorem ld_take_append_eq:
  j <= LENGTH a /\ TAKE j b = TAKE j a ==>
  TAKE j (b ++ y) = TAKE j (a ++ x)
Proof
  strip_tac >> `j <= LENGTH b` by metis_tac[ld_take_length] >>
  simp[listTheory.TAKE_APPEND1]
QED

Theorem ld_take_append_right:
  LENGTH a < j /\ TAKE (j - LENGTH a) y = TAKE (j - LENGTH a) x ==>
  TAKE j (a ++ y) = TAKE j (a ++ x)
Proof
  rpt strip_tac >> simp[listTheory.TAKE_APPEND2]
QED

Theorem ld_step_events_fuel_take:
  m <= m' /\ j <= LENGTH (gas_events_step m C owner inst s) ==>
  TAKE j (gas_events_step m' C owner inst s) =
  TAKE j (gas_events_step m C owner inst s)
Proof
  strip_tac >>
  `?extra. gas_events_step m' C owner inst s =
           gas_events_step m C owner inst s ++ extra` by
    (irule (cj 1 (cj 1 gas_events_fuel_extension)) >> simp[]) >>
  simp[listTheory.TAKE_APPEND1]
QED

Theorem ld_block_events_fuel_take:
  m <= m' /\ j <= LENGTH (gas_events_block m C owner bb s) ==>
  TAKE j (gas_events_block m' C owner bb s) =
  TAKE j (gas_events_block m C owner bb s)
Proof
  strip_tac >>
  `?extra. gas_events_block m' C owner bb s =
           gas_events_block m C owner bb s ++ extra` by
    (irule (cj 1 (cj 2 gas_events_fuel_extension)) >> simp[]) >>
  simp[listTheory.TAKE_APPEND1]
QED

Theorem ld_blocks_events_fuel_take:
  m <= m' /\ j <= LENGTH (gas_events_blocks m C fn s) ==>
  TAKE j (gas_events_blocks m' C fn s) = TAKE j (gas_events_blocks m C fn s)
Proof
  strip_tac >>
  `?extra. gas_events_blocks m' C fn s =
           gas_events_blocks m C fn s ++ extra` by
    (irule (cj 1 (cj 3 gas_events_fuel_extension)) >> simp[]) >>
  simp[listTheory.TAKE_APPEND1]
QED

Theorem ld_block_events_unfold:
  !fuel C owner bb s inst.
    get_instruction bb s.vs_inst_idx = SOME inst ==>
    gas_events_block fuel C owner bb s =
    gas_events_step fuel C owner inst s ++
    (case step_inst fuel C inst s of
       OK s' => if is_terminator inst.inst_opcode then []
                else gas_events_block fuel C owner bb
                       (s' with vs_inst_idx := SUC s.vs_inst_idx)
     | _ => [])
Proof
  rpt strip_tac >> CONV_TAC (LHS_CONV (REWR_CONV gas_events_block_def)) >>
  simp[]
QED

Theorem ld_block_events_step_stop:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (!v. step_inst fuel C inst s = OK v ==> is_terminator inst.inst_opcode) ==>
  gas_events_block fuel C owner bb s = gas_events_step fuel C owner inst s
Proof
  strip_tac >> CONV_TAC (LHS_CONV (REWR_CONV gas_events_block_def)) >>
  Cases_on `step_inst fuel C inst s` >> simp[]
QED

Theorem ld_block_events_step_length:
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  LENGTH (gas_events_step fuel C owner inst s) <=
  LENGTH (gas_events_block fuel C owner bb s)
Proof
  strip_tac >> CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV gas_events_block_def))) >>
  simp[]
QED

Theorem ld_step_budget:
  step_inst fuel C inst s = OK v /\
  j + LENGTH vs.vs_gas_readings <= ncut + LENGTH s.vs_gas_readings /\
  LENGTH (gas_events_step fuel C owner inst s) < j ==>
  j - LENGTH (gas_events_step fuel C owner inst s) + LENGTH vs.vs_gas_readings <=
    ncut + LENGTH v.vs_gas_readings /\
  0 < j - LENGTH (gas_events_step fuel C owner inst s)
Proof
  strip_tac >> drule ld_step_ok_readings >>
  disch_then (qspec_then `owner` assume_tac) >>
  drule_all ld_budget_drop >> simp[]
QED

Theorem ld_block_budget:
  exec_block fuel C bb s = OK v /\
  j + LENGTH vs.vs_gas_readings <= ncut + LENGTH s.vs_gas_readings /\
  LENGTH (gas_events_block fuel C owner bb s) < j ==>
  j - LENGTH (gas_events_block fuel C owner bb s) + LENGTH vs.vs_gas_readings <=
    ncut + LENGTH v.vs_gas_readings /\
  0 < j - LENGTH (gas_events_block fuel C owner bb s)
Proof
  strip_tac >> drule ld_block_ok_readings >>
  disch_then (qspec_then `owner` assume_tac) >>
  drule_all ld_budget_drop >> simp[]
QED

Theorem ld_run_zero[local]:
  run_blocks 0 C fn s = Error "out of fuel" /\ gas_events_blocks 0 C fn s = []
Proof
  conj_tac >- simp[Once run_blocks_def] >> simp[Once gas_events_blocks_def]
QED

Theorem ld_run_enters:
  terminates (run_blocks k C fn v) \/ gas_events_blocks k C fn v <> [] ==>
  ?sn. enters_block fn v sn
Proof
  Cases_on `k` >- simp[ld_run_zero, terminates_def] >>
  simp[Once run_blocks_def, Once gas_events_blocks_def] >>
  Cases_on `lookup_block v.vs_current_bb fn.fn_blocks` >> simp[terminates_def] >>
  rename1 `lookup_block v.vs_current_bb fn.fn_blocks = SOME dest` >>
  `(?p. eval_phis v dest.bb_instructions = OK p) \/
   (?e. eval_phis v dest.bb_instructions = Error e)` by
    metis_tac[eval_phis_ok_or_error_defs] >>
  gvs[terminates_def, enters_block_def]
QED

val sinT = ``s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions``;
val tinT = ``s_phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions``;

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
  Cases_on `fuel` >- gvs[ld_run_zero, terminates_def] >>
  qpat_assum `enters_block fn s s1`
    (strip_assume_tac o REWRITE_RULE [enters_block_def]) >>
  qpat_assum `enters_block fn' t0 t1`
    (strip_assume_tac o REWRITE_RULE [enters_block_def]) >>
  gvs[] >>
  `s_phi.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `s_phi'.vs_current_bb = t0.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `s_phi.vs_gas_readings = s.vs_gas_readings` by
    metis_tac[gas_count_phis_ok] >>
  `get_instruction bb (phi_prefix_length bb.bb_instructions) = SOME i` by
    (qpat_x_assum `active_inst fn i _` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb''` by
       (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
     gvs[get_instruction_def]) >>
  rename1 `run_blocks (SUC k) C fn s` >>
  `lookup_block (^sinT).vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb (^sinT).vs_inst_idx = SOME i /\
   (^sinT).vs_gas_readings = s.vs_gas_readings /\
   lookup_block (^tinT).vs_current_bb fn'.fn_blocks = SOME bb' /\
   lookup_block s_phi.vs_current_bb fn.fn_blocks = SOME bb` by
    simp[] >>
  `j + LENGTH vs.vs_gas_readings <= ncut + LENGTH s_phi.vs_gas_readings /\
   j + LENGTH vs.vs_gas_readings <= ncut + LENGTH (^sinT).vs_gas_readings` by
    simp[] >>
  `run_blocks (SUC k) C fn s =
     case exec_block k C bb (^sinT) of
       OK v => if v.vs_halted then Halt v else run_blocks k C fn v
     | IntRet vals se => IntRet vals se
     | other => other` by
    (CONV_TAC (LHS_CONV (REWR_CONV run_blocks_def)) >> simp[]) >>
  `gas_events_blocks (SUC k) C fn s =
     gas_events_block k C fn.fn_name bb (^sinT) ++
     (case exec_block k C bb (^sinT) of
        OK v => if v.vs_halted then [] else gas_events_blocks k C fn v
      | _ => [])` by
    (CONV_TAC (LHS_CONV (REWR_CONV gas_events_blocks_def)) >>
     simp[]) >>
  `!m. run_blocks (SUC m) C' fn' t0 =
     case exec_block m C' bb' (^tinT) of
       OK v => if v.vs_halted then Halt v else run_blocks m C' fn' v
     | IntRet vals se => IntRet vals se
     | other => other` by
    (gen_tac >> CONV_TAC (LHS_CONV (REWR_CONV run_blocks_def)) >>
     simp[]) >>
  `!m. gas_events_blocks (SUC m) C' fn' t0 =
     gas_events_block m C' fn'.fn_name bb' (^tinT) ++
     (case exec_block m C' bb' (^tinT) of
        OK v => if v.vs_halted then [] else gas_events_blocks m C' fn' v
      | _ => [])` by
    (gen_tac >> CONV_TAC (LHS_CONV (REWR_CONV gas_events_blocks_def)) >>
     simp[]) >>
  `LENGTH (gas_events_block k C fn.fn_name bb (^sinT)) <=
   LENGTH (gas_events_blocks (SUC k) C fn s)` by simp[] >>
  Cases_on `j <= LENGTH (gas_events_block k C fn.fn_name bb (^sinT))`
  >- suspend "prefix" >>
  `LENGTH (gas_events_block k C fn.fn_name bb (^sinT)) < j` by decide_tac >>
  Cases_on `exec_block k C bb (^sinT)`
  >- suspend "branch"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "return"
  >> gvs[terminates_def]
QED

Resume ld_runner_run_clause[prefix]:
  conj_tac >- (strip_tac >> `F` suffices_by simp[] >> decide_tac) >>
  strip_tac >>
  first_x_assum (drule_all_then (mp_tac o CONJUNCT2)) >>
  impl_tac >- simp[] >> strip_tac >> gvs[] >>
  qexists_tac `SUC m` >> simp[] >>
  irule ld_take_append_eq >> simp[]
QED

val ld_run_final_tac =
  first_x_assum (drule_all_then (mp_tac o CONJUNCT1)) >>
  impl_tac >- simp[terminates_def] >> strip_tac >>
  `LENGTH (gas_events_blocks (SUC k) C fn s) < j` by simp[] >>
  reverse conj_tac
  >- (strip_tac >> `F` suffices_by simp[] >> decide_tac) >>
  strip_tac >> gvs[] >>
  qpat_assum `Abbrev (RR = _)` (fn rr =>
    qpat_assum `RR _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o SIMP_RULE (srw_ss())
        [REWRITE_RULE [markerTheory.Abbrev_def] rr])) >>
  gvs[] >>
  qexists_tac `SUC m` >> simp[] >>
  qpat_x_assum `RR _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[];

Resume ld_runner_run_clause[halt]:
  ld_run_final_tac
QED

Resume ld_runner_run_clause[abort]:
  ld_run_final_tac
QED

Resume ld_runner_run_clause[return]:
  ld_run_final_tac
QED

Resume ld_runner_run_clause[branch]:
  `~v.vs_halted` by metis_tac[exec_block_OK_not_halted] >>
  `run_blocks (SUC k) C fn s = run_blocks k C fn v /\
   gas_events_blocks (SUC k) C fn s =
     gas_events_block k C fn.fn_name bb (^sinT) ++ gas_events_blocks k C fn v` by
    simp[] >>
  reverse (Cases_on
    `terminates (run_blocks k C fn v) \/ gas_events_blocks k C fn v <> []`)
  >- gvs[] >>
  first_x_assum (drule_all_then (mp_tac o CONJUNCT1)) >>
  impl_tac >- simp[terminates_def] >> strip_tac >> gvs[] >>
  qpat_assum `Abbrev (RR = _)` (fn rr =>
    qpat_assum `RR _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o SIMP_RULE (srw_ss())
        [REWRITE_RULE [markerTheory.Abbrev_def] rr])) >>
  `MEM bi.inst_opcode [JMP; JNZ; DJMP]` by simp[] >>
  `?sn. enters_block fn v sn` by metis_tac[ld_run_enters] >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ld_branch_endpoint_consume) >>
  strip_tac >> gvs[] >>
  `j - LENGTH (gas_events_block k C fn.fn_name bb (^sinT)) +
     LENGTH vs.vs_gas_readings <= ncut + LENGTH v.vs_gas_readings /\
   0 < j - LENGTH (gas_events_block k C fn.fn_name bb (^sinT))` by
    (irule ld_block_budget >> simp[]) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  `exec_block m C' bb' (^tinT) = OK te` by simp[] >>
  `~te.vs_halted` by metis_tac[exec_block_OK_not_halted] >>
  `!m'. m <= m' ==> exec_block m' C' bb' (^tinT) = OK te /\
     gas_events_block m' C' fn'.fn_name bb' (^tinT) =
     gas_events_block m C' fn'.fn_name bb' (^tinT)` by
    (rpt strip_tac
     >- (irule EQ_TRANS >> qexists_tac `exec_block m C' bb' (^tinT)` >>
         conj_tac >- (irule exec_block_terminates_mono >> simp[terminates_def]) >>
         simp[]) >>
     irule (cj 2 (cj 2 (cj 2 gas_events_fuel_extension))) >> simp[]) >>
  (conj_tac
  >- (
      strip_tac >>
      qpat_x_assum `terminates _ /\ _ < _ ==> _` mp_tac >>
      impl_tac >- (fs[] >> decide_tac) >> strip_tac >>
      rename1 `gas_events_blocks mr C' fn' te = _` >>
      `terminates (run_blocks mr C' fn' te)` by
        (qpat_assum `Abbrev (RR = _)` (fn rr =>
          qpat_assum `RR _ _ _ _ _ _ _ _ (run_blocks k C fn v) _`
            (mp_tac o REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] rr])) >>
         CONV_TAC (LAND_CONV (DEPTH_CONV BETA_CONV)) >>
         disch_tac >>
         drule (SIMP_RULE (srw_ss()) [] ld_runner_packet_terminates) >> simp[]) >>
      `run_blocks (MAX m mr) C' fn' te = run_blocks mr C' fn' te` by
        (irule run_blocks_terminates_mono >> simp[]) >>
      `gas_events_blocks (MAX m mr) C' fn' te = gas_events_blocks mr C' fn' te` by
        (irule (cj 2 (cj 2 (cj 3 gas_events_fuel_extension))) >>
         simp[] >> Cases_on `run_blocks mr C' fn' te` >> fs[terminates_def]) >>
      `m <= MAX m mr` by simp[] >>
      qexists_tac `SUC (MAX m mr)` >> simp[]) >>
  (
      strip_tac >>
      `j - LENGTH (gas_events_block k C fn.fn_name bb (^sinT)) <=
       LENGTH (gas_events_blocks k C fn v)` by decide_tac >>
      qpat_x_assum `_ <= _ ==> _` (drule_then strip_assume_tac) >>
      rename1 `TAKE _ (gas_events_blocks mr C' fn' te)` >>
      `TAKE (j - LENGTH (gas_events_block k C fn.fn_name bb (^sinT)))
         (gas_events_blocks (MAX m mr) C' fn' te) =
       TAKE (j - LENGTH (gas_events_block k C fn.fn_name bb (^sinT)))
         (gas_events_blocks mr C' fn' te)` by
        (irule ld_blocks_events_fuel_take >> simp[] >>
         `j - LENGTH (gas_events_block k C fn.fn_name bb (^sinT)) <=
          LENGTH (gas_events_blocks mr C' fn' te)` by
           (irule ld_take_length >>
            qexists_tac `gas_events_blocks k C fn v` >> simp[]) >>
         decide_tac) >>
      `m <= MAX m mr` by simp[] >>
      qexists_tac `SUC (MAX m mr)` >> simp[] >>
      irule ld_take_append_right >> simp[]))
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

Theorem ld_runner_run_clause_fuel:
  ^(List.nth(ldClausesFuel,2))
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

Resume ld_runner_run_clause_fuel[halt]:
  `?te. bt = Halt te` by fs[Abbr `RR`] >>
  qpat_x_assum `Abbrev (Halt v = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `exec_block k C' bb'
      (s_phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = Halt te` by
    fs[Abbr `bt`] >>
  simp[Once run_blocks_def] >> simp[Once run_blocks_def] >>
  qpat_x_assum `RR _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[]
QED
Resume ld_runner_run_clause_fuel[abort]:
  `?te. bt = Abort a' te` by fs[Abbr `RR`] >>
  qpat_x_assum `Abbrev (Abort _ _ = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `exec_block k C' bb'
      (s_phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = Abort a' te` by
    fs[Abbr `bt`] >>
  simp[Once run_blocks_def] >> simp[Once run_blocks_def] >>
  qpat_x_assum `RR _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[]
QED
Resume ld_runner_run_clause_fuel[return]:
  `?jr tr. bt = IntRet jr tr` by
    (fs[Abbr `RR`] >> metis_tac[]) >>
  qpat_x_assum `Abbrev (IntRet _ _ = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `exec_block k C' bb'
      (s_phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = IntRet jr tr` by
    fs[Abbr `bt`] >>
  simp[Once run_blocks_def] >> simp[Once run_blocks_def] >>
  qpat_x_assum `RR _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[]
QED
Resume ld_runner_run_clause_fuel[branch]:
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
  strip_tac >> gvs[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  `~te.vs_halted` by metis_tac[exec_block_OK_not_halted] >>
  `run_blocks (SUC k) C fn s = run_blocks k C fn v` by
    (qpat_assum `run_block_non_phis k C bb sin = OK v`
       (mp_tac o SIMP_RULE (srw_ss()) [Abbr `sin`]) >>
     simp[Once run_blocks_def]) >>
  `run_blocks (SUC k) C' fn' t0 = run_blocks k C' fn' te` by
    simp[Once run_blocks_def] >>
  simp[]
QED
Finalise ld_runner_run_clause_fuel

Theorem ld_runner_conditional_induction_fuel:
  ^(mk_imp(list_mk_conj [List.nth(ldClausesFuel,0), List.nth(ldClausesFuel,1)],
           snd(dest_imp ldIndFuel)))
Proof
  strip_tac >> irule run_defs_ind >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  MATCH_ACCEPT_TAC ld_runner_run_clause_fuel
QED
