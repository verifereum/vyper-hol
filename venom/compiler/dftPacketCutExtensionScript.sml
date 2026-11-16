Theory dftPacketCutExtension
Ancestors
  dftPacketNativeContinuation dftGasFromListReadings dftGasFromListTraceDefs
  rich_list dftPacketRootedCompose

Theorem dft_packet_native_child_insert:
  !F C root_fn root_entry T b j a e sf c u nm ops csf args cs
    child_before visit child_after.
    T = trace_blocks [] 0 F C root_fn root_entry /\
    b = (e,c.inst_id)::a /\
    j < LENGTH T /\ EL j T = ((a,e,c.inst_id),sf,c,u) /\
    c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME csf /\
    eval_operands ops u = SOME args /\ setup_callee csf args u = SOME cs /\
    trace_blocks b e (F-e) C csf cs =
      child_before ++ [visit] ++ child_after ==>
    (?after. T = TAKE j T ++ [((a,e,c.inst_id),sf,c,u)] ++
      child_before ++ [visit] ++ after) /\
    trace_gas (TAKE j T ++ [((a,e,c.inst_id),sf,c,u)] ++ child_before) =
      trace_gas (TAKE j T) ++ trace_gas child_before /\
    (!K0 gs0 K1 gs1.
      trace_gas (TAKE j T) = ZIP (K0,gs0) /\
      trace_gas child_before = ZIP (K1,gs1) /\
      LENGTH K0 = LENGTH gs0 /\ LENGTH K1 = LENGTH gs1 ==>
      trace_gas (TAKE j T ++ [((a,e,c.inst_id),sf,c,u)] ++ child_before) =
        ZIP (K0 ++ K1,gs0 ++ gs1))
Proof
  rpt gen_tac >> strip_tac >>
  reverse conj_tac
  >- (simp[visit_gas_def] >> rpt strip_tac >> simp[GSYM ZIP_APPEND]) >>
  gvs[] >> drule_all native_trace_blocks_continuation >> strip_tac >>
  drule_then assume_tac trace_block_visit >>
  drule_all trace_step_invoke >> strip_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `child_before ++ [visit] ++ child_after ++ caller_tail ++ rest` >>
  qexists_tac `child_after ++ caller_tail ++ rest` >>
  qpat_x_assum `DROP j _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `TAKE j rt` >>
  strip_tac >>
  qspecl_then [`j`,`rt`] mp_tac listTheory.TAKE_DROP >>
  pure_asm_rewrite_tac [GSYM APPEND_ASSOC,listTheory.APPEND] >>
  metis_tac[]
QED

Theorem dft_packet_fresh_level_semantics:
  !R (P : string -> (basic_block # num # instruction list) list ->
       venom_state -> (string # num) list # exec_result)
    (S : instruction -> venom_state -> exec_result)
    pre sf plan c csf bb e z entry cs M0 M1 E0 E1 gs0 gs1.
  R = (\levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
          (prior ++ FST (P sf.fn_name plan ent),
           case SND (P sf.fn_name plan ent) of
             OK caller => (case call of NONE => OK caller | SOME c => S c caller)
           | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs0 /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M1 gs1 /\
  (!t.
    (?extra. E0 = FST (R (pre ++ [(sf,plan,NONE)])
      (entry with vs_gas_readings := gs0 ++ t)) ++ extra) /\
    (!events u.
      R (pre ++ [(sf,plan,NONE)])
        (entry with vs_gas_readings := gs0 ++ t) = (events,OK u) ==>
      events = E0 /\ u.vs_gas_readings = t /\
      (!t'. R (pre ++ [(sf,plan,NONE)])
        (entry with vs_gas_readings := gs0 ++ t') =
          (E0,OK (u with vs_gas_readings := t'))))) /\
  (!t u.
    R (pre ++ [(sf,plan,NONE)])
      (entry with vs_gas_readings := gs0 ++ gs1 ++ t) = (E0,OK u) ==>
    S c u = OK (cs with vs_gas_readings := gs1 ++ t)) /\
  (!t.
    (?extra. E1 = FST (R [(csf,[(bb,e,z)],NONE)]
      (cs with vs_gas_readings := gs1 ++ t)) ++ extra) /\
    (!events v.
      R [(csf,[(bb,e,z)],NONE)]
        (cs with vs_gas_readings := gs1 ++ t) = (events,OK v) ==>
      events = E1 /\ v.vs_gas_readings = t /\
      (!t'. R [(csf,[(bb,e,z)],NONE)]
        (cs with vs_gas_readings := gs1 ++ t') =
          (E1,OK (v with vs_gas_readings := t'))))) ==>
  !tail.
    (?extra. E0 ++ E1 =
      FST (R (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(bb,e,z)],NONE)])
        (entry with vs_gas_readings := gs0 ++ gs1 ++ tail)) ++ extra) /\
    (!events v.
      R (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(bb,e,z)],NONE)])
        (entry with vs_gas_readings := gs0 ++ gs1 ++ tail) = (events,OK v) ==>
      events = E0 ++ E1 /\ v.vs_gas_readings = tail /\
      (!tail'. R (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(bb,e,z)],NONE)])
        (entry with vs_gas_readings := gs0 ++ gs1 ++ tail') =
          (E0 ++ E1,OK (v with vs_gas_readings := tail')))) /\
    (!events r.
      R (pre ++ [(sf,plan,NONE)])
        (entry with vs_gas_readings := gs0 ++ gs1 ++ tail) = (events,r) /\
      (~?u. r = OK u) ==>
      R (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(bb,e,z)],NONE)])
        (entry with vs_gas_readings := gs0 ++ gs1 ++ tail) = (events,r)) /\
    (!u.
      R (pre ++ [(sf,plan,NONE)])
        (entry with vs_gas_readings := gs0 ++ gs1 ++ tail) = (E0,OK u) ==>
      R (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(bb,e,z)],NONE)])
        (entry with vs_gas_readings := gs0 ++ gs1 ++ tail) =
        (E0 ++ FST (R [(csf,[(bb,e,z)],NONE)]
          (cs with vs_gas_readings := gs1 ++ tail)),
         SND (R [(csf,[(bb,e,z)],NONE)]
          (cs with vs_gas_readings := gs1 ++ tail))))
Proof
  rpt gen_tac >> strip_tac >>
  `!tail events r.
    R (pre ++ [(sf,plan,NONE)])
      (entry with vs_gas_readings := gs0 ++ gs1 ++ tail) = (events,r) /\
    (~?u. r = OK u) ==>
    R (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(bb,e,z)],NONE)])
      (entry with vs_gas_readings := gs0 ++ gs1 ++ tail) = (events,r)` by
    (rpt strip_tac >>
     irule dft_packet_rooted_call_stopped >>
     metis_tac[APPEND]) >>
  `!tail u.
    R (pre ++ [(sf,plan,NONE)])
      (entry with vs_gas_readings := gs0 ++ gs1 ++ tail) = (E0,OK u) ==>
    R (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(bb,e,z)],NONE)])
      (entry with vs_gas_readings := gs0 ++ gs1 ++ tail) =
      (E0 ++ FST (R [(csf,[(bb,e,z)],NONE)]
        (cs with vs_gas_readings := gs1 ++ tail)),
       SND (R [(csf,[(bb,e,z)],NONE)]
        (cs with vs_gas_readings := gs1 ++ tail)))` by
    (rpt strip_tac >>
     irule dft_packet_rooted_call_append >> metis_tac[APPEND]) >>
  qpat_x_assum `R = _` kall_tac >>
  qx_gen_tac `tail` >>
  qpat_assum `!t. (?extra. E0 = _) /\ _`
    (qspec_then `gs1 ++ tail` strip_assume_tac) >>
  qpat_assum `!t. (?extra. E1 = _) /\ _`
    (qspec_then `tail` strip_assume_tac) >>
  Cases_on `R (pre ++ [(sf,plan,NONE)])
    (entry with vs_gas_readings := gs0 ++ gs1 ++ tail)` >>
  rename1 `_ = (old_events,old_result)` >>
  Cases_on `?u. old_result = OK u`
  >- (pop_assum (qx_choose_then `u` SUBST_ALL_TAC) >>
      qpat_x_assum `!events u. R (pre ++ _) _ = _ ==> _`
        (qspecl_then [`old_events`,`u`] mp_tac) >>
      (impl_tac >- metis_tac[APPEND_ASSOC]) >>
      strip_tac >>
      qpat_x_assum `old_events = E0` SUBST_ALL_TAC >>
      `!t. R (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(bb,e,z)],NONE)])
        (entry with vs_gas_readings := gs0 ++ gs1 ++ t) =
        (E0 ++ FST (R [(csf,[(bb,e,z)],NONE)]
          (cs with vs_gas_readings := gs1 ++ t)),
         SND (R [(csf,[(bb,e,z)],NONE)]
          (cs with vs_gas_readings := gs1 ++ t)))` by
        (gen_tac >> first_x_assum irule >> metis_tac[APPEND_ASSOC]) >>
      qpat_x_assum `!t. (?extra. E0 = _) /\ _` kall_tac >>
      qpat_x_assum `!t. (?extra. E1 = _) /\ _` kall_tac >>
      qpat_x_assum `!t'. R (pre ++ [(sf,plan,NONE)]) _ = _` kall_tac >>
      qpat_x_assum `E0 = _ ++ extra` kall_tac >>
      conj_tac >- (qexists_tac `extra'` >> metis_tac[APPEND_ASSOC,pairTheory.FST]) >>
      qpat_x_assum `E1 = _ ++ extra'` kall_tac >>
      reverse conj_tac >- (simp[] >> metis_tac[]) >>
      Cases_on `R [(csf,[(bb,e,z)],NONE)]
        (cs with vs_gas_readings := gs1 ++ tail)` >>
      rename1 `_ = (child_events,child_result)` >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!events v. (child_events,child_result) = _ ==> _`
        (qspecl_then [`child_events`,`v`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >> simp[]) >>
  qpat_x_assum `!t. (?extra. E0 = _) /\ _` kall_tac >>
  qpat_x_assum `!t. (?extra. E1 = _) /\ _` kall_tac >>
  `R (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(bb,e,z)],NONE)])
    (entry with vs_gas_readings := gs0 ++ gs1 ++ tail) =
      (old_events,old_result)` by metis_tac[] >>
  conj_tac
  >- (qexists_tac `extra ++ E1` >> metis_tac[APPEND_ASSOC,pairTheory.FST]) >>
  qpat_x_assum `E0 = _ ++ extra` kall_tac >>
  qpat_x_assum `E1 = _ ++ extra'` kall_tac >>
  simp[] >> metis_tac[pairTheory.PAIR_EQ]
QED

Theorem dft_packet_levels_call_extend:
  !F C rooted_eval plan_ok levels_ok pre sf plan paths incoming root_fn entry
    a bb0 e0 z0 c nm ops csf bb e z.
  levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
    levels <> [] /\ LENGTH paths = LENGTH levels /\
    LENGTH incoming = LENGTH levels /\
    HD paths = root_path /\ HD incoming = root_depth /\
    FST (HD levels) = root_fn /\
    (!i sf plan call.
      i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
      plan <> [] /\
      (!prior ent.
        rooted_eval F C (TAKE i levels) root_entry = (prior,OK ent) ==>
        plan_ok F C sf (EL i incoming) plan ent) /\
      (if SUC i < LENGTH levels then
        ?c nm ops bb e z.
          call = SOME c /\ LAST plan = (bb,e,z) /\
          c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
            bb.bb_instructions) /\
          c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
          lookup_function nm C.ctx_functions = SOME (FST (EL (SUC i) levels)) /\
          EL (SUC i) incoming = e /\
          EL (SUC i) paths = (e,c.inst_id)::EL i paths
       else call = NONE))) /\
  levels_ok F C (pre ++ [(sf,plan,NONE)]) paths incoming root_fn entry [] 0 /\
  LAST paths = a /\ LAST plan = (bb0,e0,z0) /\
  c = EL (LENGTH z0) (DROP (phi_prefix_length bb0.bb_instructions)
    bb0.bb_instructions) /\
  c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME csf /\
  (!prior ent.
    rooted_eval F C (pre ++ [(sf,plan,SOME c)]) entry = (prior,OK ent) ==>
    plan_ok F C csf e0 [(bb,e,z)] ent) ==>
  levels_ok F C (pre ++ [(sf,plan,SOME c);(csf,[(bb,e,z)],NONE)])
    (paths ++ [(e0,c.inst_id)::a]) (incoming ++ [e0]) root_fn entry [] 0
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `levels_ok = _` SUBST_ALL_TAC >>
  gvs[] >>
  rpt conj_tac
  >- (Cases_on `paths` >> gvs[])
  >- (Cases_on `incoming` >> gvs[])
  >- (Cases_on `pre` >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `i < LENGTH pre`
  >- (qpat_x_assum `EL i (pre ++ _) = _` mp_tac >>
      simp[EL_APPEND] >> strip_tac >>
      qpat_x_assum `!i sf' plan' call. _`
        (qspecl_then [`i`,`sf'`,`plan'`,`call`] mp_tac) >>
      `i <= LENGTH pre /\ SUC i <= LENGTH pre` by decide_tac >>
      simp[TAKE_APPEND1,EL_APPEND] >>
      Cases_on `SUC i < LENGTH pre`
      >- (simp[] >> metis_tac[]) >>
      `SUC i = LENGTH pre` by decide_tac >> simp[] >> metis_tac[]) >>
  Cases_on `i = LENGTH pre`
  >- (gvs[EL_APPEND] >>
      qpat_x_assum `!i sf' plan' call. _`
        (qspecl_then [`LENGTH pre`,`sf`,`plan`,`NONE`] mp_tac) >>
      simp[EL_APPEND,TAKE_APPEND1] >> strip_tac >>
      `paths <> []` by (Cases_on `paths` >> gvs[]) >>
      simp[GSYM arithmeticTheory.ADD1,listTheory.LAST_EL]) >>
  `i = LENGTH pre + 1` by decide_tac >>
  gvs[EL_APPEND,arithmeticTheory.ADD1,TAKE_APPEND] >>
  simp[listTheory.TAKE_LENGTH_TOO_LONG]
QED
