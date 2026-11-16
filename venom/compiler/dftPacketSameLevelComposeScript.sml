Theory dftPacketSameLevelCompose
Ancestors
  dftPacketRootedCompose dftPacketNativeContinuation dftPacketNativeSlice
  dftGasFromListReadings venomExecSemantics venomInst venomState list rich_list

Theorem dft_packet_rooted_row_extend:
  !R (P : string -> (basic_block # num # instruction list) list ->
       venom_state -> (string # num) list # exec_result)
    (S : instruction -> venom_state -> exec_result)
    (row_eval : string -> (basic_block # num # instruction list) ->
       venom_state -> (string # num) list # exec_result)
    H pre sf rows bb e z0 z1 entry.
  P = (\owner plan ent.
    FOLDL (\(ev,r) row. case r of
      OK u => (ev ++ FST (row_eval owner row u), SND (row_eval owner row u))
    | other => (ev,other)) ([],OK ent) plan) /\
  R = (\levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
          (prior ++ FST (P sf.fn_name plan ent),
           case SND (P sf.fn_name plan ent) of
             OK caller => (case call of NONE => OK caller | SOME c => S c caller)
           | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  (!u. row_eval sf.fn_name (bb,e,z1) u =
    (case SND (row_eval sf.fn_name (bb,e,z0) u) of
       OK v => (FST (row_eval sf.fn_name (bb,e,z0) u) ++ FST (H v), SND (H v))
     | other => (FST (row_eval sf.fn_name (bb,e,z0) u),other))) ==>
  R (pre ++ [(sf,rows ++ [(bb,e,z1)],NONE)]) entry =
    (case SND (R (pre ++ [(sf,rows ++ [(bb,e,z0)],NONE)]) entry) of
       OK v => (FST (R (pre ++ [(sf,rows ++ [(bb,e,z0)],NONE)]) entry) ++
                  FST (H v), SND (H v))
     | other => (FST (R (pre ++ [(sf,rows ++ [(bb,e,z0)],NONE)]) entry),other))
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `FOLDL fstep` >>
  simp[FOLDL_APPEND, FOLDL] >>
  Cases_on `FOLDL fstep ([],OK entry) pre` >>
  rename1 `FOLDL fstep ([],OK entry) pre = (prior,result)` >>
  Cases_on `result` >> simp[Abbr `fstep`, FOLDL_APPEND, FOLDL] >>
  qmatch_goalsub_abbrev_tac `FOLDL rstep` >>
  Cases_on `FOLDL rstep ([],OK v) rows` >>
  rename1 `FOLDL rstep ([],OK v) rows = (events,row_result)` >>
  Cases_on `row_result` >> simp[Abbr `rstep`] >>
  Cases_on `row_eval sf.fn_name (bb,e,z0) v'` >>
  rename1 `row_eval sf.fn_name (bb,e,z0) v' = (local_events,local_result)` >>
  first_x_assum (qspec_then `v'` mp_tac) >>
  Cases_on `local_result` >> simp[APPEND_ASSOC] >> strip_tac >> simp[] >>
  Cases_on `SND (H v'')` >> simp[]
QED

Theorem dft_packet_same_level_semantics:
  !(A : bytes32 list -> (string # num) list # exec_result) D
    (H : venom_state -> (string # num) list # exec_result)
    (J : bytes32 list -> exec_result) G U V gs1 E0 E1.
  (!t. D t = (case SND (A t) of
       OK u => (FST (A t) ++ FST (H u), SND (H u))
     | other => (FST (A t),other))) /\
  (!t. (?extra. E0 = FST (A t) ++ extra) /\
    (!ev u. A t = (ev,OK u) ==> ev = E0 /\ u.vs_gas_readings = t /\
      (!t'. A t' = (E0,OK (u with vs_gas_readings := t'))))) /\
  (!t ev r. A t = (ev,r) /\ (~?u. r = OK u) ==> J t = r /\ G t = ev) /\
  (!t u. A t = (E0,OK u) ==> J t = U u /\ G t = E0 ++ V u) /\
  (!t u. A (gs1 ++ t) = (E0,OK u) ==>
    (?extra. E1 = FST (H u) ++ extra) /\
    (!ev v. H u = (ev,OK v) ==> ev = E1 /\ v.vs_gas_readings = t /\
      (!t'. H (u with vs_gas_readings := gs1 ++ t') =
        (E1,OK (v with vs_gas_readings := t')))) /\
    (!ev r. H u = (ev,r) /\ (~?v. r = OK v) ==> U u = r /\ V u = ev)) ==>
  !tail.
    (?extra. E0 ++ E1 = FST (D (gs1 ++ tail)) ++ extra) /\
    (!ev v. D (gs1 ++ tail) = (ev,OK v) ==>
      ev = E0 ++ E1 /\ v.vs_gas_readings = tail /\
      (!tail'. D (gs1 ++ tail') = (E0 ++ E1,OK (v with vs_gas_readings := tail')))) /\
    (!ev r. D (gs1 ++ tail) = (ev,r) /\ (~?v. r = OK v) ==>
      J (gs1 ++ tail) = r /\ G (gs1 ++ tail) = ev)
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "compose")
    (CONJUNCTS_THEN2 (mk_asm "old")
      (CONJUNCTS_THEN2 (mk_asm "old_stop")
        (CONJUNCTS_THEN2 (mk_asm "continue") (mk_asm "local"))))) >>
  gen_tac >> Cases_on `A (gs1 ++ tail)` >>
  rename1 `A (gs1 ++ tail) = (old_events,old_result)` >>
  Cases_on `?u. old_result = OK u`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      asm "old" (qspec_then `gs1 ++ tail` mp_tac) >>
      disch_then (CONJUNCTS_THEN2 kall_tac
        (qspecl_then [`old_events`,`u`] mp_tac)) >> simp[] >>
      disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
        (CONJUNCTS_THEN2 (mk_asm "gas") (mk_asm "old_tail"))) >>
      asm "local" (qspecl_then [`tail`,`u`] mp_tac) >> simp[] >>
      disch_then (CONJUNCTS_THEN2 (mk_asm "coverage")
        (CONJUNCTS_THEN2 (mk_asm "local_success") (mk_asm "local_stop"))) >>
      asm "continue" (qspecl_then [`gs1 ++ tail`,`u`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `H u` >> rename1 `H u = (events,result)` >>
      Cases_on `result`
      >- (asm "local_success" (qspecl_then [`events`,`v`] mp_tac) >>
          simp[] >>
          disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
            (CONJUNCTS_THEN2 (mk_asm "new_gas") (mk_asm "local_tail"))) >>
          simp[markerLib.L "compose", markerLib.L "old_tail", markerLib.L "local_tail", markerLib.L "new_gas"]) >>
      asm "local_stop" (qspecl_then [`events`,`SND (H u)`] mp_tac) >>
      simp[] >> strip_tac >> simp[markerLib.L "compose"] >>
      asm "coverage" mp_tac >> simp[] >> metis_tac[APPEND_ASSOC]) >>
  `J (gs1 ++ tail) = old_result /\ G (gs1 ++ tail) = old_events` by
    (asm "old_stop" (qspecl_then [`gs1 ++ tail`,`old_events`,`old_result`] mp_tac) >> gvs[]) >>
  `D (gs1 ++ tail) = (old_events,old_result)` by
    (Cases_on `old_result` >> simp[markerLib.L "compose"] >> gvs[]) >>
  asm "old" (qspec_then `gs1 ++ tail` mp_tac) >> simp[] >> strip_tac >>
  simp[] >> metis_tac[APPEND_ASSOC]
QED

Theorem dft_packet_native_row_cut:
  !F C root_fn root_entry a e sf bb s i0 k t i1 before after K0 gs0 K1 gs1 T.
  T = trace_blocks [] 0 F C root_fn root_entry /\
  T = before ++ [((a,e,i0.inst_id),sf,i0,s)] ++ after /\
  lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
  s.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
  EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) /\
  FOLDR (dft_exec_cons (F-e) C) OK
    (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) s = OK t /\
  get_instruction bb t.vs_inst_idx = SOME i1 /\
  trace_gas before = ZIP (K0,gs0) /\
  trace_gas (trace_block a e (F-e) C sf
    (bb with bb_instructions := TAKE (s.vs_inst_idx+k) bb.bb_instructions) s) =
      ZIP (K1,gs1) /\
  LENGTH K0 = LENGTH gs0 /\ LENGTH K1 = LENGTH gs1 ==>
  ?before' after'.
    T = before' ++ [((a,e,i1.inst_id),sf,i1,t)] ++ after' /\
    trace_gas before' = ZIP (K0 ++ K1,gs0 ++ gs1)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `T' = trace_blocks [] 0 fuel C root_fn root_entry` >>
  `LENGTH before < LENGTH (trace_blocks [] 0 fuel C root_fn root_entry) /\
   EL (LENGTH before) (trace_blocks [] 0 fuel C root_fn root_entry) =
     ((a,e,i0.inst_id),sf,i0,s)` by
    (qpat_x_assum `T' = trace_blocks _ _ _ _ _ _` (SUBST1_TAC o SYM) >> simp[EL_APPEND]) >>
  drule_all native_trace_blocks_continuation >> strip_tac >>
  `bt = bb` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  drule_at (Pat `FOLDR _ _ _ _ = _`) native_trace_block_prefix_split >> simp[] >>
  disch_then (qspecl_then [`a`,`sf`,`e`] strip_assume_tac) >>
  `?suffix. trace_block a e (fuel-e) C sf bb t =
    ((a,e,i1.inst_id),sf,i1,t)::suffix` by
      (qpat_x_assum `get_instruction bb s.vs_inst_idx = _` kall_tac >>
       drule dftGasFromListTraceDefsTheory.trace_block_visit >> simp[]) >>
  qmatch_asmsub_abbrev_tac `trace_gas pref = ZIP (K1,gs1)` >>
  qexistsl_tac [`before ++ pref`,`suffix ++ rest`] >>
  conj_tac
  >- (qpat_x_assum `DROP (LENGTH before) _ = _` mp_tac >>
      simp[Abbr `pref`, APPEND_ASSOC] >>
      qpat_x_assum `_ = trace_blocks _ _ _ _ _ _` (SUBST1_TAC o SYM) >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  simp[ZIP_APPEND]
QED
