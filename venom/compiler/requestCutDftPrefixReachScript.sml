Theory requestCutDftPrefixReach
Ancestors
  dftGasFromListCalleeSeed dftGasFromListReachBoundary dftGasFromListReplay
  dftGasFromListReadings
  dftGasFromListReplayBoundary dftGasFromListRestore dftGasFromListTraceDefs
  gasOracleReplay dftGasOracleDefs contextCodegenRel contextCodegenRelProps
  venomExecSemantics venomInst venomState list rich_list alist sorting

Theorem trace_point_append[local]:
  xs ++ ys = pre ++ [x] ++ post ==>
  (?rest. xs = pre ++ [x] ++ rest) \/
  (?past. pre = xs ++ past /\ ys = past ++ [x] ++ post)
Proof
  strip_tac >>
  `pre ++ [x] ++ post = xs ++ ys` by simp[] >>
  fs[APPEND_EQ_APPEND_MID] >> metis_tac[APPEND]
QED

(* Agreement through the preceding visits is enough to reach the next
   cursor, even when the rest of the native trace uses other readings. *)
Theorem trace_prefix_visits_reachable:
  (!p d fuel ctx fn inst s. !orc vs0 gs.
    active_inst fn inst s /\
    ev_reachable orc vs0 ctx p d fn inst (s with vs_gas_readings := gs) ==>
    !pre post q e id f i t.
      trace_step p d fuel ctx fn inst s = pre ++ ((q,e,id),f,i,t)::post /\
      trace_agrees orc pre ==>
      ev_reachable orc vs0 ctx q e f i (t with vs_gas_readings := gs)) /\
  (!p d fuel ctx fn bb s. !orc vs0 gs.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (!i. active_inst fn i s ==>
      ev_reachable orc vs0 ctx p d fn i (s with vs_gas_readings := gs)) ==>
    !pre post q e id f i t.
      trace_block p d fuel ctx fn bb s = pre ++ ((q,e,id),f,i,t)::post /\
      trace_agrees orc pre ==>
      ev_reachable orc vs0 ctx q e f i (t with vs_gas_readings := gs)) /\
  (!p d fuel ctx fn s. !orc vs0 gs.
    (!u i. enters_block fn s u /\ active_inst fn i u ==>
      ev_reachable orc vs0 ctx p (SUC d) fn i (u with vs_gas_readings := gs)) ==>
    !pre post q e id f i t.
      trace_blocks p d fuel ctx fn s = pre ++ ((q,e,id),f,i,t)::post /\
      trace_agrees orc pre ==>
      ev_reachable orc vs0 ctx q e f i (t with vs_gas_readings := gs))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_prefix_visits_reachable[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (Cases_on `decode_invoke inst`
      >- simp[Once trace_defs] >>
      rename1 `decode_invoke inst = SOME decoded` >> PairCases_on `decoded` >>
      Cases_on `lookup_function decoded0 ctx.ctx_functions`
      >- simp[Once trace_defs] >>
      rename1 `lookup_function _ _ = SOME callee` >>
      Cases_on `eval_operands decoded1 s`
      >- simp[Once trace_defs] >>
      rename1 `eval_operands _ _ = SOME args` >>
      Cases_on `setup_callee callee args s`
      >- simp[Once trace_defs] >>
      rename1 `setup_callee callee args s = SOME cs` >>
      drule_all trace_step_invoke >> disch_then (fn th =>
        RULE_ASSUM_TAC (REWRITE_RULE [th]) >> rewrite_tac[th]) >>
      rpt strip_tac >>
      qpat_x_assum `!v nm ops fn args cs. _`
        (mp_tac o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]) >>
      disch_then drule >> disch_then drule >>
      disch_then drule >> disch_then drule >>
      disch_then (qspecl_then [`orc`,`vs0`,`gs`] mp_tac) >>
      simp[APPEND] >> metis_tac[restored_callee_entry]) >>
  simp[trace_step_noninvoke]
QED

Resume trace_prefix_visits_reachable[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once trace_defs] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  `active_inst fn inst s` by (irule lookup_instruction_active >> simp[]) >>
  `ev_reachable orc vs0 ctx p d fn inst (s with vs_gas_readings := gs)` by
    metis_tac[] >>
  rpt gen_tac >>
  Cases_on `pre`
  >- (simp[Once (cj 2 trace_defs)] >> strip_tac >> gvs[]) >>
  simp[Once (cj 2 trace_defs)] >>
  strip_tac >>
  drule trace_point_append >> strip_tac >- suspend "block_child" >>
  suspend "block_next"
QED

Resume trace_prefix_visits_reachable[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- simp[] >>
  rename1 `trace_blocks p d (SUC k) ctx fn s` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once trace_defs] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[Once trace_defs] >> gvs[] >>
  rename1 `eval_phis _ _ = OK sp` >>
  `sp.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  `enters_block fn s (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[enters_block_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  drule trace_point_append >> strip_tac >- suspend "blocks_body" >>
  suspend "blocks_next"
QED

Resume trace_prefix_visits_reachable[block_child]:
  `trace_agrees orc t'` by
    (qpat_assum `trace_agrees orc (h::t')` mp_tac >>
     qpat_assum `((p,d,inst.inst_id),fn,inst,s) = h`
       (fn eq => rewrite_tac[GSYM eq]) >> simp[trace_agrees_cons]) >>
  qpat_x_assum `!inst'. SOME inst = SOME inst' ==> _`
    (mp_tac o SRULE []) >>
  disch_then (qspecl_then [`orc`,`vs0`,`gs`] mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`t'`, `rest`, `q`, `e`, `id`, `f`, `i`, `t`] mp_tac) >>
  simp[]
QED

Resume trace_prefix_visits_reachable[block_next]:
  Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
  rename1 `step_inst _ _ _ _ = OK out` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  `trace_agrees orc (((p,d,inst.inst_id),fn,inst,s)::
    trace_step p d fuel ctx fn inst s)` by fs[trace_agrees_cons] >>
  `ev_step orc p d fuel ctx inst (s with vs_gas_readings := gs) =
    OK (out with vs_gas_readings := gs)` by
    (drule (cj 1 trace_replay) >>
     disch_then (qspec_then `gs` mp_tac) >> simp[restore_rel_cases]) >>
  `out.vs_current_bb = s.vs_current_bb` by
    (drule_all ev_step_preserves_current_bb >> simp[]) >>
  qpat_x_assum `!orc vs0 gs. lookup_block _ _ = _ /\ _ ==> _`
    (qspecl_then [`orc`,`vs0`,`gs`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      `ev_reachable orc vs0 ctx p d fn inst (s with vs_gas_readings := gs)` by metis_tac[] >>
      `active_inst fn inst (s with vs_gas_readings := gs)` by simp[active_inst_restore] >>
      `active_inst fn i' ((out with vs_gas_readings := gs) with
        vs_inst_idx := SUC (s with vs_gas_readings := gs).vs_inst_idx)` by
        (fs[active_inst_def] >> metis_tac[]) >>
      drule_all ev_reachable_next >> simp[]) >>
  fs[trace_agrees_cons] >> metis_tac[]
QED

Resume trace_prefix_visits_reachable[blocks_body]:
  qpat_x_assum `!orc vs0 gs. lookup_block _ _ = _ /\ _ ==> _`
    (qspecl_then [`orc`,`vs0`,`gs`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum `!u i. _` (drule_at Any) >> simp[]) >>
  metis_tac[]
QED

Resume trace_prefix_visits_reachable[blocks_next]:
  Cases_on `exec_block k ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> gvs[] >>
  rename1 `exec_block _ _ _ _ = OK out` >>
  Cases_on `out.vs_halted` >> gvs[] >>
  `ev_block orc p (SUC d) k ctx bb
      ((sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
        with vs_gas_readings := gs) = OK (out with vs_gas_readings := gs)` by
    (drule (cj 2 trace_replay) >>
     disch_then (qspec_then `gs` mp_tac) >> simp[restore_rel_cases]) >>
  qpat_x_assum `!orc vs0 gs. (!u i. _) ==> _`
    (qspecl_then [`orc`,`vs0`,`gs`] mp_tac) >>
  impl_tac
  >- (rpt strip_tac >>
      drule enters_block_restore >> disch_then (qspec_then `gs` assume_tac) >>
      `active_inst fn i' (u with vs_gas_readings := gs)` by simp[] >>
      irule ev_block_next_entry >> conj_tac >- simp[] >>
      qexistsl_tac [`bb`,`k`,
        `(sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
          with vs_gas_readings := gs`, `out with vs_gas_readings := gs`] >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!u i. _` (drule_at Any) >> simp[]) >>
  metis_tac[]
QED

Finalise trace_prefix_visits_reachable

Theorem trace_context_prefix_visit:
  trace_context fuel ctx s = pre ++ ((p,d,id),fn,inst,t)::post /\
  trace_agrees orc pre ==>
  ev_reachable orc (s with vs_gas_readings := gs) ctx p d fn inst
    (t with vs_gas_readings := gs)
Proof
  Cases_on `ctx.ctx_entry` >- simp[trace_context_def] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions` >- simp[trace_context_def] >>
  rename1 `lookup_function _ _ = SOME entry_fn` >>
  Cases_on `fn_entry_label entry_fn` >- simp[trace_context_def, trace_function_def] >>
  rename1 `fn_entry_label entry_fn = SOME lbl` >>
  simp[trace_context_def, trace_function_def] >> strip_tac >>
  mp_tac (Q.SPECL [`[]`,`0`,`fuel`,`ctx`,`entry_fn`,
    `s with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>`,
    `orc`,`s with vs_gas_readings := gs`,`gs`] (cj 3 trace_prefix_visits_reachable)) >>
  impl_tac
  >- (rpt strip_tac >>
      `enters_block entry_fn
        ((s with vs_gas_readings := gs) with
          <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
        (u with vs_gas_readings := gs)` by
        (drule enters_block_restore >>
         disch_then (qspec_then `gs` mp_tac) >> simp[]) >>
      `active_inst entry_fn i (u with vs_gas_readings := gs)` by
        simp[active_inst_restore] >>
      simp[] >> irule ev_reachable_entry >> simp[] >> metis_tac[]) >>
  disch_then (qspecl_then [`pre`,`post`,`p`,`d`,`id`,`fn`,`inst`,`t`] mp_tac) >>
  simp[]
QED

(* The observations made by the stopped native prefix determine the
   event reach of every retained target cursor, irrespective of the filling. *)
Theorem trace_context_observed_visit:
  tr = trace_context fuel ctx v /\
  n <= j /\ n < LENGTH tr /\ EL n tr = ((p,d,id),fn,i,t) /\
  obs = trace_gas (TAKE j tr) /\ ALL_DISTINCT (MAP FST obs) ==>
  ev_reachable
    (\key. case ALOOKUP (obs ++ filling) key of NONE => 0w | SOME w => w)
    v ctx p d fn i (t with vs_gas_readings := v.vs_gas_readings)
Proof
  strip_tac >>
  `DROP n tr = ((p,d,id),fn,i,t)::DROP (SUC n) tr` by
    simp[Once DROP_EL_CONS, GSYM arithmeticTheory.ADD1] >>
  `trace_context fuel ctx v = TAKE n tr ++ ((p,d,id),fn,i,t)::DROP (SUC n) tr` by
    (qpat_assum `DROP n tr = _` (SUBST1_TAC o SYM) >> fs[TAKE_DROP]) >>
  `arithmetic$MIN n j = n` by simp[arithmeticTheory.MIN_DEF] >>
  `TAKE n tr = TAKE n (TAKE j tr)` by
    (pure_rewrite_tac[TAKE_TAKE_MIN] >>
     qpat_assum `arithmetic$MIN n j = n` SUBST1_TAC >> REFL_TAC) >>
  `?remaining. obs = trace_gas (TAKE n tr) ++ remaining` by
    (qexists_tac `trace_gas (DROP n (TAKE j tr))` >>
     qpat_assum `obs = _` SUBST1_TAC >>
     qpat_assum `TAKE n tr = _` SUBST1_TAC >>
     pure_rewrite_tac [GSYM trace_gas_append, TAKE_DROP] >> REFL_TAC) >>
  qpat_x_assum `TAKE n tr = _` kall_tac >>
  `!key w. MEM (key,w) (trace_gas (TAKE n tr)) ==> ALOOKUP obs key = SOME w` by
    metis_tac[ALOOKUP_ALL_DISTINCT_MEM, MEM_APPEND] >>
  drule trace_context_prefix_visit >>
  disch_then (qspecl_then
    [`\key. case ALOOKUP (obs ++ filling) key of NONE => 0w | SOME w => w`,
     `v.vs_gas_readings`] mp_tac) >>
  disch_then (irule o SIMP_RULE (srw_ss()) []) >>
  simp_tac bool_ss [trace_agrees_def, EVERY_MEM] >>
  qx_gen_tac `kw` >> Cases_on `kw` >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> strip_tac >>
  rename1 `MEM (key,w) (trace_gas (TAKE n tr))` >>
  `ALOOKUP obs key = SOME w` by metis_tac[] >>
  qpat_assum `ALOOKUP obs key = SOME w`
    (fn eq => simp_tac bool_ss [ALOOKUP_APPEND, eq, optionTheory.option_case_def])
QED

(* All retained visits use the oracle of the full selected filling. *)
Theorem request_cut_trace_selected_oracle:
  ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT keys /\
  LENGTH keys = LENGTH vals /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (MAP (ALOOKUP obs) keys) vals /\
  n <= LENGTH keys /\ trace_gas src = ZIP (TAKE n keys,TAKE n vals) /\
  EVERY (\kv. MEM kv obs) (trace_gas tgt) ==>
  trace_agrees
    (\key. case ALOOKUP (obs ++ ZIP (keys,vals)) key of NONE => 0w | SOME w => w) src /\
  trace_agrees
    (\key. case ALOOKUP (obs ++ ZIP (keys,vals)) key of NONE => 0w | SOME w => w) tgt
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP FST (ZIP (keys,vals)))` by simp[MAP_ZIP] >>
  `!key w. MEM (key,w) (ZIP (keys,vals)) ==>
     ALOOKUP obs key = NONE \/ ALOOKUP obs key = SOME w` by
    (rpt gen_tac >> simp[MEM_ZIP] >> strip_tac >>
     rename1 `m < LENGTH vals` >> gvs[] >>
     qpat_assum `LIST_REL _ _ _`
       (mp_tac o CONJUNCT2 o SIMP_RULE (srw_ss()) [LIST_REL_EL_EQN, EL_MAP]) >>
     disch_then (qspec_then `m` mp_tac) >> simp[]) >>
  `!kw. MEM kw (trace_gas src) ==> MEM kw (ZIP (keys,vals))` by
    (qpat_assum `trace_gas src = _` SUBST1_TAC >>
     simp[ZIP_TAKE] >> metis_tac[MEM_TAKE]) >>
  fs[EVERY_MEM] >>
  conj_tac >> simp[trace_agrees_def, EVERY_MEM] >>
  qx_gen_tac `kw` >> Cases_on `kw` >> simp[] >> strip_tac >>
  rename1 `(case ALOOKUP (obs ++ ZIP (keys,vals)) key of NONE => 0w | SOME x => x) = w`
  >- (`MEM (key,w) (ZIP (keys,vals))` by metis_tac[] >>
      `ALOOKUP (ZIP (keys,vals)) key = SOME w` by
        metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
      `ALOOKUP obs key = NONE \/ ALOOKUP obs key = SOME w` by metis_tac[] >>
      simp[ALOOKUP_APPEND]) >>
  `MEM (key,w) obs` by metis_tac[] >>
  `ALOOKUP obs key = SOME w` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
  simp[ALOOKUP_APPEND]
QED

Theorem request_cut_mask_matches_observations:
  ALL_DISTINCT keys /\ ALL_DISTINCT (MAP FST obs) /\
  LENGTH keys = LENGTH slots /\
  PERM (MAP (\(key,slot). (key,THE slot))
    (FILTER (\(key,slot). IS_SOME slot) (ZIP (keys,slots)))) obs ==>
  slots = MAP (ALOOKUP obs) keys
Proof
  strip_tac >>
  `!key w. MEM (key,w) obs <=> MEM (key,SOME w) (ZIP (keys,slots))` by
    (gen_tac >> gen_tac >> drule PERM_MEM_EQ >>
     disch_then (qspec_then `(key,w)` (SUBST1_TAC o SYM)) >>
     simp[MEM_MAP, MEM_FILTER, pairTheory.EXISTS_PROD] >>
     eq_tac >> rpt strip_tac
     >- (Cases_on `p_2` >> gvs[]) >>
     qexists_tac `SOME w` >> simp[]) >>
  `ALL_DISTINCT (MAP FST (ZIP (keys,slots)))` by simp[MAP_ZIP] >>
  simp[LIST_EQ_REWRITE, EL_MAP] >> rpt strip_tac >>
  `MEM (EL x keys,EL x slots) (ZIP (keys,slots))` by (simp[MEM_ZIP] >> qexists_tac `x` >> simp[]) >>
  Cases_on `EL x slots` >> simp[]
  >- (Cases_on `ALOOKUP obs (EL x keys)` >> simp[] >>
      metis_tac[ALOOKUP_MEM, ALOOKUP_ALL_DISTINCT_MEM, optionTheory.SOME_11, optionTheory.NOT_NONE_SOME]) >>
  metis_tac[ALOOKUP_ALL_DISTINCT_MEM]
QED

(* The selected mask pairs these two executed prefixes. In particular,
   it does not require agreement with a C8 visit beyond the stopped walk. *)
Theorem request_cut_masked_visit_pair:
  trace_context fuel7 C7 v7 = pre7 ++ ((p7,d7,id7),fn7,i7,s7)::after7 /\
  trace_context N C8 v8 = pre8 ++ ((p8,d8,id8),fn8,i8,s8)::after8 /\
  LENGTH pre8 <= j /\ obs = trace_gas (TAKE j (trace_context N C8 v8)) /\
  ALL_DISTINCT keys /\ ALL_DISTINCT (MAP FST obs) /\ LENGTH keys = LENGTH slots /\
  PERM (MAP (\(key,slot). (key,THE slot))
    (FILTER (\(key,slot). IS_SOME slot) (ZIP (keys,slots)))) obs /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots vals /\
  n <= LENGTH keys /\ trace_gas pre7 = ZIP (TAKE n keys,TAKE n vals) ==>
  ev_reachable (\key. case ALOOKUP (obs ++ ZIP (keys,vals)) key of NONE => 0w | SOME w => w) (v7 with vs_gas_readings := gs) C7 p7 d7 fn7 i7
      (s7 with vs_gas_readings := gs) /\
  ev_reachable (\key. case ALOOKUP (obs ++ ZIP (keys,vals)) key of NONE => 0w | SOME w => w) (v8 with vs_gas_readings := gs) C8 p8 d8 fn8 i8
      (s8 with vs_gas_readings := gs)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH keys = LENGTH vals` by metis_tac[LIST_REL_LENGTH] >>
  drule_all request_cut_mask_matches_observations >> strip_tac >>
  `EVERY (\kv. MEM kv obs) (trace_gas pre8)` by
    (qpat_assum `obs = _` SUBST1_TAC >>
     qpat_assum `trace_context N C8 v8 = _` SUBST1_TAC >>
     simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG, EVERY_MEM, MEM_APPEND]) >>
  qpat_x_assum `slots = _` SUBST_ALL_TAC >>
  drule_all request_cut_trace_selected_oracle >> strip_tac >>
  conj_tac >> irule trace_context_prefix_visit >>
  goal_assum (drule_at (Pat `trace_context _ _ _ = _`)) >> simp[]
QED
