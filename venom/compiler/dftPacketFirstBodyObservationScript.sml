Theory dftPacketFirstBodyObservation
Ancestors
  dftPacketSuccessorObservation dftPacketPseudoSegment dftPacketLiteralRowExtend
  dftPacketSameLevelCompose dftGasFromListReplayBoundary dftGasInvMemoryObservation
  dftRunRel dftScheduleOrder dftWf dftGasInvForwardActive
  o1ScheduleDecompHelpers venomExecProps venomWf venomInst venomState
  dftPacketFreshRow dftGasInvCrossingProbe list rich_list sorting dftGasFromListTraceDefs dftIndexedExec gasEvents venomExecSemantics

Theorem dft_packet_invoke_memory_order:
  !x y. x.inst_opcode = INVOKE /\ inv_memory_observation y.inst_opcode ==>
    dft_must_order x y
Proof
  rpt gen_tac >> Cases_on `y.inst_opcode` >>
  simp[inv_memory_observation_def, dft_must_order_def,
       venomEffectsTheory.read_effects_def, venomEffectsTheory.write_effects_def,
       venomEffectsTheory.all_effects_def, is_terminator_def,
       pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem dft_packet_first_body_schedule:
  !sf tf bb bt ps xs ys rho q.
  dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\x. is_pseudo x.inst_opcode) ps /\
  EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
  EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
  LENGTH xs = LENGTH ys /\ PERM rho (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) rho ys /\
  ys <> [] /\ q = EL 0 rho /\ inv_memory_observation (HD ys).inst_opcode ==>
  q < LENGTH xs /\ EL q xs = HD ys /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  EVERY (\i. i.inst_opcode <> INVOKE) (TAKE q xs)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `q < LENGTH xs /\ from_block [EL q xs] (HD ys)` by
    (fs[LIST_REL_EL_EQN] >> first_x_assum (qspec_then `0` mp_tac) >>
     `0 < LENGTH ys` by (Cases_on `ys` >> fs[]) >> simp[EL,HD]) >>
  qpat_x_assum `q = EL 0 _` kall_tac >>
  `EL q xs = HD ys` by
    (drule_all inv_memory_observation_original >> simp[]) >>
  `wf_function sf` by fs[dft_fn_rel_def] >>
  `MEM bb sf.fn_blocks` by
    metis_tac[FIND_MEM, lookup_block_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  `FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions = ps /\
   FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = xs` by
    (`FILTER (\i. is_pseudo i.inst_opcode) ps = ps /\
      FILTER (\i. is_pseudo i.inst_opcode) xs = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) ps = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) xs = xs` by
       simp[FILTER_EQ_ID, FILTER_EQ_NIL] >> simp[FILTER_APPEND_DISTRIB]) >>
  simp[] >> conj_tac
  >- (rewrite_tac[EVERY_EL] >> qx_gen_tac `n` >> disch_tac >>
      `n < q /\ n < LENGTH xs` by (gvs[LENGTH_TAKE] >> decide_tac) >>
      simp[EL_TAKE] >> irule dft_wf_order_nonterminator >>
      qexistsl_tac [`bb`, `sf`, `EL q xs`] >> simp[] >>
      conj_tac >- metis_tac[MEM_EL, MEM_APPEND] >>
      irule id_before_append_right >> simp[id_before_def] >>
      qexistsl_tac [`n`, `q`] >> simp[EL_MAP]) >>
  suspend "no_invoke"
QED

Resume dft_packet_first_body_schedule[no_invoke]:
  simp[EVERY_EL,LENGTH_TAKE,EL_TAKE] >> rpt strip_tac >>
  rename1 `(EL r xs).inst_opcode = INVOKE` >>
  `r < LENGTH xs` by decide_tac >>
  `MEM (EL r xs) bb.bb_instructions /\ MEM (EL q xs) bb.bb_instructions` by
    metis_tac[MEM_EL, MEM_APPEND] >>
  `~is_pseudo (EL r xs).inst_opcode /\ ~is_pseudo (EL q xs).inst_opcode` by
    (fs[EVERY_EL] >> metis_tac[]) >>
  `id_before (MAP (\i. i.inst_id) bb.bb_instructions)
     (EL r xs).inst_id (EL q xs).inst_id` by
    (simp[] >> irule id_before_append_right >> simp[id_before_def] >>
     qexistsl_tac [`r`, `q`] >> simp[EL_MAP]) >>
  `dft_must_order (EL r xs) (EL q xs)` by
    metis_tac[dft_packet_invoke_memory_order] >>
  `id_before (MAP (\i. i.inst_id) bt.bb_instructions)
     (EL r xs).inst_id (EL q xs).inst_id` by
    (qpat_x_assum `dft_block_rel bb bt`
       (strip_assume_tac o REWRITE_RULE [dft_block_rel_def]) >>
     fs[] >> irule id_before_append_right >> metis_tac[]) >>
  `~MEM (EL r xs).inst_id (MAP (\i. i.inst_id) ps) /\
   ~MEM (EL q xs).inst_id (MAP (\i. i.inst_id) ps)` by
    (`MEM (EL r xs).inst_id (MAP (\i. i.inst_id) xs) /\
      MEM (EL q xs).inst_id (MAP (\i. i.inst_id) xs)` by
       (conj_tac >> simp[MEM_MAP] >> metis_tac[MEM_EL]) >>
     qpat_x_assum `ALL_DISTINCT (MAP _ bb.bb_instructions)` mp_tac >>
     asm_rewrite_tac[MAP_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `id_before (MAP (\i. i.inst_id) ys) (EL r xs).inst_id (HD ys).inst_id` by
    (qpat_x_assum `id_before (MAP _ bt.bb_instructions) _ _` mp_tac >>
     gvs[id_before_append_suffix]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) xs)` by
    (qpat_x_assum `ALL_DISTINCT (MAP _ bb.bb_instructions)` mp_tac >>
     simp[MAP_APPEND,ALL_DISTINCT_APPEND]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) ys)` by
    (qpat_x_assum `dft_block_rel bb bt`
       (strip_assume_tac o REWRITE_RULE [dft_block_rel_def]) >>
     fs[] >> metis_tac[ALL_DISTINCT_PERM]) >>
  qpat_x_assum `id_before (MAP _ ys) _ (HD ys).inst_id` mp_tac >>
  qpat_x_assum `ALL_DISTINCT (MAP _ ys)` mp_tac >>
  rpt (pop_assum kall_tac) >> Cases_on `ys` >> simp[id_before_def] >>
  rpt strip_tac >> Cases_on `j` >> gvs[] >>
  spose_not_then strip_assume_tac >>
  `n < LENGTH (MAP (\i. i.inst_id) t)` by simp[] >>
  drule_then assume_tac EL_MEM >> metis_tac[]
QED

Finalise dft_packet_first_body_schedule

Theorem dft_packet_first_body_rooted_observation:
  !(fuel:num). row_eval = (\owner (b,e,z) ent.
    case eval_phis ent b.bb_instructions of
      OK sp =>
        (gas_events_block (fuel-e) C7 owner
          (b with bb_instructions := TAKE (phi_prefix_length b.bb_instructions) b.bb_instructions ++ z)
          (sp with vs_inst_idx := phi_prefix_length b.bb_instructions),
         FOLDR (dft_exec_cons (fuel-e) C7) OK z
          (sp with vs_inst_idx := phi_prefix_length b.bb_instructions))
    | other => ([],other)) /\
  plan_eval = (\owner plan ent.
    FOLDL (\(ev,r) row. case r of
      OK v => (ev ++ FST(row_eval owner row v),SND(row_eval owner row v))
    | other => (ev,other)) ([],OK ent) plan) /\
  call_setup = (\c v.
    case decode_invoke c of NONE => Error "invoke: bad operand format"
    | SOME(nm,ops) => case lookup_function nm C7.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee => case eval_operands ops v of
          NONE => Error "invoke: undefined argument"
        | SOME args => case setup_callee callee args v of
            NONE => Error "invoke: empty function"
          | SOME cs => OK cs) /\
  rooted_eval = (\levels ent.
    FOLDL (\(prior,r) (f,plan,call). case r of
      OK v => (prior ++ FST(plan_eval f.fn_name plan v),
        case SND(plan_eval f.fn_name plan v) of
          OK caller => (case call of NONE => OK caller | SOME c => call_setup c caller)
        | other => other)
    | other => (prior,other)) ([],OK ent) levels) /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  dft_fn_rel sf tf /\ MEM bb sf.fn_blocks /\
  lookup_block name sf.fn_blocks = SOME bb /\
  lookup_block name tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY inst_shape_ok bb.bb_instructions /\ bb_well_formed bt /\
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  l = phi_prefix_length bb.bb_instructions /\ l <= k /\ k < LENGTH ps /\
  SUC k = LENGTH ps /\ s.vs_inst_idx = k /\
  step_inst g C8 (EL k ps) s = OK t /\ s1 = t with vs_inst_idx := SUC k /\
  dft_remaining_inv sf bb xs s1 /\
  q < LENGTH xs /\ ys <> [] /\ EL q xs = HD ys /\
  inv_memory_observation (EL q xs).inst_opcode /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q xs) /\
  ms = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs) /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
  z0 = DROP l (TAKE k ps) /\ z1 = DROP l ps ++ TAKE q xs /\
  levels0 = pre ++ [(sf,rows ++ [(bb,d,z0)],NONE)] /\
  levels1 = pre ++ [(sf,rows ++ [(bb,d,z1)],NONE)] /\
  (!ev v. rooted_eval levels0 entry = (ev,OK v) ==>
    v = s with vs_gas_readings := FLAT kgss ++ tail) /\
  rooted_eval levels1 entry = (events,OK u) ==>
  FOLDR (dft_exec_cons (fuel-d) C7) OK (TAKE q xs)
    (s1 with vs_gas_readings := FLAT kgss ++ tail) = OK u /\
  (!op. MEM op (EL q xs).inst_operands ==>
    eval_operand op u = eval_operand op s1) /\
  u.vs_initial_fmp = s1.vs_initial_fmp
Proof
  qx_gen_tac `fuel` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `segment = [EL k ps] ++ TAKE q xs` >>
  `z1 = z0 ++ segment /\
   z1 = TAKE (LENGTH z1) (DROP l bb.bb_instructions) /\
   LENGTH z1 <= LENGTH (DROP l bb.bb_instructions) /\
   EVERY (\i. ~is_terminator i.inst_opcode) z1` by
    suspend "geometry" >>
  qabbrev_tac `H = (\v.
    (gas_events_block (fuel-d) C7 sf.fn_name
       (bb with bb_instructions := TAKE l bb.bb_instructions ++ z1) v,
     FOLDR (dft_exec_cons (fuel-d) C7) OK segment v))` >>
  `!ent. row_eval sf.fn_name (bb,d,z1) ent =
    (case SND (row_eval sf.fn_name (bb,d,z0) ent) of
       OK v => (FST (row_eval sf.fn_name (bb,d,z0) ent) ++ FST (H v),SND (H v))
     | other => (FST (row_eval sf.fn_name (bb,d,z0) ent),other))` by
    suspend "row_extend" >>
  `rooted_eval levels1 entry =
    (case SND (rooted_eval levels0 entry) of
       OK v => (FST (rooted_eval levels0 entry) ++ FST (H v),SND (H v))
     | other => (FST (rooted_eval levels0 entry),other))` by
    suspend "root_extend" >>
  `FOLDR (dft_exec_cons (fuel-d) C7) OK (TAKE q xs)
    (s1 with vs_gas_readings := FLAT kgss ++ tail) = OK u` by
    suspend "source_success" >>
  conj_tac >- first_assum ACCEPT_TAC >> suspend "observation"
QED

Resume dft_packet_first_body_rooted_observation[geometry]:
  map_every (fn p => qpat_x_assum p kall_tac)
    [`row_eval = _`,`plan_eval = _`,`call_setup = _`,`rooted_eval = _`,
     `!ev v. _`] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) ps` by
    (qpat_assum `EVERY (\i. is_pseudo i.inst_opcode) ps` mp_tac >>
     simp[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `EVERY _ ps` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `i` mp_tac) >> simp[] >>
     Cases_on `i.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs)` by fs[EVERY_CONJ] >>
  `ps = TAKE k ps ++ [EL k ps]` by
    (sym_tac >> irule vyperMiscTheory.TAKE_SNOC_EL >> simp[]) >>
  `DROP l ps = DROP l (TAKE k ps) ++ [EL k ps]` by
    (qpat_assum `ps = TAKE k ps ++ _`
       (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
     irule DROP_APPEND1 >> gvs[LENGTH_TAKE]) >>
  `l <= LENGTH ps` by decide_tac >>
  `LENGTH z1 = LENGTH ps - l + q` by
    (qpat_assum `z1 = DROP l ps ++ _` SUBST1_TAC >> simp[LENGTH_TAKE]) >>
  rpt conj_tac
  >- (simp[Abbr `segment`,APPEND_ASSOC] >> metis_tac[])
  >- (qpat_x_assum `ps = TAKE k ps ++ _` kall_tac >>
      qpat_x_assum `DROP l ps = _` kall_tac >>
      qpat_x_assum `l = _` kall_tac >>
      qpat_x_assum `z1 = DROP l ps ++ _` SUBST1_TAC >>
      qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
      simp[DROP_APPEND1,TAKE_APPEND,LENGTH_DROP,LENGTH_TAKE])
  >- (qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
      simp[LENGTH_DROP] >> decide_tac) >>
  qpat_x_assum `ps = TAKE k ps ++ _` kall_tac >>
  qpat_x_assum `DROP l ps = _` kall_tac >>
  qpat_x_assum `z1 = DROP l ps ++ _` SUBST1_TAC >>
  simp[EVERY_APPEND] >> irule EVERY_DROP >> first_assum ACCEPT_TAC
QED

Resume dft_packet_first_body_rooted_observation[row_extend]:
  qpat_assum `z1 = z0 ++ segment`
    (mp_then (Pat `z1 = z0 ++ segment`) mp_tac dft_packet_literal_row_extend) >>
  disch_then (qspecl_then [`l`,`bb`,`fuel-d`,`C7`,`sf.fn_name`,
    `\z ent. row_eval sf.fn_name (bb,d,z) ent`,`H`] mp_tac) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- simp[NoAsms,Abbr `H`] >>
     qpat_x_assum `row_eval = _` SUBST1_TAC >>
     qpat_x_assum `l = _` SUBST1_TAC >> simp[NoAsms])) >>
  simp[NoAsms]
QED

Resume dft_packet_first_body_rooted_observation[root_extend]:
  qpat_x_assum `levels1 = _` SUBST1_TAC >>
  qpat_x_assum `levels0 = _` SUBST1_TAC >>
  irule dft_packet_rooted_row_extend >>
  qexistsl_tac [`plan_eval`,`call_setup`,`row_eval`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_first_body_rooted_observation[source_success]:
  qpat_x_assum `rooted_eval levels1 entry = _` (mk_asm "extend") >>
  Cases_on `rooted_eval levels0 entry` >>
  rename1 `rooted_eval levels0 entry = (old_events,r)` >>
  Cases_on `r` >>
  asm_x "extend" mp_tac >>
  simp[NoAsms] >>
  qpat_assum `rooted_eval levels1 entry = (events,OK u)`
    (fn th => pure_rewrite_tac[th,pairTheory.PAIR_EQ,exec_result_11,exec_result_distinct]) >>
  strip_tac >>
  `v = s with vs_gas_readings := FLAT kgss ++ tail` by metis_tac[] >>
  `is_pseudo (EL k ps).inst_opcode` by fs[EVERY_EL] >>
  `step_inst (fuel-d) C7 (EL k ps) (s with vs_gas_readings := FLAT kgss ++ tail) =
    OK (t with vs_gas_readings := FLAT kgss ++ tail)` by
    (qpat_assum `is_pseudo (EL k ps).inst_opcode` mp_tac >>
     qpat_assum `step_inst g C8 _ _ = OK t` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `(EL k ps).inst_opcode <> INVOKE /\
      (EL k ps).inst_opcode <> GAS` by
       (qpat_assum `is_pseudo _` mp_tac >>
        Cases_on `(EL k ps).inst_opcode` >> gvs[is_pseudo_def]) >>
     qpat_x_assum `step_inst g C8 _ _ = OK t` mp_tac >>
     simp[step_inst_non_invoke] >> strip_tac >>
     drule gasOracleReplayTheory.gas_base_non_gas >>
     disch_then (qspec_then `s` mp_tac) >>
     simp[NoAsms,gasOracleReplayTheory.gas_replay_at_def] >>
     disch_then (qspec_then `FLAT kgss ++ tail` mp_tac) >>
     Cases_on `step_inst_base (EL k ps) (s with vs_gas_readings := FLAT kgss ++ tail)` >>
     simp[stateEquivTheory.lift_result_def]) >>
  `~is_terminator (EL k ps).inst_opcode` by
    (qpat_assum `is_pseudo _` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `(EL k ps).inst_opcode` >> simp[is_pseudo_def,is_terminator_def]) >>
  qpat_x_assum `OK u = SND (H v)` mp_tac >>
  simp[NoAsms,Abbr `H`,Abbr `segment`,dft_exec_cons_def] >>
  qpat_x_assum `v = s with vs_gas_readings := _` SUBST1_TAC >>
  qpat_assum `step_inst (fuel-d) C7 _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `~is_terminator _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `s.vs_inst_idx = k` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `s1 = _` (fn th => pure_rewrite_tac[th]) >>
  simp[NoAsms] >>
  qpat_assum `s.vs_inst_idx = k` (fn th => rewrite_tac[th])
QED

Resume dft_packet_first_body_rooted_observation[observation]:
  map_every (fn p => qpat_x_assum p kall_tac)
    [`row_eval = _`,`plan_eval = _`,`call_setup = _`,`rooted_eval = _`,
     `!ev v. _`,`rooted_eval levels1 entry = (events,OK u)`,
     `z1 = TAKE _ _`,`z1 = z0 ++ segment`,
     `!ent. row_eval _ _ _ = _`,`rooted_eval levels1 entry = _`] >>
  `s1.vs_inst_idx = LENGTH ps` by simp[] >>
  `q <= LENGTH xs` by decide_tac >>
  qabbrev_tac `ess = GENLIST (\r. if (EL r xs).inst_opcode = GAS
    then [(sf.fn_name,(EL r xs).inst_id)] else []) (LENGTH xs)` >>
  qabbrev_tac `ks = GENLIST (\r. if (EL r xs).inst_opcode = GAS
    then [(([]:(num # num) list),d,(EL r xs).inst_id)] else []) (LENGTH xs)` >>
  `ess = GENLIST (\r. if (EL r xs).inst_opcode = GAS
    then [(sf.fn_name,(EL r xs).inst_id)] else []) (LENGTH xs)` by simp[Abbr `ess`] >>
  `ks = GENLIST (\r. if (EL r xs).inst_opcode = GAS
    then [(([]:(num # num) list),d,(EL r xs).inst_id)] else []) (LENGTH xs)` by simp[Abbr `ks`] >>
  drule_all dft_packet_fresh_row_replay >>
  disch_then (qspecl_then [`tail`,`fuel-d`,`C7`] strip_assume_tac) >>
  qpat_x_assum `!u. FOLDR _ _ _ _ = OK u ==> _` drule >> strip_tac >>
  `ALL_DISTINCT (FLAT ks)` by
    (qpat_assum `ks = _` SUBST1_TAC >>
     qpat_assum `ALL_DISTINCT (MAP (\i. i.inst_id) xs)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[GENLIST_EL_MAP] >>
     Induct_on `xs` >> simp[] >> rpt strip_tac >>
     Cases_on `h.inst_opcode = GAS` >> simp[] >>
     gvs[MEM_FLAT,MEM_MAP] >> gen_tac >> CCONTR_TAC >> gvs[] >>
     rename1 `MEM ii xs` >> Cases_on `ii.inst_opcode = GAS` >> gvs[]) >>
  `ALL_DISTINCT (FLAT (TAKE q ks))` by
    (`ALL_DISTINCT (FLAT (TAKE q ks) ++ FLAT (DROP q ks))` by
       (pure_rewrite_tac[GSYM FLAT_APPEND,TAKE_DROP] >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `ALL_DISTINCT (_ ++ _)` mp_tac >>
     simp[NoAsms,ALL_DISTINCT_APPEND]) >>
  `LENGTH (FLAT (TAKE q ks)) = LENGTH (FLAT kgss)` by
    (`MAP LENGTH (TAKE q ks) = MAP LENGTH (TAKE q ms)` by
       (qpat_assum `ks = _` SUBST1_TAC >> qpat_assum `ms = _` SUBST1_TAC >>
        rpt (pop_assum kall_tac) >>
        simp[GENLIST_EL_MAP,GSYM MAP_TAKE,MAP_MAP_o,combinTheory.o_DEF,COND_RAND]) >>
     qpat_assum `LIST_REL (LIST_REL _) (TAKE q ms) kgss` mp_tac >>
     qpat_assum `MAP LENGTH _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[LENGTH_FLAT] >> strip_tac >> strip_tac >>
     AP_TERM_TAC >> irule LIST_EQ >>
     fs[LIST_REL_EL_EQN,EL_MAP] >> metis_tac[LIST_REL_LENGTH]) >>
  qmatch_asmsub_abbrev_tac `trace_gas source = ZIP (FLAT (TAKE q ks),FLAT kgss)` >>
  qabbrev_tac `target = trace_block [] d (fuel-d) C8 tf
    (bt with bb_instructions := TAKE (LENGTH ps + 0) bt.bb_instructions) s1` >>
  `trace_gas target = []` by
    (qpat_assum `s1.vs_inst_idx = LENGTH ps` mp_tac >>
     qpat_assum `bt.bb_instructions = ps ++ ys` mp_tac >>
     simp[NoAsms,Abbr `target`] >> rpt (pop_assum kall_tac) >> rpt strip_tac >>
     simp[Once trace_defs,get_instruction_def,LENGTH_TAKE,trace_gas_def]) >>
  qspecl_then [`[]`,`FLAT (TAKE q ks)`,`FLAT kgss`,`source`,`target`]
    mp_tac trace_agrees_lookup_fill >>
  (impl_tac >-
    (simp[NoAsms] >> rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- (simp[NoAsms,EVERY_MEM] >> Cases >> simp[NoAsms])
     >- first_assum ACCEPT_TAC >>
     qpat_assum `trace_gas target = []` (fn th => simp[NoAsms,th]))) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `trace_agrees orc source` >>
  irule dft_packet_successor_observation_agreement >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `FOLDR _ _ _ _ = OK u`)) >>
  goal_assum (drule_at (Pat `LIST_REL dft_fn_rel _ _`)) >>
  goal_assum (drule_at (Pat `dft_fn_rel sf tf`)) >>
  goal_assum (drule_at (Pat `lookup_block _ _ = SOME bt`)) >>
  qexistsl_tac [`bb`,`d`,`0`,`orc`,`[]`,`ps`,`fuel-d`,`ys`] >>
  simp[NoAsms,TAKE_0,FOLDR] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (Cases_on `ys` >> fs[])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `EL q xs = HD ys` SUBST1_TAC >> Cases_on `ys` >> simp[NoAsms])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `EVERY (\i. ~is_terminator _ /\ _) _` mp_tac >> simp[NoAsms,EVERY_CONJ])
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `trace_agrees orc source` mp_tac >>
      simp[NoAsms,Abbr `source`,arithmeticTheory.ADD_SYM])
  >- (qpat_assum `trace_agrees orc target` mp_tac >>
      simp[NoAsms,Abbr `target`]) >>
  first_assum ACCEPT_TAC
QED

Finalise dft_packet_first_body_rooted_observation
