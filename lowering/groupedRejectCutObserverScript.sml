(* Bound the actual initializer instructions before the positional decoder. *)
Theory groupedRejectCutObserver
Ancestors
  ptrDiscipline list fragExec fragGasPath pred_set venomExecSemantics venomInst venomState
  entryRejectAllocationIds callRejectMemory[ignore_grammar] venomExecProofs exprLoweringProps
  selectedAcceptedFold compileEnv vyperContext emitHelperProps fragFuel finite_map rich_list
  words pair arithmetic groupedEntryCut runtimeDefaultRejectExpr groupedRegistrationCounters
  groupedEntryCounters fragObserverCodeProps fragFuelConfinement fragFuelRuntimeBody
  fragFuelExpr exprSimAbiGasBridge loweringShapeDefs relation vyperAST
Libs
  runtimeDefaultRejectSyntaxLib groupedRejectCutLib

val _ = Parse.hide "tops";

Triviality row22_observer_index:
  cs_extends sa cut /\ fn_has_code sa cut obs /\
  ~MEM cut.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa cut)) /\
  at_point sa s ==>
  IS_SOME (lookup_block s.vs_current_bb obs.fn_blocks) /\
  (s.vs_current_bb = cut.cs_current_bb ==> s.vs_inst_idx <= LENGTH cut.cs_current_insts)
Proof
  strip_tac >> drule frag_extends_emitted_shape >>
  Cases_on `emitted_blocks sa cut = []` >> simp[] >> strip_tac >>
  fs[at_point_def, fn_has_code_def]
  >- fs[IS_PREFIX_APPEND] >>
  `MEM (LAST (emitted_blocks sa cut)) (emitted_blocks sa cut)` by simp[LAST_MEM] >>
  conj_tac >- metis_tac[optionTheory.IS_SOME_DEF] >>
  fs[MEM_MAP] >> metis_tac[]
QED

val row22_observed = ``\obs cut (s:venom_state).
  IS_SOME (lookup_block s.vs_current_bb obs.fn_blocks) /\
  (s.vs_current_bb = cut.cs_current_bb ==> s.vs_inst_idx <= LENGTH cut.cs_current_insts)``;

Triviality row22_observer_fetch:
  fn_has_code checks cut fn /\ obs = frag_observer checks cut fn 0 /\
  ^row22_observed obs cut s /\ ~s.vs_halted /\ ~at_point cut s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i ==>
  ?b. lookup_block s.vs_current_bb obs.fn_blocks = SOME b /\
      get_instruction b s.vs_inst_idx = SOME i
Proof
  simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `obs = _` SUBST_ALL_TAC >>
  Cases_on `lookup_block s.vs_current_bb (frag_observer checks cut fn 0).fn_blocks` >>
  gvs[] >> drule frag_observer_lookup_cases >> strip_tac
  >- (`s.vs_inst_idx < LENGTH cut.cs_current_insts` by (fs[at_point_def] >> decide_tac) >>
      gvs[fn_has_code_def, IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN]) >>
  fs[fn_has_code_def] >> metis_tac[optionTheory.SOME_11]
QED

Triviality row22_observer_cut_bound:
  (!l b. lookup_block l fn.fn_blocks = SOME b ==> phi_prefix_length b.bb_instructions = 0) /\
  ^row22_observed obs cut v /\ ~at_point cut v /\
  gas_path_edge ctx fn v n (OK t) ==>
  (t.vs_current_bb = cut.cs_current_bb ==> t.vs_inst_idx <= LENGTH cut.cs_current_insts) /\
  (lookup_block t.vs_current_bb obs.fn_blocks = NONE ==> t.vs_inst_idx = 0)
Proof
  simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all grouped_registration_edge_pc >> strip_tac >>
  `~v.vs_halted` by fs[gas_path_edge_def] >>
  Cases_on `is_terminator i.inst_opcode` >> gvs[at_point_def] >>
  conj_tac
  >- (strip_tac >> fs[] >> decide_tac) >>
  metis_tac[optionTheory.IS_SOME_DEF]
QED

Triviality row22_observer_guarded_path:
  frag_fuel Wv {} {} start cut Kb /\ at_point start s /\ ~s.vs_halted /\
  fn_has_code start cut obs /\ no_phi_fn obs /\ callees_stable G ctx obs /\
  lookup_block cut.cs_current_bb obs.fn_blocks = SOME bcut /\
  get_instruction bcut (LENGTH cut.cs_current_insts) = SOME (mk_inst id STOP [] []) /\
  no_phi_fn fn /\
  (!l b. lookup_block l fn.fn_blocks = SOME b ==> phi_prefix_length b.bb_instructions = 0) /\
  ^row22_observed obs cut s /\
  (!u bb i. ^row22_observed obs cut u /\ ~u.vs_halted /\ ~at_point cut u /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME i ==>
    ?b. lookup_block u.vs_current_bb obs.fn_blocks = SOME b /\
        get_instruction b u.vs_inst_idx = SOME i) /\
  ^row22_stopped ctx fn cut s t ==>
  ^row22_observed obs cut t /\ ~t.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `row22_fetch_ok = \(u:venom_state). !bb i.
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME i ==>
    ?b. lookup_block u.vs_current_bb obs.fn_blocks = SOME b /\
        get_instruction b u.vs_inst_idx = SOME i` >>
  qabbrev_tac `confined = \w. ^row22_observed obs cut w /\ ~w.vs_halted /\
    RTC (\u v. (?n. gas_path_edge ctx fn u n (OK v)) /\ row22_fetch_ok u) s w` >>
  `confined s` by fs[Abbr `confined`, RTC_REFL, at_point_def] >>
  `confined t` suffices_by (simp[Abbr `confined`]) >>
  irule RTC_lifts_invariants >> rule_assum_tac BETA_RULE >>
  qexistsl_tac [`\u v. ~at_point cut u /\ ?n. gas_path_edge ctx fn u n (OK v)`,`s`] >>
  simp[] >> qx_genl_tac [`v`,`w`] >> simp[Abbr `confined`] >> strip_tac >>
  `row22_fetch_ok v` by (simp[Abbr `row22_fetch_ok`] >> metis_tac[]) >>
  `RTC (\u v. (?n. gas_path_edge ctx fn u n (OK v)) /\ row22_fetch_ok u) s w` by
    (irule (cj 2 RTC_RULES_RIGHT1) >> qexists_tac `v` >> simp[] >> metis_tac[]) >>
  `~w.vs_halted` by metis_tac[gas_path_edge_normal] >>
  `^row22_observed obs cut v` by simp[] >>
  drule_all (BETA_RULE row22_observer_cut_bound |> REWRITE_RULE [GSYM CONJ_ASSOC]) >>
  strip_tac >> simp[] >>
  Cases_on `lookup_block w.vs_current_bb obs.fn_blocks` >> simp[] >>
  `w.vs_inst_idx = 0` by fs[] >>
  `!host. no_phi_fn host /\ callees_stable G ctx host /\
    (!l b. lookup_block l obs.fn_blocks = SOME b ==> lookup_block l host.fn_blocks = SOME b) ==>
    ?cost. !f. G <= f ==> run_from (f + cost) ctx host s = run_from f ctx host w` by
    (rpt strip_tac >> irule frag_observed_prefix_fuel >> simp[] >> qexists_tac `fn` >> simp[] >>
     irule RTC_MONOTONE >> goal_assum (drule_at Any) >>
     simp[Abbr `row22_fetch_ok`] >> metis_tac[]) >>
  drule_all frag_fuel_excludes_unlisted_jump_stable >> simp[]
QED

Triviality row22_fragment_opcodes:
  cs_extends si cut /\ EVERY P si.cs_current_insts /\ EVERY P (frag_code si cut) ==>
  EVERY P cut.cs_current_insts /\
  EVERY (\b. EVERY P b.bb_instructions) (emitted_blocks si cut)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule frag_extends_emitted_shape >>
  Cases_on `emitted_blocks si cut = []` >> simp[] >> strip_tac
  >- gvs[frag_code_def, emitted_insts_def, IS_PREFIX_APPEND, DROP_LENGTH_APPEND, EVERY_APPEND] >>
  `emitted_blocks si cut = FRONT (emitted_blocks si cut) ++ [LAST (emitted_blocks si cut)]`
    by simp[APPEND_FRONT_LAST] >>
  fs[frag_code_def, NULL_EQ, EVERY_APPEND, EVERY_FLAT, EVERY_MAP, combinTheory.o_DEF] >>
  fs[IS_PREFIX_APPEND] >>
  qpat_x_assum `emitted_blocks si cut = FRONT _ ++ _` (fn th => ONCE_REWRITE_TAC [th]) >>
  gvs[EVERY_APPEND, DROP_LENGTH_APPEND]
QED

Triviality row22_entry_checks_same_blocks:
  compile_entry_checks mincd pay checks = ((),si) ==>
  checks.cs_blocks = si.cs_blocks
Proof
  strip_tac >> drule externalEntryChecksTheory.compile_entry_checks_same_blocks >>
  simp[same_blocks_def]
QED

Triviality row22_observer_instruction_bounds:
  EVERY ^row22_opcode_ok cut.cs_current_insts /\
  EVERY (\b. EVERY ^row22_opcode_ok b.bb_instructions) (emitted_blocks checks cut) ==>
  !i. MEM i (fn_insts (frag_observer checks cut fn (0:num))) ==>
    i = mk_inst 0 STOP [] [] \/ (^row22_opcode_ok i /\ MEM i (state_insts cut))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[frag_observer_def, fn_insts_def, fn_insts_blocks_def,
    MEM_APPEND, unitShapeDefsTheory.MEM_fn_insts_blocks_iff, MEM_FILTER, state_insts_def,
    all_blocks_def, MEM_FLAT, MEM_MAP, MEM_REVERSE] >>
  `!b. MEM b (emitted_blocks checks cut) ==> MEM b cut.cs_blocks` by
    (simp[emitted_blocks_def] >> metis_tac[MEM_TAKE]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Triviality row22_frame_edge:
  gas_path_edge ctx fn s n (OK t) /\ no_phi_fn fn /\
  (!bb i. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i ==> i.inst_opcode <> INVOKE) ==>
  t.vs_call_ctx = s.vs_call_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `gas_path_edge _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_path_edge_def]) >>
  `inst.inst_opcode <> INVOKE` by metis_tac[] >>
  gvs[exit_result_def, step_inst_non_invoke, jump_to_def]
  >- metis_tac[step_inst_base_preserves_call_ctx]
  >- (`phi_prefix_length target.bb_instructions = 0` by
       (fs[no_phi_fn_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
     gvs[eval_phis_no_phi] >> metis_tac[step_inst_base_preserves_call_ctx]) >>
  qpat_x_assum `OK t = step_inst_base inst s` (fn th => fs[GSYM th, exit_result_def])
QED

Triviality row22_stopped_annotate:
  !R s t. RTC R s t ==> RTC (\u v. RTC R s u /\ R u v) s t
Proof
  gen_tac >> ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1 >> simp[RTC_REFL] >>
  rpt strip_tac >> irule (cj 2 RTC_RULES_RIGHT1) >>
  goal_assum (drule_at Any) >> simp[]
QED

Triviality row22_frame_rtc:
  !ctx fn P s t.
    RTC (\u v. P u /\ ?n. gas_path_edge ctx fn u n (OK v)) s t /\ no_phi_fn fn /\
    (!u bb i. P u /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb u.vs_inst_idx = SOME i ==> i.inst_opcode <> INVOKE) ==>
    t.vs_call_ctx = s.vs_call_ctx
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `RTC _ s t` mp_tac >> map_every qid_spec_tac [`t`,`s`] >>
  ho_match_mp_tac RTC_INDUCT >> simp[] >> rpt strip_tac >>
  `s''.vs_call_ctx = s.vs_call_ctx` by
    (irule row22_frame_edge >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Triviality row22_initializer_observer_bounds:
  checks.cs_current_insts = [] /\ compile_entry_checks mincd pay checks = ((),si) /\
  compile_init_kwargs ce vars off k hi si = ((),cut) /\
  cs_extends si cut /\
  EVERY (\(_,_,_,e). runtime_constant_expr mods e /\
      ~supported_expr_exists (^checked_default_expr ce) e) vars /\
  acyclic_struct_metadata ce.ce_struct_fields ==>
  EVERY ^row22_opcode_ok cut.cs_current_insts /\
  EVERY (\b. EVERY ^row22_opcode_ok b.bb_instructions) (emitted_blocks checks cut)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY ^row22_opcode_ok si.cs_current_insts` by
    (drule runtime_default_entry_checks_opcodes >> simp[]) >>
  `EVERY ^row22_opcode_ok (frag_code si cut)` by
    (irule (BETA_RULE runtime_default_init_fragment_opcodes) >>
     rule_assum_tac BETA_RULE >> asm_rewrite_tac[] >>
     qexistsl_tac [`ce`,`hi`,`k`,`mods`,`off`,`vars`] >> asm_rewrite_tac[]) >>
  drule_all row22_fragment_opcodes >> strip_tac >>
  `emitted_blocks checks cut = emitted_blocks si cut` by
    (drule row22_entry_checks_same_blocks >> simp[emitted_blocks_def]) >>
  fs[]
QED

Triviality row22_observer_real_instruction:
  obs = frag_observer checks cut fn 0 /\
  fn_has_code checks cut fn /\ ^row22_observed obs cut u /\
  ~u.vs_halted /\ ~at_point cut u /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME i /\
  EVERY ^row22_opcode_ok cut.cs_current_insts /\
  EVERY (\b. EVERY ^row22_opcode_ok b.bb_instructions) (emitted_blocks checks cut) ==>
  ^row22_opcode_ok i /\ MEM i (state_insts cut)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (BETA_RULE row22_observer_fetch |> REWRITE_RULE [GSYM CONJ_ASSOC]) >> strip_tac >>
  qpat_x_assum `obs = _` SUBST_ALL_TAC >>
  drule frag_observer_lookup_cases >> strip_tac
  >- (`u.vs_inst_idx < LENGTH cut.cs_current_insts` by (fs[at_point_def] >> decide_tac) >>
      `MEM i cut.cs_current_insts` by (fs[get_instruction_def, EL_APPEND_EQN] >> metis_tac[EL_MEM]) >>
      fs[EVERY_MEM, state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND]) >>
  `MEM i b.bb_instructions` by (fs[get_instruction_def] >> metis_tac[EL_MEM]) >>
  `MEM b cut.cs_blocks` by (fs[emitted_blocks_def] >> metis_tac[MEM_TAKE]) >>
  fs[EVERY_MEM] >> simp[state_insts_def, all_blocks_def, MEM_FLAT, MEM_MAP, MEM_REVERSE] >>
  metis_tac[]
QED

Triviality row22_observer_confinement:
  cs_extends checks start /\ cs_extends start cut /\ fn_has_code checks cut fn /\
  ~MEM cut.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks checks cut)) /\
  frag_fuel Wv {} {} start cut Kb /\ at_point start s /\ ~s.vs_halted /\
  no_phi_fn fn /\
  EVERY ^row22_opcode_ok cut.cs_current_insts /\
  EVERY (\b. EVERY ^row22_opcode_ok b.bb_instructions) (emitted_blocks checks cut) ==>
  !u bb i. ^row22_stopped ctx fn cut s u /\ ~at_point cut u /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME i ==>
    ^row22_opcode_ok i /\ MEM i (state_insts cut)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `obs = frag_observer checks cut fn 0` >>
  `fn_has_code checks cut obs` by (simp[Abbr `obs`] >> irule reject_observer_has_code >> simp[]) >>
  `fn_has_code start cut obs` by metis_tac[fn_has_code_split] >>
  `no_phi_fn obs` by metis_tac[abi_dyn_observer_no_phi, markerTheory.Abbrev_def] >>
  `^row22_observed obs cut s` by
    (BETA_TAC >> irule row22_observer_index >> qexists_tac `start` >> simp[] >>
     `~MEM cut.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks start cut))` suffices_by simp[] >>
     fs[cs_extends_def] >> `emitted_blocks start cut = new'` by metis_tac[emitted_blocks_append] >>
     `emitted_blocks checks cut = new' ++ new` by (irule emitted_blocks_append >> simp[]) >>
     fs[MAP_APPEND]) >>
  `callees_stable 0 ctx obs` by
    (simp[callees_stable_def, Abbr `obs`] >> rpt strip_tac >>
     `inst = mk_inst 0 STOP [] [] \/ ^row22_opcode_ok inst /\ MEM inst (state_insts cut)` by
       (BETA_TAC >> irule (BETA_RULE row22_observer_instruction_bounds) >> metis_tac[]) >>
     fs[mk_inst_def]) >>
  `!l b. lookup_block l fn.fn_blocks = SOME b ==> phi_prefix_length b.bb_instructions = 0` by
    (fs[no_phi_fn_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  `!u. ^row22_stopped ctx fn cut s u ==> ^row22_observed obs cut u /\ ~u.vs_halted` by
    (BETA_TAC >> gen_tac >> disch_tac >> irule (BETA_RULE row22_observer_guarded_path) >>
     rule_assum_tac BETA_RULE >> simp[] >>
     conj_tac
     >- (simp[Abbr `obs`, frag_observer_cut_lookup] >>
         qexists_tac `0` >> simp[frag_observer_cut_instruction]) >>
     qexistsl_tac [`0`,`Kb`,`Wv`,`ctx`,`fn`,`s`,`start`] >> simp[] >>
     metis_tac[BETA_RULE row22_observer_fetch, markerTheory.Abbrev_def]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule (BETA_RULE row22_observer_real_instruction) >>
  rule_assum_tac BETA_RULE >> metis_tac[markerTheory.Abbrev_def]
QED

Triviality row22_counter_code_bounds:
  cs_extends cut sd /\ entry_alloca_ids sf sd /\ state_insts sf = [] /\ shape_state sd /\
  sd.cs_next_id <= entry.cs_next_id /\ sd.cs_next_var <= entry.cs_next_var ==>
  !i. MEM i (state_insts cut) ==>
    (i.inst_opcode = ALLOCA ==> i.inst_id < entry.cs_next_id) /\
    EVERY (not_fresh_at entry) i.inst_outputs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >> strip_tac >>
  `MEM i (state_insts sd)` by metis_tac[state_insts_cs_extends, MEM_APPEND] >>
  fs[entry_alloca_ids_def, shape_state_def, shape_base_state_def, EVERY_MEM] >>
  metis_tac[LESS_LESS_EQ_TRANS, loweringShapeDefsTheory.not_fresh_at_mono]
QED

(* This relation stops at the first cut. It does not constrain the initial
   oracle or require the omitted-suffix start to be a block entry. *)

Theorem row22_before_cut_certificate_count:
  checks.cs_current_insts = [] /\ compile_entry_checks mincd pay checks = ((),si) /\
  compile_init_kwargs ce vars off k hi si = ((),cut) /\
  compile_init_kwargs ce rest off' ninit hi start = ((),cut) /\
  EVERY (\(_,_,_,e). runtime_constant_expr mods e /\
      ~supported_expr_exists (^checked_default_expr ce) e) vars /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  cs_extends checks start /\ fn_has_code si cut fn /\ ci_mono cut sd /\
  cs_extends sd final /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks final)) /\
  compile_group_dispatch_linear groups fallback sf = (jobs,sd) /\
  state_insts sf = [] /\ shape_state sd /\ no_phi_fn fn /\
  sd.cs_next_id <= entry.cs_next_id /\ sd.cs_next_var <= entry.cs_next_var /\
  selected_registration_resources ctx fn site lo start s ==>
  (!u bb i. ^row22_stopped ctx fn cut s u /\ ~at_point cut u /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME i ==> ^row22_opcode_ok i) /\
  (!w. ^row22_stopped ctx fn cut s w /\ at_point cut w ==>
    fresh_vars_wrt entry w /\ w.vs_call_ctx = s.vs_call_ctx /\
    (!id e. FLOOKUP w.vs_allocas id = SOME e ==> id < entry.cs_next_id))
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono si cut /\ ci_mono start cut` by metis_tac[compile_init_kwargs_ci_mono, SND] >>
  `cs_extends si cut /\ cs_extends start cut /\ cs_extends cut sd` by fs[ci_mono_def] >>
  `~MEM cut.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks checks cut))` by
    metis_tac[grouped_initializer_open_label, cs_extends_trans] >>
  `fn_has_code checks cut fn` by
    (`emitted_blocks checks cut = emitted_blocks si cut` by
       (drule row22_entry_checks_same_blocks >> simp[emitted_blocks_def]) >>
     fs[fn_has_code_def]) >>
  `?Kb. frag_fuel UNIV {} {} start cut Kb` by
    (`fuel_ok UNIV {} {} (compile_init_kwargs ce rest off' ninit hi)` by
       metis_tac[fuel_ok_compile_init_kwargs, cj 1 fuel_ok_compile_expr] >>
     fs[fuel_ok_def] >> metis_tac[]) >>
  qpat_assum `selected_registration_resources _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  `at_point start s` by simp[at_point_def] >>
  drule_all (BETA_RULE row22_initializer_observer_bounds) >> strip_tac >>
  `!u bb i. ^row22_stopped ctx fn cut s u /\ ~at_point cut u /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME i ==> ^row22_opcode_ok i /\ MEM i (state_insts cut)` by
    (BETA_TAC >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     irule (BETA_RULE row22_observer_confinement) >> metis_tac[]) >>
  drule entry_ids_group_dispatch >> strip_tac >>
  `!i. MEM i (state_insts cut) ==>
    (i.inst_opcode = ALLOCA ==> i.inst_id < entry.cs_next_id) /\
    EVERY (not_fresh_at entry) i.inst_outputs` by
    (gen_tac >> disch_tac >> irule row22_counter_code_bounds >> metis_tac[]) >>
  rule_assum_tac BETA_RULE >> conj_tac >- metis_tac[] >>
  qx_gen_tac `w` >> strip_tac >>
  qabbrev_tac `P = \u. ^row22_stopped ctx fn cut s u /\ ~at_point cut u` >>
  `RTC (\u v. P u /\ ?n. gas_path_edge ctx fn u n (OK v)) s w` by
    (drule row22_stopped_annotate >> simp[Abbr `P`, CONJ_ASSOC]) >>
  `!u bb i. P u /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME i ==> i.inst_opcode <> INVOKE /\
    (i.inst_opcode = ALLOCA ==> i.inst_id < entry.cs_next_id) /\
    EVERY (not_fresh_at entry) i.inst_outputs` by
    (simp[Abbr `P`] >> rpt strip_tac >> res_tac >> fs[]) >>
  `w.vs_call_ctx = s.vs_call_ctx` by metis_tac[row22_frame_rtc] >>
  `start.cs_next_var <= entry.cs_next_var /\ start.cs_next_id <= entry.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `fresh_vars_wrt entry s` by (irule fresh_vars_wrt_mono >> qexists_tac `start` >> simp[]) >>
  `!id e. FLOOKUP s.vs_allocas id = SOME e ==> id < entry.cs_next_id` by
    metis_tac[LESS_LESS_EQ_TRANS] >>
  `!l b. lookup_block l fn.fn_blocks = SOME b ==> phi_prefix_length b.bb_instructions = 0` by
    (fs[no_phi_fn_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  drule_all grouped_registration_bounds_rtc >> simp[]
QED
