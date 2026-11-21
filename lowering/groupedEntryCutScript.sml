(* The observer records the first exit from the installed entry code. *)
Theory groupedEntryCut
Ancestors
  fragFuelConfinement fragObserverCodeProps exprSimAbiGasBridge groupedRegistrationCounters
  fragFuel fragExec fragGasPath loweringShapeDefs compileEnv
  fragFuelRuntimeBody fragFuelExpr fragFuelStmt moduleLowering emitHelperProps
  venomInst venomExecSemantics venomState
  venomExecProofs loweringStateRelDefs finite_map list rich_list relation

Theorem entry_observer_preserves_execution_hyps[local]:
  fn_has_code sa sb fn /\ no_phi_fn fn /\ callees_stable G ctx fn ==>
  no_phi_fn (frag_observer sa sb fn id) /\
  callees_stable G ctx (frag_observer sa sb fn id)
Proof
  strip_tac >> conj_tac >- metis_tac[abi_dyn_observer_no_phi] >>
  simp[callees_stable_def] >> rpt strip_tac >>
  rename1 `i.inst_opcode = INVOKE` >>
  `i.inst_opcode <> STOP` by simp[] >>
  `MEM i (fn_insts fn)` by metis_tac[frag_observer_nonstop_inclusion] >>
  fs[callees_stable_def] >> metis_tac[]
QED

val before_cut = ``\sa sb fn id (s:venom_state).
  IS_SOME (lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks) /\
  (s.vs_current_bb = sb.cs_current_bb ==> s.vs_inst_idx < LENGTH sb.cs_current_insts)``;

Theorem entry_observer_matches_before_cut[local]:
  fn_has_code sa sb fn /\ ^before_cut sa sb fn id s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i ==>
  ?b. lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME b /\
      get_instruction b s.vs_inst_idx = SOME i
Proof
  simp[] >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks` >>
  gvs[] >> drule frag_observer_lookup_cases >> strip_tac
  >- (gvs[fn_has_code_def, IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN]) >>
  qpat_assum `fn_has_code sa sb fn`
    (mp_tac o REWRITE_RULE [fn_has_code_def]) >>
  disch_then (qspec_then `x` mp_tac o cj 1) >> simp[] >> metis_tac[]
QED

Theorem entry_observer_first_exit[local]:
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  ^before_cut sa sb fn id s /\ gas_path_edge ctx fn s n (OK t) /\
  ~(^before_cut sa sb fn id t) /\ ~at_point sb t ==>
  t.vs_inst_idx = 0 /\
  lookup_block t.vs_current_bb (frag_observer sa sb fn id).fn_blocks = NONE
Proof
  simp[] >> strip_tac >>
  drule_all grouped_registration_edge_pc >> strip_tac >>
  Cases_on `is_terminator i.inst_opcode` >> gvs[] >>
  `~t.vs_halted` by metis_tac[gas_path_edge_normal] >>
  fs[at_point_def] >>
  Cases_on `t.vs_current_bb = sb.cs_current_bb` >>
  gvs[frag_observer_cut_lookup] >> decide_tac
QED

Theorem grouped_entry_first_cut:
  frag_fuel Wv {} {} sa sb Kb /\ at_point sa s /\
  sa.cs_current_insts = [] /\
  fn_has_code sa sb fn /\ cs_extends sa sb /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  no_phi_fn fn /\ callees_stable G ctx fn /\
  gas_path ctx fn s n (OK t) ==>
  (?m. at_point sb s /\ gas_path ctx fn s m (OK t)) \/
  (^before_cut sa sb fn id t /\
   RTC (\a b. ^before_cut sa sb fn id a /\
     ?j. gas_path_edge ctx fn a j (OK b)) s t) \/
  ?u v k m.
    RTC (\a b. ^before_cut sa sb fn id a /\
      ?j. gas_path_edge ctx fn a j (OK b)) s u /\
    ^before_cut sa sb fn id u /\ at_point sb v /\
    gas_path_edge ctx fn u k (OK v) /\ gas_path ctx fn v m (OK t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `at_point sb s` >- (disj1_tac >> qexists_tac `n` >> simp[]) >>
  disj2_tac >>
  `!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (fs[no_phi_fn_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  `fn_has_code sa sb (frag_observer sa sb fn id)` by metis_tac[frag_observer_has_code_from_labels] >>
  `no_phi_fn (frag_observer sa sb fn id) /\
    callees_stable G ctx (frag_observer sa sb fn id)` by
    metis_tac[entry_observer_preserves_execution_hyps] >>
  qpat_assum `at_point sa s` (strip_assume_tac o REWRITE_RULE [at_point_def]) >>
  `^before_cut sa sb fn id s` by
    (Cases_on `sa.cs_current_bb = sb.cs_current_bb`
     >- (Cases_on `sb.cs_current_insts`
         >- (fs[] >> metis_tac[at_point_def]) >>
         fs[frag_observer_cut_lookup]) >>
     drule frag_extends_emitted_shape >>
     Cases_on `emitted_blocks sa sb` >> gvs[at_point_def, fn_has_code_def] >>
     `MEM (LAST (h::t')) (h::t')` by simp[MEM_LAST_NOT_NIL] >>
     strip_tac >>
     qpat_assum `!b. _ ==> lookup_block _ (frag_observer sa sb fn id).fn_blocks = _`
       (qspec_then `LAST (h::t')` mp_tac) >>
     fs[] >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  mp_tac (BETA_RULE (Q.INST
    [`P` |-> `^before_cut sa sb fn id`,
     `observer` |-> `frag_observer sa sb fn id`,
     `cut` |-> `<|bb_label := sb.cs_current_bb;
                   bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`]
    (SPEC_ALL frag_fuel_path_reaches_cut))) >>
  impl_tac
  >- (asm_rewrite_tac[frag_observer_cut_lookup, frag_observer_cut_instruction] >>
      metis_tac[entry_observer_matches_before_cut, entry_observer_first_exit]) >>
  simp[]
QED

Theorem grouped_entry_terminated_cut_no_edge:
  fn_has_code sa sb fn /\ block_is_terminated sb /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  gas_path_edge ctx fn s k (OK t) ==>
  ~at_point sb t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all grouped_registration_edge_pc >> strip_tac >>
  strip_tac >>
  Cases_on `sb.cs_current_insts` >> gvs[block_is_terminated_def, at_point_def] >>
  Cases_on `is_terminator i.inst_opcode` >> gvs[] >>
  `?rest. bb.bb_instructions = (h::t') ++ rest` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  qpat_x_assum `LENGTH t' = s.vs_inst_idx` (assume_tac o SYM) >>
  `LENGTH t' < LENGTH (h::t') /\ LENGTH t' < LENGTH ((h::t') ++ rest)` by
    (simp[LENGTH_APPEND] >> fs[] >> decide_tac) >>
  `i = EL (LENGTH t') (h::t')` by
    (qpat_x_assum `get_instruction bb _ = SOME i` mp_tac >>
     pure_rewrite_tac [get_instruction_def] >>
     asm_rewrite_tac [EL_APPEND_EQN, optionTheory.SOME_11] >>
     metis_tac[]) >>
  `LAST (h::t') = EL (LENGTH t') (h::t')` by simp[LAST_EL] >>
  metis_tac[]
QED

Theorem grouped_entry_cut_avoids_prior_labels:
  cs_extends sa sb /\ ALL_DISTINCT (MAP (\b. b.bb_label) (all_blocks sb)) /\
  MEM s.vs_current_bb (MAP (\b. b.bb_label) sa.cs_blocks) ==>
  ~(^before_cut sa sb fn id s)
Proof
  simp[] >> strip_tac >>
  qpat_x_assum `cs_extends sa sb` (strip_assume_tac o REWRITE_RULE [cs_extends_def]) >>
  drule emitted_blocks_append >> strip_tac >>
  `~MEM s.vs_current_bb (sb.cs_current_bb :: MAP (\b. b.bb_label) new)` by
    (fs[all_blocks_def, REVERSE_APPEND, MAP_REVERSE, ALL_DISTINCT_APPEND,
        ALL_DISTINCT_REVERSE, MAP_APPEND] >> metis_tac[MEM_MAP, MEM_REVERSE]) >>
  Cases_on `lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks` >>
  gvs[] >> drule frag_observer_lookup_cases >> rw[] >> fs[MEM_MAP] >> metis_tac[]
QED

Theorem grouped_entry_terminated_no_reentry:
  frag_fuel Wv {} {} sa sb Kb /\ at_point sa s /\ sa.cs_current_insts = [] /\
  fn_has_code sa sb fn /\ cs_extends sa sb /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks sb)) /\
  block_is_terminated sb /\ no_phi_fn fn /\ callees_stable G ctx fn /\
  gas_path ctx fn s n (OK t) ==>
  ~MEM t.vs_current_bb (MAP (\bb. bb.bb_label) sa.cs_blocks)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (fs[no_phi_fn_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  `~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa sb))` by
    (qpat_assum `cs_extends sa sb`
       (strip_assume_tac o REWRITE_RULE [cs_extends_def]) >>
     drule emitted_blocks_append >> strip_tac >>
     fs[all_blocks_def, REVERSE_APPEND, MAP_REVERSE, MAP_APPEND,
        ALL_DISTINCT_APPEND, MEM_REVERSE]) >>
  drule_all grouped_entry_first_cut >>
  disch_then (qspec_then `id` mp_tac) >> strip_tac
  >- (Cases_on `sb.cs_current_insts` >>
      gvs[block_is_terminated_def, at_point_def]) >>
  metis_tac[grouped_entry_cut_avoids_prior_labels,
            grouped_entry_terminated_cut_no_edge]
QED

Theorem grouped_entry_init_fragment:
  compile_entry_checks mincd pay sa = ((),sc) /\
  compile_init_kwargs ce vars off k (Lit 0w) sc = ((),sb) ==>
  cs_extends sa sb /\ ?Kb. frag_fuel UNIV {} {} sa sb Kb
Proof
  strip_tac >>
  `fuel_ok UNIV {} {} (compile_init_kwargs ce vars off k (Lit 0w))` by
    metis_tac[fuel_ok_compile_init_kwargs, cj 1 fuel_ok_compile_expr] >>
  `fuel_ok UNIV {} {}
    (comp_ignore_bind (compile_entry_checks mincd pay)
      (compile_init_kwargs ce vars off k (Lit 0w)))` by
    metis_tac[fuel_ok_ignore_bind0, fuel_ok_compile_entry_checks] >>
  fs[fuel_ok_def, comp_ignore_bind_def, comp_bind_def] >> metis_tac[]
QED

Theorem grouped_common_body_fragment:
  ce.ce_ctor_exit_label = NONE /\
  cenv_ptrs_below sa.cs_next_var (compile_register_kwarg_vars ce vars) /\
  compile_common_function_body ce args vars nr key tr view stmts rt sa = ((),sb) ==>
  cs_extends sa sb /\ ?Kb. frag_fuel UNIV {} {} sa sb Kb
Proof
  strip_tac >>
  `fuel_okS (\st. cenv_ptrs_below st.cs_next_var (compile_register_kwarg_vars ce vars))
    UNIV {} {} (compile_common_function_body ce args vars nr key tr view stmts rt)` by
    metis_tac[fuel_okS_compile_common_function_body, cj 2 fuel_okS_compile_stmt] >>
  fs[fuel_okS_def] >> metis_tac[]
QED

Theorem grouped_entry_cut_jumps_common:
  emit_inst JMP [Label common] [] cut = ((),term) /\
  fn_has_code cut term fn /\ at_point cut s /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  gas_path_edge ctx fn s k (OK t) ==>
  t.vs_current_bb = common /\ t.vs_inst_idx = 0
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all grouped_registration_edge_pc >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  `?rest. bb.bb_instructions = (cut.cs_current_insts ++
       [mk_inst cut.cs_next_id JMP [Label common] []]) ++ rest` by
    (gvs[fn_has_code_def, at_point_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  `i = mk_inst cut.cs_next_id JMP [Label common] []` by
    (qpat_x_assum `get_instruction bb _ = SOME i` mp_tac >>
     fs[at_point_def, get_instruction_def, EL_APPEND_EQN]) >>
  fs[mk_inst_def, is_terminator_def, get_successors_def, get_label_def]
QED

Theorem grouped_common_guarded_terminated:
  compile_guarded_body ce nr key tr view stmts rt sa = ((),sb) ==>
  block_is_terminated sb
Proof
  simp[compile_guarded_body_def, comp_get_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >>
  rpt (COND_CASES_TAC >> fs[]) >>
  Cases_on `rt` >> fs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  drule emit_inst_extends >> strip_tac >>
  rename1 `emit_inst _ [] [] src = ((),sb)` >>
  Cases_on `src.cs_current_insts` >>
  fs[block_is_terminated_def, LAST_CONS_cond, LAST_APPEND_CONS, mk_inst_def, is_terminator_def]
QED

Theorem grouped_entry_cut_cannot_return[local]:
  emit_inst JMP [Label common] [] cut = ((),term) /\
  fn_has_code cut term fn /\ at_point cut s /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  (!u m. u.vs_current_bb = common /\ u.vs_inst_idx = 0 ==>
    ~gas_path ctx fn u m (OK t)) /\
  gas_path ctx fn s n (OK t) ==>
  t = s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `gas_path ctx fn s n (OK t)`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_path_cases]) >>
  gvs[exit_result_def] >>
  drule_all grouped_entry_cut_jumps_common >> metis_tac[]
QED

Theorem grouped_entry_initializer_path:
  frag_fuel Wv {} {} sa cut Kb /\ at_point sa s /\ sa.cs_current_insts = [] /\
  fn_has_code sa cut fn /\ cs_extends sa cut /\
  ~MEM cut.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa cut)) /\
  emit_inst JMP [Label common] [] cut = ((),term) /\ fn_has_code cut term fn /\
  no_phi_fn fn /\ callees_stable G ctx fn /\
  (!u m. u.vs_current_bb = common /\ u.vs_inst_idx = 0 ==>
    ~gas_path ctx fn u m (OK t)) /\
  gas_path ctx fn s n (OK t) ==>
  RTC (\a b. ^before_cut sa cut fn id a /\ ?j. gas_path_edge ctx fn a j (OK b)) s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!v m. at_point cut v /\ gas_path ctx fn v m (OK t) ==> t = v` by
    (rpt gen_tac >> strip_tac >>
     `!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
       phi_prefix_length bb.bb_instructions = 0` by
       (fs[no_phi_fn_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
     metis_tac[grouped_entry_cut_cannot_return]) >>
  drule_all grouped_entry_first_cut >>
  disch_then (qspec_then `id` mp_tac) >> strip_tac
  >- (`t = s` by metis_tac[] >> simp[]) >>
  `t = v` by metis_tac[] >>
  irule (cj 2 RTC_RULES_RIGHT1) >>
  qexists_tac `u` >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem entry_observer_instruction_in_state[local]:
  fn_has_code sa cut fn /\ cs_extends sa cut /\
  ^before_cut sa cut fn id s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i ==>
  MEM i (state_insts cut)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all entry_observer_matches_before_cut >> strip_tac >>
  qpat_assum `lookup_block _ (frag_observer sa cut fn id).fn_blocks = SOME b`
     (strip_assume_tac o MATCH_MP frag_observer_lookup_cases)
  >- (`s.vs_inst_idx < LENGTH cut.cs_current_insts` by fs[] >>
      `MEM i cut.cs_current_insts` by
        (fs[get_instruction_def, EL_APPEND_EQN] >> metis_tac[EL_MEM]) >>
      simp[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND]) >>
  `MEM i b.bb_instructions` by (fs[get_instruction_def] >> metis_tac[EL_MEM]) >>
  `MEM b cut.cs_blocks` by
    (fs[cs_extends_def] >> drule emitted_blocks_append >> strip_tac >> fs[]) >>
  simp[state_insts_def, all_blocks_def, MEM_FLAT, MEM_MAP] >> metis_tac[MEM_REVERSE]
QED

Theorem grouped_entry_initializer_bounds:
  frag_fuel Wv {} {} sa cut Kb /\ at_point sa s /\ sa.cs_current_insts = [] /\
  fn_has_code sa cut fn /\ cs_extends sa cut /\
  ~MEM cut.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa cut)) /\
  emit_inst JMP [Label common] [] cut = ((),term) /\ fn_has_code cut term fn /\
  no_phi_fn fn /\ callees_stable G ctx fn /\
  (!u m. u.vs_current_bb = common /\ u.vs_inst_idx = 0 ==>
    ~gas_path ctx fn u m (OK t)) /\
  gas_path ctx fn s n (OK t) /\ fresh_vars_wrt cut s /\
  (!id pair. FLOOKUP s.vs_allocas id = SOME pair ==> id < cut.cs_next_id) /\
  (!i. MEM i (state_insts cut) ==>
    i.inst_opcode <> INVOKE /\ (i.inst_opcode = ALLOCA ==> i.inst_id < cut.cs_next_id) /\
    EVERY (not_fresh_at cut) i.inst_outputs) ==>
  fresh_vars_wrt cut t /\
  (!id pair. FLOOKUP t.vs_allocas id = SOME pair ==> id < cut.cs_next_id)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all grouped_entry_initializer_path >>
  disch_then (qspec_then `id` assume_tac) >>
  `!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (fs[no_phi_fn_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  mp_tac (BETA_RULE (Q.SPECL [`ctx`,`fn`,`cut`,
    `^before_cut sa cut fn id`,`s`,`t`] grouped_registration_bounds_rtc)) >>
  impl_tac >- (simp[] >> metis_tac[entry_observer_instruction_in_state]) >>
  simp[]
QED
