(* Scheduler boundaries that do not require SSA or acyclic dependencies. *)
Theory dftNonSsa
Ancestors
  dftCompleteness dftScheduleFixed dftStructural dftTopoSort dftDefs
  dftWf dftIdempotent dftCorrectness venomWf
  venomInst list rich_list arithmetic finite_map option
Libs
  BasicProvers

Theorem dfs_stack_empty_after_measure:
  !fuel bi order eda om fl st.
    eda_wf eda bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    dfs_good_state bi st /\ dfs_measure bi st <= fuel ==>
    (FUNPOW (dfs_step bi order eda om fl) fuel st).ds_stack = []
Proof
  Induct_on `fuel` >> rpt strip_tac
  >- gvs[dfs_measure_def]
  >> Cases_on `st.ds_stack = []`
  >- simp[funpow_dfs_step_idle]
  >> `dfs_measure bi (dfs_step bi order eda om fl st) <
      dfs_measure bi st` by
       (irule dfs_step_measure_dec >> simp[]) >>
  simp[FUNPOW] >> first_x_assum irule >>
  simp[] >> irule dfs_step_preserves_good >> simp[]
QED

Theorem schedule_entry_stack_empty:
  !bi order eda om fl.
    eda_wf eda bi /\ ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    (FUNPOW (dfs_step bi order eda om fl)
       ((LENGTH bi + 1) * (LENGTH bi + 1))
       <| ds_stack := MAP DfsProcess (entry_instructions bi order eda);
          ds_output := []; ds_visited := [] |>).ds_stack = []
Proof
  rpt strip_tac >> irule dfs_stack_empty_after_measure >> simp[] >>
  reverse conj_tac
  >- (irule init_dfs_state_good >> simp[entry_instructions_mem]) >>
  simp[dfs_measure_def, unvisited_count_def] >>
  `LENGTH (entry_instructions bi order eda) <= LENGTH bi` by
    (simp[entry_instructions_def, LET_THM] >>
     irule LESS_EQ_TRANS >>
     qexists `LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` >>
     simp[LENGTH_FILTER_LEQ]) >>
  `LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode) bi) <= LENGTH bi` by
    simp[LENGTH_FILTER_LEQ] >>
  irule LESS_EQ_TRANS >>
  qexists `LENGTH bi + LENGTH bi * (LENGTH bi + 1)` >>
  conj_tac
  >- (irule LESS_EQ_LESS_EQ_MONO >> conj_tac >- simp[] >>
      irule LESS_MONO_MULT >> simp[]) >>
  rewrite_tac[EXP_2, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] >>
  decide_tac
QED

Definition dfs_emit_accounting_def:
  dfs_emit_accounting st <=>
    ALL_DISTINCT (MAP (\i. i.inst_id) st.ds_output ++
                  stack_emit_ids st.ds_stack) /\
    EVERY (\id. MEM id st.ds_visited)
      (MAP (\i. i.inst_id) st.ds_output ++ stack_emit_ids st.ds_stack)
End

Theorem stack_emit_ids_process_prefix:
  !xs rest. stack_emit_ids (MAP DfsProcess xs ++ rest) =
            stack_emit_ids rest
Proof
  Induct >> simp[stack_emit_ids_def]
QED

Theorem dfs_emit_accounting_init:
  dfs_emit_accounting
    <|ds_stack := MAP DfsProcess entries; ds_output := []; ds_visited := []|>
Proof
  Induct_on `entries` >>
  gvs[dfs_emit_accounting_def, stack_emit_ids_def]
QED

Theorem dfs_step_preserves_emit_accounting:
  dfs_emit_accounting st ==>
  dfs_emit_accounting (dfs_step bi order eda om fl st)
Proof
  strip_tac >> Cases_on `st.ds_stack`
  >- simp[dfs_step_def] >>
  rename1 `st.ds_stack = item :: rest` >> Cases_on `item` >>
  gvs[dfs_step_def, dfs_emit_accounting_def, stack_emit_ids_def,
      ALL_DISTINCT_APPEND, EVERY_APPEND] >>
  rpt IF_CASES_TAC >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[stack_emit_ids_process_prefix, stack_emit_ids_def,
      ALL_DISTINCT_APPEND, EVERY_APPEND, flip_operands_inst_id,
      EVERY_MEM, MEM_MAP] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[stack_emit_ids_process_prefix, stack_emit_ids_def,
      flip_operands_inst_id] >> metis_tac[]
QED

Theorem dfs_funpow_preserves_emit_accounting:
  !fuel st. dfs_emit_accounting st ==>
    dfs_emit_accounting (FUNPOW (dfs_step bi order eda om fl) fuel st)
Proof
  Induct >> simp[FUNPOW] >> rpt strip_tac >>
  first_x_assum irule >> irule dfs_step_preserves_emit_accounting >> simp[]
QED

Theorem schedule_output_distinct_ids:
  ALL_DISTINCT (MAP (\i. i.inst_id)
    (schedule_from_entries bi order eda om entries))
Proof
  simp[schedule_from_entries_def] >>
  qmatch_goalsub_abbrev_tac `FUNPOW dfs budget initial` >>
  `dfs_emit_accounting (FUNPOW dfs budget initial)` by
    (simp[Abbr `dfs`] >> irule dfs_funpow_preserves_emit_accounting >>
     simp[Abbr `initial`, dfs_emit_accounting_init]) >>
  gvs[dfs_emit_accounting_def, ALL_DISTINCT_APPEND]
QED

Theorem dft_block_distinct_ids:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) (dft_block order bb).bb_instructions)
Proof
  strip_tac >> simp[dft_block_def, ALL_DISTINCT_APPEND,
                    schedule_output_distinct_ids] >>
  conj_tac
  >- (qpat_x_assum `ALL_DISTINCT _` mp_tac >>
      qspec_tac (`bb.bb_instructions`, `bi`) >> Induct >>
      simp[] >> gen_tac >> Cases_on `is_pseudo h.inst_opcode` >>
      simp[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  rpt strip_tac >> gvs[MEM_MAP, MEM_FILTER] >>
  drule_at (Pos last) schedule_output_from_block >>
  (impl_tac >- simp[build_eda_wf, EVERY_MEM, entry_instructions_mem]) >>
  strip_tac >> gvs[from_block_def, flip_operands_inst_id] >>
  qpat_x_assum `MEM _ (schedule_from_entries _ _ _ _ _)` kall_tac >>
  gvs[MEM_EL] >>
  metis_tac[ALL_DISTINCT_EL_IMP, EL_MAP, LENGTH_MAP]
QED

Theorem data_dep_has_output:
  MEM dep (inst_data_deps bi order inst) ==> dep.inst_outputs <> []
Proof
  simp[inst_data_deps_def, MEM_nub, MEM_MAP, MEM_FILTER,
       IS_SOME_EXISTS] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `is_terminator inst.inst_opcode` >>
      gvs[MEM_FILTER, MEM_MAP, IS_SOME_EXISTS] >>
      drule producing_inst_mem_outputs >> simp[]) >>
  rename1 `operand_producer bi op = SOME dep` >>
  Cases_on `op` >> gvs[operand_producer_def] >>
  drule producing_inst_mem_outputs >> simp[]
QED

Theorem last_not_dependency:
  bi <> [] /\ (LAST bi).inst_outputs = [] /\
  ~is_pseudo (LAST bi).inst_opcode /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  MEM inst bi /\ ~is_pseudo inst.inst_opcode ==>
  ~MEM (LAST bi).inst_id
    (MAP (\d. d.inst_id) (inst_all_deps bi order (build_eda bi) inst))
Proof
  rpt strip_tac >> gvs[MEM_MAP] >>
  rename1 `MEM dep (inst_all_deps bi order (build_eda bi) inst)` >>
  `MEM dep bi` by metis_tac[inst_all_deps_mem, build_eda_wf] >>
  `dep = LAST bi` by
    (qpat_x_assum `MEM dep (inst_all_deps _ _ _ _)` kall_tac >>
     `MEM (LAST bi) bi` by metis_tac[MEM_LAST_NOT_NIL] >>
     gvs[MEM_EL] >> metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP, EL_MAP]) >>
  gvs[inst_all_deps_def, MEM_nub] 
  >- metis_tac[data_dep_has_output] >>
  Cases_on `FLOOKUP (build_eda bi) inst.inst_id` >> gvs[] >>
  drule_all eda_deps_backward_plain >> strip_tac >>
  gvs[LAST_EL] >>
  `PRE (LENGTH bi) < LENGTH bi` by (Cases_on `bi` >> gvs[]) >>
  `EL i (MAP (\d. d.inst_id) bi) =
   EL (PRE (LENGTH bi)) (MAP (\d. d.inst_id) bi)` by simp[EL_MAP] >>
  `i = PRE (LENGTH bi)` by
    (qspecl_then [`MAP (\d. d.inst_id) bi`, `i`, `PRE (LENGTH bi)`]
       mp_tac ALL_DISTINCT_EL_IMP >> simp[]) >>
  gvs[]
QED

Theorem entry_instructions_last:
  bi <> [] /\ ~is_pseudo (LAST bi).inst_opcode /\
  (!inst. MEM inst bi /\ ~is_pseudo inst.inst_opcode ==>
    ~MEM (LAST bi).inst_id (MAP (\d. d.inst_id) (inst_all_deps bi order eda inst))) ==>
  entry_instructions bi order eda <> [] /\
  LAST (entry_instructions bi order eda) = LAST bi
Proof
  strip_tac >>
  `~MEM (LAST bi).inst_id
    (FLAT (MAP (\i. MAP (\d. d.inst_id) (inst_all_deps bi order eda i))
      (FILTER (\i. ~is_pseudo i.inst_opcode) bi)))` by
    (simp[MEM_FLAT, MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  simp[entry_instructions_def] >>
  qmatch_goalsub_abbrev_tac `FILTER pred (FILTER np bi)` >>
  `np (LAST bi) /\ pred (LAST bi)` by simp[Abbr `np`, Abbr `pred`] >>
  `bi = FRONT bi ++ [LAST bi]` by metis_tac[APPEND_FRONT_LAST] >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  simp[FILTER_APPEND, LAST_APPEND]
QED

Theorem entry_initial_bottom:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  entries = entry_instructions bi order eda /\ entries <> [] /\
  LAST entries = LAST bi /\ ~is_pseudo (LAST bi).inst_opcode ==>
  bottom_inv (LAST bi).inst_id
    <|ds_stack := MAP DfsProcess entries; ds_output := []; ds_visited := []|>
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) entries)` by
    (gvs[entry_instructions_def] >>
     irule dftPipelineInvarTheory.all_distinct_map_filter >>
     irule dftPipelineInvarTheory.all_distinct_map_filter >> simp[]) >>
  `~MEM (LAST bi).inst_id (MAP (\i. i.inst_id) (FRONT entries))` by
    (qspec_then `MAP (\i. i.inst_id) entries` mp_tac
       (DB.fetch "rich_list" "MEM_FRONT_NOT_LAST") >>
     simp[LAST_MAP, MAP_FRONT]) >>
  `id_not_in_stack (LAST bi).inst_id (MAP DfsProcess (FRONT entries))` by
    (pop_assum mp_tac >> qspec_tac (`FRONT entries`, `xs`) >>
     Induct >> simp[id_not_in_stack_def]) >>
  simp[bottom_inv_def] >> disj1_tac >>
  qexistsl_tac [`MAP DfsProcess (FRONT entries)`, `LAST entries`] >>
  `MAP DfsProcess entries =
   MAP DfsProcess (FRONT entries) ++ [DfsProcess (LAST entries)]` by
    metis_tac[APPEND_FRONT_LAST, MAP_APPEND, MAP] >> simp[] >> metis_tac[]
QED

Theorem schedule_last_id:
  eda_wf eda bi /\ ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  bi <> [] /\ ~is_pseudo (LAST bi).inst_opcode /\
  (!inst. MEM inst bi /\ ~is_pseudo inst.inst_opcode ==>
    ~MEM (LAST bi).inst_id (MAP (\d. d.inst_id) (inst_all_deps bi order eda inst))) ==>
  let output = schedule_from_entries bi order eda om (entry_instructions bi order eda) in
    output <> [] /\ (LAST output).inst_id = (LAST bi).inst_id
Proof
  strip_tac >>
  `entry_instructions bi order eda <> [] /\
   LAST (entry_instructions bi order eda) = LAST bi` by
    (irule entry_instructions_last >> simp[]) >>
  simp[schedule_from_entries_def] >>
  qmatch_goalsub_abbrev_tac `FUNPOW dfs budget initial` >>
  `bottom_inv (LAST bi).inst_id initial` by
    (simp[Abbr `initial`] >> irule entry_initial_bottom >>
     simp[] >> qexistsl_tac [`eda`, `order`] >> simp[]) >>
  `bottom_inv (LAST bi).inst_id (FUNPOW dfs budget initial)` by
    (simp[Abbr `dfs`] >> irule funpow_preserves_bottom_inv >> simp[] >>
     simp[Abbr `initial`, MEM_MAP] >> rpt strip_tac >>
     gvs[] >>
     mp_tac (SRULE [EVERY_MEM] entry_instructions_mem) >>
     disch_then drule >> simp[]) >>
  `(FUNPOW dfs budget initial).ds_stack = []` by
    (simp[Abbr `dfs`, Abbr `budget`, Abbr `initial`] >>
     rewrite_tac[EXP_2] >> irule schedule_entry_stack_empty >> simp[]) >>
  gvs[bottom_inv_def]
QED

Theorem dft_block_last:
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  (dft_block order bb).bb_instructions <> [] /\
  LAST (dft_block order bb).bb_instructions = LAST bb.bb_instructions
Proof
  strip_tac >>
  qpat_x_assum `bb_well_formed bb` mp_tac >>
  simp[bb_well_formed_def] >> strip_tac >>
  qabbrev_tac `term = LAST bb.bb_instructions` >>
  `MEM term bb.bb_instructions` by metis_tac[MEM_LAST_NOT_NIL] >>
  `inst_wf term` by gvs[EVERY_MEM] >>
  `~is_pseudo term.inst_opcode /\ ~is_flippable term.inst_opcode /\
   term.inst_outputs = []` by
    (qpat_x_assum `is_terminator _` mp_tac >>
     qpat_x_assum `inst_wf term` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `term.inst_opcode` >>
     simp[is_terminator_def] >>
     simp[is_pseudo_def, is_flippable_def] >>
     simp[inst_wf_def, venomEffectsTheory.is_commutative_def,
          passSharedDefsTheory.is_comparator_def] >>
     metis_tac[]) >>
  qabbrev_tac `out = schedule_from_entries bb.bb_instructions order
    (build_eda bb.bb_instructions) (build_offspring_map bb.bb_instructions order)
    (entry_instructions bb.bb_instructions order (build_eda bb.bb_instructions))` >>
  `out <> [] /\ (LAST out).inst_id = term.inst_id` by
    (simp[Abbr `out`, Abbr `term`] >>
     irule (SIMP_RULE (srw_ss()) [LET_THM] schedule_last_id) >> simp[build_eda_wf] >>
     rpt gen_tac >> strip_tac >> irule last_not_dependency >> simp[]) >>
  `from_block bb.bb_instructions (LAST out)` by
    (irule (INST_TYPE [alpha |-> ``:instruction``] (cj 1 schedule_output_from_block)) >>
     simp[build_eda_wf, EVERY_MEM, entry_instructions_mem] >>
     qexistsl_tac [`build_eda bb.bb_instructions`,
       `entry_instructions bb.bb_instructions order (build_eda bb.bb_instructions)`,
       `build_offspring_map bb.bb_instructions order`, `order`] >>
     simp[build_eda_wf, GSYM EVERY_MEM, entry_instructions_mem] >>
     qunabbrev_tac `out` >> metis_tac[MEM_LAST_NOT_NIL]) >>
  `LAST out = term` by suspend "exact_last" >>
  gvs[dft_block_def, Abbr `out`, rich_listTheory.LAST_APPEND_NOT_NIL, Abbr `term`]
QED

Resume dft_block_last[exact_last]:
  qpat_x_assum `from_block _ _` mp_tac >>
  simp[from_block_def] >> strip_tac >>
  gvs[flip_operands_inst_id]
  >- metis_tac[dftCorrectnessTheory.all_distinct_map_mem_inj] >>
  `j = term` by metis_tac[dftCorrectnessTheory.all_distinct_map_mem_inj] >>
  gvs[]
QED

Finalise dft_block_last

Theorem dft_block_succs:
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  bb_succs (dft_block order bb) = bb_succs bb
Proof
  strip_tac >> drule_all dft_block_last >>
  disch_then (qspec_then `order` strip_assume_tac) >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  simp[bb_succs_def] >>
  Cases_on `bb.bb_instructions` >>
  Cases_on `(dft_block order bb).bb_instructions` >> gvs[]
QED
