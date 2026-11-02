(* Scheduler boundaries that do not require SSA or acyclic dependencies. *)
Theory dftNonSsa
Ancestors
  dftCompleteness dftScheduleFixed dftStructural dftTopoSort dftDefs
  venomInst list rich_list arithmetic
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
