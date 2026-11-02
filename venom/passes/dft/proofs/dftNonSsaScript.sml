(* Scheduler boundaries that do not require SSA or acyclic dependencies. *)
Theory dftNonSsa
Ancestors
  dftCompleteness dftScheduleFixed dftStructural dftDefs
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
