Theory dftGasInvForwardOutput
Ancestors
  dftScheduleOrder
  dftGasInvForwardInterval dftNonSsa
  dftGasInvStackLineage dftRunRel dftDefs dftStructural dftWf dftTopoSort
  dftCorrectness dftIdempotent venomWf venomInst contextCodegenRel passSharedDefs
  venomEffects arithmetic list

Theorem inv_dfs_new_output:
  MEM item (dfs_step bi order eda om fl st).ds_output /\
  ~MEM item st.ds_output ==>
  ?rest. st.ds_stack = DfsEmit item :: rest
Proof
  Cases_on `st.ds_stack` >> simp[dfs_step_def] >>
  rename1 `work :: rest` >> Cases_on `work` >>
  simp[dfs_step_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem inv_line_output_origin:
  !n. MEM item (inv_line_state bi order eda om fl entries n).ds_output ==>
  ?k rest. k < n /\
    (inv_line_state bi order eda om fl entries k).ds_stack = DfsEmit item :: rest
Proof
  Induct >- simp[inv_line_state_def] >>
  simp[inv_line_state_def, FUNPOW_SUC] >> strip_tac >>
  Cases_on `MEM item (FUNPOW (dfs_step bi order eda om fl) n
    <|ds_stack := MAP DfsProcess entries; ds_output := []; ds_visited := []|>).ds_output`
  >- (qpat_x_assum `_ ==> ?k rest. _` (mp_tac o SIMP_RULE (srw_ss()) [inv_line_state_def]) >>
      simp[] >> strip_tac >> qexistsl [`k`, `rest`] >> simp[inv_line_state_def]) >>
  drule_all inv_dfs_new_output >> strip_tac >>
  qexistsl [`n`, `rest`] >> simp[inv_line_state_def]
QED

Theorem inv_forward_block_output:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ get_instruction bb j = SOME rev ==>
  ?pre mid post. (dft_block [] bb).bb_instructions =
    pre ++ [copy] ++ mid ++ [rev] ++ post /\
    EVERY (\a. a.inst_opcode = ASSIGN) mid
Proof
  strip_tac >>
  `bb_well_formed bb` by
    metis_tac[dft_fn_rel_def, wf_function_def, EVERY_MEM] >>
  `ALL_DISTINCT (MAP (\a. a.inst_id) bb.bb_instructions)` by
    (irule bb_inst_ids_distinct >> gvs[dft_fn_rel_def] >> metis_tac[]) >>
  `non_pseudo_defs_before_uses bb.bb_instructions` by
    (simp[non_pseudo_defs_before_uses_def] >>
     metis_tac[wf_ssa_defs_before_uses, dft_fn_rel_def]) >>
  `copy.inst_opcode = RETURNDATACOPY /\ MEM copy bb.bb_instructions` by
    (gvs[revert_forward_pair_def, get_instruction_def, AllCaseEqs()] >>
     irule EL_MEM >> decide_tac) >>
  `~is_pseudo copy.inst_opcode /\ ~is_flippable copy.inst_opcode` by
    simp[is_pseudo_def, is_flippable_def, is_commutative_def, is_comparator_def] >>
  `MEM copy (dft_block [] bb).bb_instructions` by
    metis_tac[dft_block_nonflippable_mem] >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `entries = entry_instructions bi [] (dft_eda bi)` >>
  qabbrev_tac `advance = dfs_step bi [] (dft_eda bi) (build_offspring_map bi []) T` >>
  qabbrev_tac `budget = (LENGTH bi + 1) * (LENGTH bi + 1)` >>
  `MEM copy (inv_line_state bi [] (dft_eda bi)
      (build_offspring_map bi []) T entries budget).ds_output` by
    (qpat_x_assum `MEM copy (dft_block [] bb).bb_instructions` mp_tac >>
     simp[dft_block_def, schedule_from_entries_def, inv_line_state_def,
       Abbr `bi`, Abbr `entries`, Abbr `budget`, MEM_FILTER]) >>
  drule inv_line_output_origin >> strip_tac >>
  qabbrev_tac `st = inv_line_state bi [] (dft_eda bi)
      (build_offspring_map bi []) T entries k` >>
  `inv_line_state bi [] (dft_eda bi) (build_offspring_map bi []) T entries budget =
     FUNPOW advance (budget - SUC k) (advance st)` by
    (simp[Abbr `st`, inv_line_state_def, Abbr `advance`, GSYM FUNPOW_SUC,
       GSYM FUNPOW_ADD] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac) >>
  `(FUNPOW advance (budget - SUC k) (advance st)).ds_stack = []` by
    (qpat_x_assum `inv_line_state _ _ _ _ _ _ budget = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[inv_line_state_def, Abbr `budget`, Abbr `entries`, Abbr `advance`] >>
     irule (SIMP_RULE (srw_ss()) [GSYM EXP_2] schedule_entry_stack_empty) >> simp[dft_eda_wf]) >>
  `st = inv_line_state bb.bb_instructions [] (dft_eda bb.bb_instructions)
      (build_offspring_map bb.bb_instructions []) T
      (entry_instructions bb.bb_instructions [] (dft_eda bb.bb_instructions)) k` by
    simp[Abbr `st`, Abbr `entries`, Abbr `bi`] >>
  mp_tac (Q.INST [`ticks` |-> `k`] inv_forward_initialized_interval) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qspec_then `budget - SUC k` mp_tac) >>
  (impl_tac >- (qpat_x_assum `(FUNPOW advance _ _).ds_stack = []` mp_tac >>
     simp[Abbr `advance`, Abbr `bi`])) >> strip_tac >>
  ` (dft_block [] bb).bb_instructions =
      FILTER (\a. is_pseudo a.inst_opcode) bi ++
      (FUNPOW advance (budget - SUC k) (advance st)).ds_output` by
    (qpat_x_assum `inv_line_state _ _ _ _ _ _ budget = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[dft_block_def, schedule_from_entries_def, inv_line_state_def,
       Abbr `entries`, Abbr `budget`, Abbr `bi`]) >>
  qexistsl [`FILTER (\a. is_pseudo a.inst_opcode) bi ++ st.ds_output`, `mid`, `post`] >>
  qpat_x_assum `(FUNPOW (dfs_step _ _ _ _ _) _ _).ds_output = _` mp_tac >>
  qpat_x_assum `(dft_block [] bb).bb_instructions = _` mp_tac >>
  qpat_x_assum `EVERY _ mid` mp_tac >>
  simp[NoAsms, Abbr `advance`, Abbr `bi`] >>
  POP_ASSUM_LIST (K all_tac) >> simp[APPEND_ASSOC]
QED
