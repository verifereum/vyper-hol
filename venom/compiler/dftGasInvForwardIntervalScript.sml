Theory dftGasInvForwardInterval
Ancestors
  dftGasInvSkipCut dftGasInvPendingCut dftGasInvSourceLineage dftGasInvForwardResidual
  dftGasInvForwardEffects dftGasInvInitializedTerminals dftGasInvAliasPaths
  dftGasInvStackLineage dftDefs dftStructural dftRunRel dftCorrectness
  dftWf dftTopoSort dftIdempotent venomInst venomWf passSharedDefs
  contextCodegenRel list rich_list arithmetic relation

Definition inv_forward_assign_def:
  inv_forward_assign bi q m prod <=>
    prod.inst_opcode = ASSIGN /\
    ?b. (RTC (inv_assign_edge bi) q b \/ RTC (inv_assign_edge bi) m b) /\
      operand_producer bi b = SOME prod
End

Theorem inv_forward_assign_flip[local]:
  inv_flip_closed (inv_forward_assign bi q m)
Proof
  simp[inv_flip_closed_def, inv_forward_assign_def] >> rpt strip_tac >>
  gvs[is_flippable_def, venomEffectsTheory.is_commutative_def, is_comparator_def]
QED

Theorem inv_forward_residual_closed:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ copy.inst_operands = [p;src;sz] /\
  get_instruction bb j = SOME rev /\ rev.inst_operands = [q;m] /\
  st = inv_line_state bb.bb_instructions [] (dft_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions []) T
    (entry_instructions bb.bb_instructions [] (dft_eda bb.bb_instructions)) ticks /\
  MEM copy st.ds_output ==>
  inv_skip_closed bb.bb_instructions [] (dft_eda bb.bb_instructions)
    st.ds_visited (inv_forward_assign bb.bb_instructions q m)
Proof
  strip_tac >> pure_rewrite_tac[inv_skip_closed_def] >>
  map_every qx_gen_tac [`inst`, `child`] >> strip_tac >>
  `inst.inst_opcode = ASSIGN` by metis_tac[inv_forward_assign_def] >>
  `?b. (RTC (inv_assign_edge bb.bb_instructions) q b \/
        RTC (inv_assign_edge bb.bb_instructions) m b) /\
       operand_producer bb.bb_instructions b = SOME inst` by
    metis_tac[inv_forward_assign_def] >>
  `?c. (RTC (inv_assign_edge bb.bb_instructions) q c \/
        RTC (inv_assign_edge bb.bb_instructions) m c) /\
       operand_producer bb.bb_instructions c = SOME child` by
    metis_tac[inv_forward_residual_children] >>
  `child.inst_opcode = ASSIGN \/ is_pseudo child.inst_opcode \/
   MEM child.inst_id st.ds_visited` by
    metis_tac[inv_forward_initialized_residual] >>
  simp[] >> metis_tac[inv_forward_assign_def]
QED

Theorem inv_revert_data_producer:
  rev.inst_opcode = REVERT /\ rev.inst_operands = [q;m] /\
  MEM prod (inst_data_deps bi [] rev) ==>
  operand_producer bi q = SOME prod \/ operand_producer bi m = SOME prod
Proof
  simp[inst_data_deps_def, python_stack_operands_def, ir_specific_operand_order_def,
       is_terminator_def, nub_first_def, MEM_nub, MEM_MAP, MEM_FILTER] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `ir_specific_operand_order REVERT` >> gvs[] >>
  gvs[optionTheory.IS_SOME_EXISTS]
QED

Definition inv_emit_visited_def:
  inv_emit_visited st <=>
    EVERY (\item. case item of DfsProcess inst => T
      | DfsEmit inst => MEM inst.inst_id st.ds_visited) st.ds_stack
End

Theorem inv_emit_visited_step[local]:
  inv_emit_visited st ==>
  inv_emit_visited (dfs_step bi order eda om do_flip st)
Proof
  strip_tac >> Cases_on `st.ds_stack` >> gvs[inv_emit_visited_def, dfs_step_def] >>
  rename1 `st.ds_stack = item::rest` >> Cases_on `item` >>
  gvs[inv_emit_visited_def, dfs_step_def] >>
  rpt IF_CASES_TAC >>
  gvs[EVERY_MEM, MEM_MAP, flip_operands_inst_id] >>
  rpt gen_tac >> strip_tac >> Cases_on `item` >> gvs[] >>
  rename1 `MEM (DfsEmit emitted) rest` >>
  first_x_assum (qspec_then `DfsEmit emitted` mp_tac) >> simp[]
QED

Theorem inv_initialized_emit_visited[local]:
  !ticks. inv_emit_visited (inv_line_state bi order eda om do_flip entries ticks)
Proof
  Induct >- simp[inv_emit_visited_def, inv_line_state_def, EVERY_MAP] >>
  simp[inv_line_state_def, FUNPOW_SUC] >>
  irule inv_emit_visited_step >> gvs[inv_line_state_def]
QED

Theorem inv_forward_skip_init:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ copy.inst_operands = [p;src;sz] /\
  get_instruction bb j = SOME rev /\ rev.inst_operands = [q;m] /\
  st = inv_line_state bb.bb_instructions [] (dft_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions []) T
    (entry_instructions bb.bb_instructions [] (dft_eda bb.bb_instructions)) ticks /\
  st.ds_stack = DfsEmit copy :: rest /\
  s0 = dfs_step bb.bb_instructions [] (dft_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions []) T st ==>
  inv_skip_cut s0.ds_visited (inv_forward_assign bb.bb_instructions q m)
    (\a. a.inst_opcode = ASSIGN) (st.ds_output ++ [copy]) rev s0
Proof
  strip_tac >>
  `s0.ds_stack = rest /\ s0.ds_output = st.ds_output ++ [copy] /\
   s0.ds_visited = st.ds_visited` by simp[dfs_step_def] >>
  `s0 = inv_line_state bb.bb_instructions [] (dft_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions []) T
    (entry_instructions bb.bb_instructions [] (dft_eda bb.bb_instructions)) (SUC ticks)` by
    simp[inv_line_state_def, FUNPOW_SUC] >>
  `MEM copy s0.ds_output` by simp[] >>
  `inv_emit_visited st` by metis_tac[inv_initialized_emit_visited] >>
  `MEM copy.inst_id s0.ds_visited` by gvs[inv_emit_visited_def] >>
  drule_all inv_forward_initialized_frame >> strip_tac >>
  `ALL_DISTINCT (MAP (\a. a.inst_id) bb.bb_instructions)` by
    (irule bb_inst_ids_distinct >> gvs[dft_fn_rel_def] >> metis_tac[]) >>
  `rev.inst_opcode = REVERT` by
    gvs[revert_forward_pair_def, get_instruction_def, AllCaseEqs()] >>
  `EVERY (inv_skip_work s0.ds_visited (inv_forward_assign bb.bb_instructions q m))
      (MAP DfsProcess pending)` by
    (simp[EVERY_MAP, EVERY_MEM, inv_skip_work_def] >> qx_gen_tac `prod` >> strip_tac >>
     `MEM prod (inst_all_deps bb.bb_instructions [] (dft_eda bb.bb_instructions) rev)` by
       (qpat_x_assum `inv_line_link _ _ _` mp_tac >>
        simp[inv_line_link_def] >> rpt strip_tac >>
        `MEM prod (inv_line_children bb.bb_instructions []
          (dft_eda bb.bb_instructions) (build_offspring_map bb.bb_instructions []) rev)` by
          simp[] >>
        metis_tac[inv_line_children_def, sort_children_mem]) >>
     `prod = copy \/ MEM prod (inst_data_deps bb.bb_instructions [] rev)` by
       metis_tac[inv_forward_all_deps] >>
     Cases_on `prod = copy` >- gvs[] >>
     `operand_producer bb.bb_instructions q = SOME prod \/
      operand_producer bb.bb_instructions m = SOME prod` by
       metis_tac[inv_revert_data_producer] >>
     `?b. (RTC (inv_assign_edge bb.bb_instructions) q b \/
           RTC (inv_assign_edge bb.bb_instructions) m b) /\
          operand_producer bb.bb_instructions b = SOME prod` by
       metis_tac[RTC_REFL] >>
     `prod.inst_opcode = ASSIGN \/ is_pseudo prod.inst_opcode \/
      MEM prod.inst_id s0.ds_visited` by
       metis_tac[inv_forward_initialized_residual] >>
     metis_tac[inv_forward_assign_def]) >>
  pure_rewrite_tac[inv_skip_cut_def] >> disj2_tac >>
  qexistsl [`[]`, `MAP DfsProcess pending`, `tail`] >> simp[EVERY_MEM]
QED

Theorem inv_forward_initialized_cut:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ get_instruction bb j = SOME rev /\
  st = inv_line_state bb.bb_instructions [] (dft_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions []) T
    (entry_instructions bb.bb_instructions [] (dft_eda bb.bb_instructions)) ticks /\
  st.ds_stack = DfsEmit copy :: rest /\
  s0 = dfs_step bb.bb_instructions [] (dft_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions []) T st ==>
  ?q m. rev.inst_operands = [q;m] /\
    !n. inv_skip_cut s0.ds_visited (inv_forward_assign bb.bb_instructions q m)
      (\a. a.inst_opcode = ASSIGN) (st.ds_output ++ [copy]) rev
      (FUNPOW (dfs_step bb.bb_instructions [] (dft_eda bb.bb_instructions)
        (build_offspring_map bb.bb_instructions []) T) n s0)
Proof
  strip_tac >>
  `?p src sz q m. copy.inst_operands = [p;src;sz] /\ rev.inst_operands = [q;m]` by
    (gvs[revert_forward_pair_def, get_instruction_def, AllCaseEqs()] >> metis_tac[]) >>
  qexistsl [`q`, `m`] >> simp[] >> gen_tac >>
  `s0 = inv_line_state bb.bb_instructions [] (dft_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions []) T
    (entry_instructions bb.bb_instructions [] (dft_eda bb.bb_instructions)) (SUC ticks)` by
    simp[inv_line_state_def, FUNPOW_SUC] >>
  `MEM copy s0.ds_output` by
    (qpat_assum `s0 = dfs_step _ _ _ _ _ _`
      (fn th => pure_once_rewrite_tac[th]) >> simp[dfs_step_def]) >>
  irule inv_skip_cut_run >> simp[inv_forward_assign_flip] >>
  conj_tac >- simp[inv_forward_assign_def] >>
  conj_tac >- (irule inv_forward_residual_closed >> metis_tac[]) >>
  irule inv_forward_skip_init >> metis_tac[]
QED

Theorem inv_forward_initialized_interval:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ get_instruction bb j = SOME rev /\
  st = inv_line_state bb.bb_instructions [] (dft_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions []) T
    (entry_instructions bb.bb_instructions [] (dft_eda bb.bb_instructions)) ticks /\
  st.ds_stack = DfsEmit copy :: rest ==>
  !n. (FUNPOW (dfs_step bb.bb_instructions [] (dft_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions []) T) n
    (dfs_step bb.bb_instructions [] (dft_eda bb.bb_instructions)
      (build_offspring_map bb.bb_instructions []) T st)).ds_stack = [] ==>
  ?mid post.
    (FUNPOW (dfs_step bb.bb_instructions [] (dft_eda bb.bb_instructions)
      (build_offspring_map bb.bb_instructions []) T) n
      (dfs_step bb.bb_instructions [] (dft_eda bb.bb_instructions)
        (build_offspring_map bb.bb_instructions []) T st)).ds_output =
      st.ds_output ++ [copy] ++ mid ++ [rev] ++ post /\
    EVERY (\a. a.inst_opcode = ASSIGN) mid
Proof
  strip_tac >> gen_tac >> strip_tac >>
  irule inv_skip_cut_output >>
  conj_tac >- simp[] >>
  mp_tac (Q.INST [`s0` |->
    `dfs_step bb.bb_instructions [] (dft_eda bb.bb_instructions)
      (build_offspring_map bb.bb_instructions []) T st`]
    inv_forward_initialized_cut) >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >> metis_tac[]
QED
