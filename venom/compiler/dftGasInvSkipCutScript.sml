Theory dftGasInvSkipCut
Ancestors
  dftGasInvPendingCut dftStructural dftDefs list rich_list arithmetic

Definition inv_skip_work_def:
  (inv_skip_work V A (DfsProcess i) <=>
    MEM i.inst_id V \/ is_pseudo i.inst_opcode \/ A i) /\
  (inv_skip_work V A (DfsEmit i) <=> A i)
End

Definition inv_skip_cut_def:
  inv_skip_cut V A P pre r st <=>
    (?mid post. st.ds_output = pre ++ mid ++ [r] ++ post /\ EVERY P mid) \/
    (?mid work tail. st.ds_output = pre ++ mid /\ EVERY P mid /\
      st.ds_stack = work ++ [DfsEmit r] ++ tail /\
      EVERY (inv_skip_work V A) work /\
      EVERY (\id. MEM id st.ds_visited) V)
End

Definition inv_skip_closed_def:
  inv_skip_closed bi order eda V A <=>
    !i child. A i /\ ~MEM i.inst_id V /\ ~is_pseudo i.inst_opcode /\
      MEM child (inst_all_deps bi order eda i) ==>
      MEM child.inst_id V \/ is_pseudo child.inst_opcode \/ A child
End

Theorem inv_skip_done_step[local]:
  (?mid post. st.ds_output = pre ++ mid ++ [r] ++ post /\ EVERY P mid) ==>
  inv_skip_cut V A P pre r (dfs_step bi order eda om do_flip st)
Proof
  strip_tac >> simp[inv_skip_cut_def] >> disj1_tac >>
  Cases_on `st.ds_stack` >> simp[dfs_step_def] >- metis_tac[] >>
  rename1 `st.ds_stack = item :: rest` >> Cases_on `item`
  >- (simp[dfs_step_def] >> rpt IF_CASES_TAC >> simp[] >>
      qexistsl [`mid`, `post`] >> simp[]) >>
  rename1 `st.ds_stack = DfsEmit i :: rest` >> simp[dfs_step_def] >>
  qexistsl [`mid`, `post ++ [i]`] >> simp[APPEND_ASSOC]
QED

Theorem inv_skip_cut_children[local]:
  inv_skip_closed bi order eda V A /\ A i /\
  ~MEM i.inst_id V /\ ~is_pseudo i.inst_opcode ==>
  EVERY (inv_skip_work V A)
    (MAP DfsProcess (sort_children bi order eda om i
      (inst_all_deps bi order eda i)))
Proof
  simp[EVERY_MAP, EVERY_MEM, inv_skip_work_def, inv_skip_closed_def] >>
  metis_tac[sort_children_mem]
QED

Theorem inv_skip_cut_step:
  inv_skip_closed bi order eda V A /\ inv_flip_closed A /\
  (!i. A i ==> P i) /\ inv_skip_cut V A P pre r st ==>
  inv_skip_cut V A P pre r (dfs_step bi order eda om do_flip st)
Proof
  strip_tac >>
  qpat_x_assum `inv_skip_cut V A P pre r st`
    (strip_assume_tac o REWRITE_RULE [inv_skip_cut_def])
  >- (irule inv_skip_done_step >> metis_tac[]) >>
  Cases_on `work`
  >- (simp[dfs_step_def, inv_skip_cut_def] >> disj1_tac >>
      qexistsl [`mid`, `[]`] >> simp[]) >>
  rename1 `EVERY (inv_skip_work V A) (item :: rest)` >>
  Cases_on `item` >> gns[inv_skip_work_def]
  >- (rename1 `MEM i.inst_id V \/ is_pseudo i.inst_opcode \/ A i` >>
      Cases_on `MEM i.inst_id st.ds_visited`
      >- (pure_rewrite_tac[inv_skip_cut_def] >> disj2_tac >>
          qexistsl [`mid`, `rest`, `tail`] >> simp[dfs_step_def]) >>
      `~MEM i.inst_id V` by (gvs[EVERY_MEM] >> metis_tac[]) >>
      Cases_on `is_pseudo i.inst_opcode`
      >- (pure_rewrite_tac[inv_skip_cut_def] >> disj2_tac >>
          qexistsl [`mid`, `rest`, `tail`] >>
          fs[dfs_step_def, EVERY_MEM] >> metis_tac[]) >>
      `A i` by metis_tac[] >>
      drule_all inv_skip_cut_children >> strip_tac >>
      simp[dfs_step_def] >>
      qmatch_goalsub_abbrev_tac `DfsEmit emitted` >>
      `A emitted` by
        (simp[Abbr `emitted`] >> IF_CASES_TAC >> gvs[inv_flip_closed_def]) >>
      pure_rewrite_tac[inv_skip_cut_def] >> disj2_tac >>
      qexistsl [`mid`,
        `MAP DfsProcess (sort_children bi order eda om i
           (inst_all_deps bi order eda i)) ++ [DfsEmit emitted] ++ rest`, `tail`] >>
      fs[APPEND_ASSOC, inv_skip_work_def, EVERY_MEM] >> metis_tac[]) >>
  pure_rewrite_tac[inv_skip_cut_def] >> disj2_tac >>
  qexistsl [`mid ++ [i]`, `rest`, `tail`] >> simp[dfs_step_def, APPEND_ASSOC]
QED

Theorem inv_skip_cut_run:
  inv_skip_closed bi order eda V A /\ inv_flip_closed A /\
  (!i. A i ==> P i) /\ inv_skip_cut V A P pre r st ==>
  inv_skip_cut V A P pre r (FUNPOW (dfs_step bi order eda om do_flip) n st)
Proof
  qid_spec_tac `st` >> Induct_on `n` >> simp[FUNPOW] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> irule inv_skip_cut_step >> simp[]
QED

Theorem inv_skip_cut_output:
  inv_skip_cut V A P pre r st /\ st.ds_stack = [] ==>
  ?mid post. st.ds_output = pre ++ mid ++ [r] ++ post /\ EVERY P mid
Proof
  strip_tac >> gvs[inv_skip_cut_def] >> metis_tac[]
QED
