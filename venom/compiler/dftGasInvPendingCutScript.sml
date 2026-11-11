Theory dftGasInvPendingCut
Ancestors
  dftStructural dftScheduleOrder dftDefs

Definition inv_work_def:
  (inv_work bi V P (DfsProcess i) <=>
    MEM i bi /\ (MEM i.inst_id V \/ P i)) /\
  (inv_work bi V P (DfsEmit i) <=> P i)
End

Definition inv_cut_def:
  inv_cut bi V P pre r st <=>
    (?mid post. st.ds_output = pre ++ mid ++ [r] ++ post /\ EVERY P mid) \/
    (?mid work tail. st.ds_output = pre ++ mid /\ EVERY P mid /\
      st.ds_stack = work ++ [DfsEmit r] ++ tail /\
      EVERY (inv_work bi V P) work /\
      EVERY (\id. MEM id st.ds_visited) V)
End

Definition inv_closed_def:
  inv_closed bi order eda V P <=>
    !i child. MEM i bi /\ P i /\ ~MEM i.inst_id V /\
      ~is_pseudo i.inst_opcode /\
      MEM child (inst_all_deps bi order eda i) ==>
      MEM child bi /\ (MEM child.inst_id V \/ P child)
End

Definition inv_flip_closed_def:
  inv_flip_closed P <=>
    !i. P i /\ is_flippable i.inst_opcode ==> P (flip_operands i)
End

Theorem inv_cut_pending:
  st.ds_output = pre ++ mid /\ EVERY P mid /\
  st.ds_stack = work ++ [DfsEmit r] ++ tail /\
  EVERY (inv_work bi V P) work /\
  EVERY (\id. MEM id st.ds_visited) V ==>
  inv_cut bi V P pre r st
Proof
  simp[inv_cut_def] >> metis_tac[]
QED

Theorem inv_cut_done_step:
  (?mid post. st.ds_output = pre ++ mid ++ [r] ++ post /\ EVERY P mid) ==>
  inv_cut bi V P pre r (dfs_step bi order eda om do_flip st)
Proof
  strip_tac >> simp[inv_cut_def] >> disj1_tac >>
  Cases_on `st.ds_stack` >> simp[dfs_step_def] >- metis_tac[] >>
  rename1 `st.ds_stack = item :: rest` >> Cases_on `item`
  >- (simp[dfs_step_def] >> rpt IF_CASES_TAC >> simp[] >>
      qexistsl [`mid`, `post`] >> simp[]) >>
  rename1 `st.ds_stack = DfsEmit i :: rest` >> simp[dfs_step_def] >>
  qexistsl [`mid`, `post ++ [i]`] >> simp[listTheory.APPEND_ASSOC]
QED

Theorem inv_cut_children:
  inv_closed bi order eda V P /\ MEM i bi /\ P i /\
  ~MEM i.inst_id V /\ ~is_pseudo i.inst_opcode ==>
  EVERY (inv_work bi V P)
    (MAP DfsProcess (sort_children bi order eda om i
      (inst_all_deps bi order eda i)))
Proof
  simp[listTheory.EVERY_MAP, listTheory.EVERY_MEM, inv_work_def,
       inv_closed_def] >> metis_tac[sort_children_mem]
QED

Theorem inv_cut_step:
  inv_closed bi order eda V P /\ inv_flip_closed P /\
  inv_cut bi V P pre r st ==>
  inv_cut bi V P pre r (dfs_step bi order eda om do_flip st)
Proof
  strip_tac >>
  qpat_x_assum `inv_cut bi V P pre r st`
    (strip_assume_tac o REWRITE_RULE [inv_cut_def])
  >- (irule inv_cut_done_step >> metis_tac[]) >>
  Cases_on `work`
  >- (simp[dfs_step_def, inv_cut_def] >> disj1_tac >>
      qexistsl [`mid`, `[]`] >> simp[]) >>
  rename1 `EVERY (inv_work bi V P) (item :: rest)` >>
  Cases_on `item` >> gns[inv_work_def]
  >- (rename1 `MEM i bi` >>
      Cases_on `MEM i.inst_id st.ds_visited`
      >- (pure_rewrite_tac[inv_cut_def] >> disj2_tac >>
          qexistsl [`mid`, `rest`, `tail`] >> simp[dfs_step_def]) >>
      `~MEM i.inst_id V` by
        (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
      `P i` by metis_tac[] >>
      Cases_on `is_pseudo i.inst_opcode`
      >- (pure_rewrite_tac[inv_cut_def] >> disj2_tac >>
          qexistsl [`mid`, `rest`, `tail`] >>
          fs[dfs_step_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
      fs[] >> drule_all inv_cut_children >> strip_tac >>
      simp[dfs_step_def] >>
      qmatch_goalsub_abbrev_tac `DfsEmit emitted` >>
      `P emitted` by
        (simp[Abbr `emitted`] >> IF_CASES_TAC >>
         gvs[inv_flip_closed_def]) >>
      pure_rewrite_tac[inv_cut_def] >> disj2_tac >>
      qexistsl [`mid`,
        `MAP DfsProcess (sort_children bi order eda om i
           (inst_all_deps bi order eda i)) ++ [DfsEmit emitted] ++ rest`, `tail`] >>
      fs[listTheory.APPEND_ASSOC, inv_work_def,
           listTheory.EVERY_MEM] >> metis_tac[]) >>
  pure_rewrite_tac[inv_cut_def] >> disj2_tac >>
  qexistsl [`mid ++ [i]`, `rest`, `tail`] >>
  simp[dfs_step_def, listTheory.APPEND_ASSOC]
QED

Theorem inv_cut_run:
  inv_closed bi order eda V P /\ inv_flip_closed P /\
  inv_cut bi V P pre r st ==>
  inv_cut bi V P pre r (FUNPOW (dfs_step bi order eda om do_flip) n st)
Proof
  qid_spec_tac `st` >> Induct_on `n` >>
  simp[arithmeticTheory.FUNPOW] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  irule inv_cut_step >> simp[]
QED

Theorem inv_cut_output:
  inv_cut bi V P pre r st /\ st.ds_stack = [] ==>
  ?mid post. st.ds_output = pre ++ mid ++ [r] ++ post /\ EVERY P mid
Proof
  strip_tac >> gvs[inv_cut_def] >> metis_tac[]
QED

Theorem inv_flip_closed_assign:
  inv_flip_closed (\i. i.inst_opcode = ASSIGN)
Proof
  rw[inv_flip_closed_def] >>
  gvs[is_flippable_def, venomEffectsTheory.is_commutative_def,
      passSharedDefsTheory.is_comparator_def]
QED

Theorem inv_cut_assign_run:
  inv_closed bi order eda V (\i. i.inst_opcode = ASSIGN) /\
  inv_cut bi V (\i. i.inst_opcode = ASSIGN) pre r st ==>
  inv_cut bi V (\i. i.inst_opcode = ASSIGN) pre r
    (FUNPOW (dfs_step bi order eda om do_flip) n st)
Proof
  strip_tac >> irule inv_cut_run >>
  simp[inv_flip_closed_assign]
QED
