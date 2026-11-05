Theory dftGasInvForwardStackProbe
Ancestors
  dftDefs contextCodegenRel dftGasInvPendingCut

Definition inv_competing_block_def:
  inv_competing_block = <|bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ADD [Lit 2w; Lit 3w] ["z"];
     mk_inst 1 RETURNDATACOPY [Var "z"; Lit 0w; Lit 1w] [];
     mk_inst 2 ASSIGN [Var "z"] ["trash"];
     mk_inst 3 REVERT [Var "z"; Lit 1w] []]|>
End

Theorem inv_competing_source_pair:
  revert_forward_pair inv_competing_block 1 3
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >>
  `k = 2` by decide_tac >> gvs[]
QED

Theorem inv_competing_schedule:
  MAP (\i. i.inst_id) (dft_block [] inv_competing_block).bb_instructions = [0;2;1;3]
Proof
  EVAL_TAC
QED

Theorem inv_competing_pair_kept:
  revert_forward_pair (dft_block [] inv_competing_block) 2 3
Proof
  EVAL_TAC >> simp[]
QED

Definition inv_competing_state_def:
  inv_competing_state n =
    FUNPOW (dfs_step inv_competing_block.bb_instructions []
      (dft_eda inv_competing_block.bb_instructions)
      (build_offspring_map inv_competing_block.bb_instructions []) T) n
      <|ds_stack := MAP DfsProcess
          (entry_instructions inv_competing_block.bb_instructions []
            (dft_eda inv_competing_block.bb_instructions));
        ds_output := []; ds_visited := []|>
End

Definition inv_competing_snapshot_def:
  inv_competing_snapshot n =
    (MAP (\w. case w of DfsProcess i => (F,i.inst_id)
                       | DfsEmit i => (T,i.inst_id))
         (inv_competing_state n).ds_stack,
     MAP (\i. i.inst_id) (inv_competing_state n).ds_output,
     (inv_competing_state n).ds_visited)
End

Theorem inv_competing_trace:
  MAP inv_competing_snapshot (COUNT_LIST 12) =
    [([(F,2);(F,3)],[],[]);
     ([(F,0);(T,2);(F,3)],[],[2]);
     ([(T,0);(T,2);(F,3)],[],[0;2]);
     ([(T,2);(F,3)],[0],[0;2]);
     ([(F,3)],[0;2],[0;2]);
     ([(F,1);(F,0);(T,3)],[0;2],[3;0;2]);
     ([(F,0);(T,1);(F,0);(T,3)],[0;2],[1;3;0;2]);
     ([(T,1);(F,0);(T,3)],[0;2],[1;3;0;2]);
     ([(F,0);(T,3)],[0;2;1],[1;3;0;2]);
     ([(T,3)],[0;2;1],[1;3;0;2]);
     ([],[0;2;1;3],[1;3;0;2]);
     ([],[0;2;1;3],[1;3;0;2])]
Proof
  EVAL_TAC
QED
