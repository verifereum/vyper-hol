Theory dftGasInvForwardConeProbe
Ancestors
  dftDefs contextCodegenRel dftGasInvPendingCut list rich_list

Definition inv_cone_blocks_def:
  inv_cone_blocks =
  [<|bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ASSIGN [Lit 32w] ["p"];
     mk_inst 1 ASSIGN [Var "p"] ["q"];
     mk_inst 2 RETURNDATACOPY [Var "p"; Lit 0w; Lit 8w] [];
     mk_inst 3 REVERT [Var "q"; Lit 8w] []]|>;
   <|bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ASSIGN [Lit 32w] ["p"];
     mk_inst 1 ASSIGN [Lit 8w] ["sz"];
     mk_inst 2 ASSIGN [Var "p"] ["p1"];
     mk_inst 3 ASSIGN [Var "sz"] ["s1"];
     mk_inst 4 RETURNDATACOPY [Var "p1"; Lit 0w; Var "s1"] [];
     mk_inst 5 ASSIGN [Var "p"] ["p2"];
     mk_inst 6 ASSIGN [Var "p2"] ["p3"];
     mk_inst 7 ASSIGN [Var "sz"] ["s2"];
     mk_inst 8 REVERT [Var "p3"; Var "s2"] []]|>;
   <|bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ADD [Lit 2w; Lit 3w] ["z"];
     mk_inst 1 ASSIGN [Var "z"] ["unused"];
     mk_inst 2 ASSIGN [Lit 32w] ["p"];
     mk_inst 3 ASSIGN [Var "p"] ["q"];
     mk_inst 4 RETURNDATACOPY [Var "p"; Lit 0w; Lit 8w] [];
     mk_inst 5 REVERT [Var "q"; Lit 8w] []]|>;
   <|bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ADD [Lit 16w; Lit 16w] ["p"];
     mk_inst 1 ADD [Lit 4w; Lit 4w] ["sz"];
     mk_inst 2 ASSIGN [Var "p"] ["trash"];
     mk_inst 3 ASSIGN [Var "p"] ["q"];
     mk_inst 4 ASSIGN [Var "sz"] ["n"];
     mk_inst 5 RETURNDATACOPY [Var "p"; Lit 0w; Var "sz"] [];
     mk_inst 6 REVERT [Var "q"; Var "n"] []]|>]
End

Definition inv_cone_state_def:
  inv_cone_state bi order n =
    FUNPOW (dfs_step bi order (dft_eda bi) (build_offspring_map bi order) T) n
      <|ds_stack := MAP DfsProcess (entry_instructions bi order (dft_eda bi));
        ds_output := []; ds_visited := []|>
End

Definition inv_cone_snapshot_def:
  inv_cone_snapshot st =
    (MAP (\w. case w of DfsProcess i => (F,i.inst_id) | DfsEmit i => (T,i.inst_id)) st.ds_stack,
     MAP (\i. i.inst_id) st.ds_output, st.ds_visited)
End

Theorem inv_cone_source_pairs:
  revert_forward_pair (EL 0 inv_cone_blocks) 2 3 /\
  revert_forward_pair (EL 1 inv_cone_blocks) 4 8 /\
  revert_forward_pair (EL 2 inv_cone_blocks) 4 5 /\
  revert_forward_pair (EL 3 inv_cone_blocks) 5 6
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >>
  `k = 5 \/ k = 6 \/ k = 7` by decide_tac >> gvs[]
QED

Theorem inv_cone_find_cuts:
  MAP (\bb. FIND (\n. EXISTS (\i. i.inst_opcode = RETURNDATACOPY)
         (inv_cone_state bb.bb_instructions [] n).ds_output) (COUNT_LIST 40))
      inv_cone_blocks = [SOME 5; SOME 11; SOME 9; SOME 10]
Proof
  EVAL_TAC
QED

Theorem inv_cone_ordered_cuts:
  MAP (\bb. FIND (\n. EXISTS (\i. i.inst_opcode = RETURNDATACOPY)
         (inv_cone_state bb.bb_instructions ["p"] n).ds_output) (COUNT_LIST 40))
      inv_cone_blocks = [SOME 5; SOME 11; SOME 9; SOME 10]
Proof
  EVAL_TAC
QED

Definition inv_cone_cases_def:
  (inv_cone_cases : (num # num # num) list) = [(0,5,2); (1,11,4); (2,9,4); (3,10,5)]
End

Theorem inv_cone_cut_snapshots:
  MAP (\(b,n,c). inv_cone_snapshot
      (inv_cone_state (EL b inv_cone_blocks).bb_instructions [] n)) inv_cone_cases =
  [([(F,1); (T,3)],[0;2],[0;2;3]);
   ([(F,7); (F,6); (T,8)],[1;3;0;2;4],[0;2;1;3;4;8]);
   ([(F,3); (T,5)],[0;1;2;4],[2;4;5;0;1]);
   ([(F,4); (F,3); (T,6)],[0;2;1;5],[1;5;6;0;2])]
Proof
  EVAL_TAC
QED

Theorem inv_cone_schedules:
  MAP (\bb. MAP (\i. i.inst_id) (dft_block [] bb).bb_instructions) inv_cone_blocks =
  [[0;2;1;3]; [1;3;0;2;4;7;5;6;8]; [0;1;2;4;3;5]; [0;2;1;5;4;3;6]]
Proof
  EVAL_TAC
QED

Theorem inv_cone_front_not_visited:
  !order. MEM order [[]; ["p"]] ==>
  MAP (\(b,n,c). EVERY (\i. MEM i.inst_id
      (inv_cone_state (EL b inv_cone_blocks).bb_instructions order n).ds_visited)
      (TAKE (SUC c) (EL b inv_cone_blocks).bb_instructions)) inv_cone_cases = [F;T;F;F]
Proof
  simp[MEM] >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem inv_cone_emitted_closure:
  !order. MEM order [[]; ["p"]] ==>
  EVERY (\(b,n,c). inv_closed (EL b inv_cone_blocks).bb_instructions order
      (dft_eda (EL b inv_cone_blocks).bb_instructions)
      (MAP (\i. i.inst_id) (inv_cone_state (EL b inv_cone_blocks).bb_instructions order n).ds_output)
      (\i. i.inst_opcode = ASSIGN)) inv_cone_cases
Proof
  simp[MEM, DISJ_IMP_THM, FORALL_AND_THM] >> conj_tac
  >- suspend "empty"
  >> suspend "ordered"
QED

Resume inv_cone_emitted_closure[empty]:
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``inv_closed``]) >>
  simp[inv_closed_def, MEM] >> rpt strip_tac >> gvs[] >>
  rule_assum_tac (CONV_RULE EVAL) >> gvs[] >> EVAL_TAC
QED
Resume inv_cone_emitted_closure[ordered]:
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``inv_closed``]) >>
  simp[inv_closed_def, MEM] >> rpt strip_tac >> gvs[] >>
  rule_assum_tac (CONV_RULE EVAL) >> gvs[] >> EVAL_TAC
QED
Finalise inv_cone_emitted_closure

Theorem inv_cone_target_pairs:
  !order. MEM order [[]; ["p"]] ==>
  revert_forward_pair (dft_block order (EL 0 inv_cone_blocks)) 1 3 /\
  revert_forward_pair (dft_block order (EL 1 inv_cone_blocks)) 4 8 /\
  revert_forward_pair (dft_block order (EL 2 inv_cone_blocks)) 3 5 /\
  revert_forward_pair (dft_block order (EL 3 inv_cone_blocks)) 3 6
Proof
  simp[MEM] >> rpt strip_tac >> gvs[] >> EVAL_TAC >> simp[] >> rpt strip_tac >>
  `k = 2 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7` by decide_tac >> gvs[]
QED

Theorem inv_cone_work_at_cut:
  !order. MEM order [[]; ["p"]] ==>
  EVERY (\(b,n,c).
    (inv_cone_state (EL b inv_cone_blocks).bb_instructions order n).ds_stack =
      TAKE (PRE (LENGTH (inv_cone_state (EL b inv_cone_blocks).bb_instructions order n).ds_stack))
        (inv_cone_state (EL b inv_cone_blocks).bb_instructions order n).ds_stack ++
      [DfsEmit (LAST (EL b inv_cone_blocks).bb_instructions)] /\
    EVERY (inv_work (EL b inv_cone_blocks).bb_instructions
      (MAP (\i. i.inst_id) (inv_cone_state (EL b inv_cone_blocks).bb_instructions order n).ds_output)
      (\i. i.inst_opcode = ASSIGN))
      (TAKE (PRE (LENGTH (inv_cone_state (EL b inv_cone_blocks).bb_instructions order n).ds_stack))
        (inv_cone_state (EL b inv_cone_blocks).bb_instructions order n).ds_stack) /\
    EVERY (\i. MEM i.inst_id (inv_cone_state (EL b inv_cone_blocks).bb_instructions order n).ds_visited)
      (inv_cone_state (EL b inv_cone_blocks).bb_instructions order n).ds_output) inv_cone_cases
Proof
  simp[MEM, DISJ_IMP_THM, FORALL_AND_THM] >> conj_tac
  >- suspend "empty"
  >> suspend "ordered"
QED
Resume inv_cone_work_at_cut[empty]:
  EVAL_TAC
QED
Resume inv_cone_work_at_cut[ordered]:
  simp_tac bool_ss
    [inv_cone_cases_def, EVERY_DEF, pairTheory.pair_case_thm,
     pairTheory.UNCURRY, pairTheory.FST, pairTheory.SND] >>
  rpt conj_tac >|
    [EVAL_TAC, EVAL_TAC, EVAL_TAC,
     EVAL_TAC, EVAL_TAC, EVAL_TAC,
     EVAL_TAC, EVAL_TAC, EVAL_TAC,
     EVAL_TAC, EVAL_TAC, EVAL_TAC]
QED
Finalise inv_cone_work_at_cut

Theorem inv_cone_ordered_snapshots:
  MAP (\(b,n,c). inv_cone_snapshot
      (inv_cone_state (EL b inv_cone_blocks).bb_instructions ["p"] n)) inv_cone_cases =
  [([(F,0); (F,1); (T,3)],[0;2],[0;2;3]);
   ([(F,0); (F,7); (F,6); (T,8)],[1;3;0;2;4],[0;2;1;3;4;8]);
   ([(F,2); (F,3); (T,5)],[0;1;2;4],[2;4;5;0;1]);
   ([(F,0); (F,4); (F,3); (T,6)],[0;2;1;5],[1;5;6;0;2])]
Proof
  EVAL_TAC
QED

Theorem inv_cone_ssa_shapes:
  EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    EVERY inst_wf bb.bb_instructions /\
    (LAST bb.bb_instructions).inst_opcode = REVERT) inv_cone_blocks
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[] >>
  `j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8` by decide_tac >>
  gvs[] >> EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC >>
  FIRST (map (fn idx => qexists_tac idx >> EVAL_TAC >> NO_TAC)
    [`0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`])
QED
