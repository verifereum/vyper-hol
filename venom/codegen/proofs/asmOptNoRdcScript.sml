(* The final assembly optimizer inserts no RETURNDATACOPY: its rewrites
 * only drop instructions, reorder them, rename label pushes, or insert
 * ISZERO, SWAP1 and DUP2.
 *
 * TOP-LEVEL: asm_opt_finalizer_no_returndatacopy
 *)
Theory asmOptNoRdc
Ancestors
  asmOptimizer list

Overload no_rdc[local] = ``\l. ~MEM (AsmOp "RETURNDATACOPY") l``

Theorem prune_unreachable_walk_no_rdc[local]:
  !l d. no_rdc l ==> no_rdc (FST (prune_unreachable_walk d l))
Proof
  Induct >> rw[prune_unreachable_walk_def] >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[pairTheory.FST]
QED

Theorem merge_iszero_pairs_no_rdc[local]:
  !l. no_rdc l ==> no_rdc (FST (merge_iszero_pairs l))
Proof
  ho_match_mp_tac merge_iszero_pairs_ind >>
  rw[merge_iszero_pairs_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem merge_iszero_jumpi_no_rdc[local]:
  !l. no_rdc l ==> no_rdc (FST (merge_iszero_jumpi l))
Proof
  ho_match_mp_tac merge_iszero_jumpi_ind >>
  rw[merge_iszero_jumpi_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem rename_push_label_op[local]:
  (rename_push_label x y i = AsmOp n <=> i = AsmOp n) /\
  (AsmOp n = rename_push_label x y i <=> AsmOp n = i)
Proof
  Cases_on `i` >> simp[asmOptimizerTheory.rename_push_label_def] >> rw[]
QED

Theorem rename_push_label_no_rdc[local]:
  no_rdc l ==> no_rdc (MAP (rename_push_label x y) l)
Proof
  simp[MEM_MAP, rename_push_label_op]
QED

Theorem merge_jumpdests_walk_no_rdc[local]:
  !d l c. no_rdc d /\ no_rdc l ==> no_rdc (FST (merge_jumpdests_walk d l c))
Proof
  ho_match_mp_tac merge_jumpdests_walk_ind >> rpt gen_tac >> strip_tac >>
  strip_tac >> ONCE_REWRITE_TAC [merge_jumpdests_walk_def] >> simp[] >>
  BasicProvers.every_case_tac >> gvs[MEM_REVERSE] >>
  first_x_assum irule >> gvs[MEM_MAP, rename_push_label_op] >> metis_tac[]
QED

Theorem prune_inefficient_jumps_no_rdc[local]:
  !l. no_rdc l ==> no_rdc (FST (prune_inefficient_jumps l))
Proof
  ho_match_mp_tac prune_inefficient_jumps_ind >>
  rw[prune_inefficient_jumps_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem optimize_inefficient_jumps_no_rdc[local]:
  !l. no_rdc l ==> no_rdc (FST (optimize_inefficient_jumps l))
Proof
  ho_match_mp_tac optimize_inefficient_jumps_ind >>
  rw[optimize_inefficient_jumps_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem stack_peephole_opts_no_rdc[local]:
  !l out c. stack_peephole_opts l = SOME (out, c) /\ no_rdc l ==> no_rdc out
Proof
  ho_match_mp_tac stack_peephole_opts_ind >> rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC [stack_peephole_opts_def] >>
  Cases_on `l` >> simp[] >> Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  rw[] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[peep_swap_pair_def, peep_swap_comm_def, peep_dup_swap_def,
      AllCaseEqs()] >>
  first_x_assum irule >> gvs[] >> metis_tac[]
QED

Theorem optimize_round_no_rdc[local]:
  optimize_round l = SOME (l', c) /\ no_rdc l ==> no_rdc l'
Proof
  rw[optimize_round_def, prune_unreachable_code_def, merge_iszero_def,
     merge_jumpdests_def, prune_unused_jumpdests_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule stack_peephole_opts_no_rdc >> simp[MEM_FILTER] >>
  metis_tac[prune_unreachable_walk_no_rdc, merge_iszero_pairs_no_rdc,
            merge_iszero_jumpi_no_rdc, merge_jumpdests_walk_no_rdc,
            prune_inefficient_jumps_no_rdc, optimize_inefficient_jumps_no_rdc,
            MEM, pairTheory.FST]
QED

Theorem optimize_assembly_rounds_no_rdc[local]:
  !n l l'. optimize_assembly_rounds n l = SOME l' /\ no_rdc l ==> no_rdc l'
Proof
  Induct >> rw[optimize_assembly_rounds_def, AllCaseEqs()] >>
  imp_res_tac optimize_round_no_rdc >> gvs[] >> metis_tac[]
QED

Theorem asm_opt_finalizer_no_returndatacopy:
  asm_opt_finalizer rpolicy prog = SOME prog' /\
  ~MEM (AsmOp "RETURNDATACOPY") prog ==>
  ~MEM (AsmOp "RETURNDATACOPY") prog'
Proof
  rw[asm_opt_finalizer_def, optimize_assembly_def] >>
  metis_tac[optimize_assembly_rounds_no_rdc]
QED
