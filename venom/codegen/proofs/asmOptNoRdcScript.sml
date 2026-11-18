(* The final assembly optimizer inserts no RETURNDATACOPY: its rewrites
 * only drop instructions, reorder them, rename label pushes, or insert
 * ISZERO, SWAP1 and DUP2.
 *
 * TOP-LEVEL: asm_opt_finalizer_no_returndatacopy
 *)
Theory asmOptNoRdc
Ancestors
  asmOptMergeJumpdests asmOptNonemptyWitness
  asmOptNonemptyCompose
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

Theorem rename_push_label_no_rdc[local]:
  no_rdc (MAP (rename_push_label x y) l) <=> no_rdc l
Proof
  simp[MEM_MAP] >> metis_tac[rename_push_label_facts]
QED

Theorem merge_jumpdests_walk_no_rdc[local]:
  !l d c. no_rdc d /\ no_rdc l ==> no_rdc (FST (merge_jumpdests_walk d l c))
Proof
  measureInduct_on `LENGTH l` >> rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC [merge_jumpdests_walk_def] >>
  BasicProvers.every_case_tac >>
  gvs[MEM_REVERSE, rename_push_label_no_rdc, rename_push_label_facts] >>
  first_x_assum irule >>
  simp[rename_push_label_no_rdc, rename_push_label_facts]
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
  rpt strip_tac >>
  qabbrev_tac `is_rdc = \i. i = AsmOp "RETURNDATACOPY"` >>
  `FILTER is_rdc out = FILTER is_rdc l` by
    (irule stack_peephole_opts_filter >>
     simp[Abbr `is_rdc`, asm_swap_op_def] >>
     first_assum (irule_at Any) >> simp[]) >>
  pop_assum (mp_tac o AP_TERM ``MEM (AsmOp "RETURNDATACOPY")``) >>
  simp[MEM_FILTER, Abbr `is_rdc`]
QED

Theorem optimize_round_no_rdc[local]:
  !p q ch. no_rdc p /\ optimize_round p = SOME (q, ch) ==> no_rdc q
Proof
  ho_match_mp_tac optimize_round_preserves_predicate >>
  simp[prune_unreachable_code_def, merge_iszero_def, merge_jumpdests_def,
       prune_unused_jumpdests_def, MEM_FILTER] >>
  rpt conj_tac
  >- simp[prune_unreachable_walk_no_rdc]
  >- (rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
      metis_tac[merge_iszero_pairs_no_rdc, merge_iszero_jumpi_no_rdc, pairTheory.FST])
  >- simp[merge_jumpdests_walk_no_rdc]
  >- simp[prune_inefficient_jumps_no_rdc]
  >- simp[optimize_inefficient_jumps_no_rdc]
  >> metis_tac[stack_peephole_opts_no_rdc]
QED

Theorem asm_opt_finalizer_no_returndatacopy:
  asm_opt_finalizer rpolicy prog = SOME prog' /\
  ~MEM (AsmOp "RETURNDATACOPY") prog ==>
  ~MEM (AsmOp "RETURNDATACOPY") prog'
Proof
  strip_tac >>
  mp_tac (BETA_RULE (Q.INST [`P` |-> `no_rdc`] asm_opt_finalizer_preserves_predicate)) >>
  impl_tac >- MATCH_ACCEPT_TAC (BETA_RULE optimize_round_no_rdc) >>
  disch_then (qspecl_then [`rpolicy`, `prog`, `prog'`] mp_tac) >>
  simp[]
QED
