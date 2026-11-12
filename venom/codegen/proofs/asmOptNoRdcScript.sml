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
  !l d c. no_rdc d /\ no_rdc l ==> no_rdc (FST (merge_jumpdests_walk d l c))
Proof
  measureInduct_on `LENGTH l` >> rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC [merge_jumpdests_walk_def] >>
  BasicProvers.every_case_tac >>
  gvs[MEM_REVERSE, MEM_MAP, rename_push_label_op] >>
  first_x_assum irule >> simp[MEM_MAP, rename_push_label_op]
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

Theorem peep_swap_pair_mem[local]:
  peep_swap_pair a b c rest = (l1, ch) /\ MEM x l1 ==> MEM x (a::b::c::rest)
Proof
  rw[peep_swap_pair_def] >> gvs[] >> metis_tac[]
QED

Theorem peep_swap_comm_mem[local]:
  peep_swap_comm l = SOME (l', ch) /\ MEM x l' ==> MEM x l
Proof
  rw[peep_swap_comm_def, AllCaseEqs()] >> gvs[] >> metis_tac[]
QED

Theorem peep_dup_swap_mem[local]:
  peep_dup_swap l = SOME (l', ch) /\ MEM x l' ==> MEM x l
Proof
  rw[peep_dup_swap_def, AllCaseEqs()] >> gvs[] >> metis_tac[]
QED

Theorem peep_chain_no_rdc[local]:
  peep_swap_pair a b c rest = (l1, ch1) ==>
  peep_swap_comm l1 = SOME (l2, ch2) ==>
  peep_dup_swap l2 = SOME (l3, ch3) ==>
  LENGTH (TL l3) <= LENGTH rest + 2 /\
  (no_rdc (a::b::c::rest) ==>
   HD l3 <> AsmOp "RETURNDATACOPY" /\ no_rdc (TL l3))
Proof
  rpt disch_tac >>
  imp_res_tac peep_swap_pair_length >> imp_res_tac peep_swap_comm_length >>
  imp_res_tac peep_dup_swap_length >>
  `!x. MEM x l3 ==> MEM x (a::b::c::rest)` by
    metis_tac[peep_swap_pair_mem, peep_swap_comm_mem, peep_dup_swap_mem] >>
  Cases_on `l3` >> fs[] >>
  `LENGTH t <= LENGTH rest + 2` by decide_tac >> simp[] >>
  rpt strip_tac >> metis_tac[MEM]
QED

Theorem stack_peephole_opts_no_rdc[local]:
  !l out c. stack_peephole_opts l = SOME (out, c) /\ no_rdc l ==> no_rdc out
Proof
  measureInduct_on `LENGTH l` >> rpt gen_tac >> strip_tac >>
  Cases_on `?a b c rest. l = a::b::c::rest`
  >- (gvs[] >>
      `!y out' c'. stack_peephole_opts y = SOME (out', c') ==>
                   LENGTH y <= LENGTH rest + 2 ==> no_rdc y ==> no_rdc out'` by
        (rpt strip_tac >> first_x_assum (qspec_then `y` mp_tac) >>
         impl_tac >- simp[] >> disch_then drule_all >> simp[]) >>
      qpat_x_assum `!y. LENGTH y < _ ==> _` kall_tac >>
      qpat_x_assum `stack_peephole_opts _ = _` mp_tac >>
      ONCE_REWRITE_TAC [stack_peephole_opts_def] >> simp[] >>
      rw[] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
      imp_res_tac peep_chain_no_rdc >> gvs[] >>
      first_x_assum (drule_then mp_tac) >> simp[]) >>
  qpat_x_assum `!y. LENGTH y < _ ==> _` kall_tac >>
  Cases_on `l` >- gvs[Once stack_peephole_opts_def] >>
  Cases_on `t` >- gvs[Once stack_peephole_opts_def] >>
  Cases_on `t'` >- gvs[Once stack_peephole_opts_def] >>
  gvs[]
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
