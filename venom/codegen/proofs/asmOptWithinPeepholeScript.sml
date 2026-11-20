(* The stack peepholes preserve the bounds of runs reading installed bytes. *)
Theory asmOptWithinPeephole
Ancestors
  asmSpliceWithinOwn asmSpliceOwn asmSplice asmOptOwnPeephole asmOptPeephole
  asmFinalizerPrefixPeephole asmSymSemWithin asmOptimizer asmWf symbolResolve
  list rich_list

Theorem swap_prefix_straight[local]:
  isPREFIX "SWAP" name ==> asm_straight_plain (AsmOp name)
Proof
  strip_tac >> BETA_TAC >> simp[swap_prefix_plain] >>
  conj_tac >> strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem commutative_straight[local]:
  asm_commutative_op (AsmOp name) ==> asm_straight_plain (AsmOp name)
Proof
  strip_tac >> BETA_TAC >> simp[commutative_plain] >>
  conj_tac >> strip_tac >> gvs[asm_commutative_op_def] >> EVAL_TAC
QED

(* Use the exact step counts from the existing own-code window proofs. *)
fun peephole_site_within pat repl results =
  BETA_TAC >>
  mp_tac (Q.INST [`pat` |-> pat, `repl` |-> repl, `post` |-> `rest`]
    asm_splice_window_within_own) >>
  (impl_tac >-
    (rpt conj_tac
     >- simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
             asm_inst_size_def, dup2_opcode, DISJ_IMP_THM, FORALL_AND_THM]
     >- simp[] >>
     disch_tac >>
     mp_tac (Q.INST [`pat` |-> pat, `repl` |-> repl, `post` |-> `rest`]
       own_window_straight_within) >>
     (impl_tac >-
       (simp[asm_plain_inst_def, is_data_inst_def,
             swap_prefix_straight, commutative_straight] >>
        rpt gen_tac >> strip_tac >>
        mp_tac (Q.INST [`pfx` |-> `pre`, `sfx` |-> `rest`] results) >> simp[])) >>
     disch_then ACCEPT_TAC)) >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> disch_then ACCEPT_TAC;

Theorem stack_peephole_opts_within_own:
  stack_peephole_opts p = SOME (q,c) ==> asm_within_own p q
Proof
  mp_tac (Q.SPEC `asm_within_own` peephole_walk_relation) >>
  (impl_tac >-
    (rpt conj_tac
     >- metis_tac[asm_within_own_refl]
     >- metis_tac[asm_within_own_trans]
     >- suspend "dup_swap2_swap1"
     >- suspend "dup_swap_pop"
     >- suspend "swap_pop_pop"
     >- suspend "swap_pair"
     >- suspend "swap_comm"
     >- suspend "dup_swap")) >>
  disch_then (qspecl_then [`p`, `[]`, `q`, `c`] mp_tac) >> simp[]
QED

Resume stack_peephole_opts_within_own[dup_swap2_swap1]:
  rpt gen_tac >>
  peephole_site_within `[AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"]`
    `[AsmOp "SWAP1"; AsmOp "DUP2"]` dup1_swap2_swap1_window_results
QED

Resume stack_peephole_opts_within_own[dup_swap_pop]:
  rpt gen_tac >>
  peephole_site_within `[AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"]`
    `[]` dup1_swap1_pop_window_results
QED

Resume stack_peephole_opts_within_own[swap_pop_pop]:
  rpt gen_tac >>
  peephole_site_within `[AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"]`
    `[AsmOp "POP"; AsmOp "POP"]` swap1_pop_pop_window_results
QED

Resume stack_peephole_opts_within_own[swap_pair]:
  rpt gen_tac >> strip_tac >>
  peephole_site_within `[AsmOp name; AsmOp name]` `[]` swap_pair_window_results
QED

Resume stack_peephole_opts_within_own[swap_comm]:
  rpt gen_tac >> strip_tac >>
  `∃name. y = AsmOp name` by (Cases_on `y` >> gvs[asm_commutative_op_def]) >>
  gvs[] >>
  peephole_site_within `[AsmOp "SWAP1"; AsmOp name]` `[AsmOp name]`
    swap1_commutative_window_results
QED

Resume stack_peephole_opts_within_own[dup_swap]:
  rpt gen_tac >>
  peephole_site_within `[AsmOp "DUP1"; AsmOp "SWAP1"]` `[AsmOp "DUP1"]`
    dup1_swap1_window_results
QED

Finalise stack_peephole_opts_within_own
