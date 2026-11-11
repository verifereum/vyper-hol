(*
 * prune_inefficient_jumps refines its input.
 *
 * The rule drops PUSHLABEL x JUMP right before LABEL x. Each drop is a
 * splice with pat = [PUSHLABEL x; JUMP] and repl = [], keeping LABEL x at
 * the head of the suffix: the jump goes exactly where falling through
 * does.
 *
 * TOP-LEVEL:
 *   prune_inefficient_jumps_refines — asm_refines p (FST (rule p))
 *)

Theory asmOptPruneJumps
Ancestors
  asmSplice asmSymPc finalizerContract asmSymSem asmOptimizer asmWf

Theorem jump_to_next_window_refines:
  asm_window_refines pfx [AsmPushLabel x; AsmOp "JUMP"] []
    (AsmLabel x :: rest)
Proof
  rw[asm_window_refines_def, asm_static_wf_def] >>
  `¬MEM (AsmLabel x) pfx`
    by (qpat_x_assum `asm_labels_unique _`
          (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                asm_labels_unique_append_not_mem)) >>
        disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  qabbrev_tac `p = pfx ++ [AsmPushLabel x; AsmOp "JUMP"] ++
                   AsmLabel x :: rest` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = AsmPushLabel x ∧
   LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx + 1) p = AsmOp "JUMP" ∧
   INDEX_OF (AsmLabel x) p = SOME (LENGTH pfx + 2)`
    by simp[Abbr `p`, listTheory.EL_APPEND_EQN, INDEX_OF_APPEND,
            INDEX_OF_CONS] >>
  qabbrev_tac `s1 = ss with <| sym_base := asm_next ss.sym_base;
                               sym_stack := Lab x 0 :: ss.sym_stack |>` >>
  `sym_step p env (AsmPushLabel x) ss = SymOK s1`
    by simp[Abbr `s1`, sym_step_push_label] >>
  `s1.sym_base.as_pc = LENGTH pfx + 1 ∧
   s1.sym_stack = Lab x 0 :: ss.sym_stack`
    by simp[Abbr `s1`, asmSemTheory.asm_next_def] >>
  `sym_step p env (AsmOp "JUMP") s1 =
   SymOK (s1 with <| sym_base := s1.sym_base with as_pc := LENGTH pfx + 2;
                     sym_stack := ss.sym_stack |>)`
    by simp[sym_step_def, sym_step_op_def, sym_jump_def,
            sym_jump_dest_def] >>
  qexistsl_tac [`2`, `0`] >>
  simp[sym_steps_pos, sym_steps_def, sym_terminal_def] >>
  simp[Abbr `s1`, splice_pc_def, sym_with_pc_def,
       sym_state_component_equality,
       asmSemTheory.asm_state_component_equality, asmSemTheory.asm_next_def]
QED

Theorem prune_inefficient_jumps_fst[local]:
  FST (prune_inefficient_jumps (a :: b :: c :: rest)) =
  if asm_jump_to_next a b c then FST (prune_inefficient_jumps (c :: rest))
  else a :: FST (prune_inefficient_jumps (b :: c :: rest))
Proof
  simp[Once prune_inefficient_jumps_def] >> rw[] >>
  pairarg_tac >> simp[]
QED

Theorem prune_inefficient_jumps_refines_under:
  ∀sfx pfx.
    asm_refines (pfx ++ sfx) (pfx ++ FST (prune_inefficient_jumps sfx))
Proof
  ho_match_mp_tac prune_inefficient_jumps_ind >>
  reverse (rpt conj_tac)
  >- simp[prune_inefficient_jumps_def, asm_refines_refl]
  >- simp[prune_inefficient_jumps_def, asm_refines_refl]
  >- simp[prune_inefficient_jumps_def, asm_refines_refl] >>
  rpt gen_tac >> strip_tac >> simp[prune_inefficient_jumps_fst] >>
  reverse IF_CASES_TAC >- (gvs[] >> irule asm_refines_cons >> simp[]) >>
  Cases_on `a` >> gvs[asm_jump_to_next_def] >>
  Cases_on `c` >> gvs[] >> gen_tac >>
  qmatch_goalsub_rename_tac `AsmPushLabel lbl` >>
  irule asm_refines_trans >>
  qexists_tac `pfx ++ AsmLabel lbl :: rest` >> simp[] >>
  mp_tac (Q.INST [`pat` |-> `[AsmPushLabel lbl; AsmOp "JUMP"]`,
                  `repl` |-> `[]`,
                  `sfx` |-> `AsmLabel lbl :: rest`] asm_splice_window_refines) >>
  impl_tac
  >- simp[asm_splice_ok_def, jump_to_next_window_refines, is_data_inst_def,
          asm_label_refs_def, symbolResolveTheory.asm_inst_size_def] >>
  REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  disch_then ACCEPT_TAC
QED

Theorem prune_inefficient_jumps_refines:
  ∀p. asm_refines p (FST (prune_inefficient_jumps p))
Proof
  gen_tac >>
  qspecl_then [`p`, `[]`] mp_tac prune_inefficient_jumps_refines_under >>
  simp[]
QED
