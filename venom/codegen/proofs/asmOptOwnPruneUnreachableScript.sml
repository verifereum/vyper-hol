(* Unreachable instructions after a terminal op can be dropped while both
   programs read the same fixed own-code bytes. *)
Theory asmOptOwnPruneUnreachable
Ancestors symbolResolve[qualified,ignore_grammar]
  asmOptPruneUnreachable asmSpliceOwn asmSymPcOwn finalizerContractOwn
  asmSplice asmSymPc asmSymOwnCode asmSymSem asmOptimizer asmWf asmSem list

Theorem sym_steps_own_one:
  sym_steps_own p env own 1 ss =
  if ss.sym_base.as_pc ≥ LENGTH p then SymError "pc out of bounds"
  else sym_step_own p env own (EL ss.sym_base.as_pc p) ss
Proof
  REWRITE_TAC [arithmeticTheory.ONE, sym_steps_own_def] >> rw[] >>
  CASE_TAC >> simp[]
QED

Theorem terminal_window_refines_own:
  asm_terminal_op t ∧ ¬asm_reachable_marker x ⇒
  asm_window_refines_own pfx [t; x] [t] rest
Proof
  rw[asm_window_refines_own_def] >>
  `∃name. t = AsmOp name` by gvs[asm_terminal_op_def] >>
  `∀l. x ≠ AsmLabel l ∧ x ≠ AsmDataHeader l`
    by (rpt strip_tac >> gvs[asm_reachable_marker_def]) >>
  qabbrev_tac `p = pfx ++ [t; x] ++ rest` >>
  qabbrev_tac `q = pfx ++ [t] ++ rest` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = t ∧
   LENGTH pfx < LENGTH q ∧ EL (LENGTH pfx) q = t`
    by simp[Abbr `p`, Abbr `q`, listTheory.EL_APPEND_EQN] >>
  `name ≠ "CODESIZE" ∧ name ≠ "CODECOPY"`
    by gvs[asm_terminal_op_def] >>
  qexistsl_tac [`1`, `1`] >>
  simp[sym_steps_own_one, sym_step_own_eq] >>
  Cases_on `name = "JUMP"`
  >- (gvs[sym_step_def, sym_step_op_def, sym_jump_def] >>
      Cases_on `ss.sym_stack` >> simp[sym_terminal_def] >>
      rename1 `ss.sym_stack = dest :: stk` >>
      Cases_on `dest` >> simp[sym_jump_dest_def, sym_terminal_def] >>
      rename1 `ss.sym_stack = Lab l d :: stk` >>
      Cases_on `d = 0` >> simp[sym_terminal_def] >>
      `INDEX_OF (AsmLabel l) q =
         OPTION_MAP (splice_pc (LENGTH pfx) 2 1) (INDEX_OF (AsmLabel l) p) ∧
       ∀i. INDEX_OF (AsmLabel l) p = SOME i ⇒
           i < LENGTH pfx ∨ LENGTH pfx + 2 ≤ i`
        by (mp_tac (Q.INST [`pat` |-> `[AsmOp "JUMP"; x]`,
                            `repl` |-> `[AsmOp "JUMP"]`,
                            `sfx` |-> `rest`] splice_index_of_label) >>
            simp[Abbr `p`, Abbr `q`]) >>
      Cases_on `INDEX_OF (AsmLabel l) p` >> gvs[sym_terminal_def] >>
      simp[splice_pc_def, sym_with_pc_def, sym_state_component_equality,
           asm_state_component_equality]) >>
  `sym_step q env (AsmOp name) ss = sym_step p env (AsmOp name) ss`
    by (irule sym_step_prog_cong >> gvs[asm_terminal_op_def] >>
        simp[Abbr `p`, Abbr `q`] >> metis_tac[]) >>
  `∀a. sym_step p env (AsmOp name) ss ≠ SymOK a`
    by (gvs[asm_terminal_op_def] >>
        simp[sym_step_def, sym_step_op_def, dup_table_def, swap_table_def,
             sym_step_concrete_def, sym_lift_def,
             asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
             asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
             asm_return_op_def, asm_revert_op_def] >>
        rpt CASE_TAC >> simp[]) >>
  simp[] >> Cases_on `sym_step p env (AsmOp name) ss` >>
  gvs[sym_terminal_def, sym_result_rel_def]
QED

Theorem prune_one_refines_own:
  asm_terminal_op t ∧ ¬asm_reachable_marker x ⇒
  asm_refines_own (pfx ++ t :: x :: rest) (pfx ++ t :: rest)
Proof
  strip_tac >> Cases_on `is_data_inst x`
  >- (simp[asm_refines_own_def] >> metis_tac[terminal_data_not_wf]) >>
  `∀l. x ≠ AsmLabel l` by (rpt strip_tac >> gvs[asm_reachable_marker_def]) >>
  `∃name. t = AsmOp name` by gvs[asm_terminal_op_def] >>
  drule_all terminal_window_refines_own >>
  disch_then (qspecl_then [`rest`, `pfx`] assume_tac) >>
  mp_tac (Q.INST [`pat` |-> `[t; x]`, `repl` |-> `[t]`, `sfx` |-> `rest`]
            asm_splice_window_refines_own) >>
  impl_tac
  >- gvs[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
         symbolResolveTheory.asm_inst_size_def] >>
  REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  disch_then ACCEPT_TAC
QED

Theorem prune_unreachable_walk_refines_own_under:
  ∀sfx d pfx.
    (d ⇒ ∃pre t. pfx = pre ++ [t] ∧ asm_terminal_op t) ⇒
    asm_refines_own (pfx ++ sfx) (pfx ++ FST (prune_unreachable_walk d sfx))
Proof
  Induct >- simp[prune_unreachable_walk_def, asm_refines_own_refl] >>
  rpt strip_tac >> simp[prune_unreachable_walk_fst] >>
  IF_CASES_TAC
  >- (gvs[] >> irule asm_refines_own_trans >>
      qexists_tac `pre ++ t :: sfx` >> conj_tac
      >- (REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
          irule prune_one_refines_own >> simp[]) >>
      first_x_assum (qspecl_then [`T`, `pre ++ [t]`] mp_tac) >>
      impl_tac >- (strip_tac >> qexistsl_tac [`pre`, `t`] >> simp[]) >>
      REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  first_x_assum (qspecl_then [`asm_terminal_op h`, `pfx ++ [h]`] mp_tac) >>
  impl_tac >- (strip_tac >> qexistsl_tac [`pfx`, `h`] >> simp[]) >>
  REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]
QED

Theorem prune_unreachable_code_refines_own:
  ∀p. asm_refines_own p (FST (prune_unreachable_code p))
Proof
  gen_tac >> simp[prune_unreachable_code_def] >>
  qspecl_then [`p`, `F`, `[]`] mp_tac prune_unreachable_walk_refines_own_under >>
  simp[]
QED
