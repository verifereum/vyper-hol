(*
 * prune_unreachable_code refines its input.
 *
 * The rule drops each non-marker instruction x that follows a terminal
 * op t (JUMP, RETURN, REVERT, STOP, INVALID), until the next label or
 * data header. Each drop is a splice with pat = [t; x] and repl = [t]:
 * the window starts at t, which never falls through to x, and x is not a
 * label, so no jump lands on it. A data item in x's place breaks
 * asm_static_wf, since everything after a data header is data and t is
 * not.
 *
 * TOP-LEVEL:
 *   prune_unreachable_code_refines — asm_refines p (FST (rule p))
 *)

Theory asmOptPruneUnreachable
Ancestors
  asmSplice asmSymPc finalizerContract asmSymSem asmOptimizer asmWf
  asmSem list

(* ===== One drop ===== *)

(* RETURN, REVERT, STOP and INVALID never continue. *)
Theorem asm_step_op_halting[local]:
  MEM name ["RETURN"; "REVERT"; "STOP"; "INVALID"] ⇒
  asm_step_op FEMPTY name s ≠ AsmOK t
Proof
  rw[] >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
       asm_return_op_def, asm_revert_op_def] >>
  rpt CASE_TAC >> simp[]
QED

Theorem sym_step_concrete_halting[local]:
  MEM name ["RETURN"; "REVERT"; "STOP"; "INVALID"] ⇒
  sym_step_concrete name ss ≠ SymOK a
Proof
  strip_tac >> simp[sym_step_concrete_def] >>
  rpt (IF_CASES_TAC ORELSE CASE_TAC) >> simp[] >>
  strip_tac >> drule sym_lift_ok >> strip_tac >>
  metis_tac[asm_step_op_halting]
QED

Theorem sym_step_halting_not_ok[local]:
  asm_terminal_op t ∧ t ≠ AsmOp "JUMP" ⇒ sym_step p env t ss ≠ SymOK a
Proof
  simp[asm_terminal_op_def] >> strip_tac >>
  gvs[sym_step_def, sym_step_op_def, dup_table_def, swap_table_def] >>
  irule sym_step_concrete_halting >> simp[]
QED

Theorem sym_steps_one[local]:
  sym_steps p env 1 ss =
  if ss.sym_base.as_pc ≥ LENGTH p then SymError "pc out of bounds"
  else sym_step p env (EL ss.sym_base.as_pc p) ss
Proof
  REWRITE_TAC [arithmeticTheory.ONE, sym_steps_def] >> rw[] >>
  CASE_TAC >> simp[]
QED

(* From t, one step of either program leaves the window or ends the same
   way. *)
Theorem terminal_window_refines:
  asm_terminal_op t ∧ ¬asm_reachable_marker x ⇒
  asm_window_refines pfx [t; x] [t] rest
Proof
  rw[asm_window_refines_def] >>
  `∃name. t = AsmOp name` by gvs[asm_terminal_op_def] >>
  `∀l. x ≠ AsmLabel l ∧ x ≠ AsmDataHeader l`
    by (rpt strip_tac >> gvs[asm_reachable_marker_def]) >>
  qabbrev_tac `p = pfx ++ [t; x] ++ rest` >>
  qabbrev_tac `q = pfx ++ [t] ++ rest` >>
  `LENGTH pfx < LENGTH p ∧ EL (LENGTH pfx) p = t ∧
   LENGTH pfx < LENGTH q ∧ EL (LENGTH pfx) q = t`
    by simp[Abbr `p`, Abbr `q`, listTheory.EL_APPEND_EQN] >>
  qexistsl_tac [`1`, `1`] >> simp[sym_steps_one] >>
  Cases_on `name = "JUMP"`
  >- (gvs[sym_step_def, sym_step_op_def, sym_jump_def] >>
      Cases_on `ss.sym_stack` >> simp[sym_terminal_def] >>
      rename1 `ss.sym_stack = dest :: stk` >>
      Cases_on `dest` >> simp[sym_jump_dest_def, sym_terminal_def] >>
      rename1 `ss.sym_stack = Lab l d :: stk` >> Cases_on `d = 0` >> simp[sym_terminal_def] >>
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
    by (gen_tac >> irule sym_step_halting_not_ok >> gvs[]) >>
  simp[] >>
  Cases_on `sym_step p env (AsmOp name) ss` >>
  gvs[sym_terminal_def, sym_result_rel_def]
QED

Theorem data_at_end_after_header[local]:
  asm_data_at_end p ∧ i ≤ k ∧ k < LENGTH p ∧ EL i p = AsmDataHeader l ⇒
  is_data_inst (EL k p)
Proof
  rw[asm_data_at_end_def] >> first_x_assum (qspec_then `i` mp_tac) >>
  simp[] >> disch_then irule >> simp[]
QED

(* A data item right after a code instruction breaks asm_static_wf. *)
Theorem terminal_data_not_wf[local]:
  asm_terminal_op t ∧ ¬asm_reachable_marker x ∧ is_data_inst x ⇒
  ¬asm_static_wf (pfx ++ t :: x :: rest)
Proof
  rpt strip_tac >>
  qabbrev_tac `p = pfx ++ t :: x :: rest` >>
  `LENGTH pfx + 1 < LENGTH p ∧ EL (LENGTH pfx) p = t ∧
   EL (LENGTH pfx + 1) p = x`
    by simp[Abbr `p`, listTheory.EL_APPEND_EQN, GSYM arithmeticTheory.ADD1] >>
  `¬is_data_inst t` by gvs[asm_terminal_op_def, is_data_inst_def] >>
  `∀l. x ≠ AsmDataHeader l`
    by (rpt strip_tac >> gvs[asm_reachable_marker_def]) >>
  qpat_x_assum `asm_static_wf _`
    (strip_assume_tac o REWRITE_RULE [asm_static_wf_def]) >>
  `∃j l. j ≤ LENGTH pfx + 1 ∧ EL j p = AsmDataHeader l`
    by (qpat_x_assum `∀i. i < LENGTH p ∧ _ ⇒ _` irule >> simp[]) >>
  `j ≠ LENGTH pfx + 1` by (strip_tac >> metis_tac[]) >>
  `is_data_inst (EL (LENGTH pfx) p)`
    by (irule data_at_end_after_header >> simp[] >>
        qexistsl_tac [`j`, `l`] >> simp[]) >>
  gvs[]
QED

Theorem prune_one_refines:
  asm_terminal_op t ∧ ¬asm_reachable_marker x ⇒
  asm_refines (pfx ++ t :: x :: rest) (pfx ++ t :: rest)
Proof
  strip_tac >>
  Cases_on `is_data_inst x`
  >- (simp[asm_refines_def] >> metis_tac[terminal_data_not_wf]) >>
  `∀l. x ≠ AsmLabel l` by (rpt strip_tac >> gvs[asm_reachable_marker_def]) >>
  `∃name. t = AsmOp name` by gvs[asm_terminal_op_def] >>
  drule_all terminal_window_refines >>
  disch_then (qspecl_then [`rest`, `pfx`] assume_tac) >>
  mp_tac (Q.INST [`pat` |-> `[t; x]`, `repl` |-> `[t]`, `sfx` |-> `rest`]
            asm_splice_window_refines) >>
  impl_tac
  >- gvs[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
         symbolResolveTheory.asm_inst_size_def] >>
  REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  disch_then ACCEPT_TAC
QED

(* ===== The walk ===== *)

Theorem prune_unreachable_walk_fst[local]:
  FST (prune_unreachable_walk d (inst :: rest)) =
  if d ∧ ¬asm_reachable_marker inst then FST (prune_unreachable_walk T rest)
  else inst :: FST (prune_unreachable_walk (asm_terminal_op inst) rest)
Proof
  simp[Once prune_unreachable_walk_def] >> rw[] >>
  rpt (pairarg_tac >> gvs[])
QED

(* While dropping, the prefix ends in a terminal op. *)
Theorem prune_unreachable_walk_refines_under:
  ∀sfx d pfx.
    (d ⇒ ∃pre t. pfx = pre ++ [t] ∧ asm_terminal_op t) ⇒
    asm_refines (pfx ++ sfx) (pfx ++ FST (prune_unreachable_walk d sfx))
Proof
  Induct >- simp[prune_unreachable_walk_def, asm_refines_refl] >>
  rpt strip_tac >> simp[prune_unreachable_walk_fst] >>
  IF_CASES_TAC
  >- (gvs[] >> irule asm_refines_trans >>
      qexists_tac `pre ++ t :: sfx` >> conj_tac
      >- (REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
          irule prune_one_refines >> simp[]) >>
      first_x_assum (qspecl_then [`T`, `pre ++ [t]`] mp_tac) >>
      impl_tac >- (strip_tac >> qexistsl_tac [`pre`, `t`] >> simp[]) >>
      REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  first_x_assum (qspecl_then [`asm_terminal_op h`, `pfx ++ [h]`] mp_tac) >>
  impl_tac >- (strip_tac >> qexistsl_tac [`pfx`, `h`] >> simp[]) >>
  REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]
QED

Theorem prune_unreachable_code_refines:
  ∀p. asm_refines p (FST (prune_unreachable_code p))
Proof
  gen_tac >> simp[prune_unreachable_code_def] >>
  qspecl_then [`p`, `F`, `[]`] mp_tac prune_unreachable_walk_refines_under >>
  simp[]
QED
