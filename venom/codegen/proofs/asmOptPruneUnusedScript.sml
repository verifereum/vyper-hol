(*
 * prune_unused_jumpdests refines its input.
 *
 * The rule drops every LABEL nothing refers to. Each drop is a splice with
 * pat = [LABEL l] and repl = []: executing the label only moves the pc on,
 * which is where the spliced program already is. Dropping a label leaves
 * the label references as they were, so the labels the rule computed as
 * unused stay unused along the chain of drops.
 *
 * TOP-LEVEL:
 *   prune_unused_jumpdests_refines — asm_refines p (FST (rule p))
 *)

Theory asmOptPruneUnused
Ancestors
  asmSplice asmSymPc finalizerContract asmSymSem asmOptimizer asmWf asmSem

Theorem unused_label_window_refines:
  asm_window_refines pfx [AsmLabel l] [] sfx
Proof
  rw[asm_window_refines_def] >>
  `LENGTH pfx < LENGTH (pfx ++ [AsmLabel l] ++ sfx) ∧
   EL (LENGTH pfx) (pfx ++ [AsmLabel l] ++ sfx) = AsmLabel l`
    by simp[listTheory.EL_APPEND_EQN] >>
  qexistsl_tac [`1`, `0`] >>
  simp[sym_steps_pos, sym_steps_def, sym_step_def, sym_lift_def,
       asm_step_def, asm_next_def, sym_terminal_def] >>
  simp[splice_pc_def, sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem filter_unused_refines_under[local]:
  ∀sfx pfx.
    (∀l. MEM l (asm_label_refs (pfx ++ sfx)) ⇒ MEM l used) ⇒
    asm_refines (pfx ++ sfx)
      (pfx ++ FILTER ($~ o asm_unused_label used) sfx)
Proof
  Induct >- simp[asm_refines_refl] >>
  rpt strip_tac >> reverse (Cases_on `asm_unused_label used h`) >> simp[]
  >- (first_x_assum (qspec_then `pfx ++ [h]` mp_tac) >>
      REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
      disch_then irule >> simp[]) >>
  Cases_on `h` >> gvs[asm_unused_label_def] >>
  irule asm_refines_trans >>
  qexists_tac `pfx ++ sfx` >>
  `∀l. MEM l (asm_label_refs (pfx ++ sfx)) ⇒ MEM l used`
    by (qpat_assum `∀l. MEM l (asm_label_refs (pfx ++ AsmLabel s :: sfx)) ⇒ _`
          mp_tac >>
        simp[label_refs_append, asm_label_refs_def]) >>
  `¬MEM s (asm_label_refs (pfx ++ AsmLabel s :: sfx))`
    by (strip_tac >> res_tac) >>
  simp[] >>
  mp_tac (Q.INST [`pat` |-> `[AsmLabel s]`, `repl` |-> `[]`]
            asm_splice_window_refines) >>
  impl_tac
  >- (simp[asm_splice_ok_def, unused_label_window_refines,
           is_data_inst_def] >>
      qpat_x_assum `¬MEM s _` mp_tac >> simp[asm_label_refs_def]) >>
  REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND,
              listTheory.APPEND_NIL] >>
  disch_then ACCEPT_TAC
QED

Theorem prune_unused_jumpdests_refines:
  ∀p. asm_refines p (FST (prune_unused_jumpdests p))
Proof
  gen_tac >>
  qspecl_then [`p`, `[]`] mp_tac
    (Q.INST [`used` |-> `asm_label_refs p`] filter_unused_refines_under) >>
  simp[prune_unused_jumpdests_def]
QED
