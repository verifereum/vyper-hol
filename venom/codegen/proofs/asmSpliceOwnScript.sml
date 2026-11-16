(* Shared own-code splice simulation. Static facts stay in asmSplice. *)
Theory asmSpliceOwn
Ancestors
  asmSymPcOwn asmSplice finalizerContractOwn
  asmOwnSpliceStep asmOwnLabels asmOwnSpliceSimulation
  asmSymOwnCode asmSymPc asmSymSem asmOptimizer asmSem

Definition sym_steps_own_def:
  sym_steps_own p env own 0 ss = SymOK ss ∧
  sym_steps_own p env own (SUC n) ss =
    if ss.sym_base.as_pc ≥ LENGTH p then SymError "pc out of bounds"
    else
      case sym_step_own p env own (EL ss.sym_base.as_pc p) ss of
        SymOK ss' => sym_steps_own p env own n ss'
      | r => r
End

Definition asm_window_refines_own_def:
  asm_window_refines_own pfx pat repl sfx ⇔
    asm_static_wf (pfx ++ pat ++ sfx) ⇒
    ∀env own ss.
      ss.sym_base.as_pc = LENGTH pfx ∧ ss.sym_base.as_stack = [] ⇒
      ∃j j'.
        0 < j ∧
        (∀a. sym_steps_own (pfx ++ pat ++ sfx) env own j ss = SymOK a ⇒
             (a.sym_base.as_pc ≤ LENGTH pfx ∨
              LENGTH pfx + LENGTH pat ≤ a.sym_base.as_pc) ∧
             sym_steps_own (pfx ++ repl ++ sfx) env own j' ss =
               SymOK (sym_with_pc
                        (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
                           a.sym_base.as_pc) a)) ∧
        (sym_terminal (sym_steps_own (pfx ++ pat ++ sfx) env own j ss) ⇒
         sym_result_rel (sym_steps_own (pfx ++ pat ++ sfx) env own j ss)
           (sym_steps_own (pfx ++ repl ++ sfx) env own j' ss))
End

Theorem asm_splice_window_refines_own:
  asm_splice_ok pat repl ∧
  (∀l. MEM (AsmLabel l) pat ⇒ ¬MEM l (asm_label_refs (pfx ++ pat ++ sfx))) ∧
  asm_window_refines_own pfx pat repl sfx ⇒
  asm_refines_own (pfx ++ pat ++ sfx) (pfx ++ repl ++ sfx)
Proof
  strip_tac >> simp[asm_refines_own_def] >> strip_tac >>
  `!l. MEM (AsmLabel l) pat ==>
       ~MEM l (asm_label_refs (pfx ++ repl ++ sfx))`
    by (gvs[asm_splice_ok_def, label_refs_append] >> metis_tac[]) >>
  `asm_static_wf (pfx ++ repl ++ sfx) /\
   FILTER is_data_inst (pfx ++ repl ++ sfx) =
     FILTER is_data_inst (pfx ++ pat ++ sfx)`
    by (irule asm_splice_static_wf >> simp[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  mp_tac (BETA_RULE (Q.INST
    [`srcSteps` |-> `sym_steps_own (pfx ++ pat ++ sfx) env own`,
     `dstSteps` |-> `sym_steps_own (pfx ++ repl ++ sfx) env own`,
     `state_inv` |-> `\ss. ss.sym_base.as_stack = [] /\
       sym_state_labels_in (asm_label_refs (pfx ++ pat ++ sfx)) ss`]
    splice_run_terminal_own_by_steps)) >>
  impl_tac
  >- (asm_rewrite_tac[sym_steps_own_def] >> rpt conj_tac
      >- (rpt gen_tac >> strip_tac >> conj_tac
          >- metis_tac[sym_step_own_base_stack] >>
          metis_tac[sym_step_own_labels_in])
      >- (rpt gen_tac >> strip_tac >> irule splice_inst_step_own_ok >> simp[] >>
          goal_assum (drule_at Any) >> simp[])
      >- (rpt strip_tac >> irule splice_inst_step_own_terminal >> simp[])
      >> gvs[asm_window_refines_own_def]) >>
  disch_then (qspecl_then [`fuel`, `sym_init s`] mp_tac) >>
  simp[sym_init_def, splice_pc_def, sym_with_pc_def,
       sym_state_labels_in_def, listTheory.MEM_MAP]
QED
