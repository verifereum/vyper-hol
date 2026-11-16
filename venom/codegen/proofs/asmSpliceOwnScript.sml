(* Shared own-code splice simulation. Static facts stay in asmSplice. *)
Theory asmSpliceOwn
Ancestors
  asmSymPcOwn asmSplice finalizerContractOwn
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
  cheat
QED
