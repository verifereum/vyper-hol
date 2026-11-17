(*
 * The step-bounded local obligation of a single-site splice.
 *
 * asm_window_refines_within is asm_window_refines with a step bound: from
 * the window's start, p' takes at most twice p's steps there, within the
 * same bounds (sym_run_within, sym_within_ok). The bound shares the
 * window's step counts j and j' with the rest, so it is stated with them,
 * not on its own. asm_window_refines stays as it is.
 *
 * TOP-LEVEL:
 *   sym_steps_ok               — n steps that P allows and Q doesn't stop at
 *   asm_window_refines_within  — the step-bounded local obligation
 *)

Theory asmSpliceWithin
Ancestors
  asmSplice asmSymSemWithin asmSymPc asmSymSem

(* Each of the first n steps from ss runs an instruction that P allows,
   with its stack, and that Q doesn't stop at. *)
Definition sym_steps_ok_def:
  (sym_steps_ok P Q p env 0 ss ⇔ T) ∧
  (sym_steps_ok P Q p env (SUC n) ss ⇔
     ss.sym_base.as_pc < LENGTH p ∧
     ¬Q (EL ss.sym_base.as_pc p) ∧
     P (EL ss.sym_base.as_pc p) ss.sym_stack ∧
     case sym_step p env (EL ss.sym_base.as_pc p) ss of
       SymOK ss' => sym_steps_ok P Q p env n ss'
     | _ => T)
End

(* From the window's start, j > 0 steps of p and j' steps of p' either
   leave the window at corresponding PCs in the same state, or end in
   related terminal results. A run of p that errs or misuses a label
   there constrains nothing. And p' takes at most twice p's steps there,
   within the same bounds: a bounded run of p from the window's start is
   matched by one of p' with twice the steps, or it passes the window's j
   steps, which Q doesn't stop at, and p''s j' steps keep P and Q. *)
Definition asm_window_refines_within_def:
  asm_window_refines_within pfx pat repl sfx ⇔
    asm_static_wf (pfx ++ pat ++ sfx) ⇒
    ∀env ss.
      ss.sym_base.as_pc = LENGTH pfx ∧ ss.sym_base.as_stack = [] ⇒
      ∃j j'.
        0 < j ∧ j' ≤ 2 * j ∧
        (∀a. sym_steps (pfx ++ pat ++ sfx) env j ss = SymOK a ⇒
             (a.sym_base.as_pc ≤ LENGTH pfx ∨
              LENGTH pfx + LENGTH pat ≤ a.sym_base.as_pc) ∧
             sym_steps (pfx ++ repl ++ sfx) env j' ss =
               SymOK (sym_with_pc
                        (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
                           a.sym_base.as_pc) a)) ∧
        (sym_terminal (sym_steps (pfx ++ pat ++ sfx) env j ss) ⇒
         sym_result_rel (sym_steps (pfx ++ pat ++ sfx) env j ss)
           (sym_steps (pfx ++ repl ++ sfx) env j' ss)) ∧
        ∀P Q k.
          sym_within_ok P Q ∧
          sym_run_within P Q (pfx ++ pat ++ sfx) env k ss ⇒
          sym_run_within P Q (pfx ++ repl ++ sfx) env (2 * k) ss ∨
          ∃a. sym_steps (pfx ++ pat ++ sfx) env j ss = SymOK a ∧ j ≤ k ∧
              sym_run_within P Q (pfx ++ pat ++ sfx) env (k - j) a ∧
              sym_steps_ok P Q (pfx ++ repl ++ sfx) env j' ss
End
