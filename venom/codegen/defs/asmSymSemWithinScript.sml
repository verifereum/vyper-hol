(*
 * Step-bounded symbolic runs and the step-bounded assembly contract.
 *
 * asm_refines is terminal-only: each terminal run of p is matched by a run
 * of p' with its own fuel, so no step bound for p' follows from it. The
 * sufficient-gas theorems need one step and memory bound for a whole
 * family of runs of the finalized program; asm_refines_within carries it,
 * beside asm_refines, which stays as it is.
 *
 * TOP-LEVEL:
 *   sym_run_within      — a run's step and per-step bound
 *   asm_plain_inst      — instructions that touch no memory and call nothing
 *   sym_within_ok       — the bounds a finalizer keeps
 *   asm_refines_within  — p' takes at most c times p's steps, in the bounds
 *)

Theory asmSymSemWithin
Ancestors
  asmSymSem asmWf

(* The run from ss ends, or reaches an instruction Q stops at, within k
   steps, with no error or label misuse, and P holds of each instruction it
   runs before that, with the stack it runs it on. The sufficient-gas
   proof needs this, not just a terminal result, to carry one step and
   memory bound for a whole family of runs from p to its finalized
   version (P bounds an instruction's memory, Q is RETURNDATACOPY). *)
Definition sym_run_within_def:
  (sym_run_within P Q p env 0 ss ⇔ F) ∧
  (sym_run_within P Q p env (SUC k) ss ⇔
     ss.sym_base.as_pc < LENGTH p ∧
     (Q (EL ss.sym_base.as_pc p) ∨
      P (EL ss.sym_base.as_pc p) ss.sym_stack ∧
      case sym_step p env (EL ss.sym_base.as_pc p) ss of
        SymOK ss' => sym_run_within P Q p env k ss'
      | SymError _ => F
      | SymBad _ => F
      | _ => T))
End

(* The same bound with a supplied symbolic instruction step. *)
Definition sym_run_within_for_def:
  (sym_run_within_for step P Q p 0 ss <=> F) /\
  (sym_run_within_for step P Q p (SUC k) ss <=>
     ss.sym_base.as_pc < LENGTH p /\
     (Q (EL ss.sym_base.as_pc p) \/
      P (EL ss.sym_base.as_pc p) ss.sym_stack /\
      case step (EL ss.sym_base.as_pc p) ss of
        SymOK ss' => sym_run_within_for step P Q p k ss'
      | SymError _ => F
      | SymBad _ => F
      | _ => T))
End

(* Instructions that touch no memory, call, create or self-destruct: the
   ones a finalizer may run where its input runs others (stack shuffles,
   jumps, pushes, labels, ISZERO and arithmetic). *)
Definition asm_plain_inst_def:
  asm_plain_inst inst ⇔
    ¬is_data_inst inst ∧
    ∀name. inst = AsmOp name ⇒
      ¬MEM name ["MLOAD"; "MSTORE"; "MSTORE8"; "SHA3"; "RETURN"; "REVERT";
                 "LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4"; "CALLDATACOPY";
                 "CODECOPY"; "RETURNDATACOPY"; "EXTCODECOPY"; "MCOPY";
                 "CALL"; "CALLCODE"; "STATICCALL"; "DELEGATECALL";
                 "CREATE"; "CREATE2"; "SELFDESTRUCT"]
End

(* The bounds a finalizer keeps: P holds of plain instructions, and Q stops
   at none. P sees only which stack items are words, and their values, not
   which labels the others are: the optimizer renames labels. *)
Definition sym_within_ok_def:
  sym_within_ok P Q ⇔
    (∀inst stk. asm_plain_inst inst ⇒ P inst stk ∧ ¬Q inst) ∧
    ∀inst stk stk'.
      MAP sval_val stk = MAP sval_val stk' ⇒ (P inst stk ⇔ P inst stk')
End

(* p' takes at most c times p's steps, for one c over all runs, with the
   same bounds on what each step does: one step and memory bound then
   covers a whole family of runs of p', as the sufficient-gas theorems
   need. It holds beside asm_refines p p', which gives the rest. *)
Definition asm_refines_within_def:
  asm_refines_within p p' ⇔
    asm_static_wf p ⇒
    ∃c. ∀P Q env s k.
      sym_within_ok P Q ∧ sym_run_within P Q p env k (sym_init s) ⇒
      sym_run_within P Q p' env (c * k) (sym_init s)
End
