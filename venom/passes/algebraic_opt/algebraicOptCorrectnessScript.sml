Theory algebraicOptCorrectness
Ancestors
  algebraicOptProofs venomWf

(* Algebraic optimization preserves function execution semantics:
   running a function before and after the transform produces
   equivalent results under state_equiv and execution_equiv. *)
Theorem ao_transform_function_correct:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (ao_transform_function fn) s)
Proof
  ACCEPT_TAC ao_transform_function_correct_proof
QED

(* ===== Obligations ===== *)

(* BLOCKER: ao_opt_eq (line 408 of algebraicOptDefsScript.sml) produces
   2-element lists where BOTH elements share the same inst_id. This violates
   fn_inst_ids_distinct (part of wf_function). Similarly, ao_cmp_flip_apply_inst
   inserts instructions with fresh outputs that may collide.
   Fix needed in defs: new instructions should use id * 1000 + offset. *)
Theorem ao_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (ao_transform_function fn)
Proof
  cheat
QED

Theorem ao_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (ao_transform_function fn)
Proof
  cheat
QED
