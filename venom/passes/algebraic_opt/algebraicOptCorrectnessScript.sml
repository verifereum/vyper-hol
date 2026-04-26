Theory algebraicOptCorrectness
Ancestors
  algebraicOptProofs venomWf

(* Algebraic optimization preserves function execution semantics:
   running a function before and after the transform produces
   equivalent results under state_equiv and execution_equiv,
   modulo fresh variables introduced by multi-instruction expansions. *)
Theorem ao_transform_function_correct:
  !fuel ctx fn s.
    let fv = ao_fn_fresh_vars fn in
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv)
    ==>
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (ao_transform_function fn) s)
Proof
  ACCEPT_TAC ao_transform_function_correct_proof
QED

(* ===== Obligations (Blocked) =====

   BLOCKER: ao_opt_eq (algebraicOptDefsScript.sml) and related helpers
   produce multi-instruction lists where ALL new instructions share the
   same inst_id as the original. This violates fn_inst_ids_distinct
   (part of wf_function).

   Fix needed in defs: helper instructions should use distinct ids,
   e.g., id * 1000 + offset. Until the defs are fixed, the following
   theorems cannot be proved and are omitted:

   ao_preserves_ssa_form  : ∀fn. ssa_form fn ⇒ ssa_form (ao_transform_function fn)
   ao_preserves_wf_function : ∀fn. wf_function fn ⇒ wf_function (ao_transform_function fn)

   These are structural obligations required for composing this pass
   with others in the pipeline.

   ===== *)
