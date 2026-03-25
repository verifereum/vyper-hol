(*
 * PHI Elimination Pass — Correctness Statement
 *
 * Single top-level theorem re-exported from proofs/.
 *)

Theory phiElimCorrectness
Ancestors
  phiCorrectnessProof

Theorem phi_elim_pass_correct:
  !ctx fn_name fuel (func:ir_function) s.
    MEM func ctx.ctx_functions /\
    func.fn_name = fn_name /\
    wf_ir_fn func /\
    func.fn_blocks <> [] /\
    s.vs_inst_idx = 0 /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label)
  ==>
    ?func'.
      MEM func' (transform_context ctx).ctx_functions /\
      func'.fn_name = fn_name /\
      lift_result (state_equiv {}) (execution_equiv {})
        (run_function fuel ctx func s)
        (run_function fuel ctx func' s)
Proof
  ACCEPT_TAC phi_elimination_correct
QED

(* ===== Obligations ===== *)

Theorem phi_elim_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (transform_function fn)
Proof
  cheat
QED

Theorem phi_elim_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (transform_function fn)
Proof
  cheat
QED
