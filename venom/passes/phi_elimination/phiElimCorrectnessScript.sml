(*
 * PHI Elimination Pass — Correctness Statements
 *
 * Top-level correctness: PHI elimination preserves execution semantics.
 *
 * Proofs live in proofs/phiCorrectnessProofScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory phiElimCorrectness
Ancestors
  phiCorrectnessProof

(* PHI elimination preserves semantics at the context level.
 * For any well-formed function in a context with non-empty blocks,
 * the transformed context contains a same-named function that produces
 * equivalent results (exact state equivalence, no fresh variables).
 * Requires either vs_prev_bb set or starting at the entry block. *)
Theorem phi_elim_pass_correct:
  !ctx fn_name fuel (func:ir_function) s result.
    MEM func ctx.ctx_functions /\
    func.fn_name = fn_name /\
    wf_ir_fn func /\
    no_invoke_in_function func /\
    func.fn_blocks <> [] /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label) /\
    run_function fuel ctx func s = result ==>
    ?func' result'.
      MEM func' (transform_context ctx).ctx_functions /\
      func'.fn_name = fn_name /\
      run_function fuel ctx func' s = result' /\
      result_equiv {} result result'
Proof
  ACCEPT_TAC phi_elimination_context_correct
QED
