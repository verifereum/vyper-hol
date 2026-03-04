(*
 * PHI Elimination Pass — Correctness Statements
 *
 * Top-level correctness: PHI elimination preserves execution semantics.
 * For any well-formed function, the original and transformed versions
 * produce equivalent results.
 *
 * Proofs live in proofs/phiCorrectnessProofScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory phiElimCorrectness
Ancestors
  phiCorrectnessProof

(* PHI elimination preserves function execution semantics.
 * Given a well-formed function with non-empty blocks, running the original
 * and transformed function from the same state produces equivalent results. *)
Theorem phi_elim_pass_correct:
  !fuel (func:ir_function) s result.
    wf_ir_fn func /\
    func.fn_blocks <> [] /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label) /\
    run_function fuel func s = result ==>
    ?result'. run_function fuel (transform_function func) s = result' /\
              result_equiv result result'
Proof
  ACCEPT_TAC phi_elimination_correct
QED

(* PHI elimination preserves semantics at the context level.
 * For any function in a context, the transformed context contains a
 * corresponding function that produces equivalent results. *)
Theorem phi_elim_context_pass_correct:
  !ctx fn_name fuel (func:ir_function) s result.
    MEM func ctx.ctx_functions /\
    func.fn_name = fn_name /\
    wf_ir_fn func /\
    func.fn_blocks <> [] /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label) /\
    run_function fuel func s = result ==>
    ?func' result'.
      MEM func' (transform_context ctx).ctx_functions /\
      func'.fn_name = fn_name /\
      run_function fuel func' s = result' /\
      result_equiv result result'
Proof
  ACCEPT_TAC phi_elimination_context_correct
QED
