(*
 * CFG Normalization Pass — Correctness Proof (cheated)
 *
 * Proves: inserting forwarding split blocks between conditional
 * predecessors and multi-predecessor targets preserves semantics.
 * Key insight: a split block S with forwarding assigns + JMP to B
 * produces the same state as jumping directly from P to B, because
 * the forwarding assigns copy exactly the values that the PHI would
 * select from P.
 *)

Theory cfgNormProof
Ancestors
  cfgNormDefs stateEquiv venomExecSemantics

(* CFG normalization preserves execution semantics at the function level.
 * Split blocks introduce fresh forwarding variables (e.g., P_split_B_fwd_x),
 * which exist only in the transformed execution. result_equiv fresh excludes
 * these from variable comparison. Split blocks also add extra block
 * transitions, so the transformed function may need different fuel. *)
Theorem cfg_norm_fn_correct:
  !func s fuel ctx.
    wf_function func /\
    (* Generated names don't collide with existing variables *)
    (!pred_lbl tgt_lbl var.
       MEM (STRCAT (split_block_name pred_lbl tgt_lbl)
                   (STRCAT "_fwd_" var)) (fn_all_vars func) ==> F) ==>
    let func' = cfg_norm_fn func in
    ?fresh fuel'.
      result_equiv fresh
        (run_function fuel ctx func s)
        (run_function fuel' ctx func' s)
Proof
  cheat
QED
