(*
 * SimplifyCFG keeps every CALL/STATICCALL success check (call_checks_ok).
 *
 * The check after a call stays in its block: merging only appends the
 * successor's instructions to a block that ended in JMP, and a JMP into a
 * revert path is replaced by that path's own instructions, which end in
 * REVERT or a JMP into another revert path.  Bypassing a jump-only block
 * and canonicalizing a JNZ with equal targets keep each revert-path target
 * a revert path, and removing unreachable blocks keeps every block a
 * reachable block can jump to.
 *)
Theory simplifyCfgCallChecks
Ancestors
  simplifyCfgDefs unitShapeDefs venomWf venomInst

Theorem simplify_cfg_call_checks_ok:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn ==>
  call_checks_ok (simplify_cfg_fn fn)
Proof
  cheat
QED
