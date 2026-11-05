Theory bodyPtrPopGlobalContainment
Ancestors
  bodyPtrPopGlobalPremises exprLoweringProps fragExec

(* The fixed unit has no internal calls in either of its two functions.
   This is an IR audit, not a certificate that the outer Pop has a frame. *)
Theorem pop_global_context_no_invoke:
  EVERY (\f. EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts f))
    pop_global_runtime_context.ctx_functions
Proof
  EVAL_TAC
QED

(* Remaining symbolic containment obligation (not proved here):
   Fix cenv = pop_global_package_env and e =
     Pop (BaseT (UintT 256)) pop_global_target.
   compile_expr's Pop clause (exprLowering:3012) first compiles its target.
   The outer SubscriptTarget clause (:2049) evaluates the index with
   lower_value in both the MapPT and non-MapPT branches. That index is
   Call ... (IntCall (NONE,"replace")) [] NONE. compile_call (:2626)
   emits INVOKE in every return convention (:2655, :2660, :2664).
   emit appends unconditionally (compileEnv:641), and new_block (:647)
   retains the current prefix in cs_blocks. Thus an INVOKE should remain
   in a new block or the final current prefix, independent of initial
   cs_current_insts, cs_blocks, label numbering and fresh-id counters.
   A checked proof that this INVOKE belongs to emitted_blocks sa sb or
   sb.cs_current_insts is still missing. Neither function in the fixed
   context can contain it, by the certificate above. This audit does not
   assert universal non-containment until that preservation step is proved.
   fn_has_code (fragExec:112) uses all emitted blocks and an isPREFIX
   constraint for the final current instructions; arbitrary old blocks
   are not themselves required to occur in the function.
*)
