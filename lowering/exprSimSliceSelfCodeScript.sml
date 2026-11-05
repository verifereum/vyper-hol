(*
 * Expression simulation: slice(self.code, start, length), admitted.
 *
 * compile_slice_self_code_case is a named residual.  self.code evaluates to
 * the source account's installed code, while the lowering (following
 * Python's _lower_adhoc_slice) reads the running code with CODESIZE and
 * CODECOPY.  The state relations leave the two independent: vs_code is free
 * at the S1 entry boundary, stays fixed across external calls that replace
 * the accounts, and during deployment holds the initcode while the account's
 * code is still empty.  Closing this case needs the running code in the
 * source context, related to vs_code from runtime and deployment entry.
 *)

Theory exprSimSliceSelfCode
Ancestors
  exprSimHypsDefs exprLowering vyperAST

Theorem compile_slice_self_code_case:
  !nocalls ctx func cenv cx ann n args.
    is_self_code (HD args) /\ exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Slice n) args)
Proof
  cheat
QED
