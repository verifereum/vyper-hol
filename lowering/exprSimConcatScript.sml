(*
 * Expression simulation: concat(...).
 *
 * compile_concat_case, the case lemma exprSimBuiltins re-exports for compile_expr_sim
 * (exprSimMain): from exprs_case of the operands, expr_vv_case of the
 * builtin.
 *)

Theory exprSimConcat
Ancestors
  exprSimHypsDefs vyperAST exprSimConcatResult

(* Why it holds (statement audit, not a proof):
   - Typing gives SUM (MAP bytelike_type_bound ts) <= n, and each operand's
     value has length <= its static bound (exactly m for bytes<m>), so
     evaluate_concat's "concat bound" RuntimeError cannot fire and the
     lowering, which has no runtime check, agrees.
   - concat_payload_capacity matches bytelike_type_bound on Bytes/String/bytesM.
   - The result buffer (concat_alloc_size) and the 64-byte offset temporary
     are allocated before any operand code runs, so later operands' code
     (fresh allocas only) cannot overwrite them; concat_data_bound covers a
     bytesM operand's full-word store past its payload.
   - The located result is tagged with ann; vv_post's footprint for a
     bytestring is 32 + LENGTH v, within the buffer. *)
Theorem compile_concat_case:
  !nocalls ctx func cenv cx ann n args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Concat n) args)
Proof
  rw[expr_vv_case_def] >> irule concat_result_vv_sim >> metis_tac[]
QED
