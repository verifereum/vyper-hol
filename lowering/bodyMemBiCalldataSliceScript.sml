(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: msg.data slices (S1: exprSimCalldataSlice's
   compile_calldata_slice_call_case). *)
Theory bodyMemBiCalldataSlice
Ancestors
  bodyMemoryPreds bodyMemBiCalldataSliceRead bodyMemBiCalldataSliceCompose
  bodyMemBiCalldataSliceFacts exprSimHypsDefs vyperTyping
  exprSimSource vyperInterpreter vyperContext exprSimCalldataSlice

Theorem body_builtin_calldata_slice_mem:
  !cx ty n es.
    (builtin_args_length_ok (CalldataSlice n) (LENGTH es) ==>
     body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty (CalldataSlice n) es)
Proof
  rpt gen_tac >> strip_tac >>
  simp[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  `well_typed_expr env (Builtin ty (CalldataSlice n) es)` by
    fs[expr_body_pre_def] >>
  drule calldata_slice_typing >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es'` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >>
     fs[expr_body_pre_def]) >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e es'` by
    (fs[builtin_args_length_ok_def, body_exprs_mem_ok_def,
        body_expr_mem_ok_def] >> metis_tac[]) >>
  conj_tac
  >- (irule compile_calldata_slice_sim_mem >> metis_tac[]) >>
  irule compile_calldata_slice_vv_sim_mem >> metis_tac[]
QED
