(*
 * abi_decode.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   abi_decode_expr_ptr_ok
 *)
Theory bodyPtrAbiDecode
Ancestors
  abiDecodePtrExprComplete abiDecodePtrExpr
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem abi_decode_expr_ptr_ok:
  !cx v11 b typ es.
    (type_builtin_args_length_ok (AbiDecode b) (LENGTH es) ==>
     body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (TypeBuiltin v11 (AbiDecode b) typ es)
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  rename1 `expr_body_pre cenv cx env (TypeBuiltin ann (AbiDecode b) typ args) st` >>
  drule abi_decode_body_pre_shape >> strip_tac >> gvs[] >>
  `body_exprs_ptr_ok cx [e]` by
    (first_x_assum irule >> simp[type_builtin_args_length_ok_def]) >>
  `body_expr_ptr_ok cx e` by fs[Once body_expr_ptr_ok_def] >>
  `expr_sim_ptr d ctx PG func cenv cx (expr_type e) e st` by
    (fs[Once body_expr_ptr_ok_def] >> metis_tac[]) >>
  Cases_on `supported_program_deploy tops`
  >- (conj_tac
      >- (irule abi_decode_unary_sim_ptr >> metis_tac[]) >>
      irule abi_decode_unary_vv_sim_ptr >> metis_tac[]) >>
  (* Admitted residual (argon, 2026-11-12): without supported_program_deploy a
     constructor body may decode to a target outside the flat scalar tuples the
     pointer sims cover, and expr_body_pre does not say which body is running.
     The whole theorem was an admitted residual on fc54ea89e. *)
  cheat
QED
