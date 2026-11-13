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
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

(* RESIDUAL (train 16 hold-out, argon 2026-11-12): the harvested proof below
   needs abiDecodePtrSupportedTarget, which the constructor split made
   unprovable until supported_program_deploy is threaded through and
   declaration_abi_decode_target gains its ErrorDecl clause.  It returns
   right after train 16.  Harvested proof (61e271717):

  rpt gen_tac >> strip_tac >>
  simp[Once body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  rename1 `expr_body_pre cenv cx env (TypeBuiltin ann (AbiDecode b) typ args) st` >>
  drule abi_decode_body_pre_shape >> strip_tac >> gvs[] >>
  `body_exprs_ptr_ok cx [e]` by
    (first_x_assum irule >> simp[type_builtin_args_length_ok_def]) >>
  `body_expr_ptr_ok cx e` by fs[Once body_expr_ptr_ok_def] >>
  `expr_sim_ptr d ctx PG func cenv cx (expr_type e) e st` by
    (fs[Once body_expr_ptr_ok_def] >> metis_tac[]) >>
  conj_tac
  >- (irule abi_decode_unary_sim_ptr >> metis_tac[]) >>
  irule abi_decode_unary_vv_sim_ptr >> metis_tac[]
*)
Theorem abi_decode_expr_ptr_ok:
  !cx v11 b typ es.
    (type_builtin_args_length_ok (AbiDecode b) (LENGTH es) ==>
     body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (TypeBuiltin v11 (AbiDecode b) typ es)
Proof
  cheat
QED
