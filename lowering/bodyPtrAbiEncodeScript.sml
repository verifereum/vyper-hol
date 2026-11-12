(*
 * abi_encode.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   abi_encode_expr_ptr_ok
 *)
Theory bodyPtrAbiEncode
Ancestors
  bodyPtrAbiEncodeSingle bodyPtrAbiEncodeTuple exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem abi_encode_expr_ptr_ok:
  !cx v11 b m typ es.
    (type_builtin_args_length_ok (AbiEncode b m) (LENGTH es) ==>
     body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (TypeBuiltin v11 (AbiEncode b m) typ es)
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `LENGTH es = 1 /\ ~b`
  >- (gvs[LENGTH_EQ_NUM_compute] >>
      `body_exprs_ptr_ok cx [h]` by
        (first_x_assum irule >> simp[type_builtin_args_length_ok_def]) >>
      `body_expr_ptr_ok cx h` by fs[body_exprs_ptr_ok_def] >>
      irule abi_encode_single_sim_ptr >> metis_tac[]) >>
  irule abi_encode_tuple_sim_ptr >> metis_tac[]
QED
