(*
 * Hashing: keccak256 and sha256.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   hash_builtin_expr_ptr_ok
 *)
Theory bodyPtrHashBuiltins
Ancestors
  bodyPtrHashBuiltinsKeccakUnary bodyPtrHashBuiltinsShaTyped bodyPtrHashBuiltinsCases
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem hash_builtin_expr_ptr_ok:
  !cx ty bt es.
    (bt = Keccak256 \/ bt = Sha256) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[body_expr_ptr_ok_def] >> reverse conj_tac
  >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `LENGTH es = 1` by metis_tac[hash_body_pre_arity] >>
  `?e. es = [e]` by (Cases_on `es` >> gvs[LENGTH_EQ_NUM]) >>
  gvs[] >> (
  `expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es'` by
    (irule (cj 1 hash_builtin_operand_ptr) >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at Any) >> simp[builtin_args_length_ok_def]) >>
  reverse conj_tac
  >- (FIRST [irule hash_compile_typed_keccak256_unary_vv_sim_ptr,
             irule hash_sha256_typed_vv_sim_ptr] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule expr_sim_ptr_of_vv >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  FIRST [irule hash_compile_typed_keccak256_unary_vv_sim_ptr,
         irule hash_sha256_typed_vv_sim_ptr] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[])
QED
