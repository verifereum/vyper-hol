(*
 * Builtins reading the environment, lengths and method ids.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   env_builtin_expr_ptr_ok
 *)
Theory bodyPtrEnvBuiltins
Ancestors
  bodyPtrEnvBuiltinsLenCase bodyPtrEnvBuiltinsScalar bodyPtrEnvBuiltinsGas
  bodyPtrEnvBuiltinsPrevHash bodyPtrEnvBuiltinsAccountCase
  bodyPtrEnvBuiltinsBlockHashCase bodyPtrEnvBuiltinsBlobHashCase bodyPtrEnvBuiltinsMethodCase
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem env_builtin_expr_ptr_ok:
  !cx ty bt es.
    (bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i) \/ (?i. bt = Acc i) \/
     bt = BlockHash \/ bt = BlobHash \/ bt = MethodId) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas ==>
       body_exprs_ptr_ok cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_ptr_ok cx (HD es)) ==>
    body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> strip_tac >> gvs[]
  >- (irule len_builtin_body_ptr_ok >> rpt gen_tac >> Cases_on `x` >> metis_tac[])
  >- simp[body_calldata_ptr_case]
  >- (Cases_on `i = MsgGas` >- gvs[body_msg_gas_ptr_case] >>
      Cases_on `i = PrevHash` >- gvs[body_prevhash_ptr_case] >>
      irule body_env_ptr_case >> simp[])
  >- (irule body_account_ptr_case >> rpt gen_tac >> Cases_on `x` >> metis_tac[])
  >- (irule body_blockhash_ptr_case >> rpt gen_tac >> Cases_on `x` >> metis_tac[])
  >- (irule body_blobhash_ptr_case >> rpt gen_tac >> Cases_on `x` >> metis_tac[]) >>
  irule body_method_id_ptr_case >> rpt gen_tac >> Cases_on `x` >> metis_tac[]
QED
