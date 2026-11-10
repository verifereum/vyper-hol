(*
 * The pointer twin of bodySimMain's induction: the cases for the expressions with internal calls in their operands.
 * Each is the pointer twin of the S1 case of the same name (bodySim*Cases),
 * over bodyPtrPreds's predicates; bodySimPtrMain's body_sim_ptr_mutual
 * uses them.  Each case is proved in its own leaf theory, the builtins
 * and type builtins one leaf per family.
 *
 * TOP-LEVEL:
 *   body_ifexp_case_ptr
 *   body_structlit_case_ptr
 *   body_subscript_case_ptr
 *   body_attribute_case_ptr
 *   body_builtin_case_ptr
 *   body_pop_case_ptr
 *   body_type_builtin_case_ptr
 *)
Theory bodyPtrExprCases
Ancestors
  bodyPtrIfExp bodyPtrStructLit bodyPtrSubscript bodyPtrAttribute bodyPtrPop
  bodyPtrBop bodyPtrBopIn bodyPtrMakeArray bodyPtrWordBuiltins
  bodyPtrEnvBuiltins bodyPtrHashBuiltins bodyPtrBytestringBuiltins
  bodyPtrPrecompileBuiltins bodyPtrTypeBuiltins bodyPtrAbiEncode
  bodyPtrAbiDecode
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem body_ifexp_case_ptr:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ptr_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ptr_ok cx e3) /\
    body_expr_ptr_ok cx e1 ==>
    body_expr_ptr_ok cx (IfExp v5 e1 e2 e3)
Proof
  MATCH_ACCEPT_TAC ifexp_expr_ptr_ok
QED

Theorem body_structlit_case_ptr:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_ptr_ok cx (MAP SND kes)) ==>
    body_expr_ptr_ok cx (StructLit v7 (src_id_opt,id) kes)
Proof
  MATCH_ACCEPT_TAC structlit_expr_ptr_ok
QED

Theorem body_subscript_case_ptr:
  !cx v8 e1 e2.
    (!s'' res t. eval_expr cx e1 s'' = (INL res,t) ==> body_expr_ptr_ok cx e2) /\
    body_expr_ptr_ok cx e1 ==>
    body_expr_ptr_ok cx (Subscript v8 e1 e2)
Proof
  MATCH_ACCEPT_TAC subscript_expr_ptr_ok
QED

Theorem body_attribute_case_ptr:
  !cx v9 e id. body_expr_ptr_ok cx e ==> body_expr_ptr_ok cx (Attribute v9 e id)
Proof
  MATCH_ACCEPT_TAC attribute_expr_ptr_ok
QED

Theorem body_builtin_case_ptr:
  !cx ty bt es.
    (!s'' x t v code_ty addr s3 tail_vs t'.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas /\
       code_slice_source bt es = SOME v /\ v = (code_ty,addr) /\
       eval_exprs cx (TL es) s3 = (INL tail_vs,t') ==>
       body_exprs_ptr_ok cx [addr]) /\
    (!s'' x t v code_ty addr.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas /\
       code_slice_source bt es = SOME v /\ v = (code_ty,addr) ==>
       body_exprs_ptr_ok cx (TL es)) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas /\
       code_slice_source bt es = NONE ==>
       body_exprs_ptr_ok cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_ptr_ok cx (HD es)) ==>
    body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> strip_tac >>
  `builtin_args_length_ok bt (LENGTH es) /\ bt <> Len /\ bt <> Env MsgGas ==>
   body_exprs_ptr_ok cx es` by
    (strip_tac >> first_x_assum irule >> simp[type_check_def, assert_def]) >>
  Cases_on `bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i) \/ (?i. bt = Acc i) \/
             bt = BlockHash \/ bt = BlobHash \/ bt = MethodId`
  >- metis_tac[env_builtin_expr_ptr_ok] >>
  Cases_on `?bop. bt = Bop bop`
  >- (gvs[] >> Cases_on `bop = In \/ bop = NotIn`
      >- (irule bop_in_expr_ptr_ok >> gvs[]) >>
      irule bop_expr_ptr_ok >> gvs[]) >>
  Cases_on `bt` >> gvs[] >>
  FIRST (map (fn th => irule th >> simp[] >> NO_TAC)
    [make_array_expr_ptr_ok, word_builtin_expr_ptr_ok,
     hash_builtin_expr_ptr_ok, bytestring_builtin_expr_ptr_ok,
     precompile_builtin_expr_ptr_ok])
QED

Theorem body_pop_case_ptr:
  !cx v10 bt. body_base_target_ptr_ok cx bt ==> body_expr_ptr_ok cx (Pop v10 bt)
Proof
  MATCH_ACCEPT_TAC pop_expr_ptr_ok
QED

Theorem body_type_builtin_case_ptr:
  !cx v11 tb typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (TypeBuiltin v11 tb typ es)
Proof
  rpt gen_tac >> strip_tac >>
  `type_builtin_args_length_ok tb (LENGTH es) ==> body_exprs_ptr_ok cx es` by
    (strip_tac >> first_x_assum irule >> simp[type_check_def, assert_def]) >>
  Cases_on `tb`
  >~ [`AbiEncode _ _`] >- (irule abi_encode_expr_ptr_ok >> simp[])
  >~ [`AbiDecode _`] >- (irule abi_decode_expr_ptr_ok >> simp[]) >>
  irule type_builtin_expr_ptr_ok >> simp[]
QED
