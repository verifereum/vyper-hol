(* Ordinary builtin dispatch over the lower guarded prefix introductions. *)
Theory s1PrefixGuardedOrdinary
Ancestors
  s1PrefixPreds bodyFullPreds vyperInterpreter vyperAST vyperContext vyperState list
  s1PrefixGuardedMsgGas s1PrefixGuardedEnv
  s1PrefixGuardedBopIn s1PrefixGuardedBopOther s1PrefixGuardedMakeArray
  s1PrefixGuardedWord s1PrefixGuardedEC s1PrefixGuardedBytestring s1PrefixHash

Theorem body_builtin_ordinary_case_prefix:
  !cx ty bt es.
  bt <> NamedConst /\
  (!is_and n. bt <> BoolChain is_and n) /\
  (!s'' x t v code_ty addr tail_s tail_vs t'.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
       v = (code_ty,addr) /\
       eval_exprs cx (TL es) tail_s = (INL tail_vs,t') ==>
       body_exprs_full_ok cx [addr]) /\
  (!s'' x t v code_ty addr.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = SOME v ==>
       body_exprs_full_ok cx (TL es)) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = NONE ==>
       body_exprs_full_ok cx es) /\
  (!s'' x t v code_ty addr tail_s tail_vs t'.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
       v = (code_ty,addr) /\
       eval_exprs cx (TL es) tail_s = (INL tail_vs,t') ==>
       body_exprs_prefix_ok cx [addr]) /\
  (!s'' x t v code_ty addr.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = SOME v ==>
       body_exprs_prefix_ok cx (TL es)) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = NONE ==>
       body_exprs_prefix_ok cx es) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_full_ok cx (HD es)) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_prefix_ok cx (HD es)) ==>
  body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bt = Env MsgGas`
  >- (gvs[] >> irule s1PrefixGuardedMsgGasTheory.body_msg_gas_prefix_case) >>
  reverse (Cases_on `code_slice_source bt es`)
  >- (rename1 `code_slice_source bt es = SOME src` >>
      Cases_on `src` >> gvs[code_slice_source_SOME] >>
      irule s1PrefixGuardedBytestringTheory.bytestring_builtin_expr_prefix_ok >>
      gvs[code_slice_source_def, type_check_def, assert_def,
          builtin_args_length_ok_def] >> metis_tac[]) >>
  `builtin_args_length_ok bt (LENGTH es) /\ bt <> Len ==>
   body_exprs_full_ok cx es` by
    metis_tac[type_check_def, assert_def] >>
  `builtin_args_length_ok bt (LENGTH es) /\ bt <> Len ==>
   body_exprs_prefix_ok cx es` by
    metis_tac[type_check_def, assert_def] >>
  Cases_on `bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i) \/
             (?i. bt = Acc i) \/ bt = BlockHash \/ bt = BlobHash \/ bt = MethodId`
  >- (irule s1PrefixGuardedEnvTheory.env_builtin_expr_prefix_ok >>
      rpt conj_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `?bop. bt = Bop bop`
  >- (gvs[] >> Cases_on `bop = In \/ bop = NotIn`
      >- (irule s1PrefixGuardedBopInTheory.bop_in_expr_prefix_ok >> gvs[])
      >> irule s1PrefixGuardedBopOtherTheory.bop_expr_prefix_ok >> gvs[]) >>
  Cases_on `bt` >> gvs[] >>
  FIRST (map (fn th => irule th >> simp[] >> NO_TAC)
    [s1PrefixGuardedMakeArrayTheory.make_array_expr_prefix_ok,
     s1PrefixGuardedWordTheory.word_builtin_expr_prefix_ok,
     s1PrefixHashTheory.hash_expr_prefix_ok,
     s1PrefixGuardedBytestringTheory.bytestring_builtin_expr_prefix_ok,
     s1PrefixGuardedECTheory.precompile_builtin_expr_prefix_ok])
QED
