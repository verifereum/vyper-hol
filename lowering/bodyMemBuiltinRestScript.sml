(* Memory case of the body induction (bodyMemory's body_mem_mutual): the
   builtins with no other case: not the binary operators, array literals,
   ecadd and ecmul, msg.data length (bodyCalldataMemory), or neg, abs and not
   on one operand. The environment reads are here: bodyEnvMemory's
   body_env_mem_case predates the gas-counted expr_sim_mem and needs porting. *)
Theory bodyMemBuiltinRest
Ancestors
  bodyMemBiEnv bodyMemBiLen bodyMemBiCalldataSlice bodyMemBiKeccak
  bodyMemBiSha256 bodyMemBiWord bodyMemBiCeil bodyMemBiBlockHash
  bodyMemBiBlobHash bodyMemBiAcc bodyMemBiMethodId bodyMemBiECRecover
  bodyMemBiConcat bodyMemBiSlice bodyMemBiUint2Str
  bodyMemoryPreds vyperTypeBuiltins vyperTypeSystem vyperContext vyperState
  vyperAST

(* A builtin applied to a number of operands it does not take fails to type
   check, so expr_body_pre never holds of it. *)
Theorem body_builtin_bad_arity_mem[local]:
  !cx ty bt es.
    ~builtin_args_length_ok bt (LENGTH es) ==>
    body_expr_mem_ok cx (Builtin ty bt es)
Proof
  rw[body_expr_mem_ok_def] >>
  gvs[exprSimHypsDefsTheory.expr_body_pre_def, well_typed_expr_def] >>
  drule well_typed_builtin_app_length >> simp[]
QED

Theorem body_builtin_rest_mem_case:
  !cx ty bt es.
    (!bop. bt <> Bop bop) /\ (!t n. bt <> MakeArray t n) /\
    bt <> ECAdd /\ bt <> ECMul /\ bt <> CalldataLen /\
    (!e. es = [e] ==> bt <> Neg /\ bt <> Abs /\ bt <> Not) /\
    (!s'' x t v code_ty addr s3 tail_vs t'.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas /\
       code_slice_source bt es = SOME v /\ v = (code_ty,addr) /\
       eval_exprs cx (TL es) s3 = (INL tail_vs,t') ==>
       body_exprs_mem_ok cx [addr]) /\
    (!s'' x t v code_ty addr.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas /\
       code_slice_source bt es = SOME v /\ v = (code_ty,addr) ==>
       body_exprs_mem_ok cx (TL es)) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas /\
       code_slice_source bt es = NONE ==>
       body_exprs_mem_ok cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_mem_ok cx (HD es)) ==>
    body_expr_mem_ok cx (Builtin ty bt es)
Proof
  rpt strip_tac >>
  reverse (Cases_on `builtin_args_length_ok bt (LENGTH es)`)
  >- simp[body_builtin_bad_arity_mem] >>
  `bt = Len ==> body_expr_mem_ok cx (HD es)` by
    (strip_tac >> first_x_assum irule >> simp[type_check_def, assert_def]) >>
  Cases_on `?n. bt = Slice n`
  >- (gvs[] >> irule body_builtin_slice_mem >> rpt conj_tac >> rpt strip_tac >>
      first_x_assum irule >> simp[type_check_def, assert_def] >> metis_tac[]) >>
  `bt <> Len /\ bt <> Env MsgGas /\ code_slice_source bt es = NONE ==>
   body_exprs_mem_ok cx es` by
    (strip_tac >> first_x_assum irule >> simp[type_check_def, assert_def]) >>
  `code_slice_source bt es = NONE` by
    (Cases_on `code_slice_source bt es` >> simp[] >>
     rename1 `SOME p` >> PairCases_on `p` >> gvs[code_slice_source_SOME]) >>
  Cases_on `bt` >> gvs[] >>
  gvs[body_builtin_env_mem, body_builtin_len_mem,
      body_builtin_calldata_slice_mem, body_builtin_keccak256_mem,
      body_builtin_sha256_mem, body_builtin_word_mem, body_builtin_ceil_mem,
      body_builtin_blockhash_mem, body_builtin_blobhash_mem,
      body_builtin_acc_mem, body_builtin_method_id_mem,
      body_builtin_ecrecover_mem, body_builtin_concat_mem,
      body_builtin_uint2str_mem] >>
  (* neg, abs and not on other than one operand *)
  gvs[builtin_args_length_ok_def, listTheory.LENGTH_EQ_NUM_compute]
QED
