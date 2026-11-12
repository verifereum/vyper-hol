Theory exprSimAbiEncodeArgsTupleProbe
Ancestors
  exprSimAbiEncodeArgsLayoutContracts supportedTypes vyperTypeSystem
  loweringPosts exprLowering compileEnv finite_map

Definition tuple_narrow_def:
  tuple_narrow = TupleT [BaseT (BytesT (Dynamic 32)); BaseT (BytesT (Dynamic 32))]
End

Definition tuple_wide_def:
  tuple_wide = TupleT [BaseT (BytesT (Dynamic 64)); BaseT (BytesT (Dynamic 64))]
End

Theorem tuple_return_supported:
  supported_return_type tops tuple_narrow
Proof
  EVAL_TAC
QED

Theorem tuple_annotation_widening:
  type_widens_to tenv tuple_narrow tuple_wide
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def,
                  vfmConstantsTheory.word_size_def]
QED

Theorem tuple_call_typing:
  FLOOKUP env.fn_sigs (NONE,"f") = SOME sig /\
  sig.ret_ty = tuple_narrow /\ sig.param_types = [] ==>
  well_typed_expr env (Call tuple_wide (IntCall (NONE,"f")) [] NONE)
Proof
  simp[well_typed_expr_def, tuple_annotation_widening,
       tuple_wide_def, well_formed_type_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def,
                  vfmConstantsTheory.word_size_def]
QED

Definition tuple_memory_def:
  tuple_memory : byte list =
    REPLICATE 31 0w ++ [1w; 170w] ++ REPLICATE 31 0w ++
    REPLICATE 31 0w ++ [1w; 187w] ++ REPLICATE 31 0w
End

Theorem tuple_memory_mismatch:
  val_in_memory (TupleTV [BaseTV (BytesT (Dynamic 32)); BaseTV (BytesT (Dynamic 32))])
    (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) 0 tuple_memory /\
  ~val_in_memory (TupleTV [BaseTV (BytesT (Dynamic 64)); BaseTV (BytesT (Dynamic 64))])
    (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) 0 tuple_memory
Proof
  EVAL_TAC >> simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def,
                  wordsTheory.dimindex_8]
QED

Theorem tuple_physical_mismatch:
  post_value_type (ce with ce_func_return_type := (\_. tuple_narrow))
    (Call tuple_wide (IntCall (NONE,"f")) [] NONE) = tuple_narrow /\
  type_memory_bytes ce tuple_narrow = 128 /\
  type_memory_bytes ce tuple_wide = 192
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def,
                  vfmConstantsTheory.word_size_def]
QED

Theorem tuple_abi_typing:
  FLOOKUP env.fn_sigs (NONE,"f") = SOME sig /\
  sig.ret_ty = tuple_narrow /\ sig.param_types = [] ==>
  well_typed_expr env
    (TypeBuiltin (BaseT (BytesT (Dynamic 320))) (AbiEncode T NONE)
       (TupleT [tuple_wide])
       [Call tuple_wide (IntCall (NONE,"f")) [] NONE])
Proof
  rpt strip_tac >>
  `well_typed_expr env (Call tuple_wide (IntCall (NONE,"f")) [] NONE)` by
    (irule tuple_call_typing >> simp[] >> metis_tac[]) >>
  simp[well_typed_expr_def, type_builtin_result_ok_def,
       well_typed_type_builtin_args_def, well_formed_type_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem tuple_singleton_compile:
  cfn ce tuple_wide (Call tuple_wide (IntCall (NONE,"f")) [] NONE) sa =
    (StackValue tuple_narrow op,sb) ==>
  compile_abi_encode_args cfn ce
    [Call tuple_wide (IntCall (NONE,"f")) [] NONE] sa = ([op],sb)
Proof
  simp[compile_abi_encode_args_def, expr_can_mutate_def,
       vyperASTTheory.expr_type_def, unwrap_value_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

Definition tuple_call_def:
  tuple_call = Call tuple_wide (IntCall (NONE,"f")) [] NONE
End

Definition tuple_abi_def:
  tuple_abi = TypeBuiltin (BaseT (BytesT (Dynamic 320))) (AbiEncode T NONE)
    (TupleT [tuple_wide]) [tuple_call]
End

Theorem tuple_singleton_cases:
  exprs_case F ctx func ce cx [tuple_call] <=>
  (!env ty es. expr_body_pre ce cx env tuple_call es ==>
    expr_sim ctx func ce cx ty tuple_call es) /\
  (!env ty es. expr_body_pre ce cx env tuple_call es ==>
    expr_vv_sim ctx func ce cx ty tuple_call es)
Proof
  simp[exprSimHypsDefsTheory.exprs_case_def,
       exprSimHypsDefsTheory.expr_sim_case_def,
       exprSimHypsDefsTheory.expr_vv_case_def]
QED

Theorem tuple_body_pre_contract:
  expr_body_pre ce cx env tuple_abi es <=>
    expr_sim_inv ce cx env es /\ well_typed_expr env tuple_abi /\
    byte_widths_expr tuple_abi /\ alloc_limits_expr ce tuple_abi /\
    call_evaluation_safe cx [(NONE,"f")] /\
    ~expr_has_evm_run tuple_abi /\
    ~supported_expr_exists call_operands_effect_root tuple_abi /\
    (?tops. supported_program tops /\ get_module_code cx NONE = SOME tops /\
       IS_SOME (supported_function_decl tops (NONE,"f") Internal)) /\
    (!target. supported_expr_exists (expr_abi_decode_target_root target) tuple_abi ==>
       occurs_abi_decode_target target (cx_tops cx)) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target))
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def, tuple_abi_def, tuple_call_def,
       vyperTypeCallGraphTheory.int_calls_expr_def]
QED
