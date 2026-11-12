(* Source-level boundaries for non-self slices. *)
Theory exprSimSliceSource
Ancestors
  exprSimSource vyperInterpreter vyperState vyperContext
  vyperValueOperation vyperValue vyperTypeSystem exprLowering
  vyperTypeExprSoundness vyperTyping

Theorem slice_code_address_body_pre:
  expr_body_pre cenv cx env
    (Builtin ann (Slice n) [Builtin ct (Acc Code) [a]; start; len]) es /\
  expr_sim_inv cenv cx env es' ==>
  expr_body_pre cenv cx env a es'
Proof
  strip_tac >>
  `alloc_limits_expr cenv a` by
    (gvs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     qpat_x_assum `alloc_limits_expr _ _` mp_tac >>
     simp[Once allocLimitsTheory.alloc_limits_expr_def, exprLoweringTheory.is_extcode_def,
          exprLoweringTheory.extcode_addr_expr_def] >>
     simp[allocLimitsTheory.alloc_limits_expr_def]) >>
  gvs[exprSimHypsDefsTheory.expr_body_pre_def, well_typed_expr_def, vyperTypeCallGraphTheory.int_calls_expr_def,
      exprSimHypsDefsTheory.byte_widths_expr_def,
      supportedExprTraverseTheory.supported_expr_exists_def,
      supportedExprTraverseTheory.supported_exprs_exists_every, listTheory.EXISTS_MEM] >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, listTheory.EXISTS_MEM] >>
  metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left,
            vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]
QED

Theorem slice_bytes_nat:
  evaluate_slice (BytesV bs) (IntV (&start)) (IntV (&len)) n =
  if start + len <= LENGTH bs then
    if len <= n then INL (BytesV (TAKE len (DROP start bs)))
    else INR (RuntimeError "evaluate_slice bound")
  else INR (RuntimeError "evaluate_slice range")
Proof
  simp[evaluate_slice_def, dest_NumV_def, compatible_bound_def]
QED

Theorem slice_string_nat:
  evaluate_slice (StringV bs) (IntV (&start)) (IntV (&len)) n =
  if start + len <= LENGTH bs then
    if len <= n then INL (StringV (TAKE len (DROP start bs)))
    else INR (RuntimeError "evaluate_slice bound")
  else INR (RuntimeError "evaluate_slice range")
Proof
  simp[evaluate_slice_def, dest_NumV_def, compatible_bound_def]
QED

(* Includes empty slices at the end of the source. *)
Theorem slice_runtime_capacity:
  (start:num) + len <= src_len /\ (len <= n \/ src_len <= cap /\ cap <= n) ==>
  len <= n
Proof
  decide_tac
QED

Theorem slice_builtin_types:
  well_typed_builtin_app ty (Slice n) [src; st; ln] <=>
  st = BaseT (UintT 256) /\ ln = BaseT (UintT 256) /\
  ((ty = BaseT (BytesT (Dynamic n)) /\ ?bd. src = BaseT (BytesT bd)) \/
   (ty = BaseT (StringT n) /\ ?m. src = BaseT (StringT m)))
Proof
  simp[well_typed_builtin_app_def]
QED

Theorem slice_extcode_literal_bound:
  slice_operands_ok (Slice n)
    [Builtin ct (Acc Code) [a]; start; Literal lt (IntL len)] <=>
  1 <= len /\ len <= &n
Proof
  simp[slice_operands_ok_def]
QED

Theorem slice_empty_at_end[local]:
  evaluate_slice (BytesV [1w; 2w]) (IntV 2) (IntV 0) 0 =
    INL (BytesV []) /\
  evaluate_slice (StringV "ab") (IntV 2) (IntV 0) 0 =
    INL (StringV "") /\
  evaluate_slice (BytesV [1w; 2w]) (IntV 3) (IntV 0) 0 =
    INR (RuntimeError "evaluate_slice range")
Proof
  simp[evaluate_slice_def, dest_NumV_def, compatible_bound_def]
QED

Theorem slice_eval_ordinary:
  code_slice_source (Slice n) [src; start; len] = NONE ==>
  eval_expr cx (Builtin ann (Slice n) [src; start; len]) =
  do vs <- eval_exprs cx [src; start; len];
     acc <- get_accounts;
     v <- lift_sum (evaluate_builtin cx acc ann (Slice n)
                     (MAP expr_type [src; start; len]) vs);
     return (Value v)
  od
Proof
  strip_tac >>
  `type_check T "Builtin args" = return ()` by
    simp[FUN_EQ_THM, type_check_def, assert_def, return_def] >>
  simp[Once evaluate_def, builtin_args_length_ok_def,
       precompile_builtin_def, ignore_bind_def, bind_return, bind_assoc]
QED

Theorem slice_eval_extcode:
  eval_expr cx
    (Builtin ann (Slice n) [Builtin ct (Acc Code) [a]; start; len]) =
  do tail_vs <- eval_exprs cx [start; len];
     addr_vs <- eval_exprs cx [a];
     code_acc <- get_accounts;
     code_v <- lift_sum (evaluate_code_source cx code_acc (is_self_addr a)
                          ct (expr_type a) addr_vs);
     acc <- get_accounts;
     v <- lift_sum (evaluate_builtin cx acc ann (Slice n)
                    (MAP expr_type [Builtin ct (Acc Code) [a]; start; len])
                    (code_v :: tail_vs));
     return (Value v)
  od
Proof
  `type_check T "Builtin args" = return ()` by
    simp[FUN_EQ_THM, type_check_def, assert_def, return_def] >>
  simp[Once evaluate_def, builtin_args_length_ok_def,
       precompile_builtin_def, ignore_bind_def, bind_return, bind_assoc]
QED

Theorem slice_typed_args:
  well_typed_expr env (Builtin ann (Slice n) args) ==>
  ?src start len.
    args = [src; start; len] /\
    expr_type start = BaseT (UintT 256) /\
    expr_type len = BaseT (UintT 256) /\
    slice_operands_ok (Slice n) [src; start; len] /\
    ((ann = BaseT (BytesT (Dynamic n)) /\
      ?bd. expr_type src = BaseT (BytesT bd)) \/
     (ann = BaseT (StringT n) /\
      ?m. expr_type src = BaseT (StringT m)))
Proof
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  strip_tac >> gvs[listTheory.LENGTH_EQ_NUM_compute]
QED

Theorem slice_dispatch_bytestring:
  ~is_self_code src /\ ~is_extcode src /\
  is_bytestring_type (expr_type src) ==>
  compile_builtin_dispatch_body cfn cenv ann ty (Slice n) [src; start; len] st =
  (let (src_op, st1) = lower_value cfn cenv (expr_type src) src st in
   let ((src_len, src_data), st2) = compile_bytestring_src src_op st1 in
   let (start_op, st3) = lower_value cfn cenv ty start st2 in
   let (len_op, st4) = lower_value cfn cenv ty len st3 in
   as_ptr_val ann LocMemory
     (compile_slice_data src_len src_data start_op len_op
        (type_memory_bytes cenv ann) st4))
Proof
  simp[compile_builtin_dispatch_body_def]
QED

Theorem slice_dispatch_fixed:
  ~is_self_code src /\ ~is_extcode src /\
  ~is_bytestring_type (expr_type src) ==>
  compile_builtin_dispatch_body cfn cenv ann ty (Slice n) [src; start; len] st =
  (let (src_op, st1) = lower_value cfn cenv (expr_type src) src st in
   let (tmp_alloc, st2) = compile_alloc_buffer 32 st1 in
   let tmp = tmp_alloc.buf_operand in
   let (_, st3) = emit_void MSTORE [tmp; src_op] st2 in
   let (start_op, st4) = lower_value cfn cenv ty start st3 in
   let (len_op, st5) = lower_value cfn cenv ty len st4 in
   as_ptr_val ann LocMemory
     (compile_slice_data (Lit (n2w (fixed_bytes_size (expr_type src)))) tmp
        start_op len_op (type_memory_bytes cenv ann) st5))
Proof
  simp[compile_builtin_dispatch_body_def]
QED

Theorem slice_dispatch_extcode:
  ~is_self_code (Builtin ct (Acc Code) [a]) ==>
  compile_builtin_dispatch_body cfn cenv ann ty (Slice n)
    [Builtin ct (Acc Code) [a]; start; len] st =
  (let (start_op, st1) = lower_value cfn cenv ty start st in
   let (len_op, st2) = lower_value cfn cenv ty len st1 in
   let ((out_buf, out_data), st3) =
     compile_slice_out_buf (type_memory_bytes cenv ann) st2 in
   let (addr_op, st4) = lower_value cfn cenv ty a st3 in
   as_ptr_val ann LocMemory
     (compile_slice_extcode addr_op start_op len_op out_buf out_data st4))
Proof
  simp[compile_builtin_dispatch_body_def, is_self_code_def, is_extcode_def,
       extcode_addr_expr_def]
QED

Theorem slice_literal_length_value:
  eval_exprs cx [src; start; Literal lt (IntL j)] s =
    (INL [v; sv; IntV (&k)], t) ==>
  j = &k
Proof
  simp[evaluate_def, bind_def, ignore_bind_def, return_def,
       lift_sum_def, read_result_def, evaluate_literal_def,
       AllCaseEqs()] >> metis_tac[]
QED


Theorem slice_literal_static_bound[local]:
  !src. slice_operands_ok (Slice n) [src; start; Literal lt (IntL j)] ==>
  j <= &n
Proof
  recInduct is_extcode_ind >> rpt conj_tac >> rpt gen_tac >>
  CONV_TAC (LAND_CONV
    (computeLib.RESTR_EVAL_CONV [``expr_type``, ``bytelike_type_bound``])) >>
  simp[]
QED

Theorem slice_nonliteral_match[local]:
  (!lt j. len <> Literal lt (IntL j)) ==>
  (case len of Literal lt (IntL j) => P j | _ => B) = B
Proof
  strip_tac >> Cases_on `len` >> simp[] >>
  rename1 `Literal lt lit` >> Cases_on `lit` >> simp[] >>
  metis_tac[]
QED

Theorem slice_nonliteral_static_bound[local]:
  !src. (!lt j. len <> Literal lt (IntL j)) ==>
    slice_operands_ok (Slice n) [src; start; len] ==>
    bytelike_type_bound (expr_type src) <= n
Proof
  recInduct is_extcode_ind >> rpt conj_tac >> rpt gen_tac >>
  disch_tac >>
  CONV_TAC (LAND_CONV
    (computeLib.RESTR_EVAL_CONV [``expr_type``, ``bytelike_type_bound``])) >>
  Cases_on `len` >> simp[] >>
  rename1 `!lt j. Literal lty lit <> Literal lt (IntL j)` >>
  Cases_on `lit` >> gvs[]
QED

Theorem slice_capacity_alternatives:
  slice_operands_ok (Slice n) [src; start; len] ==>
  (?lt j. len = Literal lt (IntL j) /\ j <= &n) \/
  bytelike_type_bound (expr_type src) <= n
Proof
  strip_tac >> Cases_on `?lt j. len = Literal lt (IntL j)`
  >- (gvs[] >> disj1_tac >> drule slice_literal_static_bound >> simp[]) >>
  disj2_tac >> irule slice_nonliteral_static_bound >>
  qexistsl [`len`, `start`] >> simp[] >> metis_tac[]
QED

Theorem slice_bytes_runtime_length[local]:
  value_runtime_typed env (BaseT (BytesT bd)) (BytesV bs) ==>
  LENGTH bs <= bytelike_type_bound (BaseT (BytesT bd))
Proof
  Cases_on `bd` >>
  simp[value_runtime_typed_def, evaluate_type_def, value_has_type_def,
       bytelike_type_bound_def]
QED

Theorem slice_string_runtime_length[local]:
  value_runtime_typed env (BaseT (StringT m)) (StringV bs) ==>
  LENGTH bs <= bytelike_type_bound (BaseT (StringT m))
Proof
  simp[value_runtime_typed_def, evaluate_type_def, value_has_type_def,
       bytelike_type_bound_def]
QED

Theorem slice_bytes_capacity:
  slice_operands_ok (Slice n) [src; start; len] /\
  eval_exprs cx [src; start; len] s =
    (INL [BytesV bs; IntV (&i); IntV (&k)], t) /\
  expr_type src = BaseT (BytesT bd) /\
  value_runtime_typed env (expr_type src) (BytesV bs) /\
  i + k <= LENGTH bs ==> k <= n
Proof
  strip_tac >> drule slice_capacity_alternatives >> strip_tac
  >- (gvs[] >> drule slice_literal_length_value >> simp[] >> intLib.ARITH_TAC) >>
  `LENGTH bs <= bytelike_type_bound (expr_type src)` by
    (gvs[] >> drule slice_bytes_runtime_length >> simp[]) >>
  decide_tac
QED

Theorem slice_string_capacity:
  slice_operands_ok (Slice n) [src; start; len] /\
  eval_exprs cx [src; start; len] s =
    (INL [StringV bs; IntV (&i); IntV (&k)], t) /\
  expr_type src = BaseT (StringT m) /\
  value_runtime_typed env (expr_type src) (StringV bs) /\
  i + k <= LENGTH bs ==> k <= n
Proof
  strip_tac >> drule slice_capacity_alternatives >> strip_tac
  >- (gvs[] >> drule slice_literal_length_value >> simp[] >> intLib.ARITH_TAC) >>
  `LENGTH bs <= bytelike_type_bound (expr_type src)` by
    (gvs[] >> drule slice_string_runtime_length >> simp[]) >>
  decide_tac
QED
