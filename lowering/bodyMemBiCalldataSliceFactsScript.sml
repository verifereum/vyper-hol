(* Source/compiler boundaries for the memory proof.  The six local
   prerequisites below are restated from exprSimCalldataSliceScript.sml;
   that non-body theory cannot be edited under this task's scope. *)
Theory bodyMemBiCalldataSliceFacts
Ancestors
  exprSimCalldataSlice exprSimMemoryRead bodyMemoryPreds
  vyperTyping vyperInterpreter vyperValueOperation vyperTypeSystem
  exprLowering exprLoweringProps builtinSimple emitHelper compileEnv
  loweringSlice context fragExec emitHelperProps freshWrites exprSimHypsDefs
  exprBopLowering list builtinBytes vyperContext allocLimits
  vyperAST vyperState vyperValue venomInst venomState

Theorem calldata_slice_typing:
  well_typed_expr env (Builtin ann (CalldataSlice n) args) ==>
  ?e. args = [e] /\ expr_type e = BaseT (UintT 256) /\
      ann = BaseT (BytesT (Dynamic n)) /\ 0 < n /\ n < 2 ** 256
Proof
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  strip_tac >> Cases_on `args` >> gvs[] >>
  rename1 `MAP expr_type rest = []` >> Cases_on `rest` >> gvs[]
QED

(* Also local in exprSimCalldataSlice: dispatch prerequisite. *)
Theorem names_builtin_calldata_slice[local]:
  !args. ~names_builtin (CalldataSlice n) args
Proof
  `!bt args. names_builtin bt args ==> bt <> CalldataSlice n` suffices_by
    metis_tac[] >>
  ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]
QED

Theorem compile_calldata_slice_parts:
  !cenv ty ann n e sa.
    compile_expr cenv ty (Builtin ann (CalldataSlice n) [e]) sa =
    let (start_op, sb) = lower_value compile_expr cenv (expr_type e) e sa in
    as_ptr_val ann LocMemory
      (compile_slice_calldata start_op (Lit (n2w n))
        (type_memory_bytes cenv ann) sb)
Proof
  rpt gen_tac >>
  simp[compile_expr_builtin_dispatch, names_builtin_calldata_slice] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def]
QED

Theorem evaluate_calldata_slice_uint:
  evaluate_calldata_slice bs (IntV &start) n =
  if n = 0 \/ 2 ** 256 <= start + n then
    INR (RuntimeError "calldata slice overflow")
  else if start + n <= LENGTH bs then
    INL (BytesV (TAKE n (DROP start bs)))
  else INR (RuntimeError "evaluate_slice range")
Proof
  simp[evaluate_calldata_slice_def, evaluate_slice_def, dest_NumV_def,
       compatible_bound_def]
QED

Theorem eval_calldata_slice_cases:
  eval_expr cx (Builtin ann (CalldataSlice n) [e]) es = (res, es') ==>
  (?exc. eval_exprs cx [e] es = (INR exc, es') /\ res = INR exc) \/
  ?vs. eval_exprs cx [e] es = (INL vs, es') /\
       res = (case vs of
         [v] => (case evaluate_calldata_slice cx.txn.calldata v n of
                   INL out => INL (Value out)
                 | INR err => INR (Error err))
       | _ => INR (Error (TypeError "builtin")))
Proof
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx [e] es` >> rename1 `_ = (rr,es1)` >>
  Cases_on `rr` >> simp[get_accounts_def, bind_def, return_def,
                         builtin_args_length_ok_def] >>
  rename1 `eval_exprs cx [e] es = (INL vs,es1)` >>
  simp[evaluate_builtin_def, lift_sum_def, bind_def, return_def, raise_def] >>
  Cases_on `vs` >> simp[raise_def] >>
  rename1 `eval_exprs cx [e] es = (INL (v::rest),es1)` >>
  Cases_on `rest` >> simp[raise_def] >>
  Cases_on `evaluate_calldata_slice cx.txn.calldata v n` >>
  simp[return_def, raise_def] >> rpt strip_tac >> gvs[]
QED

Theorem slice_calldata_parts:
  !start_op length_op sz sa ptr sb.
  compile_slice_calldata start_op length_op sz sa = (ptr, sb) ==>
  ?buf sm data s1 len s2 s3 s4.
    compile_alloc_buffer sz sa = (buf, sm) /\ ptr = buf.buf_operand /\
    emit_op ADD [ptr; Lit 32w] sm = (data, s1) /\
    emit_op CALLDATASIZE [] s1 = (len, s2) /\
    compile_assert_slice_bounds start_op length_op len s2 = ((), s3) /\
    emit_void CALLDATACOPY [data; start_op; length_op] s3 = ((), s4) /\
    emit_void MSTORE [ptr; length_op] s4 = ((), sb)
Proof
  rpt gen_tac >> simp[compile_slice_calldata_def, compile_slice_out_buf_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (goal_assum $ drule_at Any) >> simp[]
QED

Theorem slice_calldata_shape:
  !op num_op sz sa buf_op sb.
  compile_slice_calldata op num_op sz sa = (buf_op,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sb.cs_next_id = sa.cs_next_id + 11 /\
  sb.cs_next_var = sa.cs_next_var + 8 /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]) (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  rpt gen_tac >>
  simp[compile_slice_calldata_def, compile_slice_out_buf_def,
       contextTheory.compile_alloc_buffer_def, compile_assert_slice_bounds_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[same_blocks_def, emitted_insts_def, rich_listTheory.DROP_APPEND1,
       mk_inst_def, is_terminator_def]
QED

Theorem calldata_slice_memory_bytes:
  type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) =
    32 + 32 * word_size n
Proof
  simp[type_memory_bytes_def, vfmConstantsTheory.word_size_def]
QED

Theorem calldata_slice_lowered_value_type:
  lowered_value_type cenv (Builtin (BaseT (BytesT (Dynamic n)))
    (CalldataSlice n) [e]) = BaseT (BytesT (Dynamic n))
Proof
  simp[lowered_value_type_def, expr_type_def]
QED

Theorem calldata_slice_allocation_limit:
  expr_body_pre cenv cx env (Builtin ann (CalldataSlice n) args) es ==>
  32 + 32 * word_size n < 2 ** 64
Proof
  simp[expr_body_pre_def, Once alloc_limits_expr_def]
QED

(* Extension consequence of local slice_bounds_shape in
   exprSimCalldataSliceScript.sml. *)
Theorem calldata_slice_bounds_extends:
  compile_assert_slice_bounds a n limit sa = ((),sb) ==>
  inst_extends sa sb
Proof
  simp[compile_assert_slice_bounds_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED

Theorem calldata_slice_after_alloc_extends:
  emit_op ADD [buf_op; Lit 32w] sa = (data,s1) /\
  emit_op CALLDATASIZE [] s1 = (len,s2) /\
  compile_assert_slice_bounds start num len s2 = ((),s3) /\
  emit_void CALLDATACOPY [data; start; num] s3 = ((),s4) /\
  emit_void MSTORE [buf_op; num] s4 = ((),sb) ==>
  inst_extends sa sb
Proof
  strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  drule calldata_slice_bounds_extends >> strip_tac >>
  metis_tac[inst_extends_trans]
QED

Theorem calldata_slice_allocation_split:
  compile_slice_calldata op num sz sa = (buf_op,sb) /\
  compile_alloc_buffer sz sa = (buf,sm) ==>
  emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb
Proof
  strip_tac >> drule slice_calldata_parts >> strip_tac >> gvs[] >>
  `inst_extends sm sb` by
    (irule calldata_slice_after_alloc_extends >> metis_tac[]) >>
  `inst_extends sa sm` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
     drule inst_extends_emit_op >> simp[]) >>
  irule emitted_insts_append >> gvs[inst_extends_def]
QED
