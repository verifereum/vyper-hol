Theory bodyPtrBytestringBuiltinsSliceDispatch
Ancestors
  exprLowering exprBopLowering bodyPtrBytestringBuiltinsExternalSlice
  vyperAST list exprSimHypsDefs exprCallbackContracts
  exprSimWordArgs vyperContext vyperState vyperInterpreter

(* The source pseudo-expression is not lowered for external buffers. *)
Theorem slice_calldata_compile_cut:
  is_msg_data src /\
  compile_expr cenv ty (Builtin ann (Slice n) [src; start; len]) sa = (vv,sb) ==>
  ?a s1 b s2.
    lower_value compile_expr cenv ty start sa = (a,s1) /\
    lower_value compile_expr cenv ty len s1 = (b,s2) /\
    as_ptr_val ann LocMemory
      (compile_slice_calldata a b (type_memory_bytes cenv ann) s2) = (vv,sb)
Proof
  `!bt args. names_builtin bt args ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin (Slice n) [src; start; len]` by metis_tac[] >>
  simp[compile_expr_builtin_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
  strip_tac >> gvs[] >>
  ntac 2 (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem slice_code_compile_cut:
  ~is_msg_data src /\ is_self_code src /\
  compile_expr cenv ty (Builtin ann (Slice n) [src; start; len]) sa = (vv,sb) ==>
  ?a s1 b s2.
    lower_value compile_expr cenv ty start sa = (a,s1) /\
    lower_value compile_expr cenv ty len s1 = (b,s2) /\
    as_ptr_val ann LocMemory
      (compile_slice_code a b (type_memory_bytes cenv ann) s2) = (vv,sb)
Proof
  `!bt args. names_builtin bt args ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin (Slice n) [src; start; len]` by metis_tac[] >>
  simp[compile_expr_builtin_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
  strip_tac >> gvs[] >>
  ntac 2 (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem slice_extcode_compile_cut:
  ~is_msg_data src /\ ~is_self_code src /\ is_extcode src /\
  compile_expr cenv ty (Builtin ann (Slice n) [src; start; len]) sa = (vv,sb) ==>
  ?a s1 b s2 out data s3 addr s4.
    lower_value compile_expr cenv ty start sa = (a,s1) /\
    lower_value compile_expr cenv ty len s1 = (b,s2) /\
    compile_slice_out_buf (type_memory_bytes cenv ann) s2 = ((out,data),s3) /\
    lower_value compile_expr cenv ty (extcode_addr_expr src) s3 = (addr,s4) /\
    as_ptr_val ann LocMemory
      (compile_slice_extcode addr a b out data s4) = (vv,sb)
Proof
  `!bt args. names_builtin bt args ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin (Slice n) [src; start; len]` by metis_tac[] >>
  simp[compile_expr_builtin_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
  strip_tac >> gvs[] >>
  `expr_size (extcode_addr_expr src) < list_size expr_size [src; start; len]` by
    (irule extcode_child_bound >> simp[]) >>
  fs[list_size_def, expr_size_def, lower_value_child_call] >>
  ntac 4 (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem slice_memory_compile_cut:
  ~is_msg_data src /\ ~is_self_code src /\ ~is_extcode src /\
  is_bytestring_type (expr_type src) /\
  compile_expr cenv ty (Builtin ann (Slice n) [src; start; len]) sa = (vv,sb) ==>
  ?src_op s1 src_len src_data s2 a s3 b s4.
    lower_value compile_expr cenv (expr_type src) src sa = (src_op,s1) /\
    compile_bytestring_src src_op s1 = ((src_len,src_data),s2) /\
    lower_value compile_expr cenv ty start s2 = (a,s3) /\
    lower_value compile_expr cenv ty len s3 = (b,s4) /\
    as_ptr_val ann LocMemory
      (compile_slice_data src_len src_data a b (type_memory_bytes cenv ann) s4) = (vv,sb)
Proof
  `!bt args. names_builtin bt args ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin (Slice n) [src; start; len]` by metis_tac[] >>
  simp[compile_expr_builtin_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
  strip_tac >> gvs[] >>
  ntac 4 (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem slice_fixed_compile_cut:
  ~is_msg_data src /\ ~is_self_code src /\ ~is_extcode src /\
  ~is_bytestring_type (expr_type src) /\
  compile_expr cenv ty (Builtin ann (Slice n) [src; start; len]) sa = (vv,sb) ==>
  ?src_op s1 tmp s2 s3 a s4 b s5.
    lower_value compile_expr cenv (expr_type src) src sa = (src_op,s1) /\
    compile_alloc_buffer 32 s1 = (tmp,s2) /\
    emit_void MSTORE [tmp.buf_operand; src_op] s2 = ((),s3) /\
    lower_value compile_expr cenv ty start s3 = (a,s4) /\
    lower_value compile_expr cenv ty len s4 = (b,s5) /\
    as_ptr_val ann LocMemory
      (compile_slice_data (Lit (n2w (fixed_bytes_size (expr_type src))))
        tmp.buf_operand a b (type_memory_bytes cenv ann) s5) = (vv,sb)
Proof
  `!bt args. names_builtin bt args ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin (Slice n) [src; start; len]` by metis_tac[] >>
  simp[compile_expr_builtin_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
  strip_tac >> gvs[] >>
  ntac 5 (pairarg_tac >> gvs[]) >> metis_tac[]
QED

(* Source evaluation retains surface-list order.  In particular, this does
   not claim that the external-code address can be moved past start/length. *)
Theorem slice_source_action:
  vyperState$bind
    (eval_expr cx (Builtin ann (Slice n) [src; start; len])) (read_result cx) =
  vyperState$bind (eval_exprs cx [src; start; len])
    (\vs ee. (builtin_result cx ee.accounts ann (Slice n)
      [expr_type src; expr_type start; expr_type len] vs,ee))
Proof
  mp_tac (Q.INST [`bt` |-> `Slice n`, `args` |-> `[src; start; len]`]
    eval_expr_builtin_action) >>
  simp[builtin_args_length_ok_def, precompile_builtin_def]
QED
