Theory bodyPtrPopExternalBoundary
Ancestors bodyPtrPopPrecompileBoundary bodyPtrPopPowBoundary
  bodyPtrPopTraversalBoundary bodyPtrPopCompilerBoundary bodyPtrPopMaterialization
  bodyPtrPopArithmeticBoundary bodyPtrPopTypedCopyBoundary bodyPtrPopAbiDecodeBoundary
  bodyPtrPopAllocationBoundary bodyPtrPopAbiEncodeBoundary
  exprLowering builtinSimple compileEnv emitHelper venomInst list

Theorem pop_compile_extcodesize_check_boundary:
  pop_comp_boundary sa /\ compile_extcodesize_check addr sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_extcodesize_check_def] >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_staticcall_guard_boundary >> simp[]
QED

Theorem pop_compile_return_value_decode_boundary:
  pop_comp_boundary sa /\ compile_return_value_decode buf min_size max_size sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_return_value_decode_def, compile_select_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_no_sub_finished_template >> simp[mk_inst_def]
QED

Theorem pop_compile_default_return_path_boundary:
  pop_comp_boundary sa /\
  compile_default_return_path cenv rt dt buf result default_op addr
    skip min_size max_size info sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[compile_default_return_path_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_all pop_fresh_label_boundary,
         drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary,
         drule_all pop_comp_boundary_new_block,
         drule_all pop_compile_store_memory_boundary,
         drule_all pop_compile_return_value_decode_boundary,
         drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)
           pop_compile_abi_decode_to_buf_boundary,
         (gvs[comp_return_def] >> NO_TAC),
         (Cases_on `skip` >> gvs[comp_return_def] >>
          drule_all pop_compile_extcodesize_check_boundary)] >> simp[]
QED

Theorem pop_external_return_boundary:
  pop_comp_boundary sa /\
  (if abi_size = 0 then comp_return (Lit 0w)
   else if has_default then
     do result_alloc <- compile_alloc_buffer mem_bytes;
        compile_default_return_path cenv rt dt buf result_alloc.buf_operand default_op addr
          skip min_size abi_size info od
   else
     do result_alloc <- compile_alloc_buffer mem_bytes;
        hi <- compile_return_value_decode buf min_size abi_size;
        compile_abi_decode_to_buf result_alloc.buf_operand buf MLOAD hi info;
        comp_return result_alloc.buf_operand od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `abi_size = 0` >> Cases_on `has_default` >>
  simp[comp_ignore_bind_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_all pop_compile_default_return_path_boundary,
         drule_all pop_compile_return_value_decode_boundary,
         drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)
           pop_compile_abi_decode_to_buf_boundary,
         (gvs[comp_return_def] >> NO_TAC)] >> simp[]
QED

Theorem pop_external_args_buffer_boundary:
  pop_comp_boundary sa /\
  (if vals = [] then comp_return () else
     do alloc <- compile_alloc_buffer mem_size;
        compile_extcall_store_values cenv (ZIP (vals,tys)) alloc.buf_operand 0;
        dst <- emit_op ADD [buf; Lit 32w];
        compile_abi_encode_to_buf dst alloc.buf_operand info;
        comp_return () od) sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Cases_on `vals = []` >> simp[comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_all pop_compile_extcall_store_values_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_all pop_compile_abi_encode_to_buf_boundary,
         (gvs[comp_return_def] >> NO_TAC)] >> simp[]
QED

Theorem pop_compile_external_call_kwargs_boundary:
  pop_comp_boundary sa /\
  compile_external_call_kwargs cenv addr vals tys mem_size abi_size method_id ret_size
    min_size ret_bytes static call_value gas_op skip has_default default_op rt dt
    enc_info dec_info sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[compile_external_call_kwargs_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary,
         drule_all pop_fresh_label_boundary,
         drule_all pop_comp_boundary_new_block,
         drule_at (Pat `(if _ then _ else _) _ = _`) (SRULE [comp_ignore_bind_def] pop_external_args_buffer_boundary),
         drule_at (Pat `(if _ then _ else _) _ = _`)
           (SRULE [comp_ignore_bind_def] pop_external_return_boundary),
         (rename1 `if static then _ else _` >> Cases_on `static` >> gvs[] >>
          drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]),
         (Cases_on `ret_size = 0 /\ ~skip` >> gvs[comp_return_def] >>
          drule_all pop_compile_extcodesize_check_boundary)] >> simp[]
QED
