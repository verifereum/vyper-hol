(* Exact compiler cuts for the eager request, call and return continuations. *)
Theory extcallCompilerStages
Ancestors exprLowering compileEnv context emitHelper list

val extcall_tuple_compiler = ``\ce vals tys bytes enc buf.
  if vals = [] then comp_return (Lit 4w) else
  comp_bind (compile_alloc_buffer bytes) (\args.
    comp_ignore_bind (compile_extcall_store_values ce (ZIP (vals,tys)) args.buf_operand 0)
    (comp_bind (emit_op ADD [buf; Lit 32w]) (\dst.
     comp_bind (compile_abi_encode_to_buf dst args.buf_operand enc) (\len.
       emit_op ADD [len; Lit 4w]))))``;

val extcall_effect_compiler = ``\rt skip stat addr value gas buf cap offset len.
  comp_ignore_bind
    (if rt = NoneT /\ ~skip then compile_extcodesize_check addr else comp_return ())
    (comp_bind
      (if stat then emit_op STATICCALL [gas; addr; offset; len; buf; Lit (n2w cap)]
       else emit_op CALL [gas; addr; value; offset; len; buf; Lit (n2w cap)])
      (\success. comp_bind (fresh_label "extcall_fail") (\fail.
       comp_bind (fresh_label "extcall_cont") (\cont.
       comp_ignore_bind (emit_inst JNZ [success; Label cont; Label fail] [])
       (comp_ignore_bind (new_block fail)
       (comp_bind (emit_op RETURNDATASIZE []) (\rds.
       comp_bind (compile_alloc_buffer 0) (\fb.
       comp_ignore_bind (emit_void RETURNDATACOPY [fb.buf_operand; Lit 0w; rds])
       (comp_ignore_bind (emit_inst REVERT [fb.buf_operand; rds] [])
         (new_block cont))))))))))``;

val extcall_return_compiler = ``\ce rt dt has def addr skip buf mn mx bytes info.
  if rt = NoneT then comp_return (Lit 0w) else
  comp_bind (compile_alloc_buffer bytes) (\result.
    if has then compile_default_return_path ce rt dt buf result.buf_operand def addr
      skip mn mx info
    else comp_bind (compile_return_value_decode mn mx) (\hi.
      comp_ignore_bind
        (compile_abi_decode_to_buf result.buf_operand (Lit 0w) MLOAD buf hi info)
        (comp_return result.buf_operand)))``;

Theorem extcall_compile_call_stages:
  compile_call cfn ce ann ty (ExtCall stat skip (fname,ats,rt) opts)
    (addr::rest) dflt sa = (vv,sb) ==>
  let pos = TAKE (LENGTH ats) rest;
      kws = DROP (LENGTH ats) rest;
      cats = MAP (lowered_value_type ce) pos;
      wrapped = if needs_external_call_wrap rt then TupleT [rt] else rt in
  ?a s1 vals s2 vo go default s3 gas s5 result.
    lower_value cfn ce (BaseT AddressT) addr sa = (a,s1) /\
    compile_ext_call_args cfn ce kws cats pos s1 = (vals,s2) /\
    compile_ext_call_kwargs cfn ce rt opts kws s2 = ((vo,go,default),s3) /\
    (case go of SOME g => comp_return g | NONE => emit_op GAS []) s3 = (gas,s5) /\
    (let (has,def,dt) = case default of SOME (d,t) => (T,d,t)
                                     | NONE => (F,Lit 0w,rt) in
     compile_external_call_kwargs ce a vals cats
       (SUM (MAP (type_memory_bytes ce) cats))
       (abi_size_bound ce.ce_struct_fields (TupleT cats))
       (ce.ce_method_id fname ats) (abi_size_bound ce.ce_struct_fields wrapped)
       (abi_static_size ce.ce_struct_fields wrapped) (type_memory_bytes ce rt)
       stat (case vo of SOME v => v | NONE => Lit 0w) gas skip has def rt dt
       (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT cats))
       (type_to_abi_dec_info ce.ce_struct_fields ce wrapped) s5 = (result,sb)) /\
    vv = if rt = NoneT then StackValue ann result
         else LocatedValue ann (mk_ptr result LocMemory)
Proof
  simp_tac std_ss [compile_call_def, LET_THM, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem extcall_compile_external_stages:
  compile_external_call_kwargs ce addr vals tys bytes max_args method cap mn ret_bytes
    stat value gas skip has def rt dt enc info sa = (result,sb) ==>
  ?buffer s1 s2 len s3 offset sp sr.
    compile_alloc_buffer ((if max_args > cap then max_args else cap) + 32)
      sa = (buffer,s1) /\
    emit_void MSTORE [buffer.buf_operand; Lit (n2w method)] s1 = ((),s2) /\
    (^extcall_tuple_compiler ce vals tys bytes enc buffer.buf_operand) s2 = (len,s3) /\
    emit_op ADD [buffer.buf_operand; Lit 28w] s3 = (offset,sp) /\
    (^extcall_effect_compiler rt skip stat addr value gas buffer.buf_operand cap offset len)
      sp = ((),sr) /\
    (^extcall_return_compiler ce rt dt has def addr skip buffer.buf_operand mn cap
      ret_bytes info) sr = (result,sb)
Proof
  simp_tac std_ss [compile_external_call_kwargs_def, LET_THM,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem extcall_compile_tuple_stages:
  (^extcall_tuple_compiler ce vals tys bytes enc buf) sa = (len,sb) /\ vals <> [] ==>
  ?args s1 s2 dst s3 encoded s4.
    compile_alloc_buffer bytes sa = (args,s1) /\
    compile_extcall_store_values ce (ZIP (vals,tys)) args.buf_operand 0 s1 = ((),s2) /\
    emit_op ADD [buf; Lit 32w] s2 = (dst,s3) /\
    compile_abi_encode_to_buf dst args.buf_operand enc s3 = (encoded,s4) /\
    emit_op ADD [encoded; Lit 4w] s4 = (len,sb)
Proof
  simp_tac std_ss [comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `vals = []` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >> metis_tac[]
QED
