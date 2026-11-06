(* Actual unsigned loader boundaries. No signed-residual dependency. *)
Theory bodyPtrTypeBuiltinsUnsignedLoad
Ancestors
  bodyPtrTypeBuiltinsUnsignedProbe bodyPtrTypeBuiltinsSourceCompile
  exprLowering exprLoweringProps compileEnv emitHelperProps rich_list builtinBytes

Theorem unsigned_loader_decompose:
  load_bytestring_as_word x SHR sa = ((out,bits),sb) ==>
  ?len dp data sub s1 s2 s3 s4 s5.
    emit_op MLOAD [x] sa = (len,s1) /\
    emit_op ADD [x;Lit 32w] s1 = (dp,s2) /\
    emit_op MLOAD [dp] s2 = (data,s3) /\
    emit_op SUB [Lit 32w;len] s3 = (sub,s4) /\
    emit_op MUL [sub;Lit 8w] s4 = (bits,s5) /\
    emit_op SHR [bits;data] s5 = (out,sb)
Proof
  simp[load_bytestring_as_word_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[]
QED

Theorem zero_capacity_convert_dispatch:
  is_bytestring_type (expr_type e) /\ is_word_type typ /\
  (lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
   lowered_value_type cenv e = BaseT (StringT 0)) /\
  lower_value compile_expr cenv (expr_type e) e sa = (v,sb) ==>
  compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert typ [e] sa =
    (StackValue ann (Lit 0w),sb)
Proof
  simp[compile_type_builtin_dispatch_body_def]
QED

Theorem unsigned_loader_source_prefix:
  load_bytestring_as_word x SHR sa = ((out,bits),sb) ==>
  ?len dp sm data sub s3 s4 s5.
    compile_bytestring_src x sa = ((len,dp),sm) /\
    emit_op MLOAD [dp] sm = (data,s3) /\
    emit_op SUB [Lit 32w;len] s3 = (sub,s4) /\
    emit_op MUL [sub;Lit 8w] s4 = (bits,s5) /\
    emit_op SHR [bits;data] s5 = (out,sb)
Proof
  strip_tac >> drule unsigned_loader_decompose >> strip_tac >>
  simp[compile_bytestring_src_def, comp_bind_def, comp_return_def] >>
  metis_tac[]
QED
