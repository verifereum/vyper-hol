Theory stmtSimLogData
Ancestors
  loweringPosts
  stmtSimLogTopics exprSimBufferStore stmtLowering context compileEnv
  supportedTypes vyperValue valueEncoding words list abiEncoderInput
  emitHelper exprLoweringProps venomExecSemantics venomInst venomState emitHelperProps

Theorem compile_log_store_data_cons:
  supported_scalar_type ty ==>
  compile_log_store_data cenv ((src,ty)::rest) buf off =
    do dst <- emit_op ADD [buf; Lit (n2w off)];
       compile_store_memory cenv src dst ty ty;
       compile_log_store_data cenv rest buf (off + type_memory_bytes cenv ty)
    od
Proof
  cheat
QED

Theorem log_scalar_memory_size:
  supported_scalar_type ty /\ evaluate_type tenv ty = SOME tv ==>
  type_memory_bytes cenv ty = type_memory_size tv
Proof
  cheat
QED

Theorem log_data_prefix_bounds:
  !cenv tys i off cap.
    i < LENGTH tys /\ off + SUM (MAP (type_memory_bytes cenv) tys) <= cap ==>
    off + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) +
      type_memory_bytes cenv (EL i tys) <= cap
Proof
  cheat
QED

Theorem log_data_address_run:
  emit_op ADD [buf; Lit (n2w off)] sa = (dst,sb) /\
  eval_operand buf s = SOME (n2w b) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand dst t = SOME (n2w (b + off)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem log_data_address_shape:
  emit_op ADD [buf; Lit (n2w off)] sa = (dst,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. dst = Var x ==> not_fresh_at sb x)
Proof
  cheat
QED

Theorem log_data_address_value:
  emit_op ADD [buf; Lit (n2w off)] sa = (dst,sb) /\
  eval_operand buf s = SOME (n2w b) /\
  expr_val_rel cx ty v src s /\
  (!x. src = Var x ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand dst t = SOME (n2w (b + off)) /\
    expr_val_rel cx ty v src t /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem log_data_field_run:
  emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm) /\
  compile_store_memory cenv src dst ty ty sm = ((),sb) /\
  supported_scalar_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ expr_val_rel cx ty v src s /\
  eval_operand buf s = SOME (n2w b) /\ b + off < dimword (:256) /\
  type_memory_bytes cenv ty < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at sa x) ==>
  ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
    val_in_memory tv v (b + off) q.vs_memory /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    (!a k. a + k <= b + off \/ b + off + type_memory_size tv <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  cheat
QED
