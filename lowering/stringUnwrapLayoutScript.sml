(* Compiler-only string unwrap boundaries; no runtime endpoint is selected. *)
Theory stringUnwrapLayout
Ancestors
  exprLowering context compileEnv exprLoweringProps emitHelper vyperValue
  vfmConstants arithmetic vyperTypeSystem loweringPosts bodyPtrDefs

Theorem unwrap_stack_value_identity:
  unwrap_value cenv (StackValue ty op) sa = (out,sb) ==>
  out = op /\ sb = sa
Proof
  simp[unwrap_value_def, comp_return_def] >> metis_tac[]
QED

Theorem string_memory_bytes_slots:
  type_memory_bytes cenv (BaseT (StringT max)) =
    32 * type_slot_size (BaseTV (StringT max)) /\
  (type_memory_bytes cenv (BaseT (StringT max)) + 31) DIV 32 =
    type_slot_size (BaseTV (StringT max))
Proof
  simp[type_memory_bytes_def, type_slot_size_def, word_size_def] >> decide_tac
QED

Theorem unwrap_string_memory_identity:
  p.ptr_location = LocMemory /\
  unwrap_value cenv (LocatedValue (BaseT (StringT max)) p) sa = (out,sb) ==>
  out = p.ptr_operand /\ sb = sa
Proof
  strip_tac >> gvs[unwrap_value_def, is_word_type_def, comp_return_def]
QED

Theorem unwrap_string_storage_layout:
  0 < max /\ (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  unwrap_value cenv (LocatedValue (BaseT (StringT max)) p) sa = (out,sb) ==>
  ?buf sc u.
    compile_alloc_buffer (32 * type_slot_size (BaseTV (StringT max))) sa = (buf,sc) /\
    compile_word_copy_loop p.ptr_operand buf.buf_operand
      (type_slot_size (BaseTV (StringT max))) p.ptr_location LocMemory F sc = (u,sb) /\
    out = buf.buf_operand
Proof
  `0 < max ==> type_slot_size (BaseTV (StringT max)) <> 1` by
    (simp[type_slot_size_def, word_size_def, DIV_EQ_0] >> decide_tac) >>
  strip_tac >>
  Cases_on `p.ptr_location = LocStorage` >> gvs[] >>
  gvs[unwrap_value_def, is_word_type_def, compile_ensure_in_memory_def,
    string_memory_bytes_slots, compile_storage_to_memory_def,
    compile_transient_to_memory_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem unwrap_string_code_layout:
  p.ptr_location = LocCode /\
  unwrap_value cenv (LocatedValue (BaseT (StringT max)) p) sa = (out,sb) ==>
  ?buf sc.
    compile_alloc_buffer (32 * type_slot_size (BaseTV (StringT max))) sa = (buf,sc) /\
    compile_imm_copy_to_memory cenv.ce_is_ctor cenv.ce_imm_alloca
      p.ptr_operand buf.buf_operand (type_slot_size (BaseTV (StringT max))) 0 sc = ((),sb) /\
    out = buf.buf_operand
Proof
  strip_tac >>
  gvs[unwrap_value_def, is_word_type_def, compile_ensure_in_memory_def,
    string_memory_bytes_slots, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem unwrap_string_storage_zero_layout:
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  unwrap_value cenv (LocatedValue (BaseT (StringT 0)) p) sa = (out,sb) ==>
  ?buf sc v sd u.
    compile_alloc_buffer 32 sa = (buf,sc) /\
    emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD)
      [p.ptr_operand] sc = (v,sd) /\
    emit_void MSTORE [buf.buf_operand;v] sd = (u,sb) /\ out = buf.buf_operand
Proof
  strip_tac >> Cases_on `p.ptr_location = LocStorage` >> gvs[] >>
  gvs[unwrap_value_def, is_word_type_def, compile_ensure_in_memory_def,
    type_memory_bytes_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem typed_assert_reason_string:
  type_stmt env ret_ty (Assert e (AssertReason se)) = SOME env' ==>
  ?max. expr_type se = BaseT (StringT max)
Proof
  simp[Once type_stmt_def] >> metis_tac[]
QED

Theorem string_located_representation:
  vv_holds cenv cx (BaseT (StringT max)) tv (LocatedValue ty p) es s ==>
  (ty = BaseT (StringT max) \/
   p.ptr_location = LocMemory /\ is_bytestring_type ty) /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocStorage \/
   p.ptr_location = LocTransient \/ p.ptr_location = LocCode)
Proof
  Cases_on `p.ptr_location` >> simp[vv_holds_def] >> metis_tac[]
QED

