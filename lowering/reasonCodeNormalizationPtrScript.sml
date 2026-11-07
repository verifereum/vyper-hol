(* Runtime code unwrap: allocation, checked copy, and semantic resources. *)
Theory reasonCodeNormalizationPtr
Ancestors
  reasonCodeResourcesPtr reasonCodeCopyPtr exprSimCopy
  storageNormalizationOwnershipPtr reasonPrefixPtr reasonAllocationFramePtr
  allocationPtr exprSimAlloc exprLoweringProps context compileEnv
  emitHelper emitHelperProps loweringPosts bodyPtrDefs venomState
  exprLowering loweringHalt
  ptrDiscipline words arithmetic fragExec fragGasPathPtr

Theorem code_unwrap_compile_parts:
  ~is_word_type ann /\ p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\
  type_memory_bytes cenv ann = 32*n /\
  (type_memory_bytes cenv ann+31) DIV 32 = n /\
  unwrap_value cenv (LocatedValue ann p) cc = (op,cb) ==>
  ?buf ca root.
    compile_alloc_buffer (32*n) cc = (buf,ca) /\
    buf.buf_operand = Var root /\ op = Var root /\
    compile_imm_copy_to_memory F cenv.ce_imm_alloca p.ptr_operand
      (Var root) n 0 ca = ((),cb)
Proof
  strip_tac >> qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `_ = (op,cb)` mp_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
