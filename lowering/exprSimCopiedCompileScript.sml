(* Definitional split of the allocate-before-read copied subscript path. *)
Theory exprSimCopiedCompile
Ancestors
  exprSimSubscriptArrayFramed exprLowering exprCallBounds vyperAST
  compileEnv valueEncoding

Theorem compile_expr_array_subscript_copied:
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  place_type ce obj = ValPT (ArrayT et bd) /\
  copies_subscript_base ce obj idx /\
  vv_type (FST (compile_expr ce ty obj sa)) = ArrayT et bd ==>
  ?bvv sm tmp sa1 src su sn iop si dst.
    compile_expr ce ty obj sa = (bvv,sm) /\
    vv_type bvv = ArrayT et bd /\
    compile_alloc_buffer (type_memory_bytes ce (ArrayT et bd)) sm = (tmp,sa1) /\
    unwrap_value ce bvv sa1 = (src,su) /\
    compile_store_memory ce src tmp.buf_operand (ArrayT et bd) (ArrayT et bd) su = ((),sn) /\
    lower_value compile_expr ce ty idx sn = (iop,si) /\
    compile_array_subscript tmp.buf_operand iop
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic _ => 0)
      (word_scale LocMemory) (elem_size_in_location ce LocMemory et)
      (is_signed_type (expr_type idx))
      (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocMemory) si = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst LocMemory)
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       compile_subscript_def, lower_value_def, expr_child_callback_def,
       comp_bind_def, comp_return_def, expr_size_def, expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[compile_snapshot_vv_def, is_word_type_def, compile_materialize_vv_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[contextTheory.vv_operand_def, contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
  goal_assum (drule_at Any) >> simp[]
QED
