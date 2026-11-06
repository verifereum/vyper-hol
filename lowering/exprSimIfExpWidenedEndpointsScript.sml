Theory exprSimIfExpWidenedEndpoints
Ancestors
  exprSimIfExpWidenedAdapter exprLowering vyperAST exprSimConcatResult

Theorem compile_changed_ifexp_copy_endpoints:
  compile_expr ce ty e s0 = (vv,sa) /\
  lowered_value_type ce e <> expr_type e /\
  ~is_word_type (expr_type e) /\
  ~is_word_type (lowered_value_type ce e) /\
  ~same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sa = (op,sb) ==>
  ?buf sm src.
    compile_alloc_buffer (type_memory_bytes ce (expr_type e)) sa = (buf,sm) /\
    unwrap_value ce vv sm = (src,sm) /\
    compile_store_memory ce src buf.buf_operand (expr_type e)
      (lowered_value_type ce e) sm = ((),sb) /\
    op = buf.buf_operand
Proof
  strip_tac >>
  `!sm. ?src. unwrap_value ce vv sm = (src,sm)` by
    (Cases_on `e` >> gvs[lowered_value_type_def, expr_type_def]
     >- (Cases_on `t` >> gvs[oneline lowered_value_type_def, expr_type_def] >>
         rename1 `BaseT bt` >> Cases_on `bt` >> gvs[]
         >- (Cases_on `l` >> gvs[] >> qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
             simp[Once compile_expr_raw_def, compile_expr_body_def,
                  expr_type_def, compile_literal_vv_def,
                  compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
             rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
             simp[unwrap_value_def, contextTheory.base_ptr_def,
                  compileEnvTheory.comp_return_def]) >>
         rename1 `BytesT sz` >> Cases_on `sz` >> gvs[] >>
         Cases_on `l` >> gvs[] >> qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
         simp[Once compile_expr_raw_def, compile_expr_body_def,
              expr_type_def, compile_literal_vv_def,
              compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
         rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
         simp[unwrap_value_def, contextTheory.base_ptr_def,
              compileEnvTheory.comp_return_def])
     >- (Cases_on `b` >> gvs[oneline lowered_value_type_def, expr_type_def] >>
         drule concat_compile_shape >> strip_tac >> gvs[] >>
         simp[unwrap_value_def, contextTheory.base_ptr_def,
              compileEnvTheory.comp_return_def])
     >- (Cases_on `t0` >> gvs[oneline lowered_value_type_def, expr_type_def] >>
         qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
         simp[Once compile_expr_raw_def, compile_expr_body_def, expr_type_def,
              expr_size_def] >>
         simp[Once (cj 3 compile_expr_raw_def), compile_type_builtin_dispatch_body_def] >>
         rpt IF_CASES_TAC >>
         rpt (pairarg_tac >> gvs[]) >>
         simp[as_ptr_val_def] >> rpt (pairarg_tac >> gvs[]) >>
         strip_tac >> gvs[oneline as_ptr_val_def, AllCaseEqs()] >>
         simp[unwrap_value_def, contextTheory.mk_ptr_def,
              compileEnvTheory.comp_return_def]) >>
     Cases_on `c` >> gvs[oneline lowered_value_type_def, expr_type_def] >>
     qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
     simp[Once compile_expr_raw_def, compile_expr_body_def, expr_type_def,
          compile_call_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt IF_CASES_TAC >>
     rpt (pairarg_tac >> gvs[]) >>
     Cases_on `return_buf` >> gvs[] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     simp[unwrap_value_def, contextTheory.base_ptr_def,
          compileEnvTheory.comp_return_def]) >>
  drule_all compile_ifexp_copy_parts >> strip_tac >>
  first_x_assum (qspec_then `sm` strip_assume_tac) >>
  gvs[] >> metis_tac[]
QED
