Theory bodyPtrTypeBuiltinsWidenCopyShape
Ancestors
  exprLowering exprLoweringProps context compileEnv emitHelper emitHelperProps
  fragExec loweringHalt bodyPtrTypeBuiltinsCopyCounted
  list rich_list arithmetic venomInst

(* This compiler-only boundary avoids importing exprSimConvertBytes, whose
   unrelated, unowned proof currently fails static compilation. *)
Theorem widen_copy_compiler_parts:
  compile_bytestring_widen_copy capacity src n sa = (op,sb) ==>
  ?buf sm. compile_alloc_buffer capacity sa = (buf,sm) /\
    op = buf.buf_operand /\
    compile_copy_memory buf.buf_operand src n sm = ((),sb)
Proof
  simp[compile_bytestring_widen_copy_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem widen_copy_code_split:
  compile_bytestring_widen_copy capacity src n sa = (op,sb) /\
  fn_has_code sa sb fn ==>
  ?buf sm. compile_alloc_buffer capacity sa = (buf,sm) /\
    op = buf.buf_operand /\ compile_copy_memory buf.buf_operand src n sm = ((),sb) /\
    ci_mono sa sm /\ ci_mono sm sb /\
    fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
    emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb
Proof
  strip_tac >> drule widen_copy_compiler_parts >> strip_tac >>
  `ci_mono sa sm` by
    (qspecl_then [`capacity`, `sa`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sm sb` by
    (qspecl_then [`buf.buf_operand`, `src`, `n`, `sm`] mp_tac
       ci_mono_compile_copy_memory >> simp[]) >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  qexistsl_tac [`buf`, `sm`] >> simp[] >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  Cases_on `n = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def, emitted_insts_def]) >>
  `emit_void MCOPY [buf.buf_operand;src;Lit (n2w n)] sm = ((),sb)` by
    (Cases_on `n` >> gvs[compile_copy_memory_def]) >>
  drule emit_void_extends >> strip_tac >>
  irule emitted_insts_append >> conj_tac
  >- simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  first_assum ACCEPT_TAC
QED

Theorem widen_copy_run_split:
  compile_bytestring_widen_copy capacity src n sa = (op,sb) /\
  fn_has_code sa sb fn /\ run_inst_seq (emitted_insts sa sb) s0 = OK t ==>
  ?buf sm s. compile_alloc_buffer capacity sa = (buf,sm) /\
    op = buf.buf_operand /\ compile_copy_memory buf.buf_operand src n sm = ((),sb) /\
    ci_mono sa sm /\ ci_mono sm sb /\
    fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
    run_inst_seq (emitted_insts sa sm) s0 = OK s /\
    run_inst_seq (emitted_insts sm sb) s = OK t
Proof
  strip_tac >> drule_all widen_copy_code_split >> strip_tac >>
  `?s. run_inst_seq (emitted_insts sa sm) s0 = OK s` by
    (spose_not_then assume_tac >> drule run_inst_seq_append_err >>
     disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> gvs[] >> metis_tac[]) >>
  drule run_inst_seq_append >>
  disch_then (qspec_then `emitted_insts sm sb` assume_tac) >>
  qexistsl_tac [`buf`, `sm`, `s`] >> gvs[]
QED

Theorem widen_copy_split_certificate:
  compile_bytestring_widen_copy capacity src n sa = (op,sb) /\
  fn_has_code sa sb fn /\ run_inst_seq (emitted_insts sa sb) s0 = OK t ==>
  ?buf sm s. compile_alloc_buffer capacity sa = (buf,sm) /\
    op = buf.buf_operand /\ compile_copy_memory buf.buf_operand src n sm = ((),sb) /\
    ci_mono sa sm /\ ci_mono sm sb /\
    fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
    run_inst_seq (emitted_insts sa sm) s0 = OK s /\
    run_inst_seq (emitted_insts sm sb) s = OK t /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w capacity)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)
Proof
  strip_tac >> drule_all widen_copy_run_split >> strip_tac >>
  qexistsl_tac [`buf`, `sm`, `s`] >> simp[] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule compile_alloc_buffer_emission >> strip_tac >>
  `fn_has_code sx sm fn` by
    (drule_all fn_has_code_split >> simp[]) >>
  drule_all emit_inst_fn_member >> gvs[]
QED
